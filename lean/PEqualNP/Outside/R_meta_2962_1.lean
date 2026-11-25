import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2962_1
    (hcore : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
      PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      PEqualNP.Core.IsLiftFixedPoint G C →
      ∃ R : Finset (Fin n),
        (∀ u v : Fin n, G.Adj u v →
          s(u, v) ∈ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) →
          u ∈ R ∨ v ∈ R) ∧
        R.card + ((PEqualNP.Core.maximalCores G C).biUnion
          (PEqualNP.TopForm.gammaE G C)).card ≤
          ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card +
            (PEqualNP.Core.maximalCores G C).card)
    (hdelete : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (M : Finset (Sym2 (Fin n))) (R T T' : Finset (Fin n)),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover G T →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (M : Set (Sym2 (Fin n)))) T' →
      (∀ u v : Fin n, G.Adj u v → s(u, v) ∈ (M : Set (Sym2 (Fin n))) → u ∈ R ∨ v ∈ R) →
      T.card ≤ T'.card + R.card) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool)
      (T T' : Finset (Fin n)),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
      PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      PEqualNP.Core.IsLiftFixedPoint G C →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover G T →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover
        (G.deleteEdges ((((PEqualNP.Core.maximalCores G C).biUnion
          (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))))) T' →
      ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤
        ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card +
          (PEqualNP.Core.maximalCores G C).card + T'.card := by
  intro n G hG C s T T' hB h4 hAO hF hL hT hT'
  let M : Finset (Sym2 (Fin n)) :=
    (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)
  let U : Finset ℕ :=
    (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)
  obtain ⟨R, hcover, hbound⟩ := hcore n G C s hB h4 hAO hF hL
  have hTbound := hdelete n G M R T T' hT hT' (by simpa [M] using hcover)
  have hbound' : R.card + M.card ≤ U.card + (PEqualNP.Core.maximalCores G C).card := by
    simpa [M, U] using hbound
  calc
    M.card + T.card = T.card + M.card := Nat.add_comm _ _
    _ ≤ (T'.card + R.card) + M.card := Nat.add_le_add_right hTbound _
    _ = (R.card + M.card) + T'.card := by omega
    _ ≤ (U.card + (PEqualNP.Core.maximalCores G C).card) + T'.card :=
      Nat.add_le_add_right hbound' _
    _ = U.card + (PEqualNP.Core.maximalCores G C).card + T'.card := by omega

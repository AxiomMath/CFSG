module

public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

open CFSG.ClassicalGroups.Orthogonal

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem card_rootGroupGL [Finite K] {Q : QuadraticForm K (ι → K)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {u : ι → K} (hu : Q u = 0) (hu0 : u ≠ 0) :
    Nat.card ↥(rootGroupGL Q u) = Nat.card K ^ (Fintype.card ι - 2) := by
  have hroot := card_rootGroup (Q := Q) hQ hu hu0
  rw [Module.finrank_fintype_fun_eq_card] at hroot
  rw [rootGroupGL, Subgroup.comap_equiv_eq_map_symm' (toLinEquiv ι K),
    Subgroup.card_map_of_injective (toLinEquiv ι K).symm.injective]
  exact hroot

theorem isPGroup_rootGroupGL [Finite K] [CharP K 2] {Q : QuadraticForm K (ι → K)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {u : ι → K} (hu : Q u = 0) (hu0 : u ≠ 0) :
    IsPGroup 2 ↥(rootGroupGL Q u) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  refine IsPGroup.of_card (n := m * (Fintype.card ι - 2)) ?_
  rw [card_rootGroupGL hQ hu hu0, Nat.card_eq_fintype_card, hm, pow_mul]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

end

module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4SetupModel
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4SylowCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4Clauses
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4ClassClauses
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4Inversion
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4SubgroupClasses
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K33ExceptionalRanks
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallD4Par

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Is3D4)

private theorem r891D4Setup_sylowConj {X : Type} [Group X] [Finite X] {n : ℕ} {S B : Subgroup X}
    (h : R891D4Setup n S B) {P : Subgroup X} (hP : IsSylowOf 3 P ⊤) :
    ∃ (S' B' : Subgroup X) (s' : X), R891D4Setup n S' B' ∧ s' ∈ S' ∧ s' ^ 3 = 1 ∧
      s' ≠ 1 ∧ ZOf P = zpowers s' := by
  obtain ⟨s, hs, hs3, hs1, g, hZ⟩ := h.exists_zOf_eq hP
  refine ⟨S.map (MulAut.conj g).toMonoidHom, B.map (MulAut.conj g).toMonoidHom,
    (MulAut.conj g) s, h.map (MulAut.conj g), Subgroup.mem_map_of_mem _ hs, ?_, ?_, ?_⟩
  · have hpow := map_pow (MulAut.conj g).toMonoidHom s 3
    rw [hs3, map_one] at hpow
    simpa using hpow.symm
  · intro h1
    refine hs1 ((MulAut.conj g).injective ?_)
    rw [map_one]
    exact h1
  · rw [hZ, MonoidHom.map_zpowers]
    rfl

theorem r891D4Core_holds :
    R891D4Core := by
  intro X _ _ n hX
  obtain ⟨S, B, h⟩ := exists_r891D4Setup hX
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hZ3 : ∀ P : Subgroup X, IsSylowOf 3 P ⊤ → Nat.card (ZOf P) = 3 := by
    intro P hP
    obtain ⟨_, _, s', -, -, hs'3, hs'1, hZ⟩ := r891D4Setup_sylowConj h hP
    rw [hZ, Nat.card_zpowers, orderOf_eq_prime hs'3 hs'1]
  refine ⟨CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.center_eq_bot_of_is3D4 hX,
    pRank_three_eq_two_of_lieModel_trialityD4 hX, hZ3, ?_, ?_⟩
  · intro P hP
    obtain ⟨_, _, s', h', hs', hs'3, hs'1, hZ⟩ := r891D4Setup_sylowConj h hP
    exact ⟨r891_exists_inv_zOf_of_card_three hX hP (hZ3 P hP),
      h'.sylow_clauses hP hs' hs'3 hs'1 hZ⟩
  · intro P hP A hA3 hA
    obtain ⟨_, _, s', h', hs', hs'3, hs'1, hZ⟩ := r891D4Setup_sylowConj h hP
    exact ⟨r891_subgroup_classes hX (hZ3 P hP) hA3 hA,
      h'.class_clauses hs' hs'3 hs'1 hZ hA3 hA⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

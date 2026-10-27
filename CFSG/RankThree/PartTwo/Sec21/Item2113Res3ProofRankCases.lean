module

import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofRankTools
import CFSG.RankThree.Native.MathieuRealThree
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative
public import CFSG.RankThree.PartTwo.Sec21.Item2113ProofStatements
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint
open Subgroup

theorem isPerfect_iOf218 {G : Type} [Group G] (K : Subgroup G) (d : G) :
    Group.IsPerfect (iOf218 K d) :=
  isPerfect_map_subtype LocalCores.layer_isPerfect

theorem lBar_facts_of_item219 {G : Type} [Group G] [Finite G]
    {K : Subgroup G} {d : G}
    (h : (Nonempty (K ≃* NativeSporadic.He) ∧
            Sec4.IsTripleCover (iOf218 K d) (alternatingGroup (Fin 7))) ∨
          ((Nonempty (lBar K ≃* NativeSporadic.M24) ∨ Nonempty (lBar K ≃* NativeSporadic.J2) ∨
              Nonempty (lBar K ≃* NativeSporadic.Ru)) ∧
            Sec4.IsTripleCover (lBar (iOf218 K d)) (alternatingGroup (Fin 6))) ∨
          (Nonempty (K ≃* NativeSporadic.J4) ∧
            Nat.card (Subgroup.center (iOf218 K d)) = 6 ∧
            Nonempty (iOf218 K d ⧸ Subgroup.center (iOf218 K d) ≃* NativeSporadic.M22)) ∨
          (∃ n : ℕ, 0 < n ∧ Even n ∧
            (ChevalleyExceptionalModel (lBar K) .G2 2 n ∨
              ChevalleyExceptionalModel (lBar K) .trialityD4 2 n) ∧
            Nonempty (lBar (iOf218 K d) ≃* SL3 n))) :
    IsQuasisimple (lBar (iOf218 K d)) ∧
      ∃ w : lBar (iOf218 K d), w ^ 3 = 1 ∧ w ∉ center (lBar (iOf218 K d)) := by
  have hIp := isPerfect_iOf218 K d
  rcases h with ⟨-, -, ⟨e⟩⟩ | ⟨-, -, ⟨e⟩⟩ | ⟨-, -, ⟨e⟩⟩ | ⟨n, -, -, -, ⟨e⟩⟩
  · have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
    obtain ⟨s, m, hs3, hs1, hm⟩ := alternating_seven_real
    obtain ⟨hq, y, hy3, hy⟩ := isQuasisimple_and_exists_of_real hIp e hs3 hs1 hm
    exact quotient_theta_of_isQuasisimple hq hy3 hy
  · have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
    obtain ⟨s, m, hs3, hs1, hm⟩ := alternating_six_real
    exact isQuasisimple_and_exists_of_real inferInstance e hs3 hs1 hm
  · have : IsSimpleGroup NativeSporadic.M22 := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    obtain ⟨s, -, m, hs, -, -, hm⟩ := Native.m22_witness
    have hs3 : s ^ 3 = 1 := hs ▸ pow_orderOf_eq_one s
    have hs1 : s ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hs; norm_num at hs
    obtain ⟨hq, y, hy3, hy⟩ := isQuasisimple_and_exists_of_real hIp e hs3 hs1 hm
    exact quotient_theta_of_isQuasisimple hq hy3 hy
  · obtain ⟨g, hg3, hg⟩ := specialLinear_three_exists (GaloisField 2 n)
    refine ⟨LocalCores.isQuasisimple_of_mulEquiv e.symm
      (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3 _
        (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))), e.symm g,
      by rw [← map_pow, hg3, map_one], fun hc => hg ?_⟩
    rw [mem_center_iff] at hc ⊢
    intro k
    simpa using congrArg e (hc (e.symm k))

end CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof

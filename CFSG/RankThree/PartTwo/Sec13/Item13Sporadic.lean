module

public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
import CFSG.Sporadic.Mathieu.M22
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem isPerfect_center_of_isSimpleGroup {S : Type*} [Group S] (hS : IsSimpleGroup S)
    (hp : ¬ (Nat.card S).Prime) : Group.IsPerfect S ∧ Subgroup.center S = ⊥ := by
  obtain ⟨a, b, hab⟩ : ∃ a b : S, a * b ≠ b * a := by
    by_contra h
    push Not at h
    let _ : CommGroup S := { ‹Group S› with mul_comm := h }
    exact hp (CommGroup.is_simple_iff_prime_card.mp hS)
  refine ⟨Group.isPerfect_def.mpr ?_, ?_⟩
  · rcases hS.eq_bot_or_eq_top_of_normal (commutator S) with h | h
    · exfalso
      apply hab
      have hmem : ⁅a, b⁆ ∈ commutator S := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    · exact h
  · rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      apply hab
      exact Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a

theorem sporadicModels131 : SporadicModels131 := by
  refine ⟨isPerfect_center_of_isSimpleGroup Sporadic.Mathieu.fam_m22_simplicity.2.2 ?_,
    isPerfect_center_of_isSimpleGroup Sporadic.Mathieu.fam_m12_simplicity.2.2 ?_,
    isPerfect_center_of_isSimpleGroup Sporadic.J2.fam_j2_simplicity.2.2 ?_⟩
  · rw [Sporadic.Mathieu.card_M22]
    norm_num
  · rw [Sporadic.Mathieu.card_M12]
    norm_num
  · rw [Sporadic.J2.card_J2]
    norm_num

end CFSG.RankThree.PartTwo.Sec13

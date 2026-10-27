module

public import CFSG.LocalAnalysis.SignalizerFunctor.CoprimeClassDegreeScalarAlternative
public import Mathlib.Algebra.Group.ConjFinite

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem conjugacyClassFinset_card_eq_index
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    (element : GroupType) : (conjugacyClassFinset element).card = (Subgroup.centralizer {element}).index := by
  classical
  let : Fintype GroupType := Fintype.ofFinite GroupType
  let stabilizer := MulAction.stabilizer (ConjAct GroupType) element
  have mapped : stabilizer.map (ConjAct.ofConjAct (G := GroupType)).toMonoidHom = Subgroup.centralizer {element} := by
    ext selected
    constructor
    · rintro ⟨conjugator, member, rfl⟩
      change conjugator ∈ MulAction.stabilizer (ConjAct GroupType) element at member
      rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def] at member
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul).mp member
    · intro member
      refine ⟨ConjAct.toConjAct selected, ?_, ConjAct.ofConjAct_toConjAct selected⟩
      change ConjAct.toConjAct selected ∈ MulAction.stabilizer (ConjAct GroupType) element
      rw [MulAction.mem_stabilizer_iff, ConjAct.toConjAct_smul,
        (Subgroup.mem_centralizer_singleton_iff.mp member), mul_assoc, mul_inv_cancel, mul_one]
  have stabilizer_card : Nat.card stabilizer = Nat.card (Subgroup.centralizer {element}) := by
    rw [← mapped]
    exact Nat.card_congr ((ConjAct.ofConjAct (G := GroupType)).subgroupMap stabilizer).toEquiv
  have class_card : (conjugacyClassFinset element).card =
      Nat.card GroupType / Nat.card stabilizer := by
    unfold conjugacyClassFinset
    rw [Set.Finite.card_toFinset, ConjClasses.card_carrier]
    simp only [Nat.card_eq_fintype_card, stabilizer]
  rw [class_card, stabilizer_card]
  exact (Nat.eq_div_of_mul_eq_left Nat.card_pos.ne' (Subgroup.centralizer {element}).index_mul_card).symm

theorem conjugacyClassFinset_card_dvd_group
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    (element : GroupType) : (conjugacyClassFinset element).card ∣ Nat.card GroupType := by
  rw [conjugacyClassFinset_card_eq_index]
  exact (Subgroup.centralizer {element}).index_dvd_card

theorem sylow_central_element_class_coprime
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (sylow : Sylow prime GroupType)
    (element : sylow) (central : element ∈ Subgroup.center sylow) :
    Nat.Coprime prime (conjugacyClassFinset (element : GroupType)).card := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  have sylow_le : (sylow : Subgroup GroupType) ≤ Subgroup.centralizer {(element : GroupType)} := by
    intro selected member
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg (fun candidate : sylow => (candidate : GroupType))
      (Subgroup.mem_center_iff.mp central ⟨selected, member⟩)
  rw [conjugacyClassFinset_card_eq_index]
  exact prime_prime.coprime_iff_not_dvd.mpr
    (fun divides => sylow.not_dvd_index (divides.trans (Subgroup.index_dvd_of_le sylow_le)))

end CFSG.SignalizerFunctor.Helpers

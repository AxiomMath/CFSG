module

public import CFSG.Quasithin.EmptyFaithful.S146zRSL

public section

namespace CFSG.Quasithin

section Ambient

open scoped MatrixGroups

variable {F : Type*} [Field F] {X : Type*} [Group X]

theorem sl2_le_normalizer_of_solvable_ambient [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F)
    {N₁ : Subgroup X} (e : ↥N₁ ≃* SL(2, F)) {U A : Subgroup X} (hUN : U ≤ N₁) (hAN : A ≤ N₁)
    (hU : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.relIndex N₁) (hUA : U ≤ A) (hA : Group.IsSolvable A) :
    A ≤ Subgroup.normalizer (U : Set X) := by
  have hU' : IsPGroup 2 (U.subgroupOf N₁) := hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUN).symm
  have hUA' : U.subgroupOf N₁ ≤ A.subgroupOf N₁ := Subgroup.subgroupOf_mono N₁ hUA
  have hA' : Group.IsSolvable (A.subgroupOf N₁) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hAN).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hAN).symm.surjective
  have h := sl2_le_normalizer_of_solvable hq e hU' hUi hUA' hA'
  rw [← Subgroup.subgroupOf_normalizer_eq hUN] at h
  intro x hx
  exact h (show (⟨x, hAN hx⟩ : N₁) ∈ A.subgroupOf N₁ from hx)

theorem sl2_normalizer_inf_solvable_dvd [Finite F] [CharP F 2]
    {N₁ : Subgroup X} (e : ↥N₁ ≃* SL(2, F)) {U : Subgroup X}
    (hUN : U ≤ N₁) (hU : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.relIndex N₁) :
    Group.IsSolvable ↥(Subgroup.normalizer (U : Set X) ⊓ N₁) ∧
      (Nat.card F - 1) ∣ Nat.card ↥(Subgroup.normalizer (U : Set X) ⊓ N₁) := by
  have hU' : IsPGroup 2 (U.subgroupOf N₁) := hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUN).symm
  obtain ⟨hs, hd⟩ := sl2_normalizer_solvable_dvd e hU' hUi
  have hN : (Subgroup.normalizer (U : Set X) ⊓ N₁).subgroupOf N₁ =
      Subgroup.normalizer ((U.subgroupOf N₁ : Subgroup N₁) : Set N₁) := by
    rw [Subgroup.inf_subgroupOf_right, Subgroup.subgroupOf_normalizer_eq hUN]
  let φ : ↥(Subgroup.normalizer (U : Set X) ⊓ N₁) ≃*
      ↥(Subgroup.normalizer ((U.subgroupOf N₁ : Subgroup N₁) : Set N₁)) :=
    (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : Subgroup.normalizer (U : Set X) ⊓ N₁ ≤ N₁)).symm.trans
      (MulEquiv.subgroupCongr hN)
  exact ⟨Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective,
    (Nat.card_congr φ.toEquiv) ▸ hd⟩

end Ambient

end CFSG.Quasithin

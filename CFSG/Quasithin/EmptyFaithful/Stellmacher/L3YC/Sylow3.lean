module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin

namespace Stellmacher.L3YC

section Sylow3

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_order_three {H : Subgroup G} (hH : padicValNat 3 (Nat.card H) = 1) {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) :
    ∃ g ∈ H, g * a * g⁻¹ ∈ Subgroup.zpowers b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let a' : H := ⟨a, ha⟩
  let b' : H := ⟨b, hb⟩
  have hcard : ∀ c : H, orderOf c = 3 →
      Nat.card (Subgroup.zpowers c) = 3 ^ (Nat.card H).factorization 3 := by
    intro c hc
    rw [Nat.card_zpowers, hc, Nat.factorization_def _ Nat.prime_three, hH]
    simp
  have ha' : orderOf a' = 3 := by rw [Subgroup.orderOf_mk]; exact ha3
  have hb' : orderOf b' = 3 := by rw [Subgroup.orderOf_mk]; exact hb3
  let Pa : Sylow 3 H := Sylow.ofCard (Subgroup.zpowers a') (hcard a' ha')
  let Pb : Sylow 3 H := Sylow.ofCard (Subgroup.zpowers b') (hcard b' hb')
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Pa Pb
  refine ⟨g, g.2, ?_⟩
  have h1 : ((g • Pa : Sylow 3 H) : Subgroup H) = Subgroup.zpowers b' := by
    rw [hg]; rfl
  have h2 : g * a' * g⁻¹ ∈ ((g • Pa : Sylow 3 H) : Subgroup H) := by
    rw [Sylow.coe_subgroup_smul]
    exact ⟨a', Subgroup.mem_zpowers a', by simp [MulAut.conj_apply]⟩
  rw [h1] at h2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h2
  exact ⟨k, by simpa [b'] using congrArg Subtype.val hk⟩

theorem exists_conj_le_of_odd_relIndex {X S E : Subgroup G} (hSX : S ≤ X) (hEX : E ≤ X)
    (hS2 : IsPGroup 2 S) (hSodd : ¬ 2 ∣ S.relIndex X) (hE2 : IsPGroup 2 E) :
    ∃ h ∈ X, ∀ e ∈ E, h⁻¹ * e * h ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS'2 : IsPGroup 2 (S.subgroupOf X) := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSX).symm
  have hE'2 : IsPGroup 2 (E.subgroupOf X) := hE2.of_equiv (Subgroup.subgroupOfEquivOfLe hEX).symm
  let Ps : Sylow 2 X := hS'2.toSylow hSodd
  obtain ⟨Q, hEQ⟩ := hE'2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Ps Q
  refine ⟨(g : G), g.2, fun e he => ?_⟩
  have h1 : (⟨e, hEX he⟩ : X) ∈ (Q : Subgroup X) := hEQ (Subgroup.mem_subgroupOf.mpr he)
  rw [← hg, Sylow.coe_subgroup_smul] at h1
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.mp h1
  have hs' : s ∈ S.subgroupOf X := hs
  have : (g : G)⁻¹ * e * (g : G) = (s : G) := by
    have := congrArg Subtype.val hse
    simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, InvMemClass.coe_inv] at this
    rw [← this]; group
  rw [this]
  exact Subgroup.mem_subgroupOf.mp hs'

omit [Finite G] in
theorem orderOf_conj_eq (g y : G) : orderOf (g * y * g⁻¹) = orderOf y := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

end Sylow3

end Stellmacher.L3YC

end CFSG.Quasithin

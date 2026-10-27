module

public import CFSG.Timmesfeld.Bridge.Asc72YTri

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.BenderSuzuki CFSG.Open

theorem mulEquiv_of_card_center_le_four {B : Type*} [Group B] [Finite B] (hB : IsBenderGroup B)
    (Q : Sylow 2 B) (h4 : Nat.card (Subgroup.center (Q : Subgroup B)) ≤ 4) :
    Nonempty (B ≃* PSL2Model 2) ∨ Nonempty (B ≃* PSU3Model 2) := by
  have hle : ∀ m : ℕ, 2 ^ m ≤ 4 → m ≤ 2 := fun m hm => by
    by_contra h
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases hB with ⟨m, hm, e⟩ | ⟨m, hm, e⟩ | ⟨m, hm, e⟩
  · have : Finite (PSL2Model m) := Finite.of_surjective e e.surjective
    have hBB := (bender_psl2_borel_full m hm).map_mulEquiv e.symm
    rw [(hBB Q).2.2.2.1] at h4
    obtain rfl : m = 2 := le_antisymm (hle m h4) hm
    exact Or.inl ⟨e⟩
  · exfalso
    have hmodel : SzModel m = Sz m := CFSG.Models.benderSzModel_eq_sz m
    let e' : B ≃* Sz m := e.trans (MulEquiv.subgroupCongr hmodel)
    have : Finite (Sz m) := Finite.of_surjective e' e'.surjective
    have hBB := (bender_suzuki_borel_full m hm).map_mulEquiv e'.symm
    rw [(hBB Q).2.2.2.1] at h4
    have := hle _ h4
    omega
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hmodel : PSU3Model m = PSU3 2 m := CFSG.Models.benderPSU3Model_eq_psu3 m
    let e' : B ≃* PSU3 2 m := e.trans (MulEquiv.subgroupCongr hmodel)
    have : Finite (PSU3 2 m) := Finite.of_surjective e' e'.surjective
    have hBB := (bender_psu3_borel_full m hm).map_mulEquiv e'.symm
    rw [(hBB Q).2.2.2.1] at h4
    obtain rfl : m = 2 := le_antisymm (hle m h4) hm
    exact Or.inr ⟨e⟩

namespace CentralQuot

theorem odd_card_center {Y : Type} [Group Y] [Finite Y] (h : CFSG.pCore 2 Y = ⊥) :
    Odd (Nat.card (Subgroup.center Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hodd)
  have hx1 : (x : Y) ≠ 1 := by
    intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    omega
  have hxx : (x : Y) * x = 1 := by
    have h2 : orderOf (x : Y) = 2 := by rw [Subgroup.orderOf_coe, hx]
    rw [← pow_two, ← h2, pow_orderOf_eq_one]
  exact hx1 (eq_one_of_mem_center h x.2 hxx)

variable {X : Type} [Group X] [Finite X] {z : X} [(Subgroup.zpowers z).Normal]

theorem mem_zpowers_of_mem_zStar (hzz : z * z = 1) (hO2 : CFSG.pCore 2 X ≤ Subgroup.zpowers z)
    {T : Subgroup X} (hT : IsPGroup 2 T) {y : X} (hyT : y ∈ T) (hy : y ∈ zStar X) :
    y ∈ Subgroup.zpowers z := by
  have hO2' := pCore_quot_eq_bot hzz hO2
  have hyc : mk z y ∈ Subgroup.center (X ⧸ Subgroup.zpowers z) := by
    rw [← zStar_eq_center_of_pCore_eq_bot hO2']
    rw [zStar_eq_comap hzz] at hy
    exact hy
  have hodd : Odd (orderOf (mk z y)) := by
    have h1 := orderOf_dvd_natCard (⟨mk z y, hyc⟩ : Subgroup.center (X ⧸ Subgroup.zpowers z))
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat (odd_card_center hO2') h1
  have h1 := eq_one_of_isPGroup_of_odd (hT.map (mk z)) ⟨y, hyT, rfl⟩ hodd
  exact (QuotientGroup.eq_one_iff y).mp h1

section Count

variable
  (hzc : z ∈ Subgroup.center X) (hzz : z * z = 1) {E : Set X} (hS : Setup X E) (hzE : z ∉ E)
  (hdisc : Disconnected E) {a b : X} (ha : a ∈ E) (hb : b ∈ E) (hab : a ≠ b) (hc : Commute a b)
  (habz : a * b * z ∈ E) (hO2 : CFSG.pCore 2 X ≤ Subgroup.zpowers z)
include hzc hzz hS hzE hdisc ha hb hab hc habz hO2

theorem card_center_sylow_le (T : Sylow 2 X) (hzT : z ∈ T) (Q : Sylow 2 (X ⧸ zStar X))
    (hQ : (Q : Subgroup (X ⧸ zStar X)) = (T : Subgroup X).map (QuotientGroup.mk' (zStar X))) :
    Nat.card (Subgroup.center (Q : Subgroup (X ⧸ zStar X))) ≤ (E ∩ (T : Set X)).ncard + 1 := by
  classical
  obtain ⟨-, hB'⟩ := quot_facts hzc hzz hS hzE hdisc ha hb hab hc habz
  have hB := isBenderGroup_zStar hzz hB'
  set π := QuotientGroup.mk' (zStar X) with hπdef
  have hzS : z ∈ zStar X := pCore_le_zStar (mem_pCore hzz)
  have hπz : π z = 1 := (QuotientGroup.eq_one_iff z).mpr hzS
  have himg : ∀ x : Subgroup.center (Q : Subgroup (X ⧸ zStar X)),
      ((x : (Q : Subgroup (X ⧸ zStar X))) : X ⧸ zStar X) ∈
        insert (1 : X ⧸ zStar X) (π '' (E ∩ (T : Set X))) := by
    intro x
    by_cases hx1 : ((x : (Q : Subgroup (X ⧸ zStar X))) : X ⧸ zStar X) = 1
    · exact Or.inl hx1
    right
    have hxQ := (x : (Q : Subgroup (X ⧸ zStar X))).2
    have hxc : ∀ y ∈ (Q : Subgroup (X ⧸ zStar X)),
        Commute ((x : (Q : Subgroup (X ⧸ zStar X))) : X ⧸ zStar X) y := fun y hy =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2 ⟨y, hy⟩)).symm
    have hxx := IsBenderGroup.mul_self_eq_one_of_commute hB Q hxQ hxc
    have hxQ' : ((x : (Q : Subgroup (X ⧸ zStar X))) : X ⧸ zStar X) ∈
        (T : Subgroup X).map (QuotientGroup.mk' (zStar X)) := hQ ▸ hxQ
    obtain ⟨t, htT, hxt⟩ := hxQ'
    rw [← hxt] at hxx hx1 ⊢
    have htt : t * t ∈ zStar X := by
      rw [← map_mul] at hxx
      exact (QuotientGroup.eq_one_iff _).mp hxx
    have htt' := mem_zpowers_of_mem_zStar hzz hO2 T.isPGroup' (T.mul_mem htT htT) htt
    rcases involution_cases hzc hzz hS hzE hdisc ha hb hab hc habz hO2 htt' with h | h | h
    · exfalso
      apply hx1
      rcases (mem_zpowers_of_mul_self hzz).mp h with rfl | rfl
      · exact map_one π
      · exact hπz
    · exact ⟨t, ⟨h, htT⟩, rfl⟩
    · exact ⟨t * z, ⟨h, T.mul_mem htT hzT⟩, by rw [map_mul, hπz, mul_one]⟩
  calc Nat.card (Subgroup.center (Q : Subgroup (X ⧸ zStar X)))
      ≤ Nat.card ↥(insert (1 : X ⧸ zStar X) (π '' (E ∩ (T : Set X)))) :=
        Nat.card_le_card_of_injective (fun x => ⟨_, himg x⟩) (fun x y hxy =>
          Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hxy)))
    _ = (insert (1 : X ⧸ zStar X) (π '' (E ∩ (T : Set X)))).ncard := Nat.card_coe_set_eq _
    _ ≤ (π '' (E ∩ (T : Set X))).ncard + 1 := Set.ncard_insert_le _ _
    _ ≤ (E ∩ (T : Set X)).ncard + 1 := by
        have := Set.ncard_image_le (f := π) (Set.toFinite (E ∩ (T : Set X)))
        omega

end Count

end CentralQuot

end CFSG.Timmesfeld.Bridge.Asc72

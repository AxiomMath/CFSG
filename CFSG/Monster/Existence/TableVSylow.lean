module

public import CFSG.Monster.Existence.ELevelBasic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short

theorem val_mem_Jstar_of_mem_cent2 {y : MGriess} (hy : y ∈ cent2 tGriess xGriess) :
    (y : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Jstar := by
  refine ⟨?_, ?_⟩
  · rw [← map_cent_xGriess]
    exact ⟨y, hy.2, rfl⟩
  · show (y : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Subgroup.centralizer {tStar}
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hy.1)

@[expose] noncomputable def cent2ToCgen : ↥(cent2 tGriess xGriess) →* Cgen where
  toFun y := ⟨(y : MGriess), Jstar_le_Cgen (val_mem_Jstar_of_mem_cent2 y.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem cent2ToCgen_injective : Function.Injective cent2ToCgen := fun _ _ h =>
  Subtype.ext (Subtype.ext (congrArg (fun g : Cgen => (g : SpaceB ≃ₗ[ℚ] SpaceB)) h))

theorem coe_cent2ToCgen (y : ↥(cent2 tGriess xGriess)) :
    ((cent2ToCgen y : Cgen) : SpaceB ≃ₗ[ℚ] SpaceB) = ((y : MGriess) : SpaceB ≃ₗ[ℚ] SpaceB) := rfl

@[expose] noncomputable def cent2ToCbar : ↥(cent2 tGriess xGriess) →* Cbar :=
  kappa.comp cent2ToCgen

theorem cent2ToCbar_mem_Jbar (y : ↥(cent2 tGriess xGriess)) : cent2ToCbar y ∈ Jbar :=
  ⟨cent2ToCgen y, Subgroup.mem_subgroupOf.2 (val_mem_Jstar_of_mem_cent2 y.2), rfl⟩

theorem cent2ToCbar_eq_one_iff (y : ↥(cent2 tGriess xGriess)) :
    cent2ToCbar y = 1 ↔ (y : MGriess) = 1 ∨ (y : MGriess) = tGriess := by
  rw [cent2ToCbar, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_kappa, Zstar,
    Short.mem_zpowers_iff_of_orderOf_eq_two]
  · constructor
    · rintro (h | h)
      · left
        exact Subtype.ext (congrArg (fun g : Cgen => (g : SpaceB ≃ₗ[ℚ] SpaceB)) h)
      · right
        exact Subtype.ext (congrArg (fun g : Cgen => (g : SpaceB ≃ₗ[ℚ] SpaceB)) h)
    · rintro (h | h)
      · left
        apply Subtype.ext
        show ((y : MGriess) : SpaceB ≃ₗ[ℚ] SpaceB) = 1
        rw [h]
        rfl
      · right
        apply Subtype.ext
        show ((y : MGriess) : SpaceB ≃ₗ[ℚ] SpaceB) = tStar
        rw [h]
        rfl
  · have h := orderOf_injective Cgen.subtype Subtype.coe_injective tStarC
    rw [Subgroup.coe_subtype] at h
    rw [← h]
    exact orderOf_tStar

theorem tGriess_ne_one' : tGriess ≠ 1 := fun h => by
  have h2 := orderOf_tGriess
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem xGriess_comm_tGriess : xGriess * tGriess = tGriess * xGriess :=
  ((Subgroup.mem_centralizer_iff.1 xGriess_mem_centralizer_FE) tGriess
    (mem_FE.2 (Or.inr (Or.inl rfl)))).symm

theorem tGriess_mem_cent2_tx : tGriess ∈ cent2 tGriess xGriess :=
  ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl,
    Subgroup.mem_centralizer_singleton_iff.2 xGriess_comm_tGriess.symm⟩

theorem xGriess_mem_cent2_tx : xGriess ∈ cent2 tGriess xGriess :=
  ⟨Subgroup.mem_centralizer_singleton_iff.2 xGriess_comm_tGriess,
    Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem cent2ToCbar_xH : cent2ToCbar ⟨xGriess, xGriess_mem_cent2_tx⟩ = xbar := rfl

theorem mem_center_of_cent2 {z : MGriess} (hz : z = tGriess ∨ z = xGriess)
    (hzH : z ∈ cent2 tGriess xGriess) :
    (⟨z, hzH⟩ : ↥(cent2 tGriess xGriess)) ∈ Subgroup.center ↥(cent2 tGriess xGriess) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  rcases hz with rfl | rfl
  · exact Subgroup.mem_centralizer_singleton_iff.1 g.2.1
  · exact Subgroup.mem_centralizer_singleton_iff.1 g.2.2

theorem factorization_two_pow_mul_odd {k m : ℕ} (hm : Odd m) :
    (2 ^ k * m).factorization 2 = k := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact absurd hm (by decide)
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm.not_two_dvd_nat, add_zero]

theorem le_sylow_of_le_center {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {Z : Subgroup H} (hZ : Z ≤ Subgroup.center H) (hp : IsPGroup p Z) (P : Sylow p H) :
    Z ≤ P := by
  have : Z.Normal := Subgroup.normal_of_le_center hZ
  exact hp.le_sylow_of_normal P

theorem mem_sylow_of_mem_center {H : Type*} [Group H] [Finite H] {z : H}
    (hz : z ∈ Subgroup.center H) (hz2 : orderOf z = 2) (P : Sylow 2 H) : z ∈ P := by
  refine le_sylow_of_le_center (Z := Subgroup.zpowers z) ?_ ?_ P (Subgroup.mem_zpowers z)
  · rw [Subgroup.zpowers_le]
    exact hz
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hz2, pow_one]

theorem center_sylow_cent2_tGriess_xGriess
    (hcardH : Nat.card ↥(cent2 tGriess xGriess) =
      2 ^ 42 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23)
    (T : Subgroup MGriess) (hT : T ≤ cent2 tGriess xGriess) (hcard : Nat.card T = 2 ^ 42)
    (y : MGriess) :
    (y ∈ T ∧ ∀ s ∈ T, y * s = s * y) ↔
      (y = 1 ∨ y = tGriess ∨ y = xGriess ∨ y = tGriess * xGriess) := by
  classical
  set H := cent2 tGriess xGriess with hHdef
  have hT' : Nat.card (T.subgroupOf H) = 2 ^ 42 := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv
  have hfac : (Nat.card ↥H).factorization 2 = 42 := by
    rw [hcardH, show 2 ^ 42 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23 = 2 ^ 42 * (3 ^ 6 * 5 ^ 3 * 7 * 11 * 23)
      by ring]
    exact factorization_two_pow_mul_odd (by decide)
  let P : Sylow 2 ↥H := Sylow.ofCard (T.subgroupOf H) (by rw [hT', hfac])
  have hP : (P : Subgroup ↥H) = T.subgroupOf H := rfl
  set tH : ↥H := ⟨tGriess, tGriess_mem_cent2_tx⟩ with htH
  set xH : ↥H := ⟨xGriess, xGriess_mem_cent2_tx⟩ with hxH
  have htZ := mem_center_of_cent2 (Or.inl rfl) tGriess_mem_cent2_tx
  have hxZ := mem_center_of_cent2 (Or.inr rfl) xGriess_mem_cent2_tx
  have ht2 : orderOf tH = 2 := by
    rw [← orderOf_injective H.subtype H.subtype_injective tH]
    exact orderOf_tGriess
  have hx2 : orderOf xH = 2 := by
    rw [← orderOf_injective H.subtype H.subtype_injective xH]
    exact orderOf_xGriess
  have htT : tGriess ∈ T := by
    have h : tH ∈ (P : Subgroup ↥H) := mem_sylow_of_mem_center htZ ht2 P
    rw [hP, Subgroup.mem_subgroupOf] at h
    exact h
  have hxT : xGriess ∈ T := by
    have h : xH ∈ (P : Subgroup ↥H) := mem_sylow_of_mem_center hxZ hx2 P
    rw [hP, Subgroup.mem_subgroupOf] at h
    exact h
  constructor
  · rintro ⟨hyT, hyc⟩
    set φ := cent2ToCbar.comp (T.subgroupOf H).subtype with hφ
    have hker : Nat.card φ.ker = 2 := by
      rw [Nat.card_eq_two_iff' (1 : φ.ker)]
      have htmem : (⟨tH, Subgroup.mem_subgroupOf.2 htT⟩ : ↥(T.subgroupOf H)) ∈ φ.ker := by
        rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, cent2ToCbar_eq_one_iff]
        exact Or.inr rfl
      refine ⟨⟨_, htmem⟩, ?_, ?_⟩
      · intro h
        apply tGriess_ne_one'
        exact congrArg (fun w : φ.ker => (((w : ↥(T.subgroupOf H)) : ↥H) : MGriess)) h
      · intro w hw
        have hw1 : cent2ToCbar ((w : ↥(T.subgroupOf H)) : ↥H) = 1 := w.2
        rcases (cent2ToCbar_eq_one_iff _).1 hw1 with h1 | h1
        · exact absurd (Subtype.ext (Subtype.ext (Subtype.ext h1))) hw
        · exact Subtype.ext (Subtype.ext (Subtype.ext h1))
    have hrange : Nat.card φ.range = 2 ^ 41 := by
      have h := Subgroup.card_ker_mul_card_range φ
      rw [hker, hT'] at h
      omega
    have hrJ : φ.range ≤ Jbar := by
      rintro _ ⟨w, rfl⟩
      exact cent2ToCbar_mem_Jbar _
    have hJfac : (Nat.card ↥Jbar).factorization 2 = 41 := by
      rw [natCard_Jbar_eq]
      exact factorization_two_pow_mul_odd (by decide)
    let Q : Sylow 2 ↥Jbar := Sylow.ofCard (φ.range.subgroupOf Jbar) (by
      rw [hJfac, ← hrange]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hrJ).toEquiv)
    obtain ⟨S, hS, hSc⟩ := short_centralizer_quotient_sylow_two.1 Q
    have hSr : (S : Subgroup Cbar) = φ.range := by
      rw [hS]
      show (φ.range.subgroupOf Jbar).map Jbar.subtype = φ.range
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hrJ]
    have hyS : cent2ToCbar ⟨y, hT hyT⟩ ∈ (S : Subgroup Cbar) := by
      rw [hSr]
      exact ⟨⟨⟨y, hT hyT⟩, Subgroup.mem_subgroupOf.2 hyT⟩, rfl⟩
    have hyc' : (⟨_, hyS⟩ : ↥(S : Subgroup Cbar)) ∈ Subgroup.center ↥(S : Subgroup Cbar) := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨g, hg⟩
      rw [hSr] at hg
      obtain ⟨⟨⟨s, hsH⟩, hsT⟩, rfl⟩ := hg
      apply Subtype.ext
      show cent2ToCbar ⟨s, hsH⟩ * cent2ToCbar ⟨y, hT hyT⟩ =
        cent2ToCbar ⟨y, hT hyT⟩ * cent2ToCbar ⟨s, hsH⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hyc s (Subgroup.mem_subgroupOf.1 hsT)).symm
    have hyx : cent2ToCbar ⟨y, hT hyT⟩ ∈ Subgroup.zpowers xbar := by
      rw [← hSc]
      exact ⟨_, hyc', rfl⟩
    rcases (Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_xbar).1 hyx with h1 | h1
    · rcases (cent2ToCbar_eq_one_iff _).1 h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inl h2)
    · have h3 : cent2ToCbar (⟨y, hT hyT⟩ * xH⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, cent2ToCbar_xH, mul_inv_cancel]
      rcases (cent2ToCbar_eq_one_iff _).1 h3 with h4 | h4
      · right; right; left
        have h5 : y * xGriess⁻¹ = 1 := h4
        exact mul_inv_eq_one.1 h5
      · right; right; right
        have h5 : y * xGriess⁻¹ = tGriess := h4
        rw [← h5, inv_mul_cancel_right]
  · intro hy
    have hcomm : ∀ s ∈ T, tGriess * s = s * tGriess ∧ xGriess * s = s * xGriess := fun s hs =>
      ⟨(Subgroup.mem_centralizer_singleton_iff.1 (hT hs).1).symm,
        (Subgroup.mem_centralizer_singleton_iff.1 (hT hs).2).symm⟩
    rcases hy with rfl | rfl | rfl | rfl
    · exact ⟨T.one_mem, fun s _ => by rw [one_mul, mul_one]⟩
    · exact ⟨htT, fun s hs => (hcomm s hs).1⟩
    · exact ⟨hxT, fun s hs => (hcomm s hs).2⟩
    · refine ⟨T.mul_mem htT hxT, fun s hs => ?_⟩
      rw [mul_assoc, (hcomm s hs).2, ← mul_assoc, (hcomm s hs).1, mul_assoc]

end CFSG.Monster.Existence

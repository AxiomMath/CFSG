module

public import CFSG.Quasithin.Vol2.Ch12Sec7I77a
public import CFSG.RankThree.PartTwo.KFacts.L34Centralizers
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful

public section

namespace CFSG.Quasithin.H13.S127.I77

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique S127.L5
open CFSG.LocalAnalysis.ComponentInitial

theorem eq_one_of_fixes {X : Type} [Group X] [Finite X] (hX : IsPSL 3 2 2 X) {P : Subgroup X}
    (hP : 168 < Nat.card P) (h3 : ∃ y ∈ P, orderOf y = 3) {α : MulAut X}
    (hα : ∃ n : ℕ, orderOf α = 2 ^ n) (hfix : ∀ x ∈ P, α x = x) : α = 1 := by
  classical
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := QA12.exists_equiv_projectiveSL hX
  have := LinearFieldFour.charP_two_of_card_eq_four hF
  have hσ : ∀ a : F, frobeniusEquiv F 2 a = a ^ 2 := fun a => by
    rw [frobeniusEquiv_apply, frobenius_def]
  by_contra hne
  obtain ⟨n, hn⟩ := hα
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hn
    exact hne hn
  have hα0 : orderOf α ≠ 0 := by rw [hn]; positivity
  have h2 : 2 ∣ orderOf α := by rw [hn]; exact dvd_pow_self 2 hn0
  set γ := α ^ (orderOf α / 2) with hγ
  have hγ2 : orderOf γ = 2 := orderOf_pow_orderOf_div hα0 h2
  have hpow : ∀ k : ℕ, ∀ x ∈ P, (α ^ k) x = x := by
    intro k
    induction k with
    | zero => intro x _; rfl
    | succ k ih =>
      intro x hx
      rw [pow_succ, MulAut.mul_apply, hfix x hx, ih x hx]
  have hγfix : ∀ x ∈ P, γ x = x := hpow _
  set β : MulAut (LinearFlag.projectiveSL 3 F) := MulAut.congr e γ with hβ
  have hβ2 : orderOf β = 2 := by rw [hβ, MulEquiv.orderOf_eq]; exact hγ2
  have hββ : β * β = 1 := by rw [← pow_two, ← hβ2, pow_orderOf_eq_one]
  have hβ1 : β ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hβ2
    norm_num at hβ2
  have hβfix : ∀ x ∈ P, β (e x) = e x := by
    intro x hx
    simp [hβ, MulAut.congr_apply, hγfix x hx]
  rcases RankThree.PartTwo.KFacts.L34.involution_cases_card hF hσ hββ with
    ⟨x, hx⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨y, hyP, hy3⟩ := h3
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hβ1
      rw [← hx, map_one]
    have hx2 : x * x = 1 := by
      apply RankThree.PartTwo.KFacts.L34.conj_injective hF
      rw [map_mul, hx, hββ, map_one]
    have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
    have hey : orderOf (e y) = 3 := by rw [MulEquiv.orderOf_eq]; exact hy3
    have hfx := hβfix y hyP
    rw [← hx, MulAut.conj_apply] at hfx
    apply RankThree.PartTwo.KFacts.L34.mul_ne_mul_of_orderOf hF hey hxo
    calc e y * x = x * e y * x⁻¹ * x := by rw [hfx]
      _ = x * e y := by group
  all_goals
    have hle : P.map e.toMonoidHom ≤ GL3TwoFixedModel.autFixed β := by
      rintro _ ⟨x, hx, rfl⟩
      exact GL3TwoFixedModel.mem_autFixed.mpr (hβfix x hx)
    have hc := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective e.injective, h] at hc
    omega

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev ltQuot (L : Subgroup G) (t : G) :
    ↥((Lt L t).subgroupOf (Kt L t)) →* (↥(Kt L t) ⧸ Subgroup.center ↥(Kt L t)) :=
  (QuotientGroup.mk' _).comp ((Lt L t).subgroupOf (Kt L t)).subtype

namespace Set77

variable {T L V : Subgroup G} {t : G} (s : Set77 G T L V t)
include s

theorem card_Lt : Nat.card ↥(Lt L t) = 3840 := by
  rw [s.d.card_Lt, s.card_pCore_Lt]

theorem card_subgroupOf_Lt : Nat.card ↥((Lt L t).subgroupOf (Kt L t)) = 3840 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (lt_le_Kt L t)).toEquiv, s.card_Lt]

theorem card_ltQuot_range : 960 ≤ Nat.card (ltQuot L t).range := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (ltQuot L t).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (ltQuot L t)).toEquiv,
    s.card_subgroupOf_Lt] at h1
  have hker : Nat.card (ltQuot L t).ker ≤ 4 := by
    have hle : (ltQuot L t).ker.map ((Lt L t).subgroupOf (Kt L t)).subtype ≤
        Subgroup.center ↥(Kt L t) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hx
      simpa [ltQuot, QuotientGroup.eq_one_iff] using hx
    have h2 := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), s.card_center] at h2
  have h3 : 3840 ≤ Nat.card (ltQuot L t).range * 4 := h1 ▸ Nat.mul_le_mul_left _ hker
  omega

theorem exists_orderOf_three : ∃ y ∈ (ltQuot L t).range, orderOf y = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥((Lt L t).subgroupOf (Kt L t))) 3
    (by rw [s.card_subgroupOf_Lt]; norm_num)
  refine ⟨ltQuot L t y, ⟨y, rfl⟩, ?_⟩
  have hdvd : orderOf (ltQuot L t y) ∣ 3 := hy ▸ orderOf_map_dvd _ y
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exfalso
    rw [orderOf_eq_one_iff] at h1
    have hyc : ((y : ↥(Kt L t))) ∈ Subgroup.center ↥(Kt L t) := by
      simpa [ltQuot, QuotientGroup.eq_one_iff] using h1
    have h4 : orderOf (⟨_, hyc⟩ : ↥(Subgroup.center ↥(Kt L t))) ∣ 4 :=
      s.card_center ▸ orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hy] at h4
    norm_num at h4
  · exact h3

theorem mem_centralizer_of {w : G} (hwN : w ∈ Subgroup.normalizer (Kt L t : Set G))
    (hw2 : ∃ n : ℕ, orderOf w = 2 ^ n) (hwL : w ∈ Subgroup.centralizer (Lt L t : Set G)) :
    w ∈ Subgroup.centralizer (Kt L t : Set G) := by
  set α : MulAut ↥(Kt L t) := (Kt L t).normalizerMonoidHom ⟨w, hwN⟩ with hα
  set β := ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥(Kt L t) α with hβ
  have hβ2 : ∃ n : ℕ, orderOf β = 2 ^ n := by
    obtain ⟨n, hn⟩ := hw2
    have h1 : orderOf β ∣ orderOf (⟨w, hwN⟩ : ↥(Subgroup.normalizer (Kt L t : Set G))) :=
      orderOf_map_dvd ((ComponentClassification.PerfectAutomorphisms.centerQuotientHom _).comp
        (Kt L t).normalizerMonoidHom) _
    rw [Subgroup.orderOf_mk, hn] at h1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact ⟨k, hk⟩
  have hαl : ∀ y : ↥((Lt L t).subgroupOf (Kt L t)), α (y : ↥(Kt L t)) = y := by
    intro y
    apply Subtype.ext
    have hy : ((y : ↥(Kt L t)) : G) ∈ Lt L t := y.2
    have hc := Subgroup.mem_centralizer_iff.mp hwL _ hy
    change w * ((y : ↥(Kt L t)) : G) * w⁻¹ = _
    rw [← hc, mul_inv_cancel_right]
  have hfix : ∀ x ∈ (ltQuot L t).range, β x = x := by
    rintro _ ⟨y, rfl⟩
    simp only [ltQuot, MonoidHom.comp_apply, QuotientGroup.mk'_apply, Subgroup.coe_subtype]
    rw [hβ, ComponentClassification.CentralCover.centerQuotientHom_apply_mk, hαl y]
  have hβ1 : β = 1 := eq_one_of_fixes s.psl (lt_of_lt_of_le (by norm_num) s.card_ltQuot_range)
    s.exists_orderOf_three hβ2 hfix
  have : Group.IsPerfect ↥(Kt L t) := ⟨s.comp.2.2.1⟩
  have hα1 : α = 1 :=
    ComponentClassification.CentralCover.perfect_central_quotient_automorphism_faithful _
      (by rw [map_one]; exact hβ1)
  have hker : (⟨w, hwN⟩ : ↥(Subgroup.normalizer (Kt L t : Set G))) ∈
      (Kt L t).normalizerMonoidHom.ker := hα1
  rw [Subgroup.normalizerMonoidHom_ker] at hker
  exact hker

end Set77

end CFSG.Quasithin.H13.S127.I77

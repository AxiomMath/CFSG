module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs518DL
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem522Y

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_mul_inv_mem_of_pow_three {K C : Subgroup G}
    (hCN : C ≤ Subgroup.normalizer (K : Set G)) (h3 : ¬ 3 ∣ Nat.card C) {d k : G}
    (hd : d ∈ Subgroup.normalizer (K : Set G)) (hd3 : d ^ 3 = 1) (hk : k ∈ K)
    (hc : d * k⁻¹ ∈ C) : d ∈ K := by
  have hKN : K ≤ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer
  set K' := K.subgroupOf (Subgroup.normalizer (K : Set G)) with hK'
  have : K'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mpr le_rfl
  set π := QuotientGroup.mk' K' with hπ
  set x : ↥(Subgroup.normalizer (K : Set G)) := ⟨d, hd⟩ with hx
  set c : ↥(Subgroup.normalizer (K : Set G)) := ⟨d * k⁻¹, hCN hc⟩ with hcdef
  have hxc : π x = π c := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hK',
      Subgroup.mem_subgroupOf]
    have e : ((x⁻¹ * c : ↥(Subgroup.normalizer (K : Set G))) : G) = k⁻¹ := by
      simp only [hx, hcdef, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact K.inv_mem hk
  have h1 : orderOf (π x) ∣ 3 := by
    apply orderOf_dvd_of_pow_eq_one
    have e : x ^ 3 = 1 := Subtype.ext (by simp [hx, hd3])
    rw [← map_pow, e, map_one]
  have h2 : orderOf (π x) ∣ Nat.card C := by
    rw [hxc]
    refine (orderOf_map_dvd π c).trans ?_
    have h' := orderOf_dvd_natCard (⟨d * k⁻¹, hc⟩ : ↥C)
    rw [Subgroup.orderOf_mk] at h'
    rwa [hcdef, Subgroup.orderOf_mk]
  have h4 : orderOf (π x) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact h
    · exact absurd (h ▸ h2) h3
  have h5 : x ∈ K' := (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h4)
  exact h5

end General

section Setting

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem B_le_normalizer_of_le_D (hF : L2TorusFact) {D₃ : Subgroup G} (hD₃ : D₃ ≤ D) :
    B ≤ Subgroup.normalizer (D₃ : Set G) := by
  have hh := h.hyp.toHyp5_0_1
  have hDcyc : IsCyclic ↥D := (hh.isCyclic_card_of_isHall hF h.notation59.2.1).1
  intro b hb
  have hbD : b ∈ Subgroup.normalizer (D : Set G) := h.notation59.2.2 hb
  set E := D₃.map (MulAut.conj b).toMonoidHom with hE
  have hED : E ≤ D := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hbD y).mp (hD₃ hy)
  have hcard : Nat.card E = Nat.card D₃ := Subgroup.card_map_of_injective
    (fun a c hac => (MulAut.conj b).injective hac :
      Function.Injective (MulAut.conj b).toMonoidHom)
  have heq : E.subgroupOf D = D₃.subgroupOf D := by
    rw [IsCyclic.subgroup_eq_iff_card_eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hED).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₃).toEquiv, hcard]
  have heq' : E = D₃ := by
    have h' := Subgroup.subgroupOf_inj.mp heq
    rwa [inf_eq_left.mpr hED, inf_eq_left.mpr hD₃] at h'
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h' : b * x * b⁻¹ ∈ E := ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rwa [heq'] at h'
  · intro hx
    rw [← heq'] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have e : y = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      exact mul_left_cancel (mul_right_cancel hyx)
    rwa [← e]

theorem eq_B_of_inner (hF : L2TorusFact) (h510 : Stmt5_1_10) (h516 : Stmt5_1_16)
    {D₃ : Subgroup G} (hD₃ : D₃ ≤ D) (h3 : Nat.card D₃ = 3)
    (hD₃M : D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    (hin : ∀ d ∈ D₃, ∃ k ∈ oTwoUpper H, d * k⁻¹ ∈ centralizerModO2 (oTwoUpper H)) :
    D₃ = B := by
  have hh := h.hyp.toHyp5_0_1
  have hC3 : ¬ 3 ∣ Nat.card ↥(centralizerModO2 (oTwoUpper H)) :=
    (h516 G T M L V H B D n h.hyp h.notation59 h.module h.l34).1
  have hD₃K : D₃ ≤ oTwoUpper H := by
    intro d hd
    obtain ⟨k, hk, hc⟩ := hin d hd
    have hd3 : d ^ 3 = 1 := by
      have h' := pow_card_eq_one' (G := ↥D₃) (x := ⟨d, hd⟩)
      rw [h3] at h'
      exact congrArg Subtype.val h'
    exact mem_of_mul_inv_mem_of_pow_three (centralizerModO2_le_normalizer (oTwoUpper H)) hC3
      (hD₃M hd) hd3 hk hc
  have hD₃MH : D₃ ≤ M ⊓ H :=
    le_inf (hD₃.trans (h.notation59.2.1.1.trans (inf_le_left.trans hh.L_le)))
      (hD₃K.trans (oTwoUpper_le H))
  have hB3 : Nat.card B = 3 := h.card_B_eq_three h510
  have hP3 : IsPGroup 3 ↥(B ⊔ D₃) := by
    have hB : IsPGroup 3 ↥B := IsPGroup.of_card (n := 1) (by rw [hB3, pow_one])
    have hD : IsPGroup 3 ↥D₃ := IsPGroup.of_card (n := 1) (by rw [h3, pow_one])
    exact hB.to_sup_of_normal_right' hD (h.B_le_normalizer_of_le_D hF hD₃)
  have hsupMH : B ⊔ D₃ ≤ M ⊓ H := sup_le h.notation59.1.1 hD₃MH
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP3
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hh.sylow.1
  have hdvd : 3 ^ a ∣ 2 ^ m * 3 := by
    rw [← ha, ← hm, ← hB3, ← h.hyp.card_inf_eq h.notation59]
    exact Subgroup.card_dvd_of_le hsupMH
  have ha1 : 3 ^ a ∣ 3 :=
    (Nat.Coprime.pow a m (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_left hdvd
  have hle : Nat.card ↥(B ⊔ D₃) ≤ Nat.card B := by
    rw [ha, hB3]
    exact Nat.le_of_dvd (by norm_num) ha1
  have hBeq : B = B ⊔ D₃ := Subgroup.eq_of_le_of_card_ge le_sup_left hle
  have hD₃B : D₃ ≤ B := by
    rw [hBeq]
    exact le_sup_right
  exact Subgroup.eq_of_le_of_card_ge hD₃B (by rw [hB3, h3])

end Hyp5_1_14

end Setting

theorem stmt5_1_18_DL_of (hF : L2TorusFact) (h510 : Stmt5_1_10) (h516 : Stmt5_1_16)
    (hOut : Stmt5_1_18_DL_outer) : Stmt5_1_18_DL := by
  intro G _ _ T M L V H B D n h hev D₃ hD₃ h3 hD₃M hne
  by_cases hin : ∀ d ∈ D₃, ∃ k ∈ oTwoUpper H, d * k⁻¹ ∈ centralizerModO2 (oTwoUpper H)
  · exact absurd (h.eq_B_of_inner hF h510 h516 hD₃ h3 hD₃M hin) hne
  · push Not at hin
    exact hOut G T M L V H B D n h hev D₃ hD₃ h3 hD₃M hin

theorem stmt5_1_18_of_reduced (hF : L2TorusFact) (h510 : Stmt5_1_10) (h515 : Stmt5_1_15)
    (h516 : Stmt5_1_16) (h5114 : Stmt5_1_14_first) (h517 : Stmt5_1_17)
    (hOut : Stmt5_1_18_DL_outer) (hD5 : Stmt5_1_18_D5) : Stmt5_1_18 :=
  stmt5_1_18_of_inputs hF h515 h5114 h517 (stmt5_1_18_DL_of hF h510 h516 hOut) hD5

end CFSG.Quasithin.H13

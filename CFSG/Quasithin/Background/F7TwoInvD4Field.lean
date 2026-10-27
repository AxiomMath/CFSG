module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalVPrelim
public import CFSG.Quasithin.Background.F7TwoInvD4Inner

public section

namespace CFSG.Quasithin.F7Two

open CFSG.LocalAnalysis.EvenBN.TrialityD4 Subgroup

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem odd_card_J : Odd (Nat.card d.J) := by
  have he := d.even_q
  have h1 : Odd (q - 1) := odd_sub_one_of_even he (by have := d.two_le_q; omega)
  have h3 : Odd (q ^ 3 - 1) :=
    odd_sub_one_of_even (he.pow_of_ne_zero (by norm_num)) (Nat.one_le_pow _ _ (by
      have := d.two_le_q; omega))
  rw [d.card_J]
  exact h1.mul h3

theorem odd_orderOf_of_mem_J {y : X} (hy : y ∈ d.J) : Odd (orderOf y) := by
  have := d.finite
  have h : orderOf (⟨y, hy⟩ : d.J) ∣ Nat.card d.J := orderOf_dvd_natCard _
  rw [← Subgroup.orderOf_coe] at h
  exact (odd_card_J d).of_dvd_nat h

variable {f : ℕ}

theorem exists_pow_ne (hq : q = 2 ^ f) (hf : Even f) :
    ∃ x : d.Γ, x ^ 2 ^ (3 * f / 2) ≠ x := by
  obtain ⟨e, rfl⟩ := hf
  have he : 1 ≤ e := by
    have h2 := d.two_le_q
    by_contra h0
    rw [hq, show e = 0 by omega] at h2
    norm_num at h2
  have hk : 3 * (e + e) / 2 = 3 * e := by omega
  rw [hk]
  by_contra hall
  push Not at hall
  have hcard : Nat.card d.Γ = (2 ^ (3 * e)) ^ 2 := by
    rw [d.card_Γ, hq, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have h1 := card_fixed_pow_two_pow (F := d.Γ) (k := 3 * e) (by omega) hcard
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), hcard] at h1
  have h2 : 2 ^ (3 * e) = 1 := by
    have h3 : 0 < 2 ^ (3 * e) := by positivity
    nlinarith [h1]
  have := Nat.one_lt_two_pow (n := 3 * e) (by omega)
  omega

theorem invAutGen_φ₀ (hq : q = 2 ^ f) (hf : Even f) : InvAutGen X (d.φ ^ (3 * f / 2)) := by
  set k := 3 * f / 2 with hk
  set δ := d.φ ^ k with hδ
  have hδJ : ∀ y ∈ d.J, δ y ∈ d.J := by
    rintro _ ⟨h, rfl⟩
    rw [hδ, d.φ_pow_torus]
    exact ⟨_, rfl⟩
  have hΞ : ∀ y ∈ d.J, δ y ≠ y → y ∈ invXiAut δ := fun y hy hne => by
    have hmem : δ y * y⁻¹ ∈ d.J := mul_mem (hδJ y hy) (inv_mem hy)
    exact not_isPGroup_two_zpowers_of_odd_orderOf (odd_orderOf_of_mem_J d hmem)
      (fun h => hne (mul_inv_eq_one.1 h))
  obtain ⟨x, hx⟩ := exists_pow_ne d hq hf
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (zero_pow (pow_ne_zero _ two_ne_zero))
  have hy₀ : δ (d.torus (1, Units.mk0 x hx0)) ≠ d.torus (1, Units.mk0 x hx0) := by
    rw [hδ, d.φ_pow_torus]
    intro h
    have := congrArg Units.val (congrArg Prod.snd (d.torus_injective h))
    exact hx (by simpa using this)
  have hne : (invXiAut δ).Nonempty := ⟨_, hΞ _ ⟨_, rfl⟩ hy₀⟩
  have hfix : fixSubgroup δ ≤ Subgroup.closure (invXiAut δ) :=
    fixSubgroup_le_closure_invXiAut hne
  set K := Subgroup.closure (invXiAut δ) with hK
  have hJK : ∀ y ∈ d.J, y ∈ K := fun y hy => by
    by_cases hδy : δ y = y
    · exact hfix (mem_fixSubgroup_iff.2 hδy)
    · exact Subgroup.subset_closure (hΞ y hy hδy)
  have hu : d.u ∈ K := hfix (mem_fixSubgroup_iff.2 (d.φ_pow_u k))
  have hv : d.v ∈ K := hfix (mem_fixSubgroup_iff.2 (d.φ_pow_v k))
  have hx₁ : d.x₁ 1 ∈ K := hfix (mem_fixSubgroup_iff.2 (by rw [hδ, d.φ_pow_x₁, one_pow]))
  have hx₂ : d.x₂ 1 ∈ K := hfix (mem_fixSubgroup_iff.2 (by rw [hδ, d.φ_pow_x₂, one_pow]))
  have h₁ : ∀ a, d.x₁ a ∈ K := fun a => by
    by_cases ha : a = 0
    · rw [ha, d.x₁_zero]
      exact one_mem _
    · have h := conj_mem (hJK _ ⟨(1, Units.mk0 a ha), rfl⟩) hx₁
      rwa [MulAut.conj_apply, d.torus_x₁, Units.val_mk0, mul_one] at h
  have h₂ : ∀ a, d.x₂ a ∈ K := fun a => by
    by_cases ha : a = 0
    · rw [ha, d.x₂_zero]
      exact one_mem _
    · have h := conj_mem (hJK _ ⟨(Units.mk0 a ha, 1), rfl⟩) hx₂
      rwa [MulAut.conj_apply, d.torus_x₂, Units.val_mk0, mul_one] at h
  have h₃ : ∀ a, d.x₃ a ∈ K := fun a => by
    have h := conj_mem hv (h₁ a)
    rwa [MulAut.conj_apply, d.v_conj_x₁] at h
  have h₄ : ∀ a, d.x₄ a ∈ K := fun a => by
    have h := conj_mem hu (h₃ a)
    rwa [MulAut.conj_apply, d.u_conj_x₃_eq_x₄] at h
  have h₅ : ∀ a, d.x₅ a ∈ K := fun a => by
    have h := conj_mem hu (h₂ a)
    rwa [MulAut.conj_apply, d.u_conj_x₂] at h
  have h₆ : ∀ a, d.x₆ a ∈ K := fun a => by
    have h := conj_mem hv (h₅ a)
    rwa [MulAut.conj_apply, d.v_conj_x₅] at h
  exact (invAutGen_iff_closure_invXiAut _).2
    (top_le_of_S_u_v d (S_le_of_root_groups d h₁ h₂ h₃ h₄ h₅ h₆) hu hv)

end CFSG.Quasithin.F7Two

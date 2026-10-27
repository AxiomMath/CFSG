module

public import CFSG.Timmesfeld.Exceptional.SigmaFar
public import CFSG.Timmesfeld.Exceptional.SigmaBasic
public import CFSG.Timmesfeld.Bridge.RootStructBasic
public import CFSG.Timmesfeld.Exceptional.KdStructure

public section

namespace CFSG.Timmesfeld.Moufang

open CFSG.Certificates CFSG.Certificates.CosetEnumeration

variable {G : Type*} [Group G] {D : Set G}

namespace SigmaFar

open TwoLines

theorem dvd_three_of_odd_of_dvd_twelve {n : ℕ} (hn : Odd n) (h : n ∣ 12) : n ∣ 3 := by
  have hcop : Nat.Coprime n 4 :=
    Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 hn)
  exact hcop.dvd_of_dvd_mul_left (by simpa using h)

theorem false_of_far (hD : IsRootInvolutionSet D) (hNP : NoPolar D) (hP1 : ExcP1 D)
    {x₀ x₁ c d₁ : G} (hx₀ : x₀ ∈ D) (hx₁ : x₁ ∈ D) (hc : c ∈ D) (hd₁ : d₁ ∈ D)
    (hrelD : ∀ r ∈ relsD, signedProd ![x₀, x₁, c] r = 1)
    (hwD : signedProd ![x₀, x₁, c] wD = d₁) (hd₁x₀ : Commute x₀ d₁) (hne : d₁ ≠ x₀)
    (h01 : orderOf (x₀ * x₁) = 4) (h3₀ : orderOf (x₀ * c) = 3)
    (h4 : orderOf (d₁ * c) ≠ 4) (h4' : orderOf (x₀ * d₁ * c) ≠ 4) : False := by
  have hx₀d₁ : x₀ * d₁ ∈ D := hNP x₀ hx₀ d₁ hd₁ hd₁x₀ (Ne.symm hne)
  have hx₀c := not_commute_of_orderOf_eq_three hD hx₀ hc h3₀
  have hodd₀ : Odd (orderOf (x₀ * c)) := by rw [h3₀]; decide
  obtain ⟨hd₁c, hx₀d₁c⟩ :=
    Bridge.not_commute_of_opposite_of_line hD hx₀ hd₁ hd₁x₀ hx₀d₁ hc hx₀c hodd₀
  have hoddd := odd_of_not_commute_of_ne_four hD hd₁ hc hd₁c h4
  have hoddxd := odd_of_not_commute_of_ne_four hD hx₀d₁ hc hx₀d₁c h4'
  set x : Fin 3 → G := ![x₀, x₁, c] with hx
  have hwXD : ∀ k : ℕ, signedProd x (List.replicate k wXD).flatten = (x₁ * d₁) ^ k := by
    intro k
    rw [signedProd_replicate, wXD, signedProd_append, hwD]
    simp [signedProd, hx]
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hx₁ hd₁ with h | h | ⟨hodd, hnc⟩
  ·
    have hrel : ∀ r ∈ relsF4, signedProd x r = 1 := by
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hrelD r hr
      · rw [List.mem_singleton.1 hr, hwXD]
        have e2 : (x₁ * d₁) ^ 2 = 1 :=
          (commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hx₁) (hD.mul_self_eq_one hd₁)).1 h
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, e2, one_pow]
    have k := Exc.signedProd_eq_one_of_mk_eq_one mk_F4 x hrel
    exact hD.ne_one hx₀ (by simpa [signedProd, hx] using k)
  ·
    have hrel : ∀ r ∈ relsF4, signedProd x r = 1 := by
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hrelD r hr
      · rw [List.mem_singleton.1 hr, hwXD, ← h]
        exact pow_orderOf_eq_one _
    have k := Exc.signedProd_eq_one_of_mk_eq_one mk_F4 x hrel
    exact hD.ne_one hx₀ (by simpa [signedProd, hx] using k)
  ·
    have hodd' : Odd (orderOf (d₁ * x₁)) := by rwa [orderOf_mul_comm_eq]
    have h3 : orderOf (d₁ * x₁) = 3 :=
      hP1 d₁ hd₁ x₁ hx₁ (fun e => hnc e.symm) hodd' x₀ hx₀ hd₁x₀.symm
        (by rw [← hd₁x₀.eq]; exact hx₀d₁) h01
    have hrel : ∀ r ∈ relsF3, signedProd x r = 1 := by
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hrelD r hr
      · rw [List.mem_singleton.1 hr, hwXD]
        have h3' : orderOf (x₁ * d₁) = 3 := by rw [orderOf_mul_comm_eq]; exact h3
        rw [← h3']
        exact pow_orderOf_eq_one _
    have k := Exc.signedProd_eq_one_of_mk_eq_one mk_wU x hrel
    rw [wU, signedProd_replicate, signedProd_append, hwD] at k
    have hcd : orderOf (d₁ * c) ∣ 12 := by
      have : (c * d₁) ^ 12 = 1 := by simpa [signedProd, hx] using k
      rw [orderOf_mul_comm_eq]
      exact orderOf_dvd_of_pow_eq_one this
    have hdvd := dvd_three_of_odd_of_dvd_twelve hoddd hcd
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3'
    ·
      rw [orderOf_eq_one_iff] at h1
      apply hx₀c
      have : c = d₁⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this, hD.inv_eq hd₁]
      exact hd₁x₀
    · exact false_of_orderOf_three_three_of_line (hD.mul_self_eq_one hx₀)
        (hD.mul_self_eq_one hd₁) (hD.mul_self_eq_one hc) hd₁x₀ h3₀ h3' hoddxd

end SigmaFar

open TwoLines

theorem orderOf_eq_five_of_two_lines_of_p1 (hD : IsRootInvolutionSet D)
    (hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (hNL : NoLevi D) (hNP : NoPolar D)
    (hPl : ExcNoPlane D) (hP1 : ExcP1 D) {p c x₀ x₁ : G} (hp : p ∈ D) (hc : c ∈ D)
    (hx₀ : x₀ ∈ D) (hx₁ : x₁ ∈ D) (hpx₀ : Commute p x₀) (hpx₁ : Commute p x₁)
    (hsq : (x₀ * x₁) ^ 2 = p) (h3₀ : orderOf (x₀ * c) = 3) (h3₁ : orderOf (x₁ * c) = 3)
    (hpc : ¬ Commute p c) (hodd : Odd (orderOf (p * c)))
    (hpx₀c : ¬ Commute (p * x₀) c) (hodd₀ : Odd (orderOf (p * x₀ * c))) :
    orderOf (p * c) = 5 := by
  have hp2 := hD.mul_self_eq_one hp
  have hc2 := hD.mul_self_eq_one hc
  have h02 := hD.mul_self_eq_one hx₀
  have h12 := hD.mul_self_eq_one hx₁
  have h03 : (x₀ * c) ^ 3 = 1 := h3₀ ▸ pow_orderOf_eq_one _
  have h13 : (x₁ * c) ^ 3 = 1 := h3₁ ▸ pow_orderOf_eq_one _
  have h014 : (x₀ * x₁) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, pow_two, hp2]
  set h := c * x₀ * x₁ * c with hh
  have hinv : h⁻¹ = c * x₁ * x₀ * c := by
    rw [hh]
    simp only [mul_inv_rev, hD.inv_eq hc, hD.inv_eq hx₀, hD.inv_eq hx₁, mul_assoc]
  have hx₀h : h * x₁ * h⁻¹ = x₀ := SigmaFar.conj_x₁ h02 h12 hc2 h03 h13
  set d₁ := h * p * h⁻¹ with hd₁
  have hd₁D : d₁ ∈ D := hconj h p hp
  have hd₁x₀ : Commute x₀ d₁ := by
    have := (Commute.conj_iff h).2 hpx₁.symm
    rwa [hx₀h] at this
  have hpx₀ne : p ≠ x₀ := by
    rintro rfl
    exact hpx₀c (by rw [hp2]; exact Commute.one_left c)
  set x : Fin 3 → G := ![x₀, x₁, c] with hx
  have hW : ∀ r ∈ relsW, signedProd x r = 1 := relsW_eq_one h02 h12 hc2 h014 h03 h13
  have hwP : signedProd x wP = p := by rw [signedProd_wP]; exact hsq
  have hwD : signedProd x wD = d₁ := by
    rw [signedProd_wD]
    show c * x₀ * x₁ * c * (x₀ * x₁) ^ 2 * (c * x₁ * x₀ * c) = h * p * h⁻¹
    rw [hsq, hinv]
  have hwPC : signedProd x wPC = p * c := by
    rw [signedProd_wPC]
    exact congrArg (· * c) hsq
  have hne1 := orderOf_ne_one_of_not_commute hpc
  have i0 : ∀ z, x₀ * (x₀ * z) = z := fun z => by rw [← mul_assoc, h02, one_mul]
  have i1 : ∀ z, x₁ * (x₁ * z) = z := fun z => by rw [← mul_assoc, h12, one_mul]
  by_cases hC : d₁ = x₀
  · exfalso
    have hpx : p = x₁ := by
      have e1 : p = h⁻¹ * d₁ * h := by rw [hd₁]; group
      have e2 : x₁ = h⁻¹ * x₀ * h := by rw [← hx₀h]; group
      rw [e1, e2, hC]
    apply hD.ne_one hx₁
    have e : x₀ * x₁ * (x₀ * x₁) = x₁ := by rw [← pow_two, hsq, hpx]
    calc x₁ = x₀ * (x₀ * x₁ * (x₀ * x₁) * x₁) * x₀ := by
          simp only [mul_assoc, i0, i1, h02, mul_one]
      _ = 1 := by rw [e, h12, mul_one, h02]
  rcases NoLevi.centralizer_cases hD hconj hNL hNP hPl hx₀ hp hd₁D hpx₀.symm hd₁x₀ hpx₀ne hC
    with hA | hB | ⟨h4, hsq₁⟩
  ·
    exfalso
    have hrel : ∀ r ∈ relsA, signedProd x r = 1 := by
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hW r hr
      · rw [List.mem_singleton.1 hr, signedProd_append, hwD, hwP, hA, hp2]
    have k := Exc.signedProd_eq_one_of_mk_eq_one mk_A x hrel
    rw [signedProd_replicate, hwPC] at k
    have hcop : Nat.Coprime (orderOf (p * c)) (2 ^ 2) :=
      Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 hodd)
    exact hne1 (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one k))
  ·
    exfalso
    have hrel : ∀ r ∈ relsB, signedProd x r = 1 := by
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hW r hr
      · rw [List.mem_singleton.1 hr, signedProd_append, signedProd_append, hwD, hwP, hB]
        simp [signedProd, hx, mul_assoc, hp2, h02]
    have k := Exc.signedProd_eq_one_of_mk_eq_one mk_B x hrel
    exact hD.ne_one hx₀ (by simpa [signedProd, hx] using k)
  ·
    have hrelD : ∀ r ∈ relsD, signedProd x r = 1 := by
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hW r hr
      · rw [List.mem_singleton.1 hr]
        simp only [signedProd_append, hwD, hwP]
        rw [← pow_two, hsq₁]
        simp [signedProd, hx, h02]
    have h01 : orderOf (x₀ * x₁) = 4 := by
      have hn : ¬ (x₀ * x₁) ^ 2 ^ 1 = 1 := by rw [pow_one, hsq]; exact hD.ne_one hp
      have hf : (x₀ * x₁) ^ 2 ^ (1 + 1) = 1 := by simpa using h014
      simpa using orderOf_eq_prime_pow hn hf
    by_cases hfar : orderOf (d₁ * c) ≠ 4 ∧ orderOf (x₀ * d₁ * c) ≠ 4
    · exact (SigmaFar.false_of_far hD hNP hP1 hx₀ hx₁ hc hd₁D hrelD hwD hd₁x₀ hC h01 h3₀
        hfar.1 hfar.2).elim
    rw [not_and_or, not_not, not_not] at hfar
    rcases hfar with h4' | h4'
    ·
      exfalso
      have hrel : ∀ r ∈ relsD1, signedProd x r = 1 := by
        intro r hr
        rcases List.mem_append.1 hr with hr | hr
        · exact hrelD r hr
        · rw [List.mem_singleton.1 hr, signedProd_replicate, signedProd_append, hwD]
          have e4 : (d₁ * c) ^ 4 = 1 := h4' ▸ pow_orderOf_eq_one _
          simpa [signedProd, hx] using e4
      have k := Exc.signedProd_eq_one_of_mk_eq_one mk_D1 x hrel
      rw [signedProd_replicate, hwPC] at k
      have h3 : orderOf (p * c) = 3 :=
        ((Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one k)).resolve_left hne1
      exact false_of_orderOf_three_three_of_line hp2 h02 hc2 hpx₀ h3 h3₀ hodd₀
    ·
      have hrel : ∀ r ∈ relsD2, signedProd x r = 1 := by
        intro r hr
        rcases List.mem_append.1 hr with hr | hr
        · exact hrelD r hr
        · rw [List.mem_singleton.1 hr, signedProd_replicate, signedProd_append,
            signedProd_append, hwD]
          have e4 : (x₀ * d₁ * c) ^ 4 = 1 := h4' ▸ pow_orderOf_eq_one _
          simpa [signedProd, hx, mul_assoc] using e4
      have k := Exc.signedProd_eq_one_of_mk_eq_one mk_D2 x hrel
      rw [signedProd_replicate, hwPC] at k
      exact ((Nat.dvd_prime (by norm_num)).1 (orderOf_dvd_of_pow_eq_one k)).resolve_left hne1

end CFSG.Timmesfeld.Moufang

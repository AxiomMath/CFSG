module

public import CFSG.Timmesfeld.Moufang.Reduction

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

@[expose] def LL5 (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ z ∈ D, ∀ c ∈ D, Commute d z → d * z ∈ D →
    ¬ Commute d c → Odd (orderOf (d * c)) → ¬ Commute z c → Odd (orderOf (z * c)) →
    ¬ Commute (d * z) c → Odd (orderOf (d * z * c)) →
    (orderOf (d * c) = 3 ∧ orderOf (z * c) = 5 ∧ orderOf (d * z * c) = 5) ∨
    (orderOf (d * c) = 5 ∧ orderOf (z * c) = 3 ∧ orderOf (d * z * c) = 5) ∨
    (orderOf (d * c) = 5 ∧ orderOf (z * c) = 5 ∧ orderOf (d * z * c) = 3)

@[expose] def NoPolar (D : Set G) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, Commute x y → x ≠ y → x * y ∈ D

theorem exists_orderOf_mul_eq_four (h : Hyp G D) {d : G} (hd : d ∈ D) :
    ∃ e ∈ D, orderOf (d * e) = 4 := by
  obtain ⟨d₀, hd₀, e₀, he₀, h4₀⟩ := h.nondeg
  obtain ⟨g, hg⟩ := isConj_iff.mp (h.isConj hd₀ hd)
  refine ⟨g * e₀ * g⁻¹, h.conj_mem g he₀, ?_⟩
  rw [← hg, show g * d₀ * g⁻¹ * (g * e₀ * g⁻¹) = g * (d₀ * e₀) * g⁻¹ by group,
    orderOf_conj_eq, h4₀]

theorem eq_of_collinear_of_odd_of_mem (hD : IsRootInvolutionSet D) {u v f : G} (hu : u ∈ D)
    (hv : v ∈ D) (huv : Commute u v) (huvD : u * v ∈ D) (hf : f ∈ D) (hfv : Commute f v)
    (hodd : Odd (orderOf (f * u))) : f = u := by
  rw [eq_inv_of_mul_eq_one_left (eq_of_collinear_of_odd hD hv huv huvD hf hfv hodd),
    hD.inv_eq hu]

theorem orderOf_eq_three_of_special_line (h : Hyp G D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hQ : CommLambda D) {d c y : G} (hd : d ∈ D) (hc : c ∈ D) (hdc : ¬ Commute d c)
    (hodd : Odd (orderOf (d * c))) (hy : y ∈ D) (hdy : Commute d y) (hdyD : d * y ∈ D)
    (hyc : orderOf (y * c) = 4) : orderOf (d * c) = 3 := by
  have hD := h.root
  obtain ⟨hwD, hyw, -, hcyc⟩ := sq_mem_of_orderOf_eq_four hD hy hc hyc
  have hywD : y * (y * c) ^ 2 ∈ D := by
    rw [← hcyc]
    have := conj_mem_of_isClass h.isClass c hy
    rwa [hD.inv_eq hc] at this
  have h4 : orderOf (d * (y * c) ^ 2) = 4 :=
    orderOf_mul_sq_eq_four h.isClass hD hd hc hdc hodd hy hdy hdyD hyc
  have hmem := hQ y hy d hd _ hwD hdy.symm (by rw [← hdy.eq]; exact hdyD) hyw hywD h4
  rw [hsing y hy, Set.mem_singleton_iff] at hmem
  have hQ' : ((y * c) ^ 2 * d) ^ 2 = y := by
    rw [← mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hd) (hD.mul_self_eq_one hwD) h4]
    exact hmem
  exact orderOf_mul_eq_three_of_line h.isClass hD hd hc hdc hodd hy hdy hdyD hyc hQ'

theorem not_commute_of_collinear (hD : IsRootInvolutionSet D) {d c y : G} (hd : d ∈ D)
    (hc : c ∈ D) (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c))) (hy : y ∈ D)
    (hdy : Commute d y) (hdyD : d * y ∈ D) : ¬ Commute y c := by
  intro hyc
  have hodd' : Odd (orderOf (c * d)) := by rwa [orderOf_mul_comm_eq]
  have hcd := eq_of_collinear_of_odd_of_mem hD hd hy hdy hdyD hc hyc.symm hodd'
  exact hdc (hcd ▸ Commute.refl c)

theorem orderOf_eq_three_or_five (h : Hyp G D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hQ : CommLambda D) (hL : LL5 D) {d c : G} (hd : d ∈ D) (hc : c ∈ D)
    (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c))) :
    orderOf (d * c) = 3 ∨ orderOf (d * c) = 5 := by
  have hD := h.root
  obtain ⟨e, he, h4⟩ := exists_orderOf_mul_eq_four h hd
  obtain ⟨hzD, hdz, -, -⟩ := sq_mem_of_orderOf_eq_four hD hd he h4
  have hdzD : d * (d * e) ^ 2 ∈ D := mul_sq_mem_of_orderOf_eq_four h.isClass hD hd he h4
  have hd2 := hD.mul_self_eq_one hd
  have hddz : Commute d (d * (d * e) ^ 2) := (Commute.refl d).mul_right hdz
  have hddzD : d * (d * (d * e) ^ 2) ∈ D := by rw [← mul_assoc, hd2, one_mul]; exact hzD
  have hcz := not_commute_of_collinear hD hd hc hdc hodd hzD hdz hdzD
  have hcdz := not_commute_of_collinear hD hd hc hdc hodd hdzD hddz hddzD
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hzD hc with hzc | h4zc | ⟨hoddz, -⟩
  · exact absurd hzc hcz
  · exact .inl (orderOf_eq_three_of_special_line h hsing hQ hd hc hdc hodd hzD hdz hdzD h4zc)
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hdzD hc with hdzc | h4dzc | ⟨hodddz, -⟩
  · exact absurd hdzc hcdz
  · exact .inl (orderOf_eq_three_of_special_line h hsing hQ hd hc hdc hodd hdzD hddz hddzD h4dzc)
  rcases hL d hd _ hzD c hc hdz hdzD hdc hodd hcz hoddz hcdz hodddz with h1 | h1 | h1
  · exact .inl h1.1
  · exact .inr h1.1
  · exact .inr h1.1

theorem opposite_of_collinear_of_five (h : Hyp G D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hQ : CommLambda D) {d c y : G} (hd : d ∈ D) (hc : c ∈ D) (h5 : orderOf (d * c) = 5)
    (hy : y ∈ D) (hdy : Commute d y) (hdyD : d * y ∈ D) :
    ¬ Commute y c ∧ Odd (orderOf (y * c)) := by
  have hD := h.root
  have hdc : ¬ Commute d c := by
    intro hdc
    have := orderOf_dvd_of_pow_eq_one ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hd)
      (hD.mul_self_eq_one hc)).1 hdc)
    rw [h5] at this
    exact absurd this (by norm_num)
  have hodd : Odd (orderOf (d * c)) := by rw [h5]; decide
  have hyc := not_commute_of_collinear hD hd hc hdc hodd hy hdy hdyD
  refine ⟨hyc, ?_⟩
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hy hc with h1 | h4 | ⟨hoddy, -⟩
  · exact absurd h1 hyc
  · have := orderOf_eq_three_of_special_line h hsing hQ hd hc hdc hodd hy hdy hdyD h4
    rw [h5] at this
    exact absurd this (by norm_num)
  · exact hoddy

theorem special_of_ne_line (h : Hyp G D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hQ : CommLambda D) (hL : LL5 D) (hNP : NoPolar D) {d c x₁ x₂ : G} (hd : d ∈ D)
    (hc : c ∈ D) (h5 : orderOf (d * c) = 5) (hx₁ : x₁ ∈ D) (hdx₁ : Commute d x₁)
    (hdx₁D : d * x₁ ∈ D) (hx₂ : x₂ ∈ D) (hdx₂ : Commute d x₂) (hdx₂D : d * x₂ ∈ D)
    (hne : x₂ ≠ x₁) (hne' : x₂ ≠ d * x₁) :
    orderOf (x₁ * x₂) = 4 ∧ (x₁ * x₂) ^ 2 = d := by
  have hD := h.root
  have hd2 := hD.mul_self_eq_one hd
  have hnc : ¬ Commute x₁ x₂ := by
    intro h12
    have h12D : x₁ * x₂ ∈ D := hNP x₁ hx₁ x₂ hx₂ h12 (Ne.symm hne)
    have hd12 : Commute d (x₁ * x₂) := hdx₁.mul_right hdx₂
    have hd12D : d * (x₁ * x₂) ∈ D := by
      refine hNP d hd _ h12D hd12 fun he => hne' ?_
      calc x₂ = x₁ * (x₁ * x₂) := by rw [← mul_assoc, hD.mul_self_eq_one hx₁, one_mul]
        _ = x₁ * d := by rw [← he]
        _ = d * x₁ := hdx₁.eq.symm
    have hcol : ∀ p ∈ D, Commute d p → d * p ∈ D → d * (d * p) ∈ D ∧ Commute d (d * p) := by
      intro p hp hdp _
      exact ⟨by rw [← mul_assoc, hd2, one_mul]; exact hp, (Commute.refl d).mul_right hdp⟩
    obtain ⟨hdx₁D', hddx₁⟩ := hcol x₁ hx₁ hdx₁ hdx₁D
    obtain ⟨hdx₂D', hddx₂⟩ := hcol x₂ hx₂ hdx₂ hdx₂D
    obtain ⟨hd12D', hdd12⟩ := hcol _ h12D hd12 hd12D
    have o1 := opposite_of_collinear_of_five h hsing hQ hd hc h5 hx₁ hdx₁ hdx₁D
    have o1' := opposite_of_collinear_of_five h hsing hQ hd hc h5 hdx₁D hddx₁ hdx₁D'
    have o2 := opposite_of_collinear_of_five h hsing hQ hd hc h5 hx₂ hdx₂ hdx₂D
    have o2' := opposite_of_collinear_of_five h hsing hQ hd hc h5 hdx₂D hddx₂ hdx₂D'
    have o3 := opposite_of_collinear_of_five h hsing hQ hd hc h5 h12D hd12 hd12D
    have o3' := opposite_of_collinear_of_five h hsing hQ hd hc h5 hd12D hdd12 hd12D'
    have hdc : ¬ Commute d c := fun hdc => by
      have := orderOf_dvd_of_pow_eq_one ((commute_iff_mul_sq_eq_one hd2
        (hD.mul_self_eq_one hc)).1 hdc)
      rw [h5] at this
      exact absurd this (by norm_num)
    have hoddd : Odd (orderOf (d * c)) := by rw [h5]; decide
    have e1 : x₁ * (d * x₂) = d * (x₁ * x₂) := by rw [← mul_assoc, ← hdx₁.eq, mul_assoc]
    have e2 : d * x₁ * x₂ = d * (x₁ * x₂) := mul_assoc _ _ _
    have e3 : d * x₁ * (d * x₂) = x₁ * x₂ := by
      rw [show d * x₁ * (d * x₂) = d * (x₁ * d) * x₂ by group, ← hdx₁.eq,
        show d * (d * x₁) * x₂ = (d * d) * (x₁ * x₂) by group, hd2, one_mul]
    have L1 := hL d hd x₁ hx₁ c hc hdx₁ hdx₁D hdc hoddd o1.1 o1.2 o1'.1 o1'.2
    have L2 := hL d hd x₂ hx₂ c hc hdx₂ hdx₂D hdc hoddd o2.1 o2.2 o2'.1 o2'.2
    have L3 := hL d hd _ h12D c hc hd12 hd12D hdc hoddd o3.1 o3.2 o3'.1 o3'.2
    have La := hL x₁ hx₁ x₂ hx₂ c hc h12 h12D o1.1 o1.2 o2.1 o2.2 o3.1 o3.2
    have hx₁dx₂ : Commute x₁ (d * x₂) := hdx₁.symm.mul_right h12
    have Lb := hL x₁ hx₁ _ hdx₂D c hc hx₁dx₂ (by rw [e1]; exact hd12D) o1.1 o1.2 o2'.1 o2'.2
      (by rw [e1]; exact o3'.1) (by rw [e1]; exact o3'.2)
    have hdx₁x₂ : Commute (d * x₁) x₂ := hdx₂.mul_left h12
    have Lc := hL _ hdx₁D x₂ hx₂ c hc hdx₁x₂ (by rw [e2]; exact hd12D) o1'.1 o1'.2 o2.1 o2.2
      (by rw [e2]; exact o3'.1) (by rw [e2]; exact o3'.2)
    have hdx₁dx₂ : Commute (d * x₁) (d * x₂) := hddx₂.mul_left (hdx₁.symm.mul_right h12)
    have Le := hL _ hdx₁D _ hdx₂D c hc hdx₁dx₂ (by rw [e3]; exact h12D) o1'.1 o1'.2 o2'.1
      o2'.2 (by rw [e3]; exact o3.1) (by rw [e3]; exact o3.2)
    rw [e1] at Lb
    rw [e2] at Lc
    rw [e3] at Le
    rw [h5] at L1 L2 L3
    omega
  have h4 : orderOf (x₁ * x₂) = 4 := by
    rcases hD.orderOf_mul hx₁ hx₂ with h2 | h4 | hodd
    · exact absurd ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hx₁)
        (hD.mul_self_eq_one hx₂)).2 (by rw [← h2]; exact pow_orderOf_eq_one _)) hnc
    · exact h4
    · have hodd' : Odd (orderOf (x₂ * x₁)) := by rwa [orderOf_mul_comm_eq]
      exact absurd (eq_of_collinear_of_odd_of_mem hD hx₁ hd hdx₁.symm
        (by rw [← hdx₁.eq]; exact hdx₁D) hx₂ hdx₂.symm hodd') hne
  refine ⟨h4, ?_⟩
  have := hQ d hd x₁ hx₁ x₂ hx₂ hdx₁ hdx₁D hdx₂ hdx₂D h4
  rwa [hsing d hd, Set.mem_singleton_iff] at this

end CFSG.Timmesfeld.Moufang

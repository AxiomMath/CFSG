module

public import CFSG.Timmesfeld.Exceptional.Coxeter
public import CFSG.Timmesfeld.Exceptional.TotallyOpposite

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

@[expose] def ExcOrderBound (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ c ∈ D, ¬ Commute d c → Odd (orderOf (d * c)) →
    orderOf (d * c) = 3 ∨ orderOf (d * c) = 5

@[expose] def ExcNoPlane (D : Set G) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, Commute x y → Commute x z → Commute y z → x ≠ y → z ≠ x →
    z ≠ y → z ≠ x * y → x * y ∈ D → x * z ∈ D → y * z ∈ D → x * y * z ∈ D → False

@[expose] def ExcP1 (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ c ∈ D, ¬ Commute d c → Odd (orderOf (d * c)) → ∀ y ∈ D, Commute d y →
    d * y ∈ D → orderOf (y * c) = 4 → orderOf (d * c) = 3

private theorem mul_mul_cancel_left' {a b : G} (ha : a * a = 1) : a * (a * b) = b := by
  rw [← mul_assoc, ha, one_mul]

theorem ll5_of_orderBound (hD : IsRootInvolutionSet D) (hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D)
    (hOB : ExcOrderBound D) : LL5 D := by
  intro d hd z hz c hc hdz hdzD n1 o1 n2 o2 n3 o3
  have hd2 := hD.mul_self_eq_one hd
  have hz2 := hD.mul_self_eq_one hz
  have hc2 := hD.mul_self_eq_one hc
  have hdz2 := hD.mul_self_eq_one hdzD
  rcases hOB d hd c hc n1 o1 with a | a <;> rcases hOB z hz c hc n2 o2 with b | b <;>
    rcases hOB _ hdzD c hc n3 o3 with e | e
  · exact (false_of_orderOf_three_three_of_line hd2 hz2 hc2 hdz a b o3).elim
  · exact (false_of_orderOf_three_three_of_line hd2 hz2 hc2 hdz a b o3).elim
  ·
    exfalso
    refine false_of_orderOf_three_three_of_line hd2 hdz2 hc2 ((Commute.refl d).mul_right hdz) a e ?_
    rwa [mul_mul_cancel_left' hd2]
  · exact .inl ⟨a, b, e⟩
  ·
    exfalso
    have hzdz : Commute z (d * z) := hdz.symm.mul_right (Commute.refl z)
    refine false_of_orderOf_three_three_of_line hz2 hdz2 hc2 hzdz b e ?_
    rwa [show z * (d * z) = d by rw [← mul_assoc, ← hdz.eq, mul_assoc, hz2, mul_one]]
  · exact .inr (.inl ⟨a, b, e⟩)
  · exact .inr (.inr ⟨a, b, e⟩)
  · exact (false_of_orderOf_five_five_five hD hconj hd hz hc hdz a b e).elim

theorem plane_of_ne (hD : IsRootInvolutionSet D) (hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D)
    (hNP : NoPolar D) {y x₁ x₂ : G} (hy : y ∈ D) (hx₁ : x₁ ∈ D) (hx₂ : x₂ ∈ D)
    (hyx₁ : Commute y x₁) (hyx₁D : y * x₁ ∈ D) (hyx₂ : Commute y x₂)
    (h4 : orderOf (x₁ * x₂) = 4) (hne : (x₁ * x₂) ^ 2 ≠ y) :
    (x₁ * x₂) ^ 2 ∈ D ∧ Commute x₁ y ∧ Commute x₁ ((x₁ * x₂) ^ 2) ∧ Commute y ((x₁ * x₂) ^ 2) ∧
      x₁ ≠ y ∧ (x₁ * x₂) ^ 2 ≠ x₁ ∧ (x₁ * x₂) ^ 2 ≠ x₁ * y ∧ x₁ * y ∈ D ∧
      x₁ * (x₁ * x₂) ^ 2 ∈ D ∧ y * (x₁ * x₂) ^ 2 ∈ D ∧ x₁ * y * (x₁ * x₂) ^ 2 ∈ D := by
  obtain ⟨htD, hx₁t, hx₂t, hconj₂⟩ := sq_mem_of_orderOf_eq_four hD hx₁ hx₂ h4
  set t := (x₁ * x₂) ^ 2 with ht
  have hyt : Commute y t := by rw [ht]; exact ((hyx₁.mul_right hyx₂).pow_right 2)
  have hnc : ¬ Commute x₁ x₂ := by
    intro h
    have := orderOf_dvd_of_pow_eq_one ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hx₁)
      (hD.mul_self_eq_one hx₂)).1 h)
    rw [h4] at this
    exact absurd this (by norm_num)
  have hx₁y : x₁ ≠ y := fun e => hD.ne_one hyx₁D (by rw [e, hD.mul_self_eq_one hy])
  have htx₁ : t ≠ x₁ := fun e => hnc (e ▸ hx₂t.symm)
  have htx₁y : t ≠ x₁ * y := by
    intro e
    apply hnc
    have h1 : Commute (x₁ * y) x₂ := e ▸ hx₂t.symm
    have h2 : x₁ = x₁ * y * y := by rw [mul_assoc, hD.mul_self_eq_one hy, mul_one]
    rw [h2]
    exact h1.mul_left hyx₂
  have hx₁yD : x₁ * y ∈ D := by rw [← hyx₁.eq]; exact hyx₁D
  have hx₁tD : x₁ * t ∈ D := by
    rw [← hconj₂]
    have := hconj x₂ x₁ hx₁
    rwa [hD.inv_eq hx₂] at this
  have hytD : y * t ∈ D := hNP y hy t htD hyt (Ne.symm hne)
  have hx₁ytD : x₁ * y * t ∈ D := by
    rw [mul_assoc]
    refine hNP x₁ hx₁ _ hytD (hyx₁.symm.mul_right hx₁t) fun e => hnc ?_
    rw [e]
    exact hyx₂.mul_left hx₂t.symm
  exact ⟨htD, hyx₁.symm, hx₁t, hyt, hx₁y, htx₁, htx₁y, hx₁yD, hx₁tD, hytD, hx₁ytD⟩

theorem eq_of_noPolar_noPlane (hD : IsRootInvolutionSet D)
    (hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (hNP : NoPolar D) (hPl : ExcNoPlane D)
    {y x₁ x₂ : G} (hy : y ∈ D) (hx₁ : x₁ ∈ D) (hx₂ : x₂ ∈ D) (hyx₁ : Commute y x₁)
    (hyx₁D : y * x₁ ∈ D) (hyx₂ : Commute y x₂) (h4 : orderOf (x₁ * x₂) = 4) :
    (x₁ * x₂) ^ 2 = y := by
  by_contra hne
  obtain ⟨htD, h1, h2, h3, h4', h5, h6, h7, h8, h9, h10⟩ :=
    plane_of_ne hD hconj hNP hy hx₁ hx₂ hyx₁ hyx₁D hyx₂ h4 hne
  exact hPl x₁ hx₁ y hy _ htD h1 h2 h3 h4' h5 hne h6 h7 h8 h9 h10

theorem commLambda_of_noPolar_noPlane (hD : IsRootInvolutionSet D)
    (hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (hNP : NoPolar D) (hPl : ExcNoPlane D) :
    CommLambda D := by
  intro y hy x₁ hx₁ x₂ hx₂ hyx₁ hyx₁D hyx₂ _ h4
  rw [eq_of_noPolar_noPlane hD hconj hNP hPl hy hx₁ hx₂ hyx₁ hyx₁D hyx₂ h4]
  exact mem_rootSet_self hy

theorem p1_of_noPolar_noPlane (h : Hyp G D) (hNP : NoPolar D) (hPl : ExcNoPlane D) : ExcP1 D := by
  intro d hd c hc hdc hodd y hy hdy hdyD hyc
  have hD := h.root
  have hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun g x hx => h.conj_mem g hx
  obtain ⟨hwD, hyw, -, -⟩ := sq_mem_of_orderOf_eq_four hD hy hc hyc
  have h4 : orderOf (d * (y * c) ^ 2) = 4 :=
    orderOf_mul_sq_eq_four h.isClass hD hd hc hdc hodd hy hdy hdyD hyc
  have heq := eq_of_noPolar_noPlane hD hconj hNP hPl hy hd hwD hdy.symm
    (by rw [← hdy.eq]; exact hdyD) hyw h4
  refine orderOf_mul_eq_three_of_line h.isClass hD hd hc hdc hodd hy hdy hdyD hyc ?_
  rw [← mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hd) (hD.mul_self_eq_one hwD) h4]
  exact heq

@[expose] def ExcTO5 (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ c ∈ D, TotallyOpposite D d c → orderOf (d * c) = 5

theorem totallyOpposite_of_p1 (hD : IsRootInvolutionSet D) (hNP : NoPolar D) (hP1 : ExcP1 D)
    {d c : G} (hd : d ∈ D) (hc : c ∈ D) (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c)))
    (h3 : orderOf (d * c) ≠ 3) : TotallyOpposite D d c := by
  intro x hx hdx
  by_cases hxd : x = d
  · subst hxd; exact ⟨hdc, hodd⟩
  have hdxD : d * x ∈ D := hNP d hd x hx hdx (Ne.symm hxd)
  have hxc := not_commute_of_collinear hD hd hc hdc hodd hx hdx hdxD
  refine ⟨hxc, ?_⟩
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hx hc with h1 | h4 | ⟨hoddx, -⟩
  · exact absurd h1 hxc
  · exact absurd (hP1 d hd c hc hdc hodd x hx hdx hdxD h4) h3
  · exact hoddx

theorem orderBound_of_to5 (h : Hyp G D) (hNP : NoPolar D) (hPl : ExcNoPlane D)
    (hTO : ExcTO5 D) : ExcOrderBound D := by
  intro d hd c hc hdc hodd
  by_cases h3 : orderOf (d * c) = 3
  · exact .inl h3
  · exact .inr (hTO d hd c hc (totallyOpposite_of_p1 h.root hNP (p1_of_noPolar_noPlane h hNP hPl)
      hd hc hdc hodd h3))

end CFSG.Timmesfeld.Moufang

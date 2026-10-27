module

public import CFSG.Timmesfeld.RootInduction

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

theorem mul_sq_comm_of_orderOf_eq_four (hD : IsRootInvolutionSet D) {a w : G} (ha : a ∈ D)
    (hw : w ∈ D) (h4 : orderOf (a * w) = 4) : (w * a) ^ 2 = (a * w) ^ 2 := by
  have hinv : ((a * w) ^ 2)⁻¹ = (a * w) ^ 2 := hD.inv_eq (hD.sq_mem ha hw h4)
  rw [← hinv, pow_two, pow_two, mul_inv_rev, mul_inv_rev, hD.inv_eq ha, hD.inv_eq hw]

theorem mul_mul_eq_mul_sq_of_orderOf_eq_four (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d e : G} (hd : d ∈ D) (he : e ∈ D) (h4 : orderOf (d * e) = 4) :
    d * e * d = e * (d * e) ^ 2 ∧ e * (d * e) ^ 2 ∈ D := by
  obtain ⟨-, -, hez, -⟩ := sq_mem_of_orderOf_eq_four hD hd he h4
  have he2 := hD.mul_self_eq_one he
  have h1 : d * e * d = e * (d * e) ^ 2 := by
    calc d * e * d = d * e * d * (e * e) := by rw [he2, mul_one]
      _ = (d * e) ^ 2 * e := by rw [pow_two]; group
      _ = e * (d * e) ^ 2 := hez.eq.symm
  refine ⟨h1, ?_⟩
  rw [← h1]
  have := conj_mem_of_isClass hclass d he
  rwa [hD.inv_eq hd] at this

theorem mem_zpowers_sq_of_odd {g : G} (hodd : Odd (orderOf g)) :
    ∃ k : ℕ, (g ^ 2) ^ k = g := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨k + 1, ?_⟩
  rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hk, pow_orderOf_eq_one,
    one_mul]

theorem orderOf_mul_sq_eq_four_of_commute (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d c e : G} (hd : d ∈ D) (hc : c ∈ D) (he : e ∈ D)
    (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c))) (hec : Commute e c)
    (h4 : orderOf (d * e) = 4) : orderOf (c * (d * e) ^ 2) = 4 := by
  obtain ⟨hzD, hdz, hez, -⟩ := sq_mem_of_orderOf_eq_four hD hd he h4
  obtain ⟨hded, hezD⟩ := mul_mul_eq_mul_sq_of_orderOf_eq_four hclass hD hd he h4
  have hd2 := hD.mul_self_eq_one hd
  have hc2 := hD.mul_self_eq_one hc
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hc hzD with hcz | h4' | ⟨hoddcz, -⟩
  · exfalso
    have h1 : Commute c (d * e * d) := by
      rw [hded]
      exact hec.symm.mul_right hcz
    have h2 : Commute (d * c * d) e := by
      have := (Commute.conj_iff d).2 h1
      rwa [hD.inv_eq hd, show d * (d * e * d) * d = (d * d) * e * (d * d) by group, hd2,
        one_mul, mul_one] at this
    have h3 : Commute e ((c * d) ^ 2) := by
      rw [show (c * d) ^ 2 = c * (d * c * d) by rw [pow_two]; group]
      exact hec.mul_right h2.symm
    have hoddcd : Odd (orderOf (c * d)) := by rwa [orderOf_mul_comm_eq]
    obtain ⟨k, hk⟩ := mem_zpowers_sq_of_odd hoddcd
    have h5 : Commute e (c * d) := by
      rw [← hk]
      exact h3.pow_right k
    have h6 : Commute e d := by
      have := hec.mul_right h5
      rwa [← mul_assoc, hc2, one_mul] at this
    have hsq := (commute_iff_mul_sq_eq_one hd2 (hD.mul_self_eq_one he)).1 h6.symm
    have hdvd := orderOf_dvd_of_pow_eq_one hsq
    rw [h4] at hdvd
    norm_num at hdvd
  · exact h4'
  · exfalso
    have hzeD : (d * e) ^ 2 * e ∈ D := by rw [← hez.eq]; exact hezD
    have h1 := eq_of_collinear_of_odd hD he hez.symm hzeD hc hec.symm hoddcz
    apply hdc
    have hcz : c = (d * e) ^ 2 := by rw [eq_inv_of_mul_eq_one_left h1, hD.inv_eq hzD]
    rw [hcz]
    exact hdz

theorem not_commute_of_collinear (hD : IsRootInvolutionSet D) {d c x : G} (hd : d ∈ D)
    (hx : x ∈ D) (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c))) (hcx : Commute c x)
    (hcxD : c * x ∈ D) : ¬ Commute d x := by
  intro hdx
  have h1 := eq_of_collinear_of_odd hD hx hcx hcxD hd hdx hodd
  apply hdc
  rw [eq_inv_of_mul_eq_one_left h1]
  exact (Commute.refl c).inv_left

theorem exists_orderOf_mul_eq_three_of_frame (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) {d c e : G} (hd : d ∈ D) (hcD : c ∈ D) (he : e ∈ D)
    (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c))) (hec : Commute e c)
    (h4 : orderOf (d * e) = 4) (hw : ((d * e) ^ 2 * c) ^ 2 ∈ rootSet D e) {a : G}
    (ha : a ∈ rootSet D d) : ∃ b ∈ rootSet D c, orderOf (a * b) = 3 := by
  have hD := h.root
  obtain ⟨hzD, hdz, -, hede⟩ := sq_mem_of_orderOf_eq_four hD hd he h4
  have hdzD : d * (d * e) ^ 2 ∈ D := by
    rw [← hede]
    have := conj_mem_of_isClass h.isClass e hd
    rwa [hD.inv_eq he] at this
  have hzc : orderOf ((d * e) ^ 2 * c) = 4 := by
    rw [orderOf_mul_comm_eq]
    exact orderOf_mul_sq_eq_four_of_commute h.isClass hD hd hcD he hdc hodd hec h4
  refine exists_orderOf_mul_eq_three h hc hs hd hcD hdc hodd hzD hdz hdzD hzc ha ?_
  have h4aw : orderOf (a * ((d * e) ^ 2 * c) ^ 2) = 4 :=
    orderOf_mul_eq_four_of_mem_rootSet hD hd he ha hw h4
  rw [mul_sq_comm_of_orderOf_eq_four hD ha.1 hw.1 h4aw]
  exact SpecialClosure.mul_sq_mem_rootSet hD hs hd he h4 ha hw

@[expose] def FrameInput (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ c ∈ D, ¬ Commute d c → Odd (orderOf (d * c)) →
    ∃ e ∈ D, Commute e c ∧ orderOf (d * e) = 4 ∧ ((d * e) ^ 2 * c) ^ 2 ∈ rootSet D e

theorem rootMoufang_of_frameInput (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hF : FrameInput D) : RootMoufang D := by
  intro d hd c hcD hdc hodd a ha
  obtain ⟨e, he, hec, h4, hw⟩ := hF d hd c hcD hdc hodd
  exact exists_orderOf_mul_eq_three_of_frame h hc hs hd hcD he hdc hodd hec h4 hw ha

theorem frameCondition_of_collinear (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hQ : CommLambda D) {d c e : G} (hd : d ∈ D) (hcD : c ∈ D)
    (he : e ∈ D) (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c))) (hec : Commute e c)
    (hecD : e * c ∈ D) (h4 : orderOf (d * e) = 4) : ((d * e) ^ 2 * c) ^ 2 ∈ rootSet D e := by
  obtain ⟨hzD, -, hez, -⟩ := sq_mem_of_orderOf_eq_four hD hd he h4
  obtain ⟨-, hezD⟩ := mul_mul_eq_mul_sq_of_orderOf_eq_four hclass hD hd he h4
  have hcz : orderOf (c * (d * e) ^ 2) = 4 :=
    orderOf_mul_sq_eq_four_of_commute hclass hD hd hcD he hdc hodd hec h4
  have := hQ e he c hcD _ hzD hec hecD hez hezD hcz
  rwa [mul_sq_comm_of_orderOf_eq_four hD hcD hzD hcz]

@[expose] def ExistsCommSpec (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ c ∈ D, ¬ Commute d c → Odd (orderOf (d * c)) →
    ∃ e ∈ D, Commute e c ∧ orderOf (d * e) = 4

theorem frameInput_of_commLambda (h : Hyp G D) (hs : SpecialClosure D) (hQ : CommLambda D)
    (hE : ExistsCommSpec D) : FrameInput D := by
  intro d hd c hcD hdc hodd
  have hD := h.root
  obtain ⟨e, he, hec, h4⟩ := hE d hd c hcD hdc hodd
  obtain ⟨hzD, hdz, -, hede⟩ := sq_mem_of_orderOf_eq_four hD hd he h4
  have hdzD : d * (d * e) ^ 2 ∈ D := by
    rw [← hede]
    have := conj_mem_of_isClass h.isClass e hd
    rwa [hD.inv_eq he] at this
  have hzc : orderOf ((d * e) ^ 2 * c) = 4 := by
    rw [orderOf_mul_comm_eq]
    exact orderOf_mul_sq_eq_four_of_commute h.isClass hD hd hcD he hdc hodd hec h4
  obtain ⟨hwD, hzw, hcw, hczc⟩ := sq_mem_of_orderOf_eq_four hD hzD hcD hzc
  have h4w : orderOf (d * ((d * e) ^ 2 * c) ^ 2) = 4 :=
    orderOf_mul_sq_eq_four h.isClass hD hd hcD hdc hodd hzD hdz hdzD hzc
  refine ⟨_, hwD, hcw.symm, h4w, ?_⟩
  have hzwD : (d * e) ^ 2 * ((d * e) ^ 2 * c) ^ 2 ∈ D := by
    rw [← hczc]
    have := conj_mem_of_isClass h.isClass c hzD
    rwa [hD.inv_eq hcD] at this
  have hzdD : (d * e) ^ 2 * d ∈ D := by rw [← hdz.eq]; exact hdzD
  have hz1 := hQ _ hzD d hd _ hwD hdz.symm hzdD hzw hzwD h4w
  exact SpecialClosure.mul_sq_mem_rootSet hD hs hzD hcD hzc hz1 (mem_rootSet_self hcD)

@[expose] def CommLambdaStep : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIH G →
    (∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) → RootClosure D → SpecialClosure D → CommLambda D

end CFSG.Timmesfeld.Bridge

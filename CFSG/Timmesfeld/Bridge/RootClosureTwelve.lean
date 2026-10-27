module

public import CFSG.Timmesfeld.Bridge.RootClosureStar
public import CFSG.Timmesfeld.Bridge.LocalA

public section

namespace CFSG.Timmesfeld.Bridge.RootClosure

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge

variable {G : Type*} [Group G] {D : Set G}

@[expose] def ThirdKindThreeStmt (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ a ∈ rootSet D d, ∀ b ∈ rootSet D d, a ≠ b → a * b ∉ D → ∀ y ∈ D,
    orderOf (a * y) = 3 → ∀ m : ℕ, Odd m → orderOf (y * (a * b)) ≠ 2 * m

private theorem dvd_three_of_odd_of_dvd_six {k : ℕ} (hk : Odd k) (h6 : k ∣ 6) : k ∣ 3 :=
  (Nat.coprime_two_right.2 hk).dvd_of_dvd_mul_left (by simpa using h6)

private theorem eq_three_of_odd_of_dvd_six {k : ℕ} (hk : Odd k) (h1 : k ≠ 1) (h6 : k ∣ 6) :
    k = 3 :=
  ((Nat.dvd_prime Nat.prime_three).1 (dvd_three_of_odd_of_dvd_six hk h6)).resolve_left h1

theorem orderOf_eq_three_of_four (hD : IsRootInvolutionSet D) {d a b y : G} (hd : d ∈ D)
    (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d) (hy : y ∈ D) (h3 : orderOf (a * y) = 3)
    (h4 : orderOf (y * (a * b)) = 4) : orderOf (b * y) = 3 := by
  have ha2 := hD.mul_self_eq_one ha.1
  have hy2 := hD.mul_self_eq_one hy
  have hu2 := (commute_of_mem_rootSet_pair hD hd ha hb).2
  have hcab : Commute a (a * b) := (Commute.refl a).mul_right (commute_of_mem_rootSet hd ha hb)
  have h6 := pow_six_of_b3 ha2 hy2 hu2 hcab (by rw [← h3]; exact pow_orderOf_eq_one _)
    (by rw [← h4]; exact pow_orderOf_eq_one _)
  rw [show y * a * (a * b) = y * b by rw [mul_assoc y a, ← mul_assoc a a, ha2, one_mul]] at h6
  obtain ⟨hby, hoddby⟩ := opposite_of_orderOf_eq_three hD hd ha hy h3 hb
  rw [orderOf_mul_comm_eq]
  refine eq_three_of_odd_of_dvd_six (by rwa [orderOf_mul_comm_eq] at hoddby) ?_
    (orderOf_dvd_of_pow_eq_one h6)
  intro h1
  apply hby
  rw [orderOf_eq_one_iff] at h1
  rw [eq_inv_of_mul_eq_one_left h1]
  exact (Commute.refl b).inv_right

theorem orderOf_eq_three_of_eight [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d a b y : G} (hd : d ∈ D) (ha : a ∈ rootSet D d)
    (hb : b ∈ rootSet D d) (hab : a ≠ b) (hy : y ∈ D) (h3 : orderOf (a * y) = 3)
    (h8 : orderOf (y * (a * b)) = 8) : orderOf (b * y) = 3 := by
  have ha2 := hD.mul_self_eq_one ha.1
  have hb2 := hD.mul_self_eq_one hb.1
  have hy2 := hD.mul_self_eq_one hy
  obtain ⟨hdy, hoddy⟩ := opposite_of_orderOf_eq_three hD hd ha hy h3 (mem_rootSet_self hd)
  obtain ⟨heD, hye, hyeD, heu⟩ := special_config_of_eight hclass hD hd ha hb hy h8
  set e := (y * (a * b)) ^ 4 with he
  obtain ⟨hea4, -, -, -, -, hpb, -, -⟩ := special_config hclass hD hd ha hb hy hdy hoddy hab
    heD hye hyeD heu
  have he2 := hD.mul_self_eq_one heD
  have hay3 : (a * y) ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one _
  have hea : (e * a) ^ 4 = 1 := by rw [← hea4]; exact pow_orderOf_eq_one _
  have hey : Commute e y := hye.symm
  have h6 : (a * (e * y)) ^ 6 = 1 := by
    have hya : (y * a) ^ 3 = 1 := by
      have : y * a = (a * y)⁻¹ := by rw [mul_inv_rev, hD.inv_eq hy, hD.inv_eq ha.1]
      rw [this, inv_pow, hay3, inv_one]
    have hae : (a * e) ^ 4 = 1 := by
      have : a * e = (e * a)⁻¹ := by rw [mul_inv_rev, hD.inv_eq heD, hD.inv_eq ha.1]
      rw [this, inv_pow, hea, inv_one]
    have := pow_six_of_b3 hy2 ha2 he2 hye hya hae
    rwa [mul_assoc, hye.eq] at this
  have hey' : e * y ∈ D := by rwa [← hye.eq]
  have haey3 : (a * e * y) ^ 3 = 1 := by
    have hdvd : orderOf (a * (e * y)) ∣ 6 := orderOf_dvd_of_pow_eq_one h6
    rcases hD.orderOf_mul ha.1 hey' with h2 | h4 | ho
    · exfalso
      have hsq2 : (a * e * y) ^ 2 = 1 := by rw [mul_assoc, ← h2]; exact pow_orderOf_eq_one _
      have hay := eq_of_q2 he2 ha2 hy2 hea hay3 hey hsq2
      rw [hay, hy2, orderOf_one] at h3
      exact absurd h3 (by norm_num)
    · rw [h4] at hdvd
      exact absurd hdvd (by norm_num)
    · rw [mul_assoc]
      exact orderOf_dvd_iff_pow_eq_one.1 (dvd_three_of_odd_of_dvd_six ho hdvd)
  set ea := a * e * a with hea'
  have hs4 := conj_eq_of_s4 he2 ha2 hy2 hea hay3 hey haey3
  set p := e * ea with hp
  have hp' : (e * a) ^ 2 = p := by rw [hp, hea', sq]; simp only [mul_assoc]
  rw [hp'] at hpb
  have hyey : y * e * y = e := by rw [← hey.eq, mul_assoc, hy2, mul_one]
  have hyp : y * p * y = ea := by
    rw [hp, show y * (e * ea) * y = (y * e * y) * (y * ea * y) by
      rw [show y * e * y * (y * ea * y) = y * e * (y * y) * ea * y by group, hy2, mul_one]
      group, hyey, hs4, ← mul_assoc, he2, one_mul]
  have hbe : b * e * b = ea := by
    have hu2 := (commute_of_mem_rootSet_pair hD hd ha hb).2
    have hb' : a * (a * b) = b := by rw [← mul_assoc, ha2, one_mul]
    have hb'' : a * b * a = b := by
      rw [mul_assoc, ← (commute_of_mem_rootSet hd ha hb).eq, ← mul_assoc, ha2, one_mul]
    have key : (a * (a * b)) * e * (a * b * a) = a * ((a * b) * e * (a * b)) * a := by group
    rw [hb', hb''] at key
    rw [key, ← heu.eq, mul_assoc e, hu2, mul_one]
  have hbea : b * ea * b = e := by
    rw [← hbe, show b * (b * e * b) * b = (b * b) * e * (b * b) by group, hb2, one_mul, mul_one]
  have hbp : b * p * b = p := by rw [← hpb.eq, mul_assoc, hb2, mul_one]
  set g := y * b with hg
  have hginv : g⁻¹ = b * y := by rw [hg, mul_inv_rev, hD.inv_eq hb.1, hD.inv_eq hy]
  have hc1 : g * e * g⁻¹ = p := by
    rw [hginv, hg, show y * b * e * (b * y) = y * (b * e * b) * y by group, hbe, hs4]
  have hc2 : g * p * g⁻¹ = ea := by
    rw [hginv, hg, show y * b * p * (b * y) = y * (b * p * b) * y by group, hbp, hyp]
  have hc3 : g * ea * g⁻¹ = e := by
    rw [hginv, hg, show y * b * ea * (b * y) = y * (b * ea * b) * y by group, hbea, hyey]
  have hr : g ^ 3 * e * (g ^ 3)⁻¹ = e := by
    rw [pow_three, show g * (g * g) * e * (g * (g * g))⁻¹ = g * (g * (g * e * g⁻¹) * g⁻¹) * g⁻¹
      by group, hc1, hc2, hc3]
  have hrc : Commute (g ^ 3) e := by
    show g ^ 3 * e = e * g ^ 3
    calc g ^ 3 * e = g ^ 3 * e * (g ^ 3)⁻¹ * g ^ 3 := by group
      _ = e * g ^ 3 := by rw [hr]
  have hpe : p ≠ e := by
    intro h1
    have hea1 : ea = 1 := mul_eq_left.mp (by rw [← hp]; exact h1)
    apply hD.ne_one heD
    rw [show e = a * ea * a by rw [hea', show a * (a * e * a) * a = (a * a) * e * (a * a) by group,
      ha2, one_mul, mul_one], hea1, mul_one, ha2]
  obtain ⟨hby, hoddby⟩ := opposite_of_orderOf_eq_three hD hd ha hy h3 hb
  have hoddg : Odd (orderOf g) := by rwa [hg, orderOf_mul_comm_eq]
  have h3dvd : 3 ∣ orderOf g := by
    by_contra hnd
    obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd)
    have hgc : Commute g e := hk ▸ hrc.pow_left k
    apply hpe
    rw [← hc1, hgc.eq, mul_inv_cancel_right]
  obtain ⟨j, hj⟩ := h3dvd
  have hor : orderOf (g ^ 3) = j := by
    rw [orderOf_pow' _ (by norm_num), hj, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _
      (by norm_num)]
  have hoddj : Odd j := by
    rw [hj] at hoddg
    exact (Nat.odd_mul.1 hoddg).2
  set r := g ^ 3 with hrdef
  have hyr : y * r * y = r⁻¹ := by
    have hyg : y * g * y = g⁻¹ := by rw [hginv, hg, ← mul_assoc, hy2, one_mul]
    rw [hrdef, show y * g ^ 3 * y = (y * g * y) ^ 3 by
      simp only [pow_succ, pow_zero, one_mul]
      rw [show y * g * y * (y * g * y) * (y * g * y) = y * g * (y * y) * g * (y * y) * g * y by
        group, hy2, mul_one, mul_one]
      group, hyg, inv_pow]
  set y' := r * y * r⁻¹ with hy'
  have hy'D : y' ∈ D := conj_mem_of_isClass hclass r hy
  have hy'y : y' * y = r ^ 2 := by
    have : y * r⁻¹ * y = r := by
      rw [show y * r⁻¹ * y = (y * r * y)⁻¹ by
        rw [mul_inv_rev, mul_inv_rev, hD.inv_eq hy]; group, hyr, inv_inv]
    rw [hy', sq, show r * y * r⁻¹ * y = r * (y * r⁻¹ * y) by group, this]
  have hy'e : Commute y' e := by
    show r * y * r⁻¹ * e = e * (r * y * r⁻¹)
    have h1 : r⁻¹ * e = e * r⁻¹ := (hrc.inv_left).eq
    have h2 : y * e = e * y := hye.eq
    rw [mul_assoc, h1, ← mul_assoc, mul_assoc r y e, h2, ← mul_assoc, hrc.eq]
    group
  have hoddy'y : Odd (orderOf (y' * y)) := by
    rw [hy'y, orderOf_pow' _ (by norm_num), hor,
      Nat.Coprime.gcd_eq_one (Nat.coprime_comm.1 (Nat.coprime_two_left.2 hoddj)), Nat.div_one]
    exact hoddj
  have h1 := Moufang.eq_of_collinear_of_odd hD heD hye hyeD hy'D hy'e hoddy'y
  rw [hy'y] at h1
  have hj1 : j = 1 := by
    rw [← hor]
    exact Nat.Coprime.eq_one_of_dvd (Nat.coprime_two_right.2 (hor ▸ hoddj))
      (orderOf_dvd_of_pow_eq_one h1)
  rw [orderOf_mul_comm_eq, ← hg, hj, hj1]

theorem twelve_of_thirdKindThree (h : Hyp G D) (h3 : ThirdKindThreeStmt D) : TwelveStmt D := by
  have := h.finite
  have hclass := h.isClass
  have hD := h.root
  intro d hd a ha b hb hab hnD y hy hay
  obtain ⟨hdy, hoddy⟩ := opposite_of_orderOf_eq_three hD hd ha hy hay (mem_rootSet_self hd)
  rcases orderOf_mul_cases hclass hD hd ha hb hy with (ho | ⟨m, hm, h2m⟩) | h4 | h8
  · exact absurd (mem_of_odd_orderOf_mul hclass hD hy
      (commute_of_mem_rootSet_pair hD hd ha hb).2 ho) hnD
  · exact absurd h2m (h3 d hd a ha b hb hab hnD y hy hay m hm)
  · exact orderOf_eq_three_of_four hD hd ha hb hy hay h4
  · exact orderOf_eq_three_of_eight hclass hD hd ha hb hab hy hay h8

end CFSG.Timmesfeld.Bridge.RootClosure

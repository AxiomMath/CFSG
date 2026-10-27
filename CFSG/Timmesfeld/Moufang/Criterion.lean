module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.Reduction.RootClass

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

theorem eq_of_collinear_of_odd (hD : IsRootInvolutionSet D) {u v f : G} (hv : v ∈ D)
    (huv : Commute u v) (huvD : u * v ∈ D) (hf : f ∈ D) (hfv : Commute f v)
    (hodd : Odd (orderOf (f * u))) : f * u = 1 := by
  have hcomm : Commute (f * u) v := hfv.mul_left huv
  have h2 := orderOf_mul_eq_two_mul_of_odd hcomm hodd (hD.orderOf_eq_two hv)
  have heq : f * (u * v) = f * u * v := by rw [mul_assoc]
  rcases hD.orderOf_mul hf huvD with h | h | h <;> rw [heq, h2] at h
  · exact orderOf_eq_one_iff.1 (by omega)
  · obtain ⟨k, hk⟩ := hodd
    omega
  · exact absurd h (Nat.not_odd_iff_even.2 (even_two_mul _))

theorem mul_mul_eq_mul_sq {w a : G} (hw : w * w = 1) : a * w * a = w * (w * a) ^ 2 := by
  rw [pow_two]
  calc a * w * a = (w * w) * a * w * a := by rw [hw, one_mul]
    _ = w * (w * a * (w * a)) := by group

theorem orderOf_mul_eq_three_of_conj_eq (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d c a b y y' w : G} (hd : d ∈ D) (hc : c ∈ D)
    (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c))) (ha : a ∈ rootSet D d)
    (hb : b ∈ rootSet D c) (hy : y ∈ D) (hdy : Commute d y) (hdyD : d * y ∈ D)
    (hy' : y' ∈ rootSet D y) (hw : w ∈ D) (hwc : Commute w c) (heq : a * w * a = b * y' * b) :
    orderOf (a * b) = 3 := by
  have haD : a ∈ D := ha.1
  have hbD : b ∈ D := hb.1
  have ha2 : a * a = 1 := hD.mul_self_eq_one haD
  have hb2 : b * b = 1 := hD.mul_self_eq_one hbD
  have hainv : a⁻¹ = a := hD.inv_eq haD
  have hbinv : b⁻¹ = b := hD.inv_eq hbD
  obtain ⟨hoddab, hab⟩ := odd_orderOf_mul_of_mem_rootSet hD hd hc ha hb hodd hdc
  have e1 : b * a * b * (b * a)⁻¹ = b * a * b * a * b := by
    rw [mul_inv_rev, hainv, hbinv]
    group
  have e2 : b * a * w * (b * a)⁻¹ = y' := by
    rw [mul_inv_rev, hainv, hbinv]
    calc b * a * w * (a * b) = b * (a * w * a) * b := by group
      _ = b * (b * y' * b) * b := by rw [heq]
      _ = (b * b) * y' * (b * b) := by group
      _ = y' := by rw [hb2, one_mul, mul_one]
  have hb'D : b * a * b * a * b ∈ D := by
    rw [← e1]
    exact conj_mem_of_isClass hclass (b * a) hbD
  have hbw : Commute b w := (hb.2 w hw).2 hwc.symm
  have hconj := (Commute.conj_iff (b * a)).2 hbw
  rw [e1, e2] at hconj
  set b' := b * a * b * a * b with hb'def
  have hb'y : Commute b' y := ((hy'.2 _ hb'D).1 hconj.symm).symm
  have hb'2 : b' * b' = 1 := hD.mul_self_eq_one hb'D
  have hb'a : b' * a = (b * a) ^ 3 := by
    rw [hb'def, pow_three]
    group
  have hodd3 : Odd (orderOf (b' * a)) := by
    rw [hb'a, orderOf_pow' _ (by norm_num : (3 : ℕ) ≠ 0)]
    have hoddba : Odd (orderOf (b * a)) := by rwa [orderOf_mul_comm_eq]
    exact Odd.of_dvd_nat hoddba (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
  have hb'a1 : b' * a = 1 := by
    by_cases hdb' : Commute d b'
    · have hab' : Commute a b' := (ha.2 _ hb'D).2 hdb'
      have h2 : (b' * a) ^ 2 = 1 := (commute_iff_mul_sq_eq_one hb'2 ha2).1 hab'.symm
      have hdvd := orderOf_dvd_of_pow_eq_one h2
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
      · exact orderOf_eq_one_iff.1 h1
      · rw [h1] at hodd3
        exact absurd hodd3 (by decide)
    · exfalso
      have h1 : Odd (orderOf (a * b')) := by rwa [orderOf_mul_comm_eq]
      have h2 : Odd (orderOf (d * b')) :=
        (odd_orderOf_mul_iff_of_mem_rootSet hD hd ha hb'D hdb').1 h1
      have h3 : Odd (orderOf (b' * d)) := by rwa [orderOf_mul_comm_eq]
      have h4 := eq_of_collinear_of_odd hD hy hdy hdyD hb'D hb'y h3
      have hb'eq : b' = d := (eq_inv_of_mul_eq_one_left h4).trans (hD.inv_eq hd)
      exact hdb' (by rw [hb'eq])
  have h3 : (b * a) ^ 3 = 1 := by rw [← hb'a, hb'a1]
  have hdvd : orderOf (b * a) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hne : orderOf (b * a) ≠ 1 := by
    intro h1
    apply hab
    rw [eq_inv_of_mul_eq_one_left (orderOf_eq_one_iff.1 h1), hainv]
  rw [← orderOf_mul_comm_eq]
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
  · exact absurd h hne
  · exact h

theorem orderOf_mul_sq_eq_four (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d c y : G} (hd : d ∈ D) (hc : c ∈ D) (hdc : ¬ Commute d c)
    (hodd : Odd (orderOf (d * c))) (hy : y ∈ D) (hdy : Commute d y) (hdyD : d * y ∈ D)
    (hyc : orderOf (y * c) = 4) : orderOf (d * (y * c) ^ 2) = 4 := by
  obtain ⟨hwD, hyw, hcw, hcyc⟩ := sq_mem_of_orderOf_eq_four hD hy hc hyc
  have hc2 : c * c = 1 := hD.mul_self_eq_one hc
  have hcinv : c⁻¹ = c := hD.inv_eq hc
  have hd2 : d * d = 1 := hD.mul_self_eq_one hd
  have hwyD : (y * c) ^ 2 * y ∈ D := by
    have := conj_mem_of_isClass hclass c hy
    rwa [hcinv, hcyc, hyw.eq] at this
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hd hwD with hdw | h4 | ⟨hoddw, hdw⟩
  · exfalso
    have h1 : Commute d (c * y * c) := by
      rw [hcyc]
      exact hdy.mul_right hdw
    have h2 := (Commute.conj_iff c).2 h1
    rw [hcinv, show c * (c * y * c) * c = (c * c) * y * (c * c) by group, hc2, one_mul,
      mul_one] at h2
    have hcdcD : c * d * c ∈ D := by
      rw [← hcinv]
      simpa [hcinv] using conj_mem_of_isClass hclass c hd
    have hodd2 : Odd (orderOf (c * d * c * d)) := by
      rw [show c * d * c * d = (c * d) ^ 2 by rw [pow_two]; group,
        orderOf_pow' _ two_ne_zero]
      have hcd : Odd (orderOf (c * d)) := by rwa [orderOf_mul_comm_eq]
      exact Odd.of_dvd_nat hcd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
    have h3 := eq_of_collinear_of_odd hD hy hdy hdyD hcdcD h2 hodd2
    have h4 : (c * d) ^ 2 = 1 := by rw [pow_two, ← mul_assoc]; exact h3
    have hcd : Odd (orderOf (c * d)) := by rwa [orderOf_mul_comm_eq]
    have hdvd := orderOf_dvd_of_pow_eq_one h4
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h5 | h5
    · apply hdc
      rw [eq_inv_of_mul_eq_one_left (orderOf_eq_one_iff.1 h5), hD.inv_eq hd]
    · rw [h5] at hcd
      exact absurd hcd (by decide)
  · exact h4
  · exfalso
    have h1 := eq_of_collinear_of_odd hD hy hyw.symm hwyD hd hdy hoddw
    apply hdc
    have hdw' : d = (y * c) ^ 2 := by
      rw [eq_inv_of_mul_eq_one_left h1, hD.inv_eq hwD]
    rw [hdw']
    exact hcw.symm

theorem exists_orderOf_mul_eq_three (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    {d c y a : G} (hd : d ∈ D) (hcD : c ∈ D) (hdc : ¬ Commute d c)
    (hodd : Odd (orderOf (d * c))) (hy : y ∈ D) (hdy : Commute d y) (hdyD : d * y ∈ D)
    (hyc : orderOf (y * c) = 4) (ha : a ∈ rootSet D d)
    (hQ : ((y * c) ^ 2 * a) ^ 2 ∈ rootSet D y) :
    ∃ b ∈ rootSet D c, orderOf (a * b) = 3 := by
  have hD := h.root
  obtain ⟨hwD, -, hcw, -⟩ := sq_mem_of_orderOf_eq_four hD hy hcD hyc
  obtain ⟨-, h2, -⟩ := special_pair_rootSet h hc hs hy hcD hyc
  obtain ⟨b, hb, hbw⟩ := h2 _ hQ _ (mem_rootSet_self hwD)
  refine ⟨b, hb, ?_⟩
  have haD := ha.1
  have hy'D : ((y * c) ^ 2 * a) ^ 2 ∈ D := hQ.1
  have h4wa : orderOf ((y * c) ^ 2 * a) = 4 := by
    rcases hD.orderOf_mul hwD haD with h2' | h4 | hodd'
    · exfalso
      refine hD.ne_one hy'D ?_
      have := pow_orderOf_eq_one ((y * c) ^ 2 * a)
      rwa [h2'] at this
    · exact h4
    · exfalso
      have hy'o : orderOf (((y * c) ^ 2 * a) ^ 2) = 2 := hD.orderOf_eq_two hy'D
      rw [orderOf_pow' _ two_ne_zero,
        Nat.Coprime.gcd_eq_one ((Nat.coprime_two_right).2 hodd'), Nat.div_one] at hy'o
      rw [hy'o] at hodd'
      exact absurd hodd' (by decide)
  obtain ⟨-, hwy', -, -⟩ := sq_mem_of_orderOf_eq_four hD hwD haD h4wa
  have hw2 := hD.mul_self_eq_one hwD
  have hy'2 := hD.mul_self_eq_one hy'D
  refine orderOf_mul_eq_three_of_conj_eq h.isClass hD hd hcD hdc hodd ha hb hy hdy hdyD
    hQ hwD hcw.symm ?_
  have e1 := mul_mul_eq_mul_sq (a := a) hw2
  have e2 : b * ((y * c) ^ 2 * a) ^ 2 * b = ((y * c) ^ 2 * a) ^ 2 * (y * c) ^ 2 := by
    rw [mul_mul_eq_mul_sq hy'2, hbw]
  rw [e1, e2, hwy'.eq]

@[expose] def CommutatorInput (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ c ∈ D, ¬ Commute d c → Odd (orderOf (d * c)) →
    ∃ y ∈ D, Commute d y ∧ d * y ∈ D ∧ orderOf (y * c) = 4 ∧
      ∀ a ∈ rootSet D d, ((y * c) ^ 2 * a) ^ 2 ∈ rootSet D y

theorem rootMoufang_of_commutatorInput (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) (hE : CommutatorInput D) : RootMoufang D := by
  intro d hd c hcD hdc hodd a ha
  obtain ⟨y, hy, hdy, hdyD, hyc, hQ⟩ := hE d hd c hcD hdc hodd
  exact exists_orderOf_mul_eq_three h hc hs hd hcD hdc hodd hy hdy hdyD hyc ha (hQ a ha)

theorem orderOf_mul_eq_three_of_line (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d c y : G} (hd : d ∈ D) (hcD : c ∈ D)
    (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c))) (hy : y ∈ D) (hdy : Commute d y)
    (hdyD : d * y ∈ D) (hyc : orderOf (y * c) = 4) (hQ : ((y * c) ^ 2 * d) ^ 2 = y) :
    orderOf (d * c) = 3 := by
  obtain ⟨hwD, hyw, hcw, hcyc⟩ := sq_mem_of_orderOf_eq_four hD hy hcD hyc
  have hw2 := hD.mul_self_eq_one hwD
  refine orderOf_mul_eq_three_of_conj_eq hclass hD hd hcD hdc hodd (mem_rootSet_self hd)
    (mem_rootSet_self hcD) hy hdy hdyD (mem_rootSet_self hy) hwD hcw.symm ?_
  rw [mul_mul_eq_mul_sq hw2, hQ, hcyc, hyw.eq]

end CFSG.Timmesfeld.Moufang

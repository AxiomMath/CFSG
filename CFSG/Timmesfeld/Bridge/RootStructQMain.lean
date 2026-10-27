module

public import CFSG.Timmesfeld.Bridge.RootStructQCenter
public import CFSG.Timmesfeld.Bridge.RootStructW96

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld RootStructQ
open scoped commutatorElement

variable {G : Type*} [Group G] {D : Set G}

namespace RootStructQ

theorem pow_three_mul_comm {x y : G} (hx : x * x = 1) (hy : y * y = 1) (h : (x * y) ^ 3 = 1) :
    (y * x) ^ 3 = 1 := by
  have e : y * x = (x * y)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy]
  rw [e, inv_pow, h, inv_one]

theorem braid_of_pow_three {a z : G} (ha : a * a = 1) (hz : z * z = 1) (h : (a * z) ^ 3 = 1) :
    z * a * z = a * z * a := by
  have e : a * z * a * (z * a * z) = 1 := by rw [← h, pow_three]; simp only [mul_assoc]
  rw [eq_inv_of_mul_eq_one_right e]
  simp only [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hz,
    mul_assoc]

theorem odd_orderOf_of_pow_three {x : G} (h : x ^ 3 = 1) : Odd (orderOf x) :=
  Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one h)

theorem eq_of_pow_three_of_commute {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (h : (x * y) ^ 3 = 1) (hc : Commute x y) : x = y := by
  have hsq : (x * y) ^ 2 = 1 := (commute_iff_mul_sq_eq_one hx hy).1 hc
  have h1 : x * y = 1 := by
    have e : (x * y) ^ 3 = (x * y) ^ 2 * (x * y) := pow_succ _ 2
    rw [h, hsq, one_mul] at e
    exact e.symm
  rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right hy]

end RootStructQ

theorem orderOf_mul_eq_four_of_pow_four (hD : IsRootInvolutionSet D) {z p : G} (hz : z ∈ D)
    (hp : p ∈ D) (hzp : ¬ Commute z p) (h : (z * p) ^ 4 = 1) : orderOf (z * p) = 4 := by
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hz hp with h' | h' | ⟨h', -⟩
  · exact absurd h' hzp
  · exact h'
  · exfalso
    have h1 : orderOf (z * p) = 1 := by
      have hdvd : orderOf (z * p) ∣ 2 ^ 2 := by simpa using orderOf_dvd_of_pow_eq_one h
      exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr h'))
        hdvd
    apply hzp
    rw [eq_inv_of_mul_eq_one_left (orderOf_eq_one_iff.1 h1), hD.inv_eq hp]

theorem mul_inv_mul_inv_eq_sq_of_mem (hD : IsRootInvolutionSet D) {s t : G} (hs : s ∈ D)
    (ht : t ∈ D) : s * t * s⁻¹ * t⁻¹ = (s * t) ^ 2 := by
  rw [hD.inv_eq hs, hD.inv_eq ht, sq, ← mul_assoc]

variable [Finite G]

theorem sq_conj_mul_eq_of_pow_three (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hOD : OppositeDetermines D)
    {d f z : G} (hd : d ∈ D) (hf : f ∈ D) (hfZ : f ∈ nCoreZ D d 2) (hz : z ∈ D)
    (h3 : (f * z) ^ 3 = 1) (hfz : ¬ Commute f z) (h4 : orderOf (z * d) = 4) :
    (z * d * z * f) ^ 2 = d := by
  have hf2 := hD.mul_self_eq_one hf
  have hz2 := hD.mul_self_eq_one hz
  have hd2 := hD.mul_self_eq_one hd
  have hz' : z⁻¹ = z := hD.inv_eq hz
  have hfN := nCoreZ_le_nCore D d 2 hfZ
  have hfQ := mem_twoCore_of_mem_nCore hfN
  have hfd : Commute f d := commute_of_mem_nCore hfN
  have hwD : z * d * z ∈ D := by simpa [hD.inv_eq hz] using conj_mem_of_isClass hclass z hd
  have hwQ : z * d * z ∈ Moufang.twoCore d :=
    conj_mem_twoCore_of_orderOf_eq_four hclass hD hz hd h4
  have hfw : ¬ Commute f (z * d * z) :=
    not_commute_conj_of_odd_special hD hf hz hd hfz (odd_orderOf_of_pow_three h3) h4 hfd
  have hbraid := braid_of_pow_three hf2 hz2 h3
  set w := z * d * z with hw
  clear_value w
  have hw2 := hD.mul_self_eq_one hwD
  have hdw : Commute d w := (Moufang.commute_of_mem_twoCore hwQ).symm
  have hcT : (f * w) ^ 2 ∈ rootSet D d :=
    sq_mem_rootSet_of_mem_nCoreZ_two hclass hD hOD hd hf hfZ hwD hwQ hfw
  have h4fw : orderOf (f * w) = 4 := orderOf_mul_eq_four_of_mem_twoCore hD hf hwD hfQ hwQ hfw
  rw [mul_sq_eq_mul_sq_comm hw2 hf2 (by rwa [orderOf_mul_comm_eq])]
  by_contra hne
  have hmem : d * (f * w) ^ 2 ∈ rootSet D d :=
    hc d hd d (mem_rootSet_self hd) _ hcT fun h => hne h.symm
  set r := f * w * f with hr
  clear_value r
  have hfwr : (f * w) ^ 2 = r * w := by rw [hr, sq]; simp only [mul_assoc]
  have hwfr : (w * f) ^ 2 = w * r := by rw [hr, sq]; simp only [mul_assoc]
  have hrw : r * w = w * r := by
    rw [← hfwr, ← hwfr, mul_sq_eq_mul_sq_comm hf2 hw2 h4fw]
  have hdr : Commute d r := by
    rw [hr]
    exact (hfd.symm.mul_right hdw).mul_right hfd.symm
  have czd : z * d * z⁻¹ = w := by rw [hz', hw]
  have czw : z * w * z⁻¹ = d := by rw [← czd, conj_conj_of_sq hz2]
  have czr : z * r * z⁻¹ = r := by
    rw [hz', hr, hw]
    calc z * (f * (z * d * z) * f) * z = (z * f * z) * d * (z * f * z) := by group
      _ = (f * z * f) * d * (f * z * f) := by rw [hbraid]
      _ = f * z * (f * d * f) * z * f := by group
      _ = f * (z * d * z) * f := by rw [hfd.eq, mul_assoc d f f, hf2, mul_one]; group
  have hzπ : Commute z (d * (f * w) ^ 2) := by
    apply commute_of_conj_eq
    rw [hfwr]
    calc z * (d * (r * w)) * z⁻¹ = (z * d * z⁻¹) * (z * r * z⁻¹) * (z * w * z⁻¹) := by group
      _ = w * r * d := by rw [czd, czr, czw]
      _ = d * (r * w) := by
          rw [mul_assoc w r d, ← hdr.eq, ← mul_assoc, ← hdw.eq, mul_assoc, ← hrw]
  exact not_commute_of_orderOf_mul_eq_four hz2 hd2 h4 ((hmem.2 z hz).1 hzπ.symm).symm

theorem mem_nCoreZ_two_of_orderOf_eq_three (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hOD : OppositeDetermines D)
    {d f y z : G} (hd : d ∈ D) (hf : f ∈ D) (hfZ : f ∈ nCoreZ D d 2) (hfd : f ∉ rootSet D d)
    (hy : y ∈ D) (hfy : Commute f y) (hyd : Commute y d) (hydD : y * d ∈ D) (hz : z ∈ D)
    (hzf : ¬ Commute z f) (hoddzf : Odd (orderOf (z * f))) (h4 : orderOf (z * d) = 4)
    (h3 : (z * y) ^ 3 = 1) (hzy : ¬ Commute z y) : y ∈ nCoreZ D d 2 := by
  have hz2 := hD.mul_self_eq_one hz
  have hd2 := hD.mul_self_eq_one hd
  have hy2 := hD.mul_self_eq_one hy
  have hfN := nCoreZ_le_nCore D d 2 hfZ
  have hfQ := mem_twoCore_of_mem_nCore hfN
  have hfd' : Commute f d := commute_of_mem_nCore hfN
  have hwD : z * d * z ∈ D := by simpa [hD.inv_eq hz] using conj_mem_of_isClass hclass z hd
  have hwQ : z * d * z ∈ Moufang.twoCore d :=
    conj_mem_twoCore_of_orderOf_eq_four hclass hD hz hd h4
  have hdw : Commute d (z * d * z) := (Moufang.commute_of_mem_twoCore hwQ).symm
  have hfw : ¬ Commute f (z * d * z) := not_commute_conj_of_odd_special hD hf hz hd
    (fun h => hzf h.symm) (by rwa [orderOf_mul_comm_eq]) h4 hfd'
  have h4wf : orderOf (z * d * z * f) = 4 :=
    orderOf_mul_eq_four_of_mem_twoCore hD hwD hf hwQ hfQ fun h => hfw h.symm
  obtain ⟨fb, hfb, hsq⟩ := exists_mem_rootSet_sq_eq_right hclass hD hc hOD hd hf hfZ hfd hwD hwQ
    h4wf (mem_rootSet_self hd)
  have hfb2 := hD.mul_self_eq_one hfb.1
  have hfbZ := mem_nCoreZ_two_of_mem_rootSet hclass hD hc hOD hd hf hfZ hfd hfb
  have hfbN := nCoreZ_le_nCore D d 2 hfbZ
  have hfbQ := mem_twoCore_of_mem_nCore hfbN
  have hfbd : Commute fb d := commute_of_mem_nCore hfbN
  have hfbnd : fb ∉ rootSet D d := fun h => hfd (by
    have e : rootSet D f = rootSet D d := (rootSet_eq_of_mem hfb).symm.trans (rootSet_eq_of_mem h)
    rw [← e]
    exact mem_rootSet_self hf)
  have hfbdD : fb * d ∈ D :=
    mul_mem_of_mem_F hclass hD hc hOD hd hfb.1 hfbZ hfbnd (mem_rootSet_self hd)
  obtain ⟨hzfb, hoddzfb⟩ := opposite_of_mem_rootSet_of_opposite hD hz hf (mem_rootSet_self hz)
    hfb ⟨hzf, hoddzf⟩
  have hfbw : fb * (z * d * z) * fb = d * (z * d * z) := by
    have e : z * d * z * fb * (z * d * z) * fb = d := by
      have h := hsq
      rw [sq] at h
      simpa only [mul_assoc] using h
    have hw2 := hD.mul_self_eq_one hwD
    calc fb * (z * d * z) * fb = (z * d * z) * (z * d * z) * fb * (z * d * z) * fb := by
          rw [hw2, one_mul]
      _ = (z * d * z) * (z * d * z * fb * (z * d * z) * fb) := by simp only [mul_assoc]
      _ = d * (z * d * z) := by rw [e, ← hdw.eq]
  have h3fb : (fb * z) ^ 3 = 1 := pow_three_eq_one_of_four_group hfb2 hz2 hd2 hdw hfbd hfbw rfl
    hfbQ (by rwa [orderOf_mul_comm_eq])
  have h1 : (z * (fb * d)) ^ 3 = 1 := pow_three_eq_one_of_orbit hclass hD hfb.1 hz hd h3fb
    (fun h => hzfb h.symm) hfbd hfbdD h4
  have h2 : (z * (y * d)) ^ 3 = 1 := pow_three_eq_one_of_orbit hclass hD hy hz hd
    (pow_three_mul_comm hz2 hy2 h3) (fun h => hzy h.symm) hyd hydD h4
  have hfby : Commute fb y := (hfb.2 y hy).2 hfy
  obtain ⟨hg, hconj⟩ := conj_eq_of_wStarD4' hfb2 hz2 hy2 hd2 h3fb h3
    (by rw [← h4]; exact pow_orderOf_eq_one _) hfby hfbd hyd h1 h2
  rw [← hconj]
  exact conj_mem_nCoreZ_of_commute hclass hD hd hg hfbZ

theorem exists_opposite_orderOf_eq_three (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hOD : OppositeDetermines D)
    {d f y z : G} (hd : d ∈ D) (hf : f ∈ D) (hfZ : f ∈ nCoreZ D d 2) (hy : y ∈ D)
    (hfy : Commute f y) (hyd : Commute y d) (hydD : y * d ∈ D) (hfyD : f * y ∈ D)
    (hfydD : f * y * d ∈ D) (hz : z ∈ D) (h3 : (f * z) ^ 3 = 1) (hfz : ¬ Commute f z)
    (hzy : ¬ Commute z y) (hoddzy : Odd (orderOf (z * y))) (h4 : orderOf (z * d) = 4) :
    ∃ z' ∈ D, (¬ Commute z' f ∧ Odd (orderOf (z' * f))) ∧ orderOf (z' * d) = 4 ∧
      (z' * y) ^ 3 = 1 ∧ ¬ Commute z' y := by
  have hf2 := hD.mul_self_eq_one hf
  have hz2 := hD.mul_self_eq_one hz
  have hd2 := hD.mul_self_eq_one hd
  have hy2 := hD.mul_self_eq_one hy
  have hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D := fun g x hx => conj_mem_of_isClass hclass g hx
  have hfN := nCoreZ_le_nCore D d 2 hfZ
  have hfd' : Commute f d := commute_of_mem_nCore hfN
  have hyQ : y ∈ Moufang.twoCore d := mem_twoCore_of_collinear hclass hD hd hy hyd hydD
  have hwD : z * d * z ∈ D := by simpa [hD.inv_eq hz] using conj_mem_of_isClass hclass z hd
  have hwQ : z * d * z ∈ Moufang.twoCore d :=
    conj_mem_twoCore_of_orderOf_eq_four hclass hD hz hd h4
  have hK := sq_conj_mul_eq_of_pow_three hclass hD hc hOD hd hf hfZ hz h3 hfz h4
  have hyw : ¬ Commute y (z * d * z) := not_commute_conj_of_odd_special hD hy hz hd
    (fun h => hzy h.symm) (by rwa [orderOf_mul_comm_eq]) h4 hyd
  have hdw : Commute d (z * d * z) := (Moufang.commute_of_mem_twoCore hwQ).symm
  have hwdD : d * (z * d * z) ∈ D := by
    have h4' : orderOf (d * z) = 4 := by rwa [orderOf_mul_comm_eq]
    rw [show d * (z * d * z) = (d * z) ^ 2 by rw [sq]; simp only [mul_assoc]]
    exact hD.sq_mem hd hz h4'
  set w := z * d * z with hw
  clear_value w
  have hw2 := hD.mul_self_eq_one hwD
  have hfwf : f * w * f = w * d := by
    have e : w * f * w * f = d := by
      have h := hK
      rw [sq] at h
      simpa only [mul_assoc] using h
    calc f * w * f = (w * w) * f * w * f := by rw [hw2, one_mul]
      _ = w * (w * f * w * f) := by simp only [mul_assoc]
      _ = w * d := by rw [e]
  have h4yw : orderOf (y * w) = 4 := orderOf_mul_eq_four_of_mem_twoCore hD hy hwD hyQ hwQ hyw
  have h4wy : orderOf (w * y) = 4 := by rwa [orderOf_mul_comm_eq]
  obtain ⟨hpD, hwp, hyp, hywy⟩ := sq_mem_of_orderOf_eq_four hD hwD hy h4wy
  have hypD : y * (w * y) ^ 2 ∈ D := by
    have := mul_sq_mem_of_orderOf_eq_four hclass hD hy hwD h4yw
    rwa [mul_sq_eq_mul_sq_comm hy2 hw2 h4yw] at this
  have hwyw : y * (w * y) ^ 2 = w * y * w := by
    have hc2 : w * y * w * (w * y * w) = 1 := by
      rw [show w * y * w * (w * y * w) = w * y * (w * w) * y * w by simp only [mul_assoc], hw2,
        mul_one, show w * y * y * w = w * (y * y) * w by simp only [mul_assoc], hy2, mul_one,
        hw2]
    have e4 : (y * w) ^ 4 = 1 := by rw [← h4yw]; exact pow_orderOf_eq_one _
    calc y * (w * y) ^ 2 = y * (w * y) ^ 2 * (w * y * w * (w * y * w)) := by rw [hc2, mul_one]
      _ = (y * w) ^ 4 * (w * y * w) := by
          rw [show (y * w) ^ 4 = y * w * y * w * y * w * y * w by
            rw [pow_succ, pow_succ, pow_succ, pow_one]; simp only [mul_assoc], sq]
          simp only [mul_assoc]
      _ = w * y * w := by rw [e4, one_mul]
  set p := (w * y) ^ 2 with hp
  clear_value p
  have hp2 := hD.mul_self_eq_one hpD
  have haD : y * w * y ∈ D := by simpa [hD.inv_eq hy] using conj_mem_of_isClass hclass y hwD
  set a := y * w * y with ha
  clear_value a
  have ha2 := hD.mul_self_eq_one haD
  have hwa : Commute w a := by rw [hywy]; exact (Commute.refl w).mul_right hwp
  have hwaD : w * a = p := by rw [hywy, ← mul_assoc, hw2, one_mul]
  have haw : a * w = p := by rw [← hwa.eq, hwaD]
  have hp1 : p ≠ 1 := hD.ne_one hpD
  have ha_not : a ∉ rootSet D w := by
    intro hmem
    have hne : w ≠ a := fun h => hp1 (by rw [← hwaD, ← h, hw2])
    have h1 := hc w hwD w (mem_rootSet_self hwD) a hmem hne
    rw [hwaD] at h1
    exact hyw (((h1.2 y hy).1 hyp.symm).symm)
  obtain ⟨b', hb'D, hab', hwb'⟩ := exists_opposite_of_not_mem_rootSet hclass hOD hwD haD ha_not
  have hnwb' : ¬ Commute w b' := (not_commute_of_opposite_of_line hD haD hwD hwa.symm
    (by rw [haw]; exact hpD) hb'D hab'.1 hab'.2).1
  have h4b'w : orderOf (b' * w) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hwD hb'D with h | h | ⟨h, h'⟩
    · exact absurd h hnwb'
    · rwa [orderOf_mul_comm_eq]
    · exact absurd ⟨h', h⟩ hwb'
  obtain ⟨z', hz'D, hz'Q, -, -, hz'a⟩ := exists_conj_eq_mul_of_odd_special hD hN haD hb'D hwD
    hab'.1 hab'.2 h4b'w hwa.symm (by rw [haw]; exact hpD)
  rw [haw] at hz'a
  have hz'2 := hD.mul_self_eq_one hz'D
  have hz'w : Commute z' w := qdCore_commute hD hN haD hb'D hwD hab'.1 hab'.2 h4b'w hwa.symm z'
    hz'Q w self_mem_qdCore
  have hpa : Commute p a := by rw [← hwaD]; exact hwa.mul_left (Commute.refl a)
  have hya : y * a * y = p * a := by
    have e1 : y * a * y = w := by
      rw [ha, show y * (y * w * y) * y = (y * y) * w * (y * y) by simp only [mul_assoc], hy2,
        one_mul, mul_one]
    have e2 : p * a = w := by rw [← hwaD, mul_assoc, ha2, mul_one]
    exact e1.trans e2.symm
  have hz'p : z' * p * z' = a := by
    rw [← hz'a, show z' * (z' * a * z') * z' = (z' * z') * a * (z' * z') by
      simp only [mul_assoc], hz'2, one_mul, mul_one]
  have hyQp : y ∈ Moufang.twoCore p := mem_twoCore_of_collinear hclass hD hpD hy hyp hypD
  have hodd := odd_orderOf_mul_of_four_group hD hy hz'D hp2 hpa hyp hya hz'p (hD.ne_one haD)
  have h3' := pow_three_eq_one_of_four_group hy2 hz'2 hp2 hpa hyp hya hz'p hyQp hodd
  have hz'y : ¬ Commute z' y := fun h => hyw (by
    rw [eq_of_pow_three_of_commute hy2 hz'2 h3' h.symm]
    exact hz'w)
  have hz'd : ¬ Commute z' d := fun h => not_opposite_of_mem_twoCore_of_commute hD hyQ hz'D h
    ⟨fun h' => hz'y h'.symm, odd_orderOf_of_pow_three h3'⟩
  have hz'd' : ¬ (¬ Commute z' d ∧ Odd (orderOf (z' * d))) := by
    rintro ⟨-, hodd'⟩
    have h1 := Moufang.eq_of_collinear_of_odd hD hwD hdw hwdD hz'D hz'w hodd'
    have e : z' = d := by rw [eq_inv_of_mul_eq_one_left h1, hD.inv_eq hd]
    subst e
    exact hz'd (Commute.refl _)
  have h4z'd : orderOf (z' * d) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hz'D hd with h | h | ⟨h, h'⟩
    · exact absurd h hz'd
    · exact h
    · exact absurd ⟨h', h⟩ hz'd'
  have hz'f : ¬ Commute z' f := by
    intro h
    have h1 : Commute z' (w * d) := by rw [← hfwf]; exact (h.mul_right hz'w).mul_right h
    have e : d = w * (w * d) := by rw [← mul_assoc, hw2, one_mul]
    exact hz'd (by rw [e]; exact hz'w.mul_right h1)
  have hda : Commute d a := by rw [ha]; exact (hyd.symm.mul_right hdw).mul_right hyd.symm
  have hfa : f * a * f = a * d := by
    have cfy : f * y * f⁻¹ = y := by rw [hfy.eq, mul_inv_cancel_right]
    have cfw : f * w * f⁻¹ = w * d := by rw [hD.inv_eq hf, hfwf]
    calc f * a * f = f * a * f⁻¹ := by rw [hD.inv_eq hf]
      _ = (f * y * f⁻¹) * (f * w * f⁻¹) * (f * y * f⁻¹) := by rw [ha]; group
      _ = y * (w * d) * y := by rw [cfy, cfw]
      _ = a * d := by
          rw [ha, show y * (w * d) * y = y * w * (d * y) by simp only [mul_assoc], ← hyd.eq]
          simp only [mul_assoc]
  have hz'f4 : orderOf (z' * f) ≠ 4 := by
    intro h4z'f
    have hfp : Commute f p := by
      apply commute_of_conj_eq
      calc f * p * f⁻¹ = (f * w * f) * (f * a * f) := by
            rw [← hwaD, hD.inv_eq hf]
            simp only [mul_assoc, ← mul_assoc f f, hf2, one_mul]
        _ = w * (d * a) * d := by rw [hfwf, hfa]; simp only [mul_assoc]
        _ = p := by rw [hda.eq, ← hwaD]; simp only [mul_assoc, hd2, mul_one]
    have hz'pc : ¬ Commute z' p := fun h => by
      have e : a = p := by rw [← hz'p, h.eq, mul_assoc, hz'2, mul_one]
      have h2 : w * a = a := by rw [hwaD, e]
      exact hD.ne_one hwD (mul_eq_right.mp h2)
    have h4z'p : orderOf (z' * p) = 4 := by
      refine orderOf_mul_eq_four_of_pow_four hD hz'D hpD hz'pc ?_
      have hsq : (z' * p) ^ 2 = a * p := by
        rw [sq, show z' * p * (z' * p) = (z' * p * z') * p by simp only [mul_assoc], hz'p]
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq]
      exact (commute_iff_mul_sq_eq_one ha2 hp2).1 hpa.symm
    have hyf : Commute y f := hfy.symm
    have hyfD : y * f ∈ D := by rw [← hfy.eq]; exact hfyD
    have e1 : (z' * (y * p)) ^ 3 = 1 := pow_three_eq_one_of_orbit hclass hD hy hz'D hpD h3'
      (fun h => hz'y h.symm) hyp hypD h4z'p
    have e2 : (z' * (f * y)) ^ 3 = 1 := by
      rw [hfy.eq]
      exact pow_three_eq_one_of_orbit hclass hD hy hz'D hf h3' (fun h => hz'y h.symm) hyf hyfD
        h4z'f
    have hyfz' : ¬ Commute (y * f) z' := (opposite_of_opposite_of_special_of_line hclass hD hy hf
      hyf hyfD hz'D (fun h => hz'y h.symm) (odd_orderOf_of_pow_three h3') h4z'f).1
    have hpd : Commute p d := by rw [← hwaD]; exact hdw.symm.mul_left hda.symm
    have hfypD : f * y * p ∈ D := by
      have hwfw : w * f * w = d * f := by
        calc w * f * w = w * (f * w * f) * f := by
              rw [show w * (f * w * f) * f = w * f * w * (f * f) by simp only [mul_assoc], hf2,
                mul_one]
          _ = d * f := by rw [hfwf, ← mul_assoc, hw2, one_mul]
      have hwdw : w * d * w = d := by rw [← hdw.eq, mul_assoc, hw2, mul_one]
      have e : w * (f * y * d) * w⁻¹ = f * y * p := by
        rw [show w * (f * y * d) * w⁻¹ = (w * f * w⁻¹) * (w * y * w⁻¹) * (w * d * w⁻¹) by group,
          hD.inv_eq hwD, hwfw, ← hwyw, hwdw]
        calc d * f * (y * p) * d = f * (d * y) * p * d := by
              rw [← hfd'.eq]; simp only [mul_assoc]
          _ = f * y * (d * p) * d := by rw [← hyd.eq]; simp only [mul_assoc]
          _ = f * y * p := by rw [← hpd.eq]; simp only [mul_assoc, hd2, mul_one]
      rw [← e]
      exact conj_mem_of_isClass hclass w hfydD
    have hfyp : Commute (f * y) p := hfp.mul_left hyp
    have e3 : (z' * (f * y * p)) ^ 3 = 1 := pow_three_eq_one_of_orbit hclass hD hfyD hz'D hpD
      (pow_three_mul_comm hz'2 (hD.mul_self_eq_one hfyD) e2)
      (by rw [hfy.eq]; exact hyfz') hfyp hfypD h4z'p
    obtain ⟨hcomm, -⟩ := conj_eq_mul_of_wStarD4 hy2 hz'2 hf2 hp2 h3'
      (by rw [← h4z'f]; exact pow_orderOf_eq_one _) (by rw [← h4z'p]; exact pow_orderOf_eq_one _)
      hyf hyp hfp e1 e2 e3
    have hfa' : Commute f a := by
      have e := (Commute.conj_iff z').2 hcomm
      rwa [hD.inv_eq hz'D, show z' * (z' * f * z') * z' = (z' * z') * f * (z' * z') by
        simp only [mul_assoc], hz'2, one_mul, mul_one, hz'p] at e
    apply hD.ne_one hd
    have e : a * d = a := by rw [← hfa, hfa'.eq, mul_assoc, hf2, mul_one]
    calc d = a * (a * d) := by rw [← mul_assoc, ha2, one_mul]
      _ = 1 := by rw [e, ha2]
  refine ⟨z', hz'D, ⟨hz'f, ?_⟩, h4z'd, pow_three_mul_comm hy2 hz'2 h3', hz'y⟩
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hz'D hf with h | h | ⟨h, -⟩
  · exact absurd h hz'f
  · exact absurd h hz'f4
  · exact h

theorem mem_nCoreZ_two_of_collinear (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hOD : OppositeDetermines D)
    {d f y : G} (hd : d ∈ D) (hf : f ∈ D) (hfZ : f ∈ nCoreZ D d 2) (hfd : f ∉ rootSet D d)
    (hy : y ∈ D) (hfy : Commute f y) (hfyD : f * y ∈ D) (hyd : Commute y d) (hydD : y * d ∈ D)
    (hfydD : f * y * d ∈ D) : y ∈ nCoreZ D d 2 := by
  have hf2 := hD.mul_self_eq_one hf
  have hd2 := hD.mul_self_eq_one hd
  have hy2 := hD.mul_self_eq_one hy
  have hfN := nCoreZ_le_nCore D d 2 hfZ
  have hfd' : Commute f d := commute_of_mem_nCore hfN
  have hfdD : f * d ∈ D := mul_mem_of_mem_F hclass hD hc hOD hd hf hfZ hfd (mem_rootSet_self hd)
  obtain ⟨z, hz, h3, hfz, h4⟩ := exists_orderOf_eq_three_of_collinear hclass hD hc hOD hf hd hfd'
    hfdD fun h => hfd (mem_rootSet_comm hf h)
  have hz2 := hD.mul_self_eq_one hz
  have hoddfz := odd_orderOf_of_pow_three h3
  have hzy : ¬ Commute y z := (not_commute_of_opposite_of_line hD hf hy hfy hfyD hz hfz hoddfz).1
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hy hz with h | h4yz | ⟨hodd, -⟩
  · exact absurd h hzy
  ·
    have h4zy : orderOf (z * y) = 4 := by rwa [orderOf_mul_comm_eq]
    have e1 : (z * (f * d)) ^ 3 = 1 :=
      pow_three_eq_one_of_orbit hclass hD hf hz hd h3 hfz hfd' hfdD h4
    have e2' : (z * (f * y)) ^ 3 = 1 :=
      pow_three_eq_one_of_orbit hclass hD hf hz hy h3 hfz hfy hfyD h4zy
    have hfyz : ¬ Commute (f * y) z := (opposite_of_opposite_of_special_of_line hclass hD hf hy
      hfy hfyD hz hfz hoddfz h4zy).1
    have e3' : (z * (f * y * d)) ^ 3 = 1 := pow_three_eq_one_of_orbit hclass hD hfyD hz hd
      (pow_three_mul_comm hz2 (hD.mul_self_eq_one hfyD) e2') hfyz (hfd'.mul_left hyd) hfydD h4
    obtain ⟨hg, hconj⟩ := conj_eq_mul_of_wStarD4 hf2 hz2 hy2 hd2 h3
      (by rw [← h4zy]; exact pow_orderOf_eq_one _) (by rw [← h4]; exact pow_orderOf_eq_one _)
      hfy hfd' hyd e1 (by rw [← hfy.eq]; exact e2') (by rw [← hfy.eq]; exact e3')
    have hfyZ : f * y ∈ nCoreZ D d 2 := by
      rw [← hconj]
      exact conj_mem_nCoreZ_of_commute hclass hD hd hg hfZ
    have e : y = f * (f * y) := by rw [← mul_assoc, hf2, one_mul]
    rw [e]
    exact (nCoreZ D d 2).mul_mem hfZ hfyZ
  ·
    obtain ⟨z', hz', hz'f, h4', h3', hz'y⟩ := exists_opposite_orderOf_eq_three hclass hD hc hOD hd
      hf hfZ hy hfy hyd hydD hfyD hfydD hz h3 hfz (fun h => hzy h.symm)
      (by rwa [orderOf_mul_comm_eq]) h4
    exact mem_nCoreZ_two_of_orderOf_eq_three hclass hD hc hOD hd hf hfZ hfd hy hfy hyd hydD hz'
      hz'f.1 hz'f.2 h4' h3' hz'y

theorem mem_nCoreZ_two_of_mem_nCoreZ_three (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hOD : OppositeDetermines D)
    {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hxd : Commute x d) (hxdD : x * d ∈ D)
    (hx3 : x ∈ nCoreZ D d 3) : x ∈ nCoreZ D d 2 := by
  by_contra hx2
  have hxN : x ∈ nCore D d := nCoreZ_le_nCore D d 3 hx3
  have hxQ := mem_twoCore_of_mem_nCore hxN
  obtain ⟨t, ht, htQ, hnot⟩ := exists_commutator_not_mem_nCoreZ (k := 1) hxN hx2
  have htN := mem_nCore_of_mem_twoCore ht htQ
  rw [mul_inv_mul_inv_eq_sq_of_mem hD hx ht] at hnot
  have hxt : ¬ Commute x t := fun h => hnot (by
    rw [(commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hx) (hD.mul_self_eq_one ht)).1 h]
    exact one_mem _)
  have h4 := orderOf_mul_eq_four_of_mem_twoCore hD hx ht hxQ htQ hxt
  obtain ⟨hαD, hxα, -, htxt⟩ := sq_mem_of_orderOf_eq_four hD hx ht h4
  have hαZ : (x * t) ^ 2 ∈ nCoreZ D d 2 := by
    have h := commutator_mem_nCoreZ (k := 2) hx3 htN
    rwa [mul_inv_mul_inv_eq_sq_of_mem hD hx ht] at h
  have hαT : (x * t) ^ 2 ∉ rootSet D d := fun h =>
    hnot (mem_nCoreZ_one_of_mem_rootSet hclass hD hd h)
  have htd : Commute t d := Moufang.commute_of_mem_twoCore htQ
  have hαxD : (x * t) ^ 2 * x ∈ D := by
    rw [← hxα.eq, ← htxt]
    simpa [hD.inv_eq ht] using conj_mem_of_isClass hclass t hx
  have hαxdD : (x * t) ^ 2 * x * d ∈ D := by
    rw [← hxα.eq, ← htxt, show t * x * t * d = t * (x * d) * t⁻¹ by
      rw [hD.inv_eq ht, mul_assoc (t * x) t d, htd.eq]; simp only [mul_assoc]]
    exact conj_mem_of_isClass hclass t hxdD
  exact hx2 (mem_nCoreZ_two_of_collinear hclass hD hc hOD hd hαD hαZ hαT hx hxα.symm hαxD hxd
    hxdD hαxdD)

theorem upperCentralSeries_nCore_two_eq_top_of_rootClosure
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D) (hc : RootClosure D)
    (hOD : OppositeDetermines D) {d : G} (hd : d ∈ D) :
    Subgroup.upperCentralSeries (nCore D d) 2 = ⊤ := by
  have := isNilpotent_nCore D d
  rw [Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le]
  by_contra! h
  obtain ⟨e, ⟨he, heQ⟩, heN, he3, he2⟩ := exists_mem_upperCentralSeries_layer
    (subset_nCore D d) (closure_eq_nCore D d)
    (fun _ hs _ ht => commutatorElement_eq_one_or_mem_twoCore hD hs.1 ht.1 hs.2 ht.2)
    (i := 3) (by norm_num) h
  have he3' : e ∈ nCoreZ D d 3 := ⟨⟨e, heN⟩, he3, rfl⟩
  have he2' : e ∉ nCoreZ D d 2 := fun h' => he2 (mem_nCoreZ_iff.1 h').2
  have he2v := hD.mul_self_eq_one he
  obtain ⟨x, hx, hxQ, hnot⟩ := exists_commutator_not_mem_nCoreZ (k := 1) heN he2'
  have hxN := mem_nCore_of_mem_twoCore hx hxQ
  have hxd : Commute x d := Moufang.commute_of_mem_twoCore hxQ
  rw [mul_inv_mul_inv_eq_sq_of_mem hD he hx] at hnot
  have hex : ¬ Commute e x := fun h' => hnot (by
    rw [(commute_iff_mul_sq_eq_one he2v (hD.mul_self_eq_one hx)).1 h']
    exact one_mem _)
  have h4ex := orderOf_mul_eq_four_of_mem_twoCore hD he hx heQ hxQ hex
  obtain ⟨hαD, heα, -, hxex⟩ := sq_mem_of_orderOf_eq_four hD he hx h4ex
  have hαZ : (e * x) ^ 2 ∈ nCoreZ D d 2 := by
    have h' := commutator_mem_nCoreZ (k := 2) he3' hxN
    rwa [mul_inv_mul_inv_eq_sq_of_mem hD he hx] at h'
  have hαT : (e * x) ^ 2 ∉ rootSet D d := fun h' =>
    hnot (mem_nCoreZ_one_of_mem_rootSet hclass hD hd h')
  have hαN := nCoreZ_le_nCore D d 2 hαZ
  have hαQ := mem_twoCore_of_mem_nCore hαN
  obtain ⟨y, hy, hyQ, hαy⟩ : ∃ y ∈ D, y ∈ Moufang.twoCore d ∧ ¬ Commute ((e * x) ^ 2) y := by
    by_contra! hall
    exact hnot ((mem_nCoreZ_one_iff hαN).2 hall)
  have hy2 := hD.mul_self_eq_one hy
  have h4yα := orderOf_mul_eq_four_of_mem_twoCore hD hy hαD hyQ hαQ fun h' => hαy h'.symm
  have hyX : ∀ d' ∈ rootSet D d, y * d' ∈ D := fun d' hd' =>
    mul_mem_of_special_F hclass hD hc hOD hd hαD hαZ hαT hy hyQ h4yα hd'
  have hyd : Commute y d := Moufang.commute_of_mem_twoCore hyQ
  have hed : Commute e d := Moufang.commute_of_mem_twoCore heQ
  by_cases hey : Commute e y
  ·
    have he'D : e * (e * x) ^ 2 ∈ D := by
      rw [← hxex]
      simpa [hD.inv_eq hx] using conj_mem_of_isClass hclass x he
    have he'3 : e * (e * x) ^ 2 ∈ nCoreZ D d 3 := by
      rw [← hxex, show x * e * x = x * e * x⁻¹ by rw [hD.inv_eq hx]]
      exact conj_mem_nCoreZ_of_commute hclass hD hd hxd he3'
    have he'2 : e * (e * x) ^ 2 ∉ nCoreZ D d 2 := fun h' => he2' (by
      have h'' := conj_mem_nCoreZ_of_commute hclass hD hd hxd h'
      rwa [← hxex, show x * (x * e * x) * x⁻¹ = (x * x) * e * (x * x⁻¹) by group,
        hD.mul_self_eq_one hx, mul_inv_cancel, one_mul, mul_one] at h'')
    have hd₁ : ((e * x) ^ 2 * y) ^ 2 ∈ rootSet D d :=
      sq_mem_rootSet_of_mem_nCoreZ_two hclass hD hOD hd hαD hαZ hy hyQ hαy
    have hsq : (e * (e * x) ^ 2 * y) ^ 2 = ((e * x) ^ 2 * y) ^ 2 := by
      have hc1 : Commute e ((e * x) ^ 2 * y) := heα.mul_right hey
      rw [mul_assoc, (hc1.mul_pow 2), sq e, he2v, one_mul]
    have he'Q : e * (e * x) ^ 2 ∈ Moufang.twoCore d := (Moufang.twoCore d).mul_mem heQ hαQ
    have he'y : ¬ Commute (e * (e * x) ^ 2) y := fun h' => hD.ne_one hd₁.1 (by
      rw [← hsq]
      exact (commute_iff_mul_sq_eq_one (hD.mul_self_eq_one he'D) hy2).1 h')
    have h4e'y := orderOf_mul_eq_four_of_mem_twoCore hD he'D hy he'Q hyQ he'y
    obtain ⟨-, he'd₁, -, hye'y⟩ := sq_mem_of_orderOf_eq_four hD he'D hy h4e'y
    rw [hsq] at he'd₁ hye'y
    have he'd₁D : e * (e * x) ^ 2 * ((e * x) ^ 2 * y) ^ 2 ∈ D := by
      rw [← hye'y]
      simpa [hD.inv_eq hy] using conj_mem_of_isClass hclass y he'D
    have h3' : e * (e * x) ^ 2 ∈ nCoreZ D (((e * x) ^ 2 * y) ^ 2) 3 := by
      rw [nCoreZ_eq_of_mem_rootSet hclass hD hd hd₁]
      exact he'3
    have h2' := mem_nCoreZ_two_of_mem_nCoreZ_three hclass hD hc hOD hd₁.1 he'D he'd₁ he'd₁D h3'
    rw [nCoreZ_eq_of_mem_rootSet hclass hD hd hd₁] at h2'
    exact he'2 h2'
  ·
    have h4ey := orderOf_mul_eq_four_of_mem_twoCore hD he hy heQ hyQ hey
    obtain ⟨hβD, heβ, hyβ, hyey⟩ := sq_mem_of_orderOf_eq_four hD he hy h4ey
    have hyN := mem_nCore_of_mem_twoCore hy hyQ
    have hβZ : (e * y) ^ 2 ∈ nCoreZ D d 2 := by
      have h' := commutator_mem_nCoreZ (k := 2) he3' hyN
      rwa [mul_inv_mul_inv_eq_sq_of_mem hD he hy] at h'
    by_cases hβT : (e * y) ^ 2 ∈ rootSet D d
    ·
      have heβD : e * (e * y) ^ 2 ∈ D := by
        rw [← hyey]
        simpa [hD.inv_eq hy] using conj_mem_of_isClass hclass y he
      have h3' : e ∈ nCoreZ D ((e * y) ^ 2) 3 := by
        rw [nCoreZ_eq_of_mem_rootSet hclass hD hd hβT]
        exact he3'
      have h2' := mem_nCoreZ_two_of_mem_nCoreZ_three hclass hD hc hOD hβD he heβ heβD h3'
      rw [nCoreZ_eq_of_mem_rootSet hclass hD hd hβT] at h2'
      exact he2' h2'
    ·
      have hβyD : (e * y) ^ 2 * y ∈ D := by
        rw [show (e * y) ^ 2 * y = e * y * e by rw [sq]; simp only [mul_assoc, hy2, mul_one]]
        simpa [hD.inv_eq he] using conj_mem_of_isClass hclass e hy
      have hy2' : ∀ g : G, y * (y * g) = g := fun g => by rw [← mul_assoc, hy2, one_mul]
      have hβydD : (e * y) ^ 2 * y * d ∈ D := by
        rw [show (e * y) ^ 2 * y * d = e * (y * d) * e⁻¹ by
          rw [hD.inv_eq he, sq]
          simp only [mul_assoc, hy2']
          rw [hed.eq]]
        exact conj_mem_of_isClass hclass e (hyX d (mem_rootSet_self hd))
      have hyZ := mem_nCoreZ_two_of_collinear hclass hD hc hOD hd hβD hβZ hβT hy hyβ.symm hβyD
        hyd (hyX d (mem_rootSet_self hd)) hβydD
      have h' := commutator_mem_nCoreZ (k := 1) hyZ heN
      rw [mul_inv_mul_inv_eq_sq_of_mem hD hy he, ← mul_sq_eq_mul_sq_comm he2v hy2 h4ey] at h'
      exact hβT (mem_rootSet_of_mem_nCoreZ_one hclass hD hOD hd hβD h')

theorem commutator_mem_rootGroup_of_mem_nCore (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hOD : OppositeDetermines D) {d : G}
    (hd : d ∈ D) {g h : G} (hg : g ∈ nCore D d) (hh : h ∈ nCore D d) :
    g * h * g⁻¹ * h⁻¹ ∈ rootGroup D d := by
  have hcen : ∀ a ∈ nCore D d, ∀ w ∈ rootGroup D d, a * w * a⁻¹ = w := by
    intro a ha w hw
    have hle : rootGroup D d ≤ Subgroup.centralizer ({a} : Set G) := by
      rw [rootGroup, Subgroup.closure_le]
      intro e he
      exact Subgroup.mem_centralizer_singleton_iff.2
        (commute_of_mem_nCore_of_mem_rootSet hclass hD hd he ha).symm.eq
    have hc' := Subgroup.mem_centralizer_singleton_iff.1 (hle hw)
    rw [← hc', mul_inv_cancel_right]
  have hgen : ∀ s ∈ D, s ∈ Moufang.twoCore d → ∀ t ∈ D, t ∈ Moufang.twoCore d →
      s * t * s⁻¹ * t⁻¹ ∈ rootGroup D d := by
    intro s hs hsQ t ht htQ
    rw [mul_inv_mul_inv_eq_sq_of_mem hD hs ht]
    by_cases hst : Commute s t
    · rw [(commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hs) (hD.mul_self_eq_one ht)).1 hst]
      exact one_mem _
    · have hsZ : s ∈ nCoreZ D d 2 := ⟨⟨s, mem_nCore_of_mem_twoCore hs hsQ⟩, by
        rw [upperCentralSeries_nCore_two_eq_top_of_rootClosure hclass hD hc hOD hd]
        exact Subgroup.mem_top _, rfl⟩
      exact rootSet_subset_rootGroup D d
        (sq_mem_rootSet_of_mem_nCoreZ_two hclass hD hOD hd hs hsZ ht htQ hst)
  have hA : ∀ s ∈ D, s ∈ Moufang.twoCore d → ∀ h ∈ nCore D d,
      s * h * s⁻¹ * h⁻¹ ∈ rootGroup D d := by
    intro s hs hsQ h hh
    rw [← closure_eq_nCore] at hh
    induction hh using Subgroup.closure_induction with
    | mem t ht => exact hgen s hs hsQ t ht.1 ht.2
    | one => simp
    | mul a b ha hb iha ihb =>
      rw [show s * (a * b) * s⁻¹ * (a * b)⁻¹ =
        s * a * s⁻¹ * a⁻¹ * (a * (s * b * s⁻¹ * b⁻¹) * a⁻¹) by group, hcen a ha _ ihb]
      exact Subgroup.mul_mem _ iha ihb
    | inv a ha iha =>
      rw [show s * a⁻¹ * s⁻¹ * a⁻¹⁻¹ = a⁻¹ * (s * a * s⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ by group,
        hcen _ (Subgroup.inv_mem _ ha) _ (Subgroup.inv_mem _ iha)]
      exact Subgroup.inv_mem _ iha
  rw [← closure_eq_nCore] at hg
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact hA s hs.1 hs.2 h hh
  | one => simp
  | mul a b ha hb iha ihb =>
    rw [show a * b * h * (a * b)⁻¹ * h⁻¹ =
      a * (b * h * b⁻¹ * h⁻¹) * a⁻¹ * (a * h * a⁻¹ * h⁻¹) by group, hcen a ha _ ihb]
    exact Subgroup.mul_mem _ ihb iha
  | inv a ha iha =>
    rw [show a⁻¹ * h * a⁻¹⁻¹ * h⁻¹ = a⁻¹ * (a * h * a⁻¹ * h⁻¹)⁻¹ * a⁻¹⁻¹ by group,
      hcen _ (Subgroup.inv_mem _ ha) _ (Subgroup.inv_mem _ iha)]
    exact Subgroup.inv_mem _ iha

end CFSG.Timmesfeld.Bridge

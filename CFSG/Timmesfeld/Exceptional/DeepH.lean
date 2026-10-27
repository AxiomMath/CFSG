module

public import CFSG.Timmesfeld.Exceptional.DeepHData
public import CFSG.Timmesfeld.Exceptional.DeepNear
public import CFSG.Timmesfeld.Exceptional.SigmaDiam

public section

namespace CFSG.Timmesfeld.Moufang.Deep

open CFSG.Timmesfeld CFSG.Timmesfeld.Moufang CFSG.Certificates

variable {G : Type*} [Group G] {D : Set G}

theorem mul_mem_collinearSet (hD : IsRootInvolutionSet D) {p y : G} (hp : p ∈ D)
    (hy : y ∈ collinearSet D p) : p * y ∈ collinearSet D p := by
  obtain ⟨hyD, hpy, hpyD⟩ := hy
  refine ⟨hpyD, (Commute.refl p).mul_right hpy, ?_⟩
  rwa [← mul_assoc, hD.mul_self_eq_one hp, one_mul]

theorem ne_of_mem_collinearSet (hD : IsRootInvolutionSet D) {p y : G} (hp : p ∈ D)
    (hy : y ∈ collinearSet D p) : y ≠ p := by
  rintro rfl
  exact hD.ne_one hy.2.2 (hD.mul_self_eq_one hp)

theorem signedProd_conj {p c : G} {x : Fin 2 → G} (g : List (Fin 4 × Bool)) :
    signedProd (lineGens p c x) (g ++ [(0, true)] ++ FreeGroup.invRev g) =
      signedProd (lineGens p c x) g * p * (signedProd (lineGens p c x) g)⁻¹ := by
  rw [signedProd_append, signedProd_append, signedProd_invRev]
  simp [signedProd]

theorem wPt_mem (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {p c : G} {x : Fin 2 → G}
    (hp : p ∈ D) (i : Fin 8) : wPt p c x i ∈ D := by
  rw [wPt, tW, signedProd_conj]
  exact conj_mem_of_isClass hclass _ hp

theorem zPt_mem (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {p c : G} {x : Fin 2 → G}
    (hp : p ∈ D) (i : Fin 4) : zPt p c x i ∈ D := by
  rw [zPt, tZ, signedProd_conj]
  exact conj_mem_of_isClass hclass _ hp

theorem yPt_mem (hD : IsRootInvolutionSet D) {p c : G} {x : Fin 2 → G} (hp : p ∈ D)
    (hx : ∀ i, x i ∈ collinearSet D p) (i : Fin 4) : yPt p c x i ∈ collinearSet D p := by
  obtain ⟨h0, h1, h2, h3⟩ := yPt_eq p c x
  fin_cases i
  · show yPt p c x 0 ∈ _
    rw [h0]
    exact mul_mem_collinearSet hD hp (hx 0)
  · show yPt p c x 1 ∈ _
    rw [h1]
    exact hx 0
  · show yPt p c x 2 ∈ _
    rw [h2]
    exact mul_mem_collinearSet hD hp (hx 1)
  · show yPt p c x 3 ∈ _
    rw [h3]
    exact hx 1

theorem ne_yPt (hD : IsRootInvolutionSet D) {p c q : G} {x : Fin 2 → G} (hp : p ∈ D)
    (hqx : ∀ i, q ≠ x i ∧ q ≠ p * x i) (i : Fin 4) :
    q ≠ yPt p c x i ∧ q ≠ p * yPt p c x i := by
  obtain ⟨h0, h1, h2, h3⟩ := yPt_eq p c x
  have hpp : ∀ g : G, p * (p * g) = g := fun g => by
    rw [← mul_assoc, hD.mul_self_eq_one hp, one_mul]
  fin_cases i
  · show q ≠ yPt p c x 0 ∧ q ≠ p * yPt p c x 0
    rw [h0, hpp]
    exact ⟨(hqx 0).2, (hqx 0).1⟩
  · show q ≠ yPt p c x 1 ∧ q ≠ p * yPt p c x 1
    rw [h1]
    exact hqx 0
  · show q ≠ yPt p c x 2 ∧ q ≠ p * yPt p c x 2
    rw [h2, hpp]
    exact ⟨(hqx 1).2, (hqx 1).1⟩
  · show q ≠ yPt p c x 3 ∧ q ≠ p * yPt p c x 3
    rw [h3]
    exact hqx 1

theorem wPt_facts (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    {p c : G} {x : Fin 2 → G} (hcfg : LineConfig p c x) (hp : p ∈ D)
    (hx : ∀ i, x i ∈ collinearSet D p) (i : Fin 8) :
    orderOf (p * wPt p c x i) = 4 ∧ (p * wPt p c x i) ^ 2 = yPt p c x (yW i) ∧
      Commute (wPt p c x i) (yPt p c x (yW i)) ∧ ¬ Commute p (wPt p c x i) := by
  have hrel : ∀ r ∈ lineRels 2 false, signedProd (lineGens p c x) r = 1 :=
    hcfg.signedProd_lineRels (by simp)
  have h := signedProd_eq_one_of_walk hrel (walk_gW i)
  have e1 : signedProd (lineGens p c x) [(0, true)] = p := by simp [signedProd]
  rw [signedProd_append, signedProd_append, signedProd_append, signedProd_append,
    signedProd_invRev, e1] at h
  have hsq : (p * wPt p c x i) ^ 2 = yPt p c x (yW i) := by
    rw [sq, ← mul_assoc]
    exact mul_inv_eq_one.1 h
  have hw := wPt_mem (c := c) (x := x) hclass hp i
  have hyD := (yPt_mem (c := c) hD hp hx (yW i)).1
  have h4 : orderOf (p * wPt p c x i) = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := p * wPt p c x i)
      (by rw [pow_one, hsq]; exact hD.ne_one hyD)
      (by rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hsq, sq, hD.mul_self_eq_one hyD])
    simpa using this
  obtain ⟨-, -, hwy, -⟩ := sq_mem_of_orderOf_eq_four hD hp hw h4
  rw [hsq] at hwy
  exact ⟨h4, hsq, hwy, not_commute_of_orderOf_eq_four (hD.mul_self_eq_one hp)
    (hD.mul_self_eq_one hw) h4⟩

theorem sq_q_yPt (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hNL : NoLevi D) (hNP : NoPolar D) (hPl : ExcNoPlane D) {p c q : G} {x : Fin 2 → G}
    (hp : p ∈ D) (hx : ∀ i, x i ∈ collinearSet D p) (hq : q ∈ collinearSet D p)
    (hqx : ∀ i, q ≠ x i ∧ q ≠ p * x i) (i : Fin 4) : (q * yPt p c x i) ^ 2 = p := by
  have hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun g x hx => conj_mem_of_isClass hclass g hx
  have hy := yPt_mem (c := c) hD hp hx i
  obtain ⟨hne1, hne2⟩ := ne_yPt (c := c) hD hp hqx i
  rcases NoLevi.centralizer_cases hD hconj hNL hNP hPl hp hy.1 hq.1 hy.2.1 hq.2.1
      (ne_of_mem_collinearSet hD hp hy) (ne_of_mem_collinearSet hD hp hq) with h | h | ⟨-, h⟩
  · exact absurd h hne1
  · exact absurd h hne2
  · have e : (q * yPt p c x i) ^ 2 = q * (yPt p c x i * q) ^ 2 * q⁻¹ := by
      simp only [sq, mul_assoc, mul_inv_cancel, mul_one]
    rw [e, h, hq.2.1.symm.eq, mul_assoc, mul_inv_cancel, mul_one]

theorem pow_three_q_wPt (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hsing : ∀ x ∈ D, rootSet D x = {x}) (hQ : CommLambda D) (hNL : NoLevi D)
    (hNP : NoPolar D) (hPl : ExcNoPlane D) (hP1 : ExcP1 D) {p c q : G} {x : Fin 2 → G}
    (hcfg : LineConfig p c x) (hp : p ∈ D) (hx : ∀ i, x i ∈ collinearSet D p)
    (hq : q ∈ collinearSet D p) (hqx : ∀ i, q ≠ x i ∧ q ≠ p * x i) (i : Fin 8) :
    (q * wPt p c x i) ^ 3 = 1 := by
  have hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun g x hx => conj_mem_of_isClass hclass g hx
  obtain ⟨h4, hsq, hwy, hpw⟩ := wPt_facts hclass hD hcfg hp hx i
  have hw := wPt_mem (c := c) (x := x) hclass hp i
  have hy := yPt_mem (c := c) hD hp hx (yW i)
  obtain ⟨hne1, hne2⟩ := ne_yPt (c := c) hD hp hqx (yW i)
  obtain ⟨hqD, hpq, hpqD⟩ := hq
  have hq3 : q ∈ nbhd D (wPt p c x i) 3 :=
    mem_nbhd_succ_of_commute hqD (mem_nbhd_succ_of_commute hp (mem_nbhd_succ_of_commute hy.1
      (mem_nbhd_self 0) hwy.symm) hy.2.1) hpq.symm
  have hq2 : q ∉ nbhd D (wPt p c x i) 2 := by
    intro h2
    rcases ((mem_nbhd_two_iff hD hNL hw).1 h2).2 with hqw | hqw
    · exact hne1 (hsq.symm.trans
        (NoLevi.sq_eq_of_commute hD hconj hNL hNP hPl hp hw hqD hpq.symm hqw hpw)).symm
    · have hc := commute_of_special_special hclass hD hsing hQ hNP hPl hp hqD hw hpq hpqD h4 hqw
      have e := NoLevi.sq_eq_of_commute hD hconj hNL hNP hPl hp hw hpqD
        ((Commute.refl p).mul_left hpq.symm) hc hpw
      refine hne2 ?_
      rw [← hsq, e, ← mul_assoc, hD.mul_self_eq_one hp, one_mul]
  have h3 := orderOf_eq_three_of_mem_nbhd_three hD hNL hNP hP1 hw hq3 hq2
  rw [← h3]
  exact pow_orderOf_eq_one _

theorem zPt_facts (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hNL : NoLevi D) (hNP : NoPolar D) (hP1 : ExcP1 D) {p c : G} {x : Fin 2 → G}
    (hcfg : LineConfig p c x) (hp : p ∈ D) (hx : ∀ i, x i ∈ collinearSet D p) (i : Fin 4) :
    p ∈ nbhd D (zPt p c x i) 3 ∧ p ∉ nbhd D (zPt p c x i) 2 ∧
      orderOf (yPt p c x (nearZ i) * zPt p c x i) = 4 ∧
      yPt p c x (farZ i) ∉ nbhd D (zPt p c x i) 3 := by
  have hrel : ∀ r ∈ lineRels 2 false, signedProd (lineGens p c x) r = 1 :=
    hcfg.signedProd_lineRels (by simp)
  set z := zPt p c x i with hz_def
  have hz : z ∈ D := zPt_mem hclass hp i
  set w := wPt p c x (wZ' i) with hw_def
  have hw : w ∈ D := wPt_mem hclass hp _
  obtain ⟨-, -, hwy, hpw⟩ := wPt_facts hclass hD hcfg hp hx (wZ' i)
  rw [yW_wZ'] at hwy
  set s := yPt p c x (nearZ i) with hs_def
  have hs := yPt_mem (c := c) hD hp hx (nearZ i)
  have hwz : Commute w z := by
    have h := signedProd_eq_one_of_walk hrel (walk_gZc i)
    rw [signedProd_append, signedProd_append, signedProd_append, signedProd_invRev,
      signedProd_invRev] at h
    have h' : w * z * w⁻¹ * z⁻¹ = 1 := h
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h'
    exact h'
  have e1 : signedProd (lineGens p c x) [(0, true)] = p := by simp [signedProd]
  have hpz3 : (p * z) ^ 3 = 1 := by
    have h := signedProd_eq_one_of_walk hrel (walk_gZ3 i)
    rw [signedProd_replicate, signedProd_append, e1] at h
    exact h
  have hzp : z ≠ p := fun e => by
    have h := hwz.symm
    rw [e] at h
    exact hpw h
  have hpz : ¬ Commute p z := by
    intro hc
    have h2 : (p * z) ^ 2 = 1 := by
      rw [sq, mul_assoc, ← mul_assoc z, ← hc.eq, mul_assoc, hD.mul_self_eq_one hz, mul_one,
        hD.mul_self_eq_one hp]
    have h1 : p * z = 1 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, h2, one_mul] at hpz3
      exact hpz3
    exact hzp (by rw [← inv_eq_of_mul_eq_one_right h1, hD.inv_eq hp])
  have hodd : Odd (orderOf (p * z)) :=
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hpz3)
  have hp2 : p ∉ nbhd D z 2 := (not_mem_nbhd_two_iff hD hNL hz hp).2 ⟨hpz, hodd⟩
  have hw1 : w ∈ nbhd D z 1 := (mem_nbhd_one_iff hz).2 ⟨hw, hwz⟩
  have hs2 : s ∈ nbhd D z 2 := mem_nbhd_succ_of_commute hs.1 hw1 hwy.symm
  have hp3 : p ∈ nbhd D z 3 := mem_nbhd_succ_of_commute hp hs2 hs.2.1
  have hs4 : orderOf (s * z) = 4 := by
    rcases ((mem_nbhd_two_iff hD hNL hz).1 hs2).2 with hsz | h4
    · exact absurd (mem_nbhd_succ_of_commute hp ((mem_nbhd_one_iff hz).2 ⟨hs.1, hsz⟩)
        hs.2.1) hp2
    · exact h4
  refine ⟨hp3, hp2, hs4, ?_⟩
  set a := yPt p c x (farZ i) with ha_def
  have ha := yPt_mem (c := c) hD hp hx (farZ i)
  have haz5 : (a * z) ^ 5 = 1 := by
    have h := signedProd_eq_one_of_walk hrel (walk_gZ5 i)
    rw [signedProd_replicate, signedProd_append] at h
    exact h
  have haz : a ≠ z := fun e => hpz (by rw [← e]; exact ha.2.1)
  have h5 : orderOf (a * z) = 5 := by
    rcases (Nat.dvd_prime (by norm_num)).1 (orderOf_dvd_of_pow_eq_one haz5) with h1 | h5
    · exfalso
      rw [orderOf_eq_one_iff] at h1
      exact haz (by rw [← inv_eq_of_mul_eq_one_right h1, hD.inv_eq ha.1])
    · exact h5
  intro ha3
  by_cases ha2 : a ∈ nbhd D z 2
  · rcases ((mem_nbhd_two_iff hD hNL hz).1 ha2).2 with hc | h4
    · have : (a * z) ^ 2 = 1 := by
        rw [sq, mul_assoc, ← mul_assoc z, ← hc.eq, mul_assoc, hD.mul_self_eq_one hz, mul_one,
          hD.mul_self_eq_one ha.1]
      have := orderOf_dvd_of_pow_eq_one this
      rw [h5] at this
      exact absurd this (by decide)
    · rw [h5] at h4
      exact absurd h4 (by decide)
  · rw [orderOf_eq_three_of_mem_nbhd_three hD hNL hNP hP1 hz ha3 ha2] at h5
    exact absurd h5 (by decide)

theorem pow_five_q_zPt (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hNL : NoLevi D) (hNP : NoPolar D) (hPl : ExcNoPlane D) (hP1 : ExcP1 D) {p c q : G}
    {x : Fin 2 → G} (hcfg : LineConfig p c x) (hp : p ∈ D) (hx : ∀ i, x i ∈ collinearSet D p)
    (hq : q ∈ collinearSet D p) (hqx : ∀ i, q ≠ x i ∧ q ≠ p * x i) (i : Fin 4)
    (hW1 : ¬ ThreeNear D (zPt p c x i) (yPt p c x (farZ i))) :
    (q * zPt p c x i) ^ 5 = 1 := by
  obtain ⟨hp3, hp2, hs4, ha3⟩ := zPt_facts hclass hD hNL hNP hP1 hcfg hp hx i
  have hz := zPt_mem (c := c) (x := x) hclass hp i
  have hs := yPt_mem (c := c) hD hp hx (nearZ i)
  have ha := yPt_mem (c := c) hD hp hx (farZ i)
  obtain ⟨hne1, hne2⟩ := ne_yPt (c := c) hD hp hqx (nearZ i)
  have hpa : p ∈ collinearSet D (yPt p c x (farZ i)) :=
    ⟨hp, ha.2.1.symm, by rw [← ha.2.1.eq]; exact ha.2.2⟩
  have hq3 : q ∉ nbhd D (zPt p c x i) 3 := by
    intro hq3
    rcases special_of_mem_nbhd_three hD hNL hNP hP1 hz hp hp3 hp2 hq hq3 with h4 | h4
    · exact hne1 (eq_of_not_threeNear hclass hD hNL hNP hPl hP1 hz ha.1 ha3 hpa hp3 hs.1
        hs.2.1 hs4 hq.1 hq.2.1 h4 hW1)
    · have e := eq_of_not_threeNear hclass hD hNL hNP hPl hP1 hz ha.1 ha3 hpa hp3 hs.1 hs.2.1
        hs4 hq.2.2 ((Commute.refl p).mul_right hq.2.1) h4 hW1
      refine hne2 ?_
      rw [← e, ← mul_assoc, hD.mul_self_eq_one hp, one_mul]
  have hq4 : q ∈ nbhd D (zPt p c x i) 4 := mem_nbhd_succ_of_commute hq.1 hp3 hq.2.1.symm
  rw [← orderOf_eq_five_of_mem_nbhd_four hclass hD hNL hNP hPl hP1 hq.1 hz hq4 hq3]
  exact pow_orderOf_eq_one _

theorem deep_relations (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hsing : ∀ x ∈ D, rootSet D x = {x}) (hQ : CommLambda D) (hNL : NoLevi D)
    (hNP : NoPolar D) (hPl : ExcNoPlane D) (hP1 : ExcP1 D) {p c q : G} {x : Fin 2 → G}
    (hcfg : LineConfig p c x) (hp : p ∈ D) (hx : ∀ i, x i ∈ collinearSet D p)
    (hq : q ∈ collinearSet D p) (hqx : ∀ i, q ≠ x i ∧ q ≠ p * x i)
    (hW1 : ∀ i, ¬ ThreeNear D (zPt p c x i) (yPt p c x (farZ i))) :
    (∀ i, (q * yPt p c x i) ^ 2 = p) ∧ (∀ i, (q * wPt p c x i) ^ 3 = 1) ∧
      ∀ i, (q * zPt p c x i) ^ 5 = 1 :=
  ⟨sq_q_yPt hclass hD hNL hNP hPl hp hx hq hqx,
    pow_three_q_wPt hclass hD hsing hQ hNL hNP hPl hP1 hcfg hp hx hq hqx,
    fun i => pow_five_q_zPt hclass hD hNL hNP hPl hP1 hcfg hp hx hq hqx i (hW1 i)⟩

end CFSG.Timmesfeld.Moufang.Deep

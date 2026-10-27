module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_a

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section1

open PFAppendixIII

/-!
# Peterfalvi, Part II, Chapter I, Section 1, Proposition 4(b)
-/

private theorem proposition_4_b_rightConjugateElem_isInvolution
    {G : Type*} [Group G] {s k : G} (hs : IsInvolution s) :
    IsInvolution (rightConjugateElem s k) := by
  constructor
  · intro h
    apply hs.ne_one
    have h' := congrArg (fun z : G => k * z * k⁻¹) h
    simpa [rightConjugateElem, mul_assoc] using h'
  · have hs2 : s * s = 1 := by
      simpa [pow_two] using hs.sq_eq_one
    calc
      (rightConjugateElem s k) ^ 2 =
          k⁻¹ * (s * s) * k := by
            simp [rightConjugateElem, pow_two, mul_assoc]
      _ = 1 := by simp [hs2]

private theorem proposition_4_b_conj_by_t_isInvolution
    {G : Type*} [Group G] {s t : G}
    (hs : IsInvolution s) (ht : IsInvolution t) :
    IsInvolution (t * s * t) := by
  have htinv : t⁻¹ = t :=
    ht.inv_eq_self
  simpa [rightConjugateElem, htinv] using
    (proposition_4_b_rightConjugateElem_isInvolution (s := s) (k := t) hs)

private theorem proposition_4_b_no_involution_in_D
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) {d : G}
    (hd : d ∈ D) (hdI : IsInvolution d) : False := by
  classical
  let dD : D := ⟨d, hd⟩
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have horder : orderOf dD = 2 := by
    refine (orderOf_eq_prime_iff (x := dD) (p := 2)).2 ⟨?_, ?_⟩
    · ext
      simpa [dD, pow_two] using hdI.sq_eq_one
    · intro h
      exact hdI.ne_one (by simpa [dD] using congrArg Subtype.val h)
  have hdiv : 2 ∣ Nat.card D := by
    simpa [horder] using orderOf_dvd_natCard dD
  exact hA1.D_odd.not_two_dvd_nat hdiv

private theorem proposition_4_b_exists_H_involution
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    ∃ u : G, u ∈ H ∧ IsInvolution u := by
  classical
  haveI : Fintype Q := Fintype.ofFinite Q
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hdiv : 2 ∣ Fintype.card Q := by
    rw [← Nat.card_eq_fintype_card]
    exact hA1.Q_even.two_dvd
  rcases exists_prime_orderOf_dvd_card (G := Q) 2 hdiv with ⟨q, hq⟩
  have hq' : (q : Q) ^ 2 = 1 ∧ (q : Q) ≠ 1 := by
    exact (orderOf_eq_prime_iff (x := q) (p := 2)).1 hq
  refine ⟨q, hA1.Q_le_H q.property, ?_⟩
  constructor
  · intro h
    exact hq'.2 (Subtype.ext h)
  · simpa using congrArg Subtype.val hq'.1


private theorem proposition_4_b_mem_rightConjugate_of_conj_mem
    {G : Type*} [Group G] {H : Subgroup G} {a t : G}
    (ht : IsInvolution t) (ha : a ∈ H)
    (hconj : rightConjugateElem a t = a⁻¹) :
    a ∈ rightConjugate H t := by
  have htinv : t⁻¹ = t := ht.inv_eq_self
  have ht2 : t * t = 1 := by
    simpa [pow_two] using ht.sq_eq_one
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
  refine ⟨a⁻¹, H.inv_mem ha, ?_⟩
  change (MulAut.conj t⁻¹) a⁻¹ = a
  have hta : t * a * t = a⁻¹ := by
    simpa [rightConjugateElem, htinv] using hconj
  calc
    (MulAut.conj t⁻¹) a⁻¹ = t * a⁻¹ * t := by simp [MulAut.conj, htinv]
    _ = t * (t * a * t) * t := by rw [hta]
    _ = (t * t) * a * (t * t) := by group
    _ = a := by simp [ht2]

private theorem proposition_4_b_K_square_root
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) {a : G}
    (ha : a ∈ peterfalviKSet D t) :
    ∃ k : G, k ∈ peterfalviKSet D t ∧ k⁻¹ * k⁻¹ = a := by
  classical
  let aD : D := ⟨a, ha.1⟩
  have hodd_order : Odd (orderOf aD) :=
    hA1.D_odd.of_dvd_nat (orderOf_dvd_natCard aD)
  rcases hodd_order with ⟨m, hm⟩
  let kD : D := aD ^ m
  have hpow_order : aD ^ (2 * m + 1) = 1 := by
    simp [← hm]
  have hmul : (aD ^ m) ^ 2 * aD = 1 := by
    calc
      (aD ^ m) ^ 2 * aD = aD ^ (m + m) * aD := by
        simp [pow_two, pow_add]
      _ = aD ^ (m + m + 1) := by
        rw [pow_succ]
      _ = aD ^ (2 * m + 1) := by
        rw [two_mul]
      _ = 1 := hpow_order
  have hsq : (aD ^ m) ^ 2 = aD⁻¹ := by
    calc
      (aD ^ m) ^ 2 = ((aD ^ m) ^ 2 * aD) * aD⁻¹ := by group
      _ = aD⁻¹ := by simp [hmul]
  have hinv_sq : (aD ^ m)⁻¹ * (aD ^ m)⁻¹ = aD := by
    have h := congrArg Inv.inv hsq
    simpa [pow_two] using h
  have hk_conj : rightConjugateElem (kD : G) t = (kD : G)⁻¹ := by
    have hmap :
        rightConjugateElem (a ^ m) t = (rightConjugateElem a t) ^ m := by
      simpa [rightConjugateElem] using
        (map_pow (MulAut.conj t⁻¹) a m)
    dsimp [kD, aD]
    rw [hmap, ha.2]
    simp
  refine ⟨kD, ⟨kD.property, hk_conj⟩, ?_⟩
  simpa [kD, aD] using congrArg Subtype.val hinv_sq

/--
Peterfalvi core for the uniqueness half of Proposition 4(b): after Proposition 3
puts two candidate involutions in the same `K`-conjugacy orbit, the canonical
form calculation in Proposition 4(a) forces the conjugating element to be
trivial.
-/
private theorem proposition_4_b_K_conjugate_solution_eq_one
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    {s₁ r₁ s₂ r₂ k : G}
    (_hs₁H : s₁ ∈ H) (_hs₁I : IsInvolution s₁) (hr₁Q : r₁ ∈ Q)
    (hs₂H : s₂ ∈ H) (hs₂I : IsInvolution s₂) (hr₂Q : r₂ ∈ Q)
    (hkK : k ∈ peterfalviKSet D t)
    (hs₂_eq : rightConjugateElem s₁ k = s₂)
    (heq₁ : t * s₁ * t = r₁⁻¹ * t * r₁)
    (heq₂ : t * s₂ * t = r₂⁻¹ * t * r₂) :
    k = 1 := by
  classical
  have htinv : t⁻¹ = t :=
    hA1.involution_t.inv_eq_self
  have ht2 : t * t = 1 := by
    simpa [pow_two] using hA1.involution_t.sq_eq_one
  have hkD : k ∈ D := hkK.1
  have hkt : t * k * t = k⁻¹ := by
    simpa [rightConjugateElem, htinv] using hkK.2
  have hkt_right : t * k = k⁻¹ * t := by
    calc
      t * k = (t * k * t) * t := by simp [ht2, mul_assoc]
      _ = k⁻¹ * t := by rw [hkt]
  have hkinv_t : k⁻¹ * t = t * k := hkt_right.symm
  have htkinv : t * k⁻¹ * t = k := by
    calc
      t * k⁻¹ * t = t * (k⁻¹ * t) := by group
      _ = t * (t * k) := by rw [hkinv_t]
      _ = k := by
        rw [← mul_assoc, ht2]
        simp
  have htk_inv_right : t * k⁻¹ = k * t := by
    calc
      t * k⁻¹ = (t * k⁻¹ * t) * t := by simp [ht2, mul_assoc]
      _ = k * t := by rw [htkinv]
  have hkt_left : k * t = t * k⁻¹ := by
    calc
      k * t = (t * t) * (k * t) := by simp [ht2]
      _ = t * ((t * k) * t) := by simp [mul_assoc]
      _ = t * k⁻¹ := by rw [hkt]
  have hktk : k * t * k = t := by
    rw [hkt_left]
    group
  have hr₁_conj_Q : k * r₁ * k⁻¹ ∈ Q := by
    let r₁H : H := ⟨r₁, hA1.Q_le_H hr₁Q⟩
    let kH : H := ⟨k, hA1.D_le_H hkD⟩
    have hr₁H : r₁H ∈ Q.subgroupOf H := by
      simpa [r₁H, Subgroup.mem_subgroupOf] using hr₁Q
    have hconj := hA1.Q_normal_in_H.conj_mem r₁H hr₁H kH
    simpa [r₁H, kH, Subgroup.mem_subgroupOf] using hconj
  have hleftH : (k * r₁ * k⁻¹)⁻¹ * (k * k) ∈ H := by
    exact H.mul_mem
      (H.inv_mem (hA1.Q_le_H hr₁_conj_Q))
      (H.mul_mem (hA1.D_le_H hkD) (hA1.D_le_H hkD))
  have hright_form :
      t * s₂ * t =
        ((k * r₁ * k⁻¹)⁻¹ * (k * k)) * t * (k * r₁ * k⁻¹) := by
    calc
      t * s₂ * t = t * rightConjugateElem s₁ k * t := by rw [hs₂_eq]
      _ = t * (k⁻¹ * s₁ * k) * t := by simp [rightConjugateElem]
      _ = (t * k⁻¹) * s₁ * (k * t) := by group
      _ = (k * t) * s₁ * (t * k⁻¹) := by rw [htk_inv_right, hkt_left]
      _ = k * (t * s₁ * t) * k⁻¹ := by group
      _ = k * (r₁⁻¹ * t * r₁) * k⁻¹ := by rw [heq₁]
      _ = k * r₁⁻¹ * t * r₁ * k⁻¹ := by simp [mul_assoc]
      _ = k * r₁⁻¹ * (k * t * k) * r₁ * k⁻¹ := by
        conv_lhs => rw [← hktk]
      _ = ((k * r₁ * k⁻¹)⁻¹ * (k * k)) * t * (k * r₁ * k⁻¹) := by
        group
  have htstI : IsInvolution (t * s₂ * t) :=
    proposition_4_b_conj_by_t_isInvolution hs₂I hA1.involution_t
  have htst_right : t * s₂ * t ∈ rightConjugate H t := by
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨s₂, hs₂H, ?_⟩
    simp [htinv, mul_assoc]
  have htst_not_H : t * s₂ * t ∉ H := by
    intro htstH
    have htstD : t * s₂ * t ∈ D := by
      rw [hA1.D_eq]
      exact ⟨htstH, htst_right⟩
    exact proposition_4_b_no_involution_in_D H D Q t hA1 htstD htstI
  rcases proposition_4_a H D Q t hA1 (t * s₂ * t) htst_not_H with
    ⟨canonical, _hcanonical, huniq⟩
  let p₂ : H × Q := (⟨r₂⁻¹, hA1.Q_le_H (Q.inv_mem hr₂Q)⟩, ⟨r₂, hr₂Q⟩)
  let pk : H × Q :=
    (⟨(k * r₁ * k⁻¹)⁻¹ * (k * k), hleftH⟩, ⟨k * r₁ * k⁻¹, hr₁_conj_Q⟩)
  have hp₂ : p₂ = canonical := by
    exact huniq p₂ (by simpa [p₂] using heq₂)
  have hpk : pk = canonical := by
    exact huniq pk (by simpa [pk] using hright_form)
  have hp₂_pk : p₂ = pk := hp₂.trans hpk.symm
  have hr₂_eq : r₂ = k * r₁ * k⁻¹ := by
    exact congrArg (fun p : H × Q => ((p.2 : Q) : G)) hp₂_pk
  have hleft_eq :
      r₂⁻¹ = (k * r₁ * k⁻¹)⁻¹ * (k * k) := by
    exact congrArg (fun p : H × Q => ((p.1 : H) : G)) hp₂_pk
  have hk_sq : k * k = 1 := by
    calc
      k * k = (k * r₁ * k⁻¹) * ((k * r₁ * k⁻¹)⁻¹ * (k * k)) := by
        group
      _ = (k * r₁ * k⁻¹) * r₂⁻¹ := by rw [← hleft_eq]
      _ = (k * r₁ * k⁻¹) * (k * r₁ * k⁻¹)⁻¹ := by rw [hr₂_eq]
      _ = 1 := by simp
  by_cases hk1 : k = 1
  · exact hk1
  · exact False.elim
      (proposition_4_b_no_involution_in_D H D Q t hA1 hkD
        ⟨hk1, by simpa [pow_two] using hk_sq⟩)

/--
Peterfalvi: Proposition 4(b), existence part. Starting with `u ∈ H ∩ I`, use
Proposition 4(a) to write `tut = x t y`; then the element `a = yx` lies in
`K`, and the odd-order squaring permutation on `K` gives `k` with `k⁻² = a`.
The resulting conjugate has form `y⁻¹ t y` with `y ∈ Q`.
-/
private theorem proposition_4_b_exists
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    ∃ p : G × G,
      p.1 ∈ H ∧ IsInvolution p.1 ∧ p.2 ∈ Q ∧
        t * p.1 * t = p.2⁻¹ * t * p.2 := by
  classical
  rcases proposition_4_b_exists_H_involution H D Q t hA1 with ⟨u, huH, huI⟩
  have htinv : t⁻¹ = t :=
    hA1.involution_t.inv_eq_self
  have ht2 : t * t = 1 := by
    simpa [pow_two] using hA1.involution_t.sq_eq_one
  have htutI : IsInvolution (t * u * t) :=
    proposition_4_b_conj_by_t_isInvolution huI hA1.involution_t
  have htut_right : t * u * t ∈ rightConjugate H t := by
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨u, huH, ?_⟩
    simp [htinv, mul_assoc]
  have htut_not_H : t * u * t ∉ H := by
    intro htutH
    have htutD : t * u * t ∈ D := by
      rw [hA1.D_eq]
      exact ⟨htutH, htut_right⟩
    exact proposition_4_b_no_involution_in_D H D Q t hA1 htutD htutI
  rcases proposition_4_a H D Q t hA1 (t * u * t) htut_not_H with
    ⟨p, hp, _huniq⟩
  let x : H := p.1
  let y : Q := p.2
  have hdecomp : t * u * t = (x : G) * t * (y : G) := by
    simpa [x, y] using hp
  let a : G := (y : G) * (x : G)
  have haH : a ∈ H := by
    exact H.mul_mem (hA1.Q_le_H y.property) x.property
  have hxty_sq : ((x : G) * t * (y : G)) ^ 2 = 1 := by
    rw [← hdecomp]
    exact htutI.sq_eq_one
  have hxty_mul : (x : G) * t * ((y : G) * (x : G)) * t * (y : G) = 1 := by
    simpa [pow_two, mul_assoc] using hxty_sq
  have hta : t * a * t = a⁻¹ := by
    have h' := congrArg (fun z : G => (x : G)⁻¹ * z * (y : G)⁻¹) hxty_mul
    calc
      t * a * t = (x : G)⁻¹ * (y : G)⁻¹ := by
        simpa [a, mul_assoc] using h'
      _ = a⁻¹ := by simp [a]
  have ha_conj : rightConjugateElem a t = a⁻¹ := by
    simpa [rightConjugateElem, htinv] using hta
  have haD : a ∈ D := by
    rw [hA1.D_eq]
    exact ⟨haH,
      proposition_4_b_mem_rightConjugate_of_conj_mem
        (H := H) hA1.involution_t haH ha_conj⟩
  have haK : a ∈ peterfalviKSet D t := ⟨haD, ha_conj⟩
  rcases proposition_4_b_K_square_root H D Q t hA1 haK with
    ⟨k, hkK, hksq⟩
  have hkD : k ∈ D := hkK.1
  have hkt : t * k * t = k⁻¹ := by
    simpa [rightConjugateElem, htinv] using hkK.2
  have hkt_right : t * k = k⁻¹ * t := by
    calc
      t * k = (t * k * t) * t := by simp [ht2, mul_assoc]
      _ = k⁻¹ * t := by rw [hkt]
  have hkinv_t : k⁻¹ * t = t * k := hkt_right.symm
  have htkinv : t * k⁻¹ * t = k := by
    calc
      t * k⁻¹ * t = t * (k⁻¹ * t) := by group
      _ = t * (t * k) := by rw [hkinv_t]
      _ = k := by
        rw [← mul_assoc, ht2]
        simp
  have htk_inv_right : t * k⁻¹ = k * t := by
    calc
      t * k⁻¹ = (t * k⁻¹ * t) * t := by simp [ht2, mul_assoc]
      _ = k * t := by rw [htkinv]
  have hkt_left : k * t = t * k⁻¹ := by
    calc
      k * t = (t * t) * (k * t) := by simp [ht2]
      _ = t * ((t * k) * t) := by simp [mul_assoc]
      _ = t * k⁻¹ := by rw [hkt]
  have hy_conj_Q : k * (y : G) * k⁻¹ ∈ Q := by
    let yH : H := ⟨y, hA1.Q_le_H y.property⟩
    let kH : H := ⟨k, hA1.D_le_H hkD⟩
    have hyH : yH ∈ Q.subgroupOf H := by
      simp [yH, Subgroup.mem_subgroupOf]
    have hconj := hA1.Q_normal_in_H.conj_mem yH hyH kH
    simpa [yH, kH, Subgroup.mem_subgroupOf] using hconj
  let s : G := k⁻¹ * u * k
  let r : G := k * (y : G) * k⁻¹
  have hsH : s ∈ H := by
    exact H.mul_mem (H.mul_mem (H.inv_mem (hA1.D_le_H hkD)) huH) (hA1.D_le_H hkD)
  have hsI : IsInvolution s := by
    simpa [s, rightConjugateElem] using
      (proposition_4_b_rightConjugateElem_isInvolution (s := u) (k := k) huI)
  have hrQ : r ∈ Q := by
    simpa [r] using hy_conj_Q
  have hx_eq : (x : G) = (y : G)⁻¹ * (k⁻¹ * k⁻¹) := by
    calc
      (x : G) = (y : G)⁻¹ * ((y : G) * (x : G)) := by group
      _ = (y : G)⁻¹ * (k⁻¹ * k⁻¹) := by rw [hksq]
  have heq : t * s * t = r⁻¹ * t * r := by
    calc
      t * s * t = (t * k⁻¹) * u * (k * t) := by
        simp [s, mul_assoc]
      _ = (k * t) * u * (t * k⁻¹) := by
        rw [htk_inv_right, hkt_left]
      _ = k * (t * u * t) * k⁻¹ := by
        group
      _ = k * ((x : G) * t * (y : G)) * k⁻¹ := by rw [hdecomp]
      _ = k * (((y : G)⁻¹ * (k⁻¹ * k⁻¹)) * t * (y : G)) * k⁻¹ := by
        rw [hx_eq]
      _ = k * (y : G)⁻¹ * k⁻¹ * (k⁻¹ * t) * (y : G) * k⁻¹ := by
        group
      _ = k * (y : G)⁻¹ * k⁻¹ * (t * k) * (y : G) * k⁻¹ := by
        rw [hkinv_t]
      _ = r⁻¹ * t * r := by
        simp [r, mul_assoc]
  exact ⟨(s, r), hsH, hsI, hrQ, heq⟩

/--
Peterfalvi: Proposition 4(b), uniqueness part. Proposition 3 identifies
`H ∩ I` with any translate `sK`; Proposition 4(a)'s canonical form then
forces the same `s` and the same `r`.
-/
private theorem proposition_4_b_unique
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    ∀ p₁ p₂ : G × G,
      p₁.1 ∈ H ∧ IsInvolution p₁.1 ∧ p₁.2 ∈ Q ∧
          t * p₁.1 * t = p₁.2⁻¹ * t * p₁.2 →
        p₂.1 ∈ H ∧ IsInvolution p₂.1 ∧ p₂.2 ∈ Q ∧
          t * p₂.1 * t = p₂.2⁻¹ * t * p₂.2 →
          p₁ = p₂ := by
  intro p₁ p₂ hp₁ hp₂
  rcases hp₁ with ⟨hs₁H, hs₁I, hr₁Q, heq₁⟩
  rcases hp₂ with ⟨hs₂H, hs₂I, hr₂Q, heq₂⟩
  have hprop3 := (proposition_3 H D Q t hA1).2 p₁.1 hs₁H hs₁I
  have hs₂_mem : p₂.1 ∈ H ∧ IsInvolution p₂.1 := ⟨hs₂H, hs₂I⟩
  rcases (hprop3 p₂.1).1 hs₂_mem with ⟨k, hkK, hs₂_eq⟩
  have hk_one : k = 1 :=
    proposition_4_b_K_conjugate_solution_eq_one H D Q t hA1
      hs₁H hs₁I hr₁Q hs₂H hs₂I hr₂Q hkK hs₂_eq heq₁ heq₂
  have hs_eq : p₂.1 = p₁.1 := by
    rw [← hs₂_eq, hk_one]
    simp [rightConjugateElem]
  have htinv : t⁻¹ = t :=
    hA1.involution_t.inv_eq_self
  have htstI : IsInvolution (t * p₁.1 * t) :=
    proposition_4_b_conj_by_t_isInvolution hs₁I hA1.involution_t
  have htst_right : t * p₁.1 * t ∈ rightConjugate H t := by
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨p₁.1, hs₁H, ?_⟩
    simp [htinv, mul_assoc]
  have htst_not_H : t * p₁.1 * t ∉ H := by
    intro htstH
    have htstD : t * p₁.1 * t ∈ D := by
      rw [hA1.D_eq]
      exact ⟨htstH, htst_right⟩
    exact proposition_4_b_no_involution_in_D H D Q t hA1 htstD htstI
  rcases proposition_4_a H D Q t hA1 (t * p₁.1 * t) htst_not_H with
    ⟨canonical, _hcanonical, huniq⟩
  let q₁ : H × Q := (⟨p₁.2⁻¹, hA1.Q_le_H (Q.inv_mem hr₁Q)⟩, ⟨p₁.2, hr₁Q⟩)
  let q₂ : H × Q := (⟨p₂.2⁻¹, hA1.Q_le_H (Q.inv_mem hr₂Q)⟩, ⟨p₂.2, hr₂Q⟩)
  have hq₁ : q₁ = canonical := by
    exact huniq q₁ (by simpa [q₁] using heq₁)
  have hq₂ : q₂ = canonical := by
    exact huniq q₂ (by simpa [q₂, hs_eq] using heq₂)
  have hr_eq : p₁.2 = p₂.2 := by
    have hpair : q₁ = q₂ := hq₁.trans hq₂.symm
    simpa [q₁, q₂] using congrArg (fun p : H × Q => ((p.2 : Q) : G)) hpair
  exact Prod.ext hs_eq.symm hr_eq

public theorem proposition_4_b
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    ∃! p : G × G,
      p.1 ∈ H ∧ IsInvolution p.1 ∧ p.2 ∈ Q ∧
        t * p.1 * t = p.2⁻¹ * t * p.2 := by
  rcases proposition_4_b_exists H D Q t hA1 with ⟨p, hp⟩
  refine ⟨p, hp, ?_⟩
  intro q hq
  exact proposition_4_b_unique H D Q t hA1 q p hq hp

end PFchapter1section1
end CFSG.BenderSuzuki

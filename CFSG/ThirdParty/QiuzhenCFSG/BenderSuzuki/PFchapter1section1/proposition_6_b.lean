module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_b
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_2_b
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_b
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_6_a
public import Mathlib.GroupTheory.GroupAction.Period

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section1

open PFAppendixIII

universe u v

/-!
# Peterfalvi, Part II, Chapter I, Section 1, Proposition 6(b)
-/

private theorem proposition_6_b_base_ne_t_inv_base
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t : G}
    (hA1 : HypothesisA1 G Ω H D Q t) {base : Ω}
    (hHbase : H = MulAction.stabilizer G base) :
    base ≠ t⁻¹ • base := by
  intro h
  have ht_inv_H : t⁻¹ ∈ H := by
    have ht_inv_stab : t⁻¹ ∈ MulAction.stabilizer G base := by
      exact h.symm
    simpa [hHbase] using ht_inv_stab
  have htH : t ∈ H := by
    simpa using H.inv_mem ht_inv_H
  exact hA1.t_not_mem_H htH

private theorem proposition_6_b_D_fixes_base
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t d : G}
    (hA1 : HypothesisA1 G Ω H D Q t) {base : Ω}
    (hHbase : H = MulAction.stabilizer G base) (hd : d ∈ D) :
    d • base = base := by
  have hdH : d ∈ H := hA1.D_le_H hd
  have hdstab : d ∈ MulAction.stabilizer G base := by
    simpa [hHbase] using hdH
  simpa using hdstab

private theorem proposition_6_b_D_fixes_t_inv_base
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t d : G}
    (hA1 : HypothesisA1 G Ω H D Q t) {base : Ω}
    (hHbase : H = MulAction.stabilizer G base) (hd : d ∈ D) :
    d • (t⁻¹ • base) = t⁻¹ • base := by
  have hd' : d ∈ H ⊓ rightConjugate H t := by
    simpa [hA1.D_eq] using hd
  have hconj :
      rightConjugate H t = MulAction.stabilizer G (t⁻¹ • base) := by
    rw [hHbase]
    exact rightConjugate_stabilizer base t
  have hdstab : d ∈ MulAction.stabilizer G (t⁻¹ • base) := by
    simpa [hconj] using hd'.2
  simpa using hdstab

public theorem proposition_6_b_eq_one_of_sq_eq_one_mem_odd_subgroup
    {G : Type*} [Group G] [Finite G] (D : Subgroup G)
    (hDodd : Odd (Nat.card D)) {x : G} (hxD : x ∈ D) (hx2 : x ^ 2 = 1) :
    x = 1 := by
  by_contra hxne
  let xD : D := ⟨x, hxD⟩
  have hxD_sq : xD ^ 2 = 1 := by
    ext
    simpa [xD] using hx2
  have hxD_ne : xD ≠ 1 := by
    intro h
    exact hxne (Subtype.ext_iff.mp h)
  have htwo_dvd : 2 ∣ orderOf xD := by
    rw [orderOf_eq_prime hxD_sq hxD_ne]
  have horder_dvd : orderOf xD ∣ Nat.card D :=
    orderOf_dvd_natCard xD
  have horder_odd : Odd (orderOf xD) :=
    Odd.of_dvd_nat hDodd horder_dvd
  exact horder_odd.not_two_dvd_nat htwo_dvd

private theorem proposition_6_b_H_decomp
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t h : G}
    (hA1 : HypothesisA1 G Ω H D Q t) (hh : h ∈ H) :
    ∃ q : G, q ∈ Q ∧ ∃ d : G, d ∈ D ∧ q * d = h := by
  classical
  let QH : Subgroup H := Q.subgroupOf H
  let DH : Subgroup H := D.subgroupOf H
  let hH : H := ⟨h, hh⟩
  have hQH_top : QH ⊔ DH = ⊤ := by
    calc
      QH ⊔ DH = (Q ⊔ D).subgroupOf H := by
        exact (Subgroup.subgroupOf_sup hA1.Q_le_H hA1.D_le_H).symm
      _ = H.subgroupOf H := by rw [hA1.Q_sup_D]
      _ = ⊤ := (Subgroup.subgroupOf_eq_top).2 le_rfl
  haveI : QH.Normal := hA1.Q_normal_in_H
  have hhH : hH ∈ QH ⊔ DH := by
    rw [hQH_top]
    trivial
  rcases (Subgroup.mem_sup_of_normal_left (s := QH) (t := DH) (x := hH)).mp hhH with
    ⟨qH, hqH, dH, hdH, hmul⟩
  refine ⟨qH, ?_, dH, ?_, ?_⟩
  · change (qH : G) ∈ Q at hqH
    exact hqH
  · change (dH : G) ∈ D at hdH
    exact hdH
  · exact congrArg Subtype.val hmul

private theorem proposition_6_b_H_decomp_unique
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t q₁ d₁ q₂ d₂ : G}
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hq₁ : q₁ ∈ Q) (hd₁ : d₁ ∈ D) (hq₂ : q₂ ∈ Q) (hd₂ : d₂ ∈ D)
    (hmul : q₁ * d₁ = q₂ * d₂) :
    q₁ = q₂ ∧ d₁ = d₂ := by
  classical
  have hqd_eq : q₂⁻¹ * q₁ = d₂ * d₁⁻¹ := by
    have haux : q₂⁻¹ * q₁ * d₁ = d₂ := by
      calc
        q₂⁻¹ * q₁ * d₁ = q₂⁻¹ * (q₁ * d₁) := by group
        _ = q₂⁻¹ * (q₂ * d₂) := by rw [hmul]
        _ = d₂ := by group
    calc
      q₂⁻¹ * q₁ = (q₂⁻¹ * q₁ * d₁) * d₁⁻¹ := by group
      _ = d₂ * d₁⁻¹ := by rw [haux]
  have hqd_mem : q₂⁻¹ * q₁ ∈ Q ⊓ D := by
    constructor
    · exact Q.mul_mem (Q.inv_mem hq₂) hq₁
    · rw [hqd_eq]
      exact D.mul_mem hd₂ (D.inv_mem hd₁)
  have hqd_one : q₂⁻¹ * q₁ = 1 := by
    have hbot : Q ⊓ D = ⊥ := hA1.Q_disjoint_D.eq_bot
    have : q₂⁻¹ * q₁ ∈ (⊥ : Subgroup G) := by
      simpa [hbot] using hqd_mem
    simpa using this
  have hq : q₁ = q₂ := by
    calc
      q₁ = q₂ * (q₂⁻¹ * q₁) := by group
      _ = q₂ := by simp [hqd_one]
  have hd : d₁ = d₂ := by
    have hmul' : q₂ * d₁ = q₂ * d₂ := by
      simpa [hq] using hmul
    exact mul_left_cancel hmul'
  exact ⟨hq, hd⟩

private theorem proposition_6_b_Q_conj_mem_of_mem_H
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t h q : G}
    (hA1 : HypothesisA1 G Ω H D Q t) (hh : h ∈ H) (hq : q ∈ Q) :
    h * q * h⁻¹ ∈ Q := by
  classical
  let hH : H := ⟨h, hh⟩
  let qH : H := ⟨q, hA1.Q_le_H hq⟩
  have hqH : qH ∈ Q.subgroupOf H := by
    simpa [qH, Subgroup.mem_subgroupOf] using hq
  have hmem := hA1.Q_normal_in_H.conj_mem qH hqH hH
  simpa [hH, qH, Subgroup.mem_subgroupOf, mul_assoc] using hmem

private theorem proposition_6_b_involution_mem_Q_of_mem_H
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t h : G}
    (hA1 : HypothesisA1 G Ω H D Q t) (hh : h ∈ H) (hinv : IsInvolution h) :
    h ∈ Q := by
  classical
  rcases proposition_6_b_H_decomp hA1 hh with ⟨q, hq, d, hd, hqd⟩
  have hdH : d ∈ H := hA1.D_le_H hd
  have hdqQ : d * q * d⁻¹ ∈ Q :=
    proposition_6_b_Q_conj_mem_of_mem_H hA1 hdH hq
  have hqpartQ : q * (d * q * d⁻¹) ∈ Q := Q.mul_mem hq hdqQ
  have hdpartD : d * d ∈ D := D.mul_mem hd hd
  have hmul_decomp : (q * (d * q * d⁻¹)) * (d * d) = 1 * 1 := by
    calc
      (q * (d * q * d⁻¹)) * (d * d) = (q * d) * (q * d) := by group
      _ = h * h := by rw [hqd]
      _ = h ^ 2 := by rw [pow_two]
      _ = 1 := hinv.sq_eq_one
      _ = 1 * 1 := by simp
  have hd_sq : d * d = 1 :=
    (proposition_6_b_H_decomp_unique hA1 hqpartQ hdpartD Q.one_mem D.one_mem
      hmul_decomp).2
  have hd_pow : d ^ 2 = 1 := by simpa [pow_two] using hd_sq
  have hd_one : d = 1 :=
    proposition_6_b_eq_one_of_sq_eq_one_mem_odd_subgroup D hA1.D_odd hd hd_pow
  have hhq : h = q := by
    calc
      h = q * d := hqd.symm
      _ = q := by simp [hd_one]
  rw [hhq]
  exact hq

private theorem proposition_6_b_mem_normalizer_zpowers_of_commute
    {G : Type*} [Group G] {a g : G} (hga : Commute g a) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨n, ?_⟩
    have hcomm : g * a ^ n = a ^ n * g := (hga.zpow_right n).eq
    exact (calc
      g * a ^ n * g⁻¹ = a ^ n := by
        rw [hcomm]
        simp [mul_assoc]).symm
  · intro hx
    rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, hn⟩
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨n, ?_⟩
    have hcomm : g * a ^ n = a ^ n * g := (hga.zpow_right n).eq
    have hx_eq : x = a ^ n := by
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * a ^ n * g := by rw [← hn]
        _ = a ^ n := by
          calc
            g⁻¹ * a ^ n * g = g⁻¹ * (a ^ n * g) := by rw [mul_assoc]
            _ = g⁻¹ * (g * a ^ n) := by rw [← hcomm]
            _ = a ^ n := by simp
    exact hx_eq.symm

private theorem proposition_6_b_centralizer_involution_le_rightConjugate
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t s u g : G}
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hsH : s ∈ H) (hsI : IsInvolution s)
    (hu_eq : u = rightConjugateElem s g) :
    Subgroup.centralizer ({u} : Set G) ≤ rightConjugate H g := by
  classical
  have hsQ : s ∈ Q := proposition_6_b_involution_mem_Q_of_mem_H hA1 hsH hsI
  have hzpow_ne : Subgroup.zpowers s ≠ (⊥ : Subgroup G) := by
    intro hbot
    have hs_bot : s ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_zpowers s
    exact hsI.ne_one (by simpa using hs_bot)
  have hzpow_le_Q : Subgroup.zpowers s ≤ Q := by
    exact Subgroup.zpowers_le.mpr hsQ
  have hcentralizer_s_le_H : Subgroup.centralizer ({s} : Set G) ≤ H := by
    intro x hx
    have hxComm : Commute x s := Subgroup.mem_centralizer_singleton_iff.mp hx
    have hxNorm : x ∈ Subgroup.normalizer ((Subgroup.zpowers s : Subgroup G) : Set G) := by
      exact proposition_6_b_mem_normalizer_zpowers_of_commute hxComm
    exact (proposition_1_b H D Q t hA1 (Subgroup.zpowers s) hzpow_ne hzpow_le_Q) hxNorm
  intro x hx
  refine ⟨g * x * g⁻¹, ?_, ?_⟩
  · apply hcentralizer_s_le_H
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxCommU : Commute x u := Subgroup.mem_centralizer_singleton_iff.mp hx
    rw [hu_eq] at hxCommU
    change (g * x * g⁻¹) * s = s * (g * x * g⁻¹)
    have hconj := congrArg (fun z => g * z * g⁻¹) hxCommU.eq
    simpa [rightConjugateElem, mul_assoc] using hconj
  · calc
      (MulAut.conj g⁻¹) (g * x * g⁻¹) =
          g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ := rfl
      _ = x := by group

private theorem proposition_6_b_orderOf_even_of_swap
    {Γ Ω : Type*} [Group Γ] [Finite Γ] [MulAction Γ Ω]
    {g : Γ} {a b : Ω}
    (hab : a ≠ b) (hga : g • a = b) (hgb : g • b = a) :
    Even (orderOf g) := by
  classical
  have hpow2 : g ^ 2 • a = a := by
    calc
      g ^ 2 • a = g • (g • a) := by rw [pow_two, mul_smul]
      _ = g • b := by rw [hga]
      _ = a := hgb
  have hperiod_dvd_two : MulAction.period g a ∣ 2 :=
    MulAction.pow_smul_eq_iff_period_dvd.mp hpow2
  have hperiod_pos : 0 < MulAction.period g a :=
    MulAction.period_pos_of_orderOf_pos (orderOf_pos g) a
  have hle_period : 2 ≤ MulAction.period g a := by
    apply MulAction.le_period hperiod_pos
    intro k hkpos hklt
    have hk : k = 1 := by omega
    subst k
    simpa [hga] using hab.symm
  have hperiod_le_two : MulAction.period g a ≤ 2 :=
    Nat.le_of_dvd (by decide) hperiod_dvd_two
  have hperiod_eq_two : MulAction.period g a = 2 :=
    le_antisymm hperiod_le_two hle_period
  have htwo_dvd_order : 2 ∣ orderOf g := by
    rw [← hperiod_eq_two]
    exact MulAction.period_dvd_orderOf g a
  exact even_iff_two_dvd.mpr htwo_dvd_order

private theorem proposition_6_b_exists_involution_of_even_order_element
    {G : Type*} [Group G] [Finite G] {K : Subgroup G} (g : K)
    (hg_even : Even (orderOf g)) :
    ∃ u : G, u ∈ K ∧ IsInvolution u := by
  classical
  have htwo_dvd_card : 2 ∣ Nat.card K :=
    hg_even.two_dvd.trans (orderOf_dvd_natCard g)
  obtain ⟨u, hu_order⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 htwo_dvd_card
  refine ⟨u, u.property, ?_⟩
  constructor
  · intro hu_one
    have horder_one : orderOf u = 1 := by
      have : u = 1 := by
        ext
        exact hu_one
      simp [this]
    omega
  · have hpow : u ^ 2 = 1 := by
      simpa [hu_order] using pow_orderOf_eq_one u
    exact congrArg Subtype.val hpow

private theorem proposition_6_b_even_card_of_contains_involution
    {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    {u : G} (huK : u ∈ K) (huI : IsInvolution u) :
    Even (Nat.card K) := by
  classical
  let uK : K := ⟨u, huK⟩
  have hpow : uK ^ 2 = 1 := by
    ext
    simpa [uK] using huI.sq_eq_one
  have hne : uK ≠ 1 := by
    intro h
    exact huI.ne_one (Subtype.ext_iff.mp h)
  have horder : orderOf uK = 2 := orderOf_eq_prime hpow hne
  have htwo_dvd_card : 2 ∣ Nat.card K := by
    rw [← horder]
    exact orderOf_dvd_natCard uK
  have hEven : Even (Nat.card K) := even_iff_two_dvd.mpr htwo_dvd_card
  simpa [Nat.card, Nat.card_coe_set_eq] using hEven

private theorem proposition_6_b_exists_fixed_ne_two
    {G Ω : Type*} [Group G] [MulAction G Ω] [Finite Ω]
    {X : Subgroup G} {a b : Ω}
    (ha : a ∈ fixedPointsOfSubgroup G Ω X)
    (hb : b ∈ fixedPointsOfSubgroup G Ω X)
    (hfixed : 3 ≤ Nat.card {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}) :
    ∃ e : Ω, e ∈ fixedPointsOfSubgroup G Ω X ∧ e ≠ a ∧ e ≠ b := by
  classical
  let Fixed : Type _ := {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}
  by_contra hno
  have hcover : ∀ p : Fixed, (p : Ω) = a ∨ (p : Ω) = b := by
    intro p
    by_contra hp
    apply hno
    exact ⟨p, p.property, fun h => hp (Or.inl h), fun h => hp (Or.inr h)⟩
  let pa : Fixed := ⟨a, ha⟩
  let pb : Fixed := ⟨b, hb⟩
  let f : Fin 2 → Fixed := fun i => if i = 0 then pa else pb
  letI : Fintype Fixed := Fintype.ofFinite Fixed
  have hsurj : Function.Surjective f := by
    intro p
    rcases hcover p with hp | hp
    · refine ⟨0, ?_⟩
      ext
      simp [f, pa, hp]
    · refine ⟨1, ?_⟩
      ext
      simp [f, pb, hp]
  have hcard_le : Fintype.card Fixed ≤ 2 := by
    simpa using Fintype.card_le_of_surjective f hsurj
  have hcard_ge : 3 ≤ Fintype.card Fixed := by
    rw [← Nat.card_eq_fintype_card]
    change 3 ≤ Nat.card {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}
    exact hfixed
  omega

private theorem proposition_6_b_centralizer_moves_base_to_fixed
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q X : Subgroup G} {t : G}
    (hA1 : HypothesisA1 G Ω H D Q t) (hX_le_D : X ≤ D) {base z : Ω}
    (hHbase : H = MulAction.stabilizer G base)
    (hdouble : ∀ a b c d : Ω,
      a ∈ fixedPointsOfSubgroup G Ω X →
      b ∈ fixedPointsOfSubgroup G Ω X →
      c ∈ fixedPointsOfSubgroup G Ω X →
      d ∈ fixedPointsOfSubgroup G Ω X →
      a ≠ b → c ≠ d →
        ∃ g : G, g ∈ Subgroup.centralizer (X : Set G) ∧ g • a = c ∧ g • b = d)
    (hfixed_card : 3 ≤ Nat.card {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X})
    (hz_fixed : z ∈ fixedPointsOfSubgroup G Ω X) :
    ∃ g : G, g ∈ Subgroup.centralizer (X : Set G) ∧ g • base = z := by
  classical
  have hbase_fixed : base ∈ fixedPointsOfSubgroup G Ω X := by
    intro x hx
    exact proposition_6_b_D_fixes_base hA1 hHbase (hX_le_D hx)
  by_cases hz_base : z = base
  · exact ⟨1, Subgroup.one_mem _, by simp [hz_base]⟩
  · rcases proposition_6_b_exists_fixed_ne_two hbase_fixed hz_fixed hfixed_card with
      ⟨e, he_fixed, he_ne_base, he_ne_z⟩
    rcases
      hdouble base e z e
        hbase_fixed he_fixed hz_fixed he_fixed he_ne_base.symm he_ne_z.symm with
      ⟨g, hgC, hgbase, _hge⟩
    exact ⟨g, hgC, hgbase⟩

public theorem proposition_6_b
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q X : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hX_le_D : X ≤ D)
    (hfixed : 3 ≤ Nat.card {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}) :
    Even (Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓ Q)) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (X : Set G)
  obtain ⟨base, hHbase⟩ := hA1.point_stabilizer
  have hdouble := (proposition_6_a H D Q X t hA1 hX_le_D hfixed).1
  have hbase_fixed : base ∈ fixedPointsOfSubgroup G Ω X := by
    intro x hx
    exact proposition_6_b_D_fixes_base hA1 hHbase (hX_le_D hx)
  have hbeta_fixed : t⁻¹ • base ∈ fixedPointsOfSubgroup G Ω X := by
    intro x hx
    exact proposition_6_b_D_fixes_t_inv_base hA1 hHbase (hX_le_D hx)
  have hbase_ne_beta : base ≠ t⁻¹ • base :=
    proposition_6_b_base_ne_t_inv_base hA1 hHbase
  rcases
    hdouble base (t⁻¹ • base) (t⁻¹ • base) base
      hbase_fixed hbeta_fixed hbeta_fixed hbase_fixed
      hbase_ne_beta hbase_ne_beta.symm with
    ⟨g, hgC, hg_base, hg_beta⟩
  let gC : C := ⟨g, hgC⟩
  have hg_even : Even (orderOf gC) := by
    apply proposition_6_b_orderOf_even_of_swap (a := base) (b := t⁻¹ • base)
    · exact hbase_ne_beta
    · simpa [gC] using hg_base
    · simpa [gC] using hg_beta
  rcases proposition_6_b_exists_involution_of_even_order_element gC hg_even with
    ⟨u, huC, huI⟩
  obtain ⟨p, hp, _hpuniq⟩ := proposition_4_b H D Q t hA1
  let s : G := p.1
  have hsH : s ∈ H := hp.1
  have hsI : IsInvolution s := hp.2.1
  rcases proposition_2_b H D Q t hA1 s u hsI huI with ⟨r, hur⟩
  have hcent_u_le_Hr :
      Subgroup.centralizer ({u} : Set G) ≤ rightConjugate H r :=
    proposition_6_b_centralizer_involution_le_rightConjugate hA1 hsH hsI hur
  have huHr : u ∈ rightConjugate H r := by
    refine ⟨s, hsH, ?_⟩
    simpa [rightConjugateElem] using hur.symm
  let omega_u : Ω := r⁻¹ • base
  have hHr_stab :
      rightConjugate H r = MulAction.stabilizer G omega_u := by
    dsimp [omega_u]
    rw [hHbase]
    exact rightConjugate_stabilizer base r
  have hu_fixes_omega : u • omega_u = omega_u := by
    have hu_stab : u ∈ MulAction.stabilizer G omega_u := by
      simpa [hHr_stab] using huHr
    simpa using hu_stab
  have homega_fixed : omega_u ∈ fixedPointsOfSubgroup G Ω X := by
    intro x hx
    have hx_cent_u : x ∈ Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm : x * u = u * x :=
        (Subgroup.mem_centralizer_iff.mp huC) x hx
      exact hcomm
    have hx_stab : x ∈ MulAction.stabilizer G omega_u := by
      simpa [hHr_stab] using hcent_u_le_Hr hx_cent_u
    simpa using hx_stab
  rcases
    proposition_6_b_centralizer_moves_base_to_fixed hA1 hX_le_D hHbase hdouble
      hfixed homega_fixed with
    ⟨c, hcC, hc_base⟩
  let v : G := rightConjugateElem u c
  have hvC : v ∈ C := by
    dsimp [v, rightConjugateElem]
    exact C.mul_mem (C.mul_mem (C.inv_mem hcC) huC) hcC
  have hvH : v ∈ H := by
    have hv_stab : v ∈ MulAction.stabilizer G base := by
      change v • base = base
      calc
        v • base = c⁻¹ • (u • (c • base)) := by
          simp [v, rightConjugateElem, mul_assoc, smul_smul]
        _ = c⁻¹ • (u • omega_u) := by rw [hc_base]
        _ = c⁻¹ • omega_u := by rw [hu_fixes_omega]
        _ = base := by
          rw [← hc_base]
          simp [smul_smul]
    simpa [hHbase] using hv_stab
  have hvI : IsInvolution v :=
    isInvolution_rightConjugateElem huI
  have hvQ : v ∈ Q := proposition_6_b_involution_mem_Q_of_mem_H hA1 hvH hvI
  exact
    proposition_6_b_even_card_of_contains_involution
      (Subgroup.centralizer (X : Set G) ⊓ Q) ⟨hvC, hvQ⟩ hvI

end PFchapter1section1
end CFSG.BenderSuzuki

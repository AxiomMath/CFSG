module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Coherence
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Remark31
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Theorem32
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Lemma33
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Lemma34
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunction
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Clifford
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Induction
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Trace
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Section 3 — Lemma 3.6

Lemma 3.6: if `χ ∈ Irr(G)` with `B(χ)` not empty and `K ⊄ Ker(χ)`, and
`ν^s ∈ Λν` for every `ν ∈ B(χ)`, then for some `α ∈ Irr(U)`,
`K ⊄ Ker(α)` and `χ(1) > 2m·α(1)`, proved below.
-/

noncomputable section

open scoped BigOperators
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.BenderGlauberman

open GorensteinWalter
open Theory.Character

-- Local instances matching `Theory.Character`'s subgroup-sum convention; see
-- `BenderGlauberman/ClassFunction.lean`.
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u v

section Section3

variable {G : Type u} [Group G] [Fintype G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable (c : Hyp11 G)

/-! ## Local K-infrastructure for Lemma 3.6 -/

/-- `U = O(H)` has odd order. -/
private lemma U_coprime_two (c : Hyp11 G) [Hyp11KData c] : Nat.Coprime 2 (Nat.card ↥c.U) := by
  have h1 : Nat.card ↥c.U = Nat.card (pPrimeCore 2 c.H) := by
    dsimp [Hyp11.U]
    rw [oddCoreOf]
    exact Subgroup.card_map_of_injective (f := c.H.subtype)
      (K := pPrimeCore 2 c.H) (Subgroup.subtype_injective c.H)
  rw [h1]
  exact pPrimeCore_coprime_card (p := 2) (G := c.H)

/-- `U ⊴ H`: conjugation by any element of `H` preserves `U = O(H)`. -/
private lemma U_normal_in_H_local (c : Hyp11 G) [Hyp11KData c] {h u : G} (hh : h ∈ c.H) (hu : u ∈ c.U) :
    h * u * h⁻¹ ∈ c.U := by
  have huU : u ∈ (pPrimeCore 2 c.H).map c.H.subtype := by
    simpa [Hyp11.U, oddCoreOf] using hu
  have huH : u ∈ c.H :=
    SetLike.le_def.1 (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)) huU
  have hchar : (pPrimeCore 2 c.H).Characteristic :=
    pPrimeCore_characteristic (p := 2) (G := c.H)
  have hcomap : (pPrimeCore 2 c.H) ≤ (pPrimeCore 2 c.H).comap
      (MulAut.conj ⟨h, hh⟩).toMonoidHom :=
    (Subgroup.characteristic_iff_le_comap.mp hchar) (MulAut.conj ⟨h, hh⟩)
  have huK : (⟨u, huH⟩ : ↥c.H) ∈ pPrimeCore 2 c.H := by
    rcases (Subgroup.mem_map.mp huU) with ⟨x, hx, hxeq⟩
    have hxeq' : (⟨u, huH⟩ : ↥c.H) = x := by
      ext
      simpa using hxeq.symm
    simpa [hxeq'] using hx
  have hconj : (MulAut.conj ⟨h, hh⟩) ⟨u, huH⟩ ∈ pPrimeCore 2 c.H :=
    Subgroup.mem_comap.mp (hcomap huK)
  refine (Subgroup.mem_map.mpr ?_)
  refine ⟨⟨h * u * h⁻¹,
    c.H.mul_mem (c.H.mul_mem hh huH) (c.H.inv_mem hh)⟩, ?_, rfl⟩
  have hcx : (MulAut.conj ⟨h, hh⟩) ⟨u, huH⟩ =
      (⟨h * u * h⁻¹,
        c.H.mul_mem (c.H.mul_mem hh huH) (c.H.inv_mem hh)⟩ : ↥c.H) := by
    ext
    simp [MulAut.conj_apply, mul_assoc]
  rw [← hcx]
  exact hconj

/-- `S ≤ N_G(U)`. -/
private lemma S_le_normalizer_U (c : Hyp11 G) [Hyp11KData c] :
    (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact U_normal_in_H_local c (S_le_H c hs) hu
  · intro hsu
    have hs' : s⁻¹ ∈ c.H := c.H.inv_mem (S_le_H c hs)
    have h1 := U_normal_in_H_local c hs' hsu
    have h2 : s⁻¹ * (s * u * s⁻¹) * (s⁻¹)⁻¹ = u := by group
    rwa [h2] at h1

/-- `K ≤ K₁`. -/
private lemma K_le_K1_local (c : Hyp11 G) [Hyp11KData c] : c.K ≤ c.K1 := by
  change c.K1 ⊓ c.K2 ≤ c.K1
  exact inf_le_left

/-- `K ≤ K₂`. -/
private lemma K_le_K2_local (c : Hyp11 G) [Hyp11KData c] : c.K ≤ c.K2 := by
  change c.K1 ⊓ c.K2 ≤ c.K2
  exact inf_le_right

/-- `K ≤ H`. -/
private lemma K_le_H_local (c : Hyp11 G) [Hyp11KData c] : c.K ≤ c.H := by
  exact le_trans (K_le_K1_local c) c.K1_le_H

/-- `K` has odd order. -/
private lemma K_odd_local (c : Hyp11 G) [Hyp11KData c] : Nat.Coprime 2 (Nat.card ↥c.K) := by
  have hdiv : Nat.card ↥c.K ∣ Nat.card ↥c.K1 :=
    Subgroup.card_dvd_of_le (K_le_K1_local c)
  exact c.K1_odd.coprime_dvd_right hdiv

/-- `t₁` inverts every element of `K`. -/
private lemma t1_inverts_K (c : Hyp11 G) [Hyp11KData c] {k : G} (hk : k ∈ c.K) :
    c.t1 * k * c.t1⁻¹ = k⁻¹ :=
  c.K1_inverted k (K_le_K1_local c hk)

/-- `t₂` inverts every element of `K`. -/
private lemma t2_inverts_K (c : Hyp11 G) [Hyp11KData c] {k : G} (hk : k ∈ c.K) :
    c.t2 * k * c.t2⁻¹ = k⁻¹ :=
  c.K2_inverted k (K_le_K2_local c hk)

/-- `t₁·t₂` centralizes `K`. -/
private lemma r0_centralizes_K (c : Hyp11 G) [Hyp11KData c] {k : G} (hk : k ∈ c.K) :
    (c.t1 * c.t2) * k * (c.t1 * c.t2)⁻¹ = k := by
  have h1 := t1_inverts_K c hk
  have h2 := t2_inverts_K c hk
  calc
    (c.t1 * c.t2) * k * (c.t1 * c.t2)⁻¹
        = c.t1 * ((c.t2 * k * c.t2⁻¹) * c.t1⁻¹) := by group
    _ = c.t1 * (k⁻¹ * c.t1⁻¹) := by rw [h2]
    _ = c.t1 * k⁻¹ * c.t1⁻¹ := by group
    _ = (c.t1 * k * c.t1⁻¹)⁻¹ := by group
    _ = (k⁻¹)⁻¹ := by rw [h1]
    _ = k := by simp

/-- An element centralized by `r` is centralized by every power of `r`. -/
private lemma centralizes_zpowers_of_centralized_local {r a : G}
    (h : r * a * r⁻¹ = a) :
    a ∈ Subgroup.centralizer ((Subgroup.zpowers r : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hcomm : r * a = a * r := by
    calc
      r * a = (r * a * r⁻¹) * r := by group
      _ = a * r := by rw [h]
  have hr : r ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  have hz : Subgroup.zpowers r ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.zpowers_le.mpr hr
  have hsa : s * a = a * s := by
    have hc := hz hs
    rwa [Subgroup.mem_centralizer_singleton_iff] at hc
  exact hsa

/-- `S0 = ⟨t₁·t₂⟩` centralizes `K`. -/
private lemma S0_centralizes_K (c : Hyp11 G) [Hyp11KData c] {k : G} (hk : k ∈ c.K) :
    k ∈ Subgroup.centralizer ((c.S0 : Subgroup G) : Set G) := by
  have hr0 : (c.t1 * c.t2) * k * (c.t1 * c.t2)⁻¹ = k := r0_centralizes_K c hk
  have hz : k ∈ Subgroup.centralizer
      ((Subgroup.zpowers (c.t1 * c.t2) : Subgroup G) : Set G) :=
    centralizes_zpowers_of_centralized_local hr0
  simpa [c.S0_eq_zpowers] using hz

/-- Every reflection of `S` is `t₁` or `t₂` up to an element of `S0`. -/
private lemma reflection_t1S0_or_t2S0 (c : Hyp11 G) [Hyp11KData c] {x : G}
    (hxS : x ∈ (c.S : Subgroup G)) (hxnot : x ∉ (c.S0 : Subgroup G)) :
    c.t1 * x ∈ (c.S0 : Subgroup G) ∨ c.t2 * x ∈ (c.S0 : Subgroup G) := by
  let K : Subgroup ↥(c.S : Subgroup G) :=
    (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)
  have hindex : K.index = 2 := by
    simpa [K] using S0_index c
  let a : ↥(c.S : Subgroup G) := ⟨c.t1, c.t1_mem_S⟩
  let b : ↥(c.S : Subgroup G) := ⟨x, hxS⟩
  have hiff := Subgroup.mul_mem_iff_of_index_two hindex (a := a) (b := b)
  have ha : a ∉ K := by
    intro ha
    exact c.t1_not_mem_S0 (Subgroup.mem_subgroupOf.mp ha)
  have hb : b ∉ K := by
    intro hb
    exact hxnot (Subgroup.mem_subgroupOf.mp hb)
  have hab : a * b ∈ K := by
    rw [hiff]
    simp [ha, hb]
  have habG : (a * b : ↥(c.S : Subgroup G)) = ⟨c.t1 * x,
      ((c.S : Subgroup G).mul_mem c.t1_mem_S hxS)⟩ := by
    ext
    rfl
  have hmem : c.t1 * x ∈ (c.S0 : Subgroup G) := by
    have h' : (⟨c.t1 * x,
        ((c.S : Subgroup G).mul_mem c.t1_mem_S hxS)⟩ : ↥(c.S : Subgroup G)) ∈ K := by
      simpa [K, habG] using hab
    exact Subgroup.mem_subgroupOf.mp h'
  exact Or.inl hmem

/-- Every reflection of `S \ S0` inverts `K`. -/
private lemma reflection_inverts_K (c : Hyp11 G) [Hyp11KData c] {x k : G}
    (hxS : x ∈ (c.S : Subgroup G)) (hxnot : x ∉ (c.S0 : Subgroup G))
    (hk : k ∈ c.K) : x * k * x⁻¹ = k⁻¹ := by
  rcases reflection_t1S0_or_t2S0 c hxS hxnot with hx1 | hx2
  · -- x = t₁·r with r = t₁·x ∈ S0
    have hrS0 : c.t1 * x ∈ (c.S0 : Subgroup G) := hx1
    let r : G := c.t1 * x
    have hx_eq : x = c.t1 * r := by
      dsimp [r]
      have ht1sq : c.t1 * c.t1 = 1 := by
        simpa [pow_two] using c.t1_involution.2
      calc
        x = (c.t1 * c.t1) * x := by rw [ht1sq]; simp
        _ = c.t1 * (c.t1 * x) := by group
    have hkcen : k ∈ Subgroup.centralizer ((c.S0 : Subgroup G) : Set G) :=
      S0_centralizes_K c hk
    have hkr0 : (c.t1 * x) * k = k * (c.t1 * x) :=
      (Subgroup.mem_centralizer_iff.mp hkcen) (c.t1 * x) hrS0
    have hkr : (c.t1 * x) * k * (c.t1 * x)⁻¹ = k := by
      rw [hkr0]
      group
    have h1 := t1_inverts_K c hk
    calc
      x * k * x⁻¹ = (c.t1 * r) * k * (c.t1 * r)⁻¹ := by rw [hx_eq]
      _ = c.t1 * (r * k * r⁻¹) * c.t1⁻¹ := by group
      _ = c.t1 * k * c.t1⁻¹ := by rw [hkr]
      _ = k⁻¹ := h1
  · -- symmetric using t₂
    have hrS0 : c.t2 * x ∈ (c.S0 : Subgroup G) := hx2
    let r : G := c.t2 * x
    have hx_eq : x = c.t2 * r := by
      dsimp [r]
      have ht2sq : c.t2 * c.t2 = 1 := by
        simpa [pow_two] using c.t2_involution.2
      calc
        x = (c.t2 * c.t2) * x := by rw [ht2sq]; simp
        _ = c.t2 * (c.t2 * x) := by group
    have hkcen : k ∈ Subgroup.centralizer ((c.S0 : Subgroup G) : Set G) :=
      S0_centralizes_K c hk
    have hkr0 : (c.t2 * x) * k = k * (c.t2 * x) :=
      (Subgroup.mem_centralizer_iff.mp hkcen) (c.t2 * x) hrS0
    have hkr : (c.t2 * x) * k * (c.t2 * x)⁻¹ = k := by
      rw [hkr0]
      group
    have h2 := t2_inverts_K c hk
    calc
      x * k * x⁻¹ = (c.t2 * r) * k * (c.t2 * r)⁻¹ := by rw [hx_eq]
      _ = c.t2 * (r * k * r⁻¹) * c.t2⁻¹ := by group
      _ = c.t2 * k * c.t2⁻¹ := by rw [hkr]
      _ = k⁻¹ := h2

/-- The chosen involution `s ∈ S \ S0` inverts `K`. -/
private lemma s_inverts_K (c : Hyp11 G) [Hyp11KData c] {k : G} (hk : k ∈ c.K) :
    c.s * k * c.s⁻¹ = k⁻¹ :=
  reflection_inverts_K c c.s_mem_S c.s_not_mem_S0 hk

/-- Every odd-order subgroup of `H` lies in the odd core `U`. -/
private lemma odd_subgroup_le_U (c : Hyp11 G) [Hyp11KData c] {X : Subgroup G}
    (hXH : X ≤ c.H) (hXodd : Nat.Coprime 2 (Nat.card ↥X)) :
    X ≤ c.U := by
  intro k hk
  have hkH : k ∈ c.H := hXH hk
  have hUleH : c.U ≤ c.H :=
    SetLike.le_def.1 (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H))
  let BH : Subgroup ↥c.H := (c.U : Subgroup G).subgroupOf c.H
  have : BH.Normal := (Subgroup.normal_subgroupOf_iff hUleH).2 (by
    intro h b hb hh
    exact U_normal_in_H_local c hh hb)
  let q : ↥c.H →* (↥c.H ⧸ BH) := QuotientGroup.mk' BH
  let kH : ↥c.H := ⟨k, hkH⟩
  have hHset : (↑c.H : Set G) = (c.U : Set G) * (↑(c.S : Subgroup G) : Set G) := by
    rw [← c.H_eq_US]
    exact Subgroup.coe_mul_of_right_le_normalizer_left c.U (c.S : Subgroup G)
      (S_le_normalizer_U c)
  have hk' : k ∈ (c.U : Set G) * (↑(c.S : Subgroup G) : Set G) := by
    rw [← hHset]
    exact hkH
  rcases hk' with ⟨u, hu, s, hs, hEq⟩
  let uH : ↥c.H := ⟨u, hUleH hu⟩
  let sH : ↥c.H := ⟨s, S_le_H c hs⟩
  have hEqH : kH = uH * sH := by
    apply Subtype.ext
    simpa [uH, sH] using hEq.symm
  have hqEq : q kH = q sH := by
    rw [hEqH, map_mul]
    have hqu : q uH = 1 := by
      exact (QuotientGroup.eq_one_iff (N := BH) (x := uH)).2
        (Subgroup.mem_subgroupOf.mpr hu)
    simp [hqu]
  have hs_pow : sH ^ (2 ^ (c.m + 1)) = 1 := by
    apply Subtype.ext
    change (s : G) ^ (2 ^ (c.m + 1)) = 1
    have hcard : Nat.card ↥(c.S : Subgroup G) = 2 ^ (c.m + 1) := by
      rw [S_nat_card c]
      ring
    have hpow : (⟨s, hs⟩ : ↥(c.S : Subgroup G)) ^ (2 ^ (c.m + 1)) = 1 := by
      rw [← hcard]
      exact pow_card_eq_one' (G := ↥(c.S : Subgroup G)) (x := ⟨s, hs⟩)
    exact congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hpow
  have hqpow : q kH ^ (2 ^ (c.m + 1)) = 1 := by
    rw [hqEq, ← map_pow, hs_pow, map_one]
  have hdvd2 : orderOf (q kH) ∣ 2 ^ (c.m + 1) :=
    orderOf_dvd_of_pow_eq_one hqpow
  have hkpow1 : kH ^ orderOf k = 1 := by
    apply Subtype.ext
    change (k : G) ^ orderOf k = 1
    exact pow_orderOf_eq_one k
  have hqpowk : q kH ^ orderOf k = 1 := by
    have hq : q (kH ^ orderOf k) = 1 := by
      simpa using congrArg q hkpow1
    simpa [map_pow] using hq
  have hdvdk : orderOf (q kH) ∣ orderOf k := orderOf_dvd_of_pow_eq_one hqpowk
  have hord_dvd : orderOf k ∣ Nat.card ↥X :=
    Subgroup.orderOf_dvd_natCard X hk
  have hodd : Nat.Coprime 2 (orderOf k) := by
    exact hXodd.coprime_dvd_right hord_dvd
  have hcopq : Nat.Coprime 2 (orderOf (q kH)) :=
    Nat.Coprime.symm (Nat.Coprime.coprime_dvd_left hdvdk (Nat.Coprime.symm hodd))
  have hcopq' : Nat.Coprime (orderOf (q kH)) (2 ^ (c.m + 1)) :=
    Nat.Coprime.pow_right (c.m + 1) (Nat.Coprime.symm hcopq)
  have hord1 : orderOf (q kH) = 1 := Nat.Coprime.eq_one_of_dvd hcopq' hdvd2
  have hq1 : q kH = 1 := orderOf_eq_one_iff.mp hord1
  have hkHmem : kH ∈ BH := by
    rw [← QuotientGroup.ker_mk' BH]
    exact MonoidHom.mem_ker.mpr hq1
  exact Subgroup.mem_subgroupOf.mp hkHmem

/-- `K ≤ U`. -/
public lemma K_le_U (c : Hyp11 G) [Hyp11KData c] : c.K ≤ c.U :=
  odd_subgroup_le_U c (K_le_H_local c) (K_odd_local c)

/-- `K₁ ≤ U`. -/
public lemma K1_le_U (c : Hyp11 G) [Hyp11KData c] : c.K1 ≤ c.U :=
  odd_subgroup_le_U c c.K1_le_H c.K1_odd

/-- `K₂ ≤ U`. -/
public lemma K2_le_U (c : Hyp11 G) [Hyp11KData c] : c.K2 ≤ c.U :=
  odd_subgroup_le_U c c.K2_le_H c.K2_odd

/-- `U ≤ H`. -/
private lemma U_le_H_local (c : Hyp11 G) [Hyp11KData c] : c.U ≤ c.H :=
  SetLike.le_def.1 (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H))

/-- Conjugating a power by an element that inverts the base inverts the power. -/
private lemma inverted_power {t x : G} (h : t * x * t⁻¹ = x⁻¹) (n : ℤ) :
    t * x ^ n * t⁻¹ = (x ^ n)⁻¹ := by
  have hc : (MulAut.conj t) (x ^ n) = ((MulAut.conj t) x) ^ n := by
    rw [map_zpow]
  calc
    t * x ^ n * t⁻¹ = (MulAut.conj t) (x ^ n) := by
      simpa [MulAut.conj_apply] using hc.symm
    _ = (MulAut.conj t) x ^ n := hc
    _ = (x⁻¹) ^ n := by
      change (t * x * t⁻¹) ^ n = (x⁻¹) ^ n
      rw [h]
    _ = (x ^ n)⁻¹ := by rw [inv_zpow]

/-- `K₁` is exactly the set of elements of `U` inverted by `t₁`. -/
public lemma K1_eq_invertedElements (c : Hyp11 G) [Hyp11KData c] :
    (c.K1 : Set G) = invertedElements c.U c.t1 := by
  ext x
  constructor
  · intro hx
    rw [invertedElements]
    exact ⟨K1_le_U c hx, c.K1_inverted x hx⟩
  · intro hx
    rw [invertedElements] at hx
    rcases hx with ⟨hxU, hxinv⟩
    let X : Subgroup G := Subgroup.zpowers x
    have hXU : X ≤ c.U := Subgroup.zpowers_le.mpr hxU
    have hXH : X ≤ c.H := le_trans hXU (U_le_H_local c)
    have hXodd : Nat.Coprime 2 (Nat.card X) := by
      have hdiv : Nat.card X ∣ Nat.card ↥c.U :=
        Subgroup.card_dvd_of_le hXU
      exact U_coprime_two c |>.coprime_dvd_right hdiv
    have hXinv : IsInvertedBy c.t1 X := by
      intro y hy
      rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
      exact inverted_power hxinv n
    have hXle : X ≤ c.K1 := c.K1_maximal X hXH hXodd hXinv
    exact hXle (Subgroup.mem_zpowers x)

/-- `K₂` is exactly the set of elements of `U` inverted by `t₂`. -/
public lemma K2_eq_invertedElements (c : Hyp11 G) [Hyp11KData c] :
    (c.K2 : Set G) = invertedElements c.U c.t2 := by
  ext x
  constructor
  · intro hx
    rw [invertedElements]
    exact ⟨K2_le_U c hx, c.K2_inverted x hx⟩
  · intro hx
    rw [invertedElements] at hx
    rcases hx with ⟨hxU, hxinv⟩
    let X : Subgroup G := Subgroup.zpowers x
    have hXU : X ≤ c.U := Subgroup.zpowers_le.mpr hxU
    have hXH : X ≤ c.H := le_trans hXU (U_le_H_local c)
    have hXodd : Nat.Coprime 2 (Nat.card X) := by
      have hdiv : Nat.card X ∣ Nat.card ↥c.U :=
        Subgroup.card_dvd_of_le hXU
      exact U_coprime_two c |>.coprime_dvd_right hdiv
    have hXinv : IsInvertedBy c.t2 X := by
      intro y hy
      rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
      exact inverted_power hxinv n
    have hXle : X ≤ c.K2 := c.K2_maximal X hXH hXodd hXinv
    exact hXle (Subgroup.mem_zpowers x)

/-- `K₁ ⊴ U`. -/
public lemma K1_normal_in_U (c : Hyp11 G) [Hyp11KData c] : IsNormalIn c.K1 c.U := by
  have h := fact_1_5_iii_inverted_subgroup_abelian_normal
    (X := c.U) (s := c.t1) c.t1_involution (U_coprime_two c)
    (by
      intro x hx
      exact S_normalizes_U c c.t1 c.t1_mem_S x hx)
    (K1_eq_invertedElements c)
  exact h.2.1

/-- `K₂ ⊴ U`. -/
public lemma K2_normal_in_U (c : Hyp11 G) [Hyp11KData c] : IsNormalIn c.K2 c.U := by
  have h := fact_1_5_iii_inverted_subgroup_abelian_normal
    (X := c.U) (s := c.t2) c.t2_involution (U_coprime_two c)
    (by
      intro x hx
      exact S_normalizes_U c c.t2 c.t2_mem_S x hx)
    (K2_eq_invertedElements c)
  exact h.2.1

/-- `K ⊴ U`. -/
public lemma K_normal_in_U (c : Hyp11 G) [Hyp11KData c] : IsNormalIn c.K c.U := by
  have h1 := K1_normal_in_U c
  have h2 := K2_normal_in_U c
  constructor
  · exact le_trans (K_le_K1_local c) (K1_le_U c)
  · intro h hh k hk
    have hk1 : k ∈ c.K1 := K_le_K1_local c hk
    have hk2 : k ∈ c.K2 := K_le_K2_local c hk
    have hc1 : h * k * h⁻¹ ∈ c.K1 := h1.2 h hh k hk1
    have hc2 : h * k * h⁻¹ ∈ c.K2 := h2.2 h hh k hk2
    change h * k * h⁻¹ ∈ c.K1 ⊓ c.K2
    exact Subgroup.mem_inf.mpr ⟨hc1, hc2⟩

/-! ## Fixed-reflection kernel core (character-orbit infrastructure) -/

/-- `K` as a subgroup of `U`. -/
private def KU (c : Hyp11 G) [Hyp11KData c] : Subgroup (↥c.U) :=
  (c.K : Subgroup G).subgroupOf c.U

/-- `K ⊴ U`, as a subgroup-of-`U` normality. -/
private lemma KU_normal (c : Hyp11 G) [Hyp11KData c] : (KU c).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (K_le_U c)).mpr ?_
  intro u hu
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hk
    exact (K_normal_in_U c).2 u hu h hk
  · intro hk
    have h1 := (K_normal_in_U c).2 u⁻¹ ((c.U).inv_mem hu) (u * h * u⁻¹) hk
    have hEq : u⁻¹ * (u * h * u⁻¹) * u = h := by group
    simpa [hEq, inv_inv] using h1

/-- `K` is abelian (from Fact 1.5(iii) applied to `K₁`). -/
private lemma KU_comm (c : Hyp11 G) [Hyp11KData c] : IsMulCommutative (↥(KU c)) := by
  have hK1 : IsMulCommutative (↥(c.K1 : Subgroup G)) := by
    have h := fact_1_5_iii_inverted_subgroup_abelian_normal
      (X := c.U) (s := c.t1) c.t1_involution (U_coprime_two c)
      (by
        intro x hx
        exact S_normalizes_U c c.t1 c.t1_mem_S x hx)
      (K1_eq_invertedElements c)
    exact h.1
  rw [isMulCommutative_iff]
  intro a b
  apply Subtype.ext
  change (a : ↥c.U) * b = b * a
  apply Subtype.ext
  change ((a : ↥c.U) : G) * ((b : ↥c.U) : G) = ((b : ↥c.U) : G) * ((a : ↥c.U) : G)
  have ha : ((a : ↥c.U) : G) ∈ (c.K1 : Subgroup G) := by
    exact K_le_K1_local c (Subgroup.mem_subgroupOf.mp a.2)
  have hb : ((b : ↥c.U) : G) ∈ (c.K1 : Subgroup G) := by
    exact K_le_K1_local c (Subgroup.mem_subgroupOf.mp b.2)
  have hc := (isMulCommutative_iff.mp hK1)
      ⟨((a : ↥c.U) : G), ha⟩ ⟨((b : ↥c.U) : G), hb⟩
  exact congrArg Subtype.val hc

/-- In an abelian group every irreducible character is linear. -/
private lemma irr_linear_of_comm {K : Type u} [Group K] [Fintype K]
    (hcomm : IsMulCommutative K) (β : IrrBG19 K) : IsLinearCharacter β.1 := by
  let : CommGroup K := { (inferInstance : Group K) with
    mul_comm := by
      intro a b
      exact (isMulCommutative_iff.mp hcomm) a b }
  constructor
  · exact β.2
  · rcases β.2 with ⟨n, ρ, hρ, hEq⟩
    rw [hEq]
    have hfin : Module.finrank ℂ (Fin n → ℂ) = 1 :=
      Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative (ρ := ρ)
    have hfinN : Module.finrank ℂ (Fin n → ℂ) = n := by
      simp
    have hn : n = 1 := hfinN.symm.trans hfin
    subst n
    simpa [Representation.character] using (LinearMap.trace_one ℂ (Fin 1 → ℂ))

/-- The inverse (complex-conjugate) of a linear character of an abelian group. -/
@[reducible] private noncomputable def irrInv {K : Type u} [Group K] [Fintype K]
    (hcomm : IsMulCommutative K) (β : IrrBG19 K) : IrrBG19 K :=
  letI : CommGroup K := { (inferInstance : Group K) with
    mul_comm := by
      intro a b
      exact (isMulCommutative_iff.mp hcomm) a b }
  let hlin : IsLinearCharacter β.1 := irr_linear_of_comm hcomm β
  let φ : K →* ℂˣ := linearCharHom hlin
  ⟨fun k => (((φ.comp invMonoidHom) k : ℂˣ) : ℂ),
    (isLinearCharacter_of_hom (φ.comp invMonoidHom)).1⟩

/-- `irrInv` is pointwise inversion. -/
private lemma irrInv_apply {K : Type u} [Group K] [Fintype K]
    (hcomm : IsMulCommutative K) (β : IrrBG19 K) (k : K) : (irrInv hcomm β).1 k = β.1 k⁻¹ := by
  rfl

/-- Inversion does not change the multiplicity of a constituent in a character
fixed by inversion. -/
private lemma scalarProduct_restrict_irrInv_eq {K : Type u} [Group K] [Fintype K]
    (hcomm : IsMulCommutative K) (α : ClassFunction K) (β : IrrBG19 K)
    (hfix : ∀ k : K, α k = α k⁻¹) :
    scalarProduct K α (irrInv hcomm β).1 = scalarProduct K α β.1 := by
  unfold scalarProduct irrInv
  congr 1
  refine Finset.sum_bij (fun k _ => k⁻¹) ?_ ?_ ?_ ?_
  · intro k hk
    simp
  · intro a ha b hb hab
    simpa using (inv_injective hab)
  · intro k hk
    refine ⟨k⁻¹, by simp, ?_⟩
    simp
  · intro k hk
    change α k * star ((irrInv hcomm β).1 k) = α k⁻¹ * star (β.1 k⁻¹)
    rw [irrInv_apply hcomm]
    rw [hfix k]

/-- A reflection in `S \ S0` that fixes `α` makes `α` inversion-invariant on `K`. -/
private lemma restrict_alpha_inv_eq (c : Hyp11 G) [Hyp11KData c] {x : G}
    (hxS : x ∈ (c.S : Subgroup G)) (hxnot : x ∉ (c.S0 : Subgroup G))
    (α : Irr (↥c.U))
    (hfix : conjIrrS c hxS α = α) :
    ∀ k : ↥(KU c), α.1 (k : ↥c.U) = α.1 ((k⁻¹ : ↥(KU c)) : ↥c.U) := by
  intro k
  have hkG : ((k : ↥c.U) : G) ∈ c.K := by
    exact Subgroup.mem_subgroupOf.mp k.2
  have hinv : x * ((k : ↥c.U) : G) * x⁻¹ = ((k : ↥c.U) : G)⁻¹ :=
    reflection_inverts_K c hxS hxnot hkG
  have hval : α.1 ⟨x * ((k : ↥c.U) : G) * x⁻¹,
      S_normalizes_U c x hxS ((k : ↥c.U) : G) (K_le_U c hkG)⟩ = α.1 (k : ↥c.U) := by
    have hc := congrFun (congrArg Subtype.val hfix) (k : ↥c.U)
    exact hc
  rw [← hval]
  apply congrArg α.1
  apply Subtype.ext
  exact hinv

/-- Conjugation action of `U` on `K`. -/
@[reducible] private noncomputable instance KU_action (c : Hyp11 G) [Hyp11KData c] :
    MulDistribMulAction (↥c.U) (↥(KU c)) :=
  letI : (KU c).Normal := KU_normal c
  MulDistribMulAction.compHom (↥(KU c)) (MulAut.conjNormal (G := ↥c.U) (H := KU c))

/-- Conjugation action of `U` on the irreducible characters of `K`. -/
@[reducible] private noncomputable instance KU_irr_action (c : Hyp11 G) [Hyp11KData c] :
    MulAction (↥c.U) (IrrBG19 (↥(KU c))) where
  smul s β := ⟨fun u => β.1 (s⁻¹ • u),
    isIrreducibleCharacter_congr
      (MulDistribMulAction.toMulEquiv (M := ↥(KU c)) (G := ↥c.U) s⁻¹) β.2⟩
  one_smul β := by
    ext u
    change β.1 ((1 : ↥c.U)⁻¹ • u) = β.1 u
    simp
  mul_smul s t β := by
    ext u
    change β.1 (((s * t)⁻¹ : ↥c.U) • u) = β.1 (t⁻¹ • (s⁻¹ • u))
    rw [mul_inv_rev, mul_smul]

/-- The `U`-orbit of a character of `K` has odd cardinality. -/
private lemma KU_orbit_odd (c : Hyp11 G) [Hyp11KData c] (β : IrrBG19 (↥(KU c))) :
    Odd (Nat.card (MulAction.orbit (↥c.U) β)) := by
  let : MulDistribMulAction (↥c.U) (↥(KU c)) := KU_action c
  let : MulAction (↥c.U) (IrrBG19 (↥(KU c))) := KU_irr_action c
  have hcop : Nat.Coprime 2 (Nat.card (↥c.U)) := U_coprime_two c
  have hdiv : Nat.card (MulAction.orbit (↥c.U) β) ∣ Nat.card (↥c.U) := by
    have hst : Fintype (MulAction.orbit (↥c.U) β) := by infer_instance
    have hstab : Fintype (MulAction.stabilizer (↥c.U) β) := by infer_instance
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥c.U) (X := IrrBG19 (↥(KU c))) β
    exact ⟨Nat.card (MulAction.stabilizer (↥c.U) β), by simpa [Nat.card_eq_fintype_card] using h.symm⟩
  have hcopOrbit : Nat.Coprime 2 (Nat.card (MulAction.orbit (↥c.U) β)) :=
    hcop.coprime_dvd_right hdiv
  exact Nat.coprime_two_left.mp hcopOrbit

/-- The character of an arbitrary finite-dimensional complex representation is
a `Theory.Character.IsCharacter`. -/
private lemma isCharacter_of_representation {K : Type u} [Group K] [Fintype K]
    {M : Type v} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (σ : Representation ℂ K M) : IsCharacter σ.character := by
  let b : Module.Basis (Fin (Module.finrank ℂ M)) ℂ M := Module.finBasis ℂ M
  let e : M ≃ₗ[ℂ] (Fin (Module.finrank ℂ M) → ℂ) := b.equivFun
  let τ : Representation ℂ K (Fin (Module.finrank ℂ M) → ℂ) := {
    toFun := fun k => e.conj (σ k)
    map_one' := by
      ext x
      simp [LinearEquiv.conj_apply]
    map_mul' := by
      intro g h
      ext x
      simp [LinearEquiv.conj_apply, map_mul]
  }
  refine ⟨Module.finrank ℂ M, τ, ?_⟩
  ext k
  change LinearMap.trace ℂ M (σ k) =
    LinearMap.trace ℂ (Fin (Module.finrank ℂ M) → ℂ) (τ k)
  rw [show τ k = e.conj (σ k) by rfl]
  simpa using (LinearMap.trace_conj' (R := ℂ) (M := M)
    (N := Fin (Module.finrank ℂ M) → ℂ) (σ k) e).symm

/-- An irreducible finite-dimensional complex representation of an abelian
group gives an `IrrBG19` character (always linear). -/
private noncomputable def charOfIrrRep {K : Type u} [CommGroup K] [Fintype K]
    {M : Type v} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (σ : Representation ℂ K M) (hσ : σ.IsIrreducible) : IrrBG19 K := by
  letI : Representation.IsIrreducible σ := hσ
  have hchar : IsCharacter σ.character := isCharacter_of_representation σ
  have hnorm : scalarProductInv K σ.character σ.character = 1 := by
    have hnon : Nonempty (σ.Equiv σ) := ⟨Representation.Equiv.refl σ⟩
    simpa [scalarProductInv, hnon] using (Representation.char_orthonormal (ρ := σ) (σ := σ))
  exact ⟨σ.character, isIrreducibleCharacter_of_norm_one_inv hchar hnorm⟩

/-- Clifford's theorem for `α|_K` at the character level: the restriction
character is the sum of the characters of the conjugate summands. -/
private lemma clifford_restrict_char_sum {H : Subgroup G} [H.Normal]
    (ρ : Representation ℂ G V) (hρ : ρ.IsIrreducible)
    (W : Subrepresentation (ρ.comp H.subtype)) (hW : W.toRepresentation.IsIrreducible) :
    ∃ (n : ℕ) (g : Fin n → G),
      DirectSum.IsInternal
        (fun i : Fin n => (Theory.Representation.conjugateSubrepresentation ρ H W (g i)).toSubmodule) ∧
      (∀ i : Fin n,
        (Theory.Representation.conjugateSubrepresentation ρ H W (g i)).toRepresentation.IsIrreducible) ∧
      (∀ i : Fin n,
        Nonempty
          ((Theory.Representation.conjugateSubrepresentation ρ H W (g i)).toRepresentation ≃ₗ
            Theory.Representation.conjugateRep W.toRepresentation (g i))) ∧
      ∀ k : H, ρ.character (k : G) =
        ∑ i : Fin n,
          ((Theory.Representation.conjugateSubrepresentation ρ H W (g i)).toRepresentation).character k := by
  classical
  rcases Theory.Representation.isaacs_theorem_6_5 ρ H hρ W hW with ⟨n, g, hsum, hirr, hequiv, heq⟩
  let _ := @heq (Fin 0 → ℂ) (by infer_instance) (by infer_instance)
  have hsum' : DirectSum.IsInternal
      (fun i : Fin n => (Theory.Representation.conjugateSubrepresentation ρ H W (g i)).toSubmodule) := by
    change DirectSum.IsInternal
      (fun i : Fin n => (Theory.Representation.conjugateSubrepresentation ρ H W (g i)).asSubmodule) at hsum
    exact hsum
  refine ⟨n, g, hsum', hirr, hequiv, ?_⟩
  intro k
  let N : Fin n → Submodule ℂ V := fun i =>
    (Theory.Representation.conjugateSubrepresentation ρ H W (g i)).toSubmodule
  have hf : ∀ i : Fin n, Set.MapsTo (ρ (k : G)) (N i) (N i) := by
    intro i x hx
    exact (Theory.Representation.conjugateSubrepresentation ρ H W (g i)).apply_mem_toSubmodule k hx
  have htr := LinearMap.trace_eq_sum_trace_restrict (R := ℂ) (M := V) (N := N) hsum' (f := ρ (k : G)) hf
  change LinearMap.trace ℂ V (ρ (k : G)) =
    ∑ i : Fin n, LinearMap.trace ℂ (N i) ((ρ (k : G)).restrict (hf i))
  rw [htr]

/-- Clifford transitivity at character level: all irreducible constituents of
`α|_K` lie in the same `U`-orbit. -/
private lemma constituents_conjugate (c : Hyp11 G) [Hyp11KData c] (α : Irr (↥c.U))
    (β : IrrBG19 (↥(KU c)))
    (hβ : scalarProduct (↥(KU c)) (fun k : ↥(KU c) => α.1 (k : ↥c.U)) β.1 ≠ 0) :
    ∀ γ : IrrBG19 (↥(KU c)),
      scalarProduct (↥(KU c)) (fun k : ↥(KU c) => α.1 (k : ↥c.U)) γ.1 ≠ 0 →
        γ ∈ MulAction.orbit (↥c.U) β := by
  classical
  rcases α.2 with ⟨n, ρ, hρ, hαeq⟩
  have : (KU c).Normal := KU_normal c
  have : Nontrivial (Fin n → ℂ) :=
    Subrepresentation.irreducible_module_nontrivial (ρ := ρ)
  rcases Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
      (ρ := ρ.comp (KU c).subtype) with ⟨W, hW⟩
  rcases clifford_restrict_char_sum (G := ↥c.U) (H := KU c) (ρ := ρ) hρ W hW with
    ⟨n0, g, hsum, hirr, hequiv, hchar⟩
  let : CommGroup (↥(KU c)) := { (inferInstance : Group (↥(KU c))) with
    mul_comm := by
      intro a b
      exact (isMulCommutative_iff.mp (KU_comm c)) a b }
  let β0 : IrrBG19 (↥(KU c)) := charOfIrrRep W.toRepresentation hW
  let : MulDistribMulAction (↥c.U) (↥(KU c)) := KU_action c
  let : MulAction (↥c.U) (IrrBG19 (↥(KU c))) := KU_irr_action c
  have hchar' : ∀ k : ↥(KU c), α.1 (k : ↥c.U) =
      ∑ i : Fin n0,
        ((Theory.Representation.conjugateSubrepresentation ρ (KU c) W (g i)).toRepresentation).character k := by
    intro k
    rw [hαeq]
    exact hchar k
  have hfun : (fun k : ↥(KU c) => α.1 (k : ↥c.U)) =
      ∑ i : Fin n0,
        ((Theory.Representation.conjugateSubrepresentation ρ (KU c) W (g i)).toRepresentation).character := by
    funext k
    simpa using hchar' k
  have hsummand_orbit (i : Fin n0) :
      charOfIrrRep
        ((Theory.Representation.conjugateSubrepresentation ρ (KU c) W (g i)).toRepresentation) (hirr i) ∈
        MulAction.orbit (↥c.U) β0 := by
    have hχi : charOfIrrRep
        ((Theory.Representation.conjugateSubrepresentation ρ (KU c) W (g i)).toRepresentation) (hirr i) =
        (((g i : ↥c.U)⁻¹) • β0) := by
      apply Subtype.ext
      ext k
      have he := Classical.choice (hequiv i)
      have heRep := Theory.Representation.RepEquiv.toRepresentationEquiv he
      have hchars := Representation.char_iso heRep
      have hchar_smul : (((g i : ↥c.U)⁻¹) • β0).1 =
          fun u : ↥(KU c) => β0.1 ((((g i : ↥c.U)⁻¹)⁻¹) • u) := rfl
      simp only [charOfIrrRep, hchar_smul, inv_inv, KU_action]
      rw [hchars]
      rfl
    rw [hχi]
    exact MulAction.mem_orbit β0 ((g i : ↥c.U)⁻¹)
  have all_mem (γ : IrrBG19 (↥(KU c)))
      (hγ : scalarProduct (↥(KU c)) (fun k : ↥(KU c) => α.1 (k : ↥c.U)) γ.1 ≠ 0) :
      γ ∈ MulAction.orbit (↥c.U) β0 := by
    have hsp_sum : scalarProduct (↥(KU c)) (fun k : ↥(KU c) => α.1 (k : ↥c.U)) γ.1 =
        ∑ i : Fin n0, scalarProduct (↥(KU c))
          ((Theory.Representation.conjugateSubrepresentation ρ (KU c) W (g i)).toRepresentation).character γ.1 := by
      rw [hfun, scalarProduct_sum_left]
    have hcoeff (i : Fin n0) :
        scalarProduct (↥(KU c))
          ((Theory.Representation.conjugateSubrepresentation ρ (KU c) W (g i)).toRepresentation).character γ.1 =
          if (charOfIrrRep
            ((Theory.Representation.conjugateSubrepresentation ρ (KU c) W (g i)).toRepresentation) (hirr i)).1 = γ.1
          then 1 else 0 := by
      have hχ : ((Theory.Representation.conjugateSubrepresentation ρ (KU c) W (g i)).toRepresentation).character =
          (charOfIrrRep
            ((Theory.Representation.conjugateSubrepresentation ρ (KU c) W (g i)).toRepresentation) (hirr i)).1 := rfl
      rw [hχ]
      exact scalarProduct_irr_ite
        (charOfIrrRep
          ((Theory.Representation.conjugateSubrepresentation ρ (KU c) W (g i)).toRepresentation) (hirr i)).2 γ.2
    have hex : ∃ i : Fin n0, (charOfIrrRep
        ((Theory.Representation.conjugateSubrepresentation ρ (KU c) W (g i)).toRepresentation) (hirr i)).1 = γ.1 := by
      by_contra hnone
      push_neg at hnone
      have hsp0 : scalarProduct (↥(KU c)) (fun k : ↥(KU c) => α.1 (k : ↥c.U)) γ.1 = 0 := by
        rw [hsp_sum]
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hne' : (charOfIrrRep
            ((Theory.Representation.conjugateSubrepresentation ρ (KU c) W (g i)).toRepresentation) (hirr i)).1 ≠ γ.1 := by
          intro h
          exact hnone i h
        rw [hcoeff i]
        exact if_neg hne'
      exact hγ hsp0
    rcases hex with ⟨i, hi⟩
    have hmem : charOfIrrRep
        ((Theory.Representation.conjugateSubrepresentation ρ (KU c) W (g i)).toRepresentation) (hirr i) ∈
        MulAction.orbit (↥c.U) β0 := hsummand_orbit i
    have hiSub : charOfIrrRep
        ((Theory.Representation.conjugateSubrepresentation ρ (KU c) W (g i)).toRepresentation) (hirr i) = γ :=
      Subtype.ext hi
    rwa [hiSub] at hmem
  intro γ hγ
  have hβorbit : β ∈ MulAction.orbit (↥c.U) β0 := all_mem β hβ
  have hγorbit : γ ∈ MulAction.orbit (↥c.U) β0 := all_mem γ hγ
  have hβ0orbit : β0 ∈ MulAction.orbit (↥c.U) β := MulAction.mem_orbit_symm.mp hβorbit
  have horbit : MulAction.orbit (↥c.U) β0 = MulAction.orbit (↥c.U) β := MulAction.orbit_eq_iff.2 hβ0orbit
  rwa [← horbit]

/-- Inversion is an involution on `IrrBG19` of an abelian group. -/
private lemma irrInv_inv {K : Type u} [Group K] [Fintype K]
    (hcomm : IsMulCommutative K) (β : IrrBG19 K) : irrInv hcomm (irrInv hcomm β) = β := by
  apply Subtype.ext
  ext k
  rw [irrInv_apply hcomm, irrInv_apply hcomm, inv_inv]

/-- If a reflection fixes `α` and inverts `K`, inversion preserves the
occurring `U`-orbit of any constituent of `α|_K`. -/
private lemma irrInv_orbit_mem (c : Hyp11 G) [Hyp11KData c] {x : G}
    (hxS : x ∈ (c.S : Subgroup G)) (hxnot : x ∉ (c.S0 : Subgroup G))
    (α : Irr (↥c.U)) (hfix : conjIrrS c hxS α = α) :
    letI : MulDistribMulAction (↥c.U) (↥(KU c)) := KU_action c
    letI : MulAction (↥c.U) (IrrBG19 (↥(KU c))) := KU_irr_action c
    ∀ (β : IrrBG19 (↥(KU c))),
      scalarProduct (↥(KU c)) (fun k : ↥(KU c) => α.1 (k : ↥c.U)) β.1 ≠ 0 →
    ∀ γ : IrrBG19 (↥(KU c)), γ ∈ MulAction.orbit (↥c.U) β → irrInv (KU_comm c) γ ∈ MulAction.orbit (↥c.U) β := by
  classical
  intro β hβ γ hγ
  have hβinv : scalarProduct (↥(KU c)) (fun k : ↥(KU c) => α.1 (k : ↥c.U)) (irrInv (KU_comm c) β).1 ≠ 0 := by
    rw [scalarProduct_restrict_irrInv_eq (KU_comm c) (fun k : ↥(KU c) => α.1 (k : ↥c.U)) β
      (restrict_alpha_inv_eq c hxS hxnot α hfix)]
    exact hβ
  have hβinvO : irrInv (KU_comm c) β ∈ MulAction.orbit (↥c.U) β :=
    constituents_conjugate c α β hβ (irrInv (KU_comm c) β) hβinv
  rcases (MulAction.mem_orbit_iff.mp hγ) with ⟨u, hu⟩
  have hcom : irrInv (KU_comm c) (u • β) = u • irrInv (KU_comm c) β := by
    apply Subtype.ext
    ext k
    rw [irrInv_apply (KU_comm c)]
    change (u • β).1 k⁻¹ = (irrInv (KU_comm c) β).1 (u⁻¹ • k)
    rw [irrInv_apply (KU_comm c)]
    change β.1 (u⁻¹ • k⁻¹) = β.1 ((u⁻¹ • k)⁻¹)
    rw [smul_inv' u⁻¹ k]
  rw [← hu, hcom]
  have hOrbEq : MulAction.orbit (↥c.U) (irrInv (KU_comm c) β) = MulAction.orbit (↥c.U) β :=
    MulAction.orbit_eq_iff.2 hβinvO
  rw [← hOrbEq]
  exact MulAction.mem_orbit (irrInv (KU_comm c) β) u

/-- The occurring `U`-orbit contains a self-inverse character. -/
private lemma exists_self_inverse_in_orbit (c : Hyp11 G) [Hyp11KData c] {x : G}
    (hxS : x ∈ (c.S : Subgroup G)) (hxnot : x ∉ (c.S0 : Subgroup G))
    (α : Irr (↥c.U)) (hfix : conjIrrS c hxS α = α) :
    letI : MulDistribMulAction (↥c.U) (↥(KU c)) := KU_action c
    letI : MulAction (↥c.U) (IrrBG19 (↥(KU c))) := KU_irr_action c
    ∀ (β : IrrBG19 (↥(KU c))),
      scalarProduct (↥(KU c)) (fun k : ↥(KU c) => α.1 (k : ↥c.U)) β.1 ≠ 0 →
    ∃ γ : IrrBG19 (↥(KU c)), γ ∈ MulAction.orbit (↥c.U) β ∧ irrInv (KU_comm c) γ = γ := by
  classical
  intro β hβ
  let O : Set (IrrBG19 (↥(KU c))) := MulAction.orbit (↥c.U) β
  let f : O ≃ O := {
    toFun := fun γ => ⟨irrInv (KU_comm c) γ.1, irrInv_orbit_mem c hxS hxnot α hfix β hβ γ.1 γ.2⟩
    invFun := fun γ => ⟨irrInv (KU_comm c) γ.1, irrInv_orbit_mem c hxS hxnot α hfix β hβ γ.1 γ.2⟩
    left_inv := by
      intro γ
      apply Subtype.ext
      exact irrInv_inv (KU_comm c) γ.1
    right_inv := by
      intro γ
      apply Subtype.ext
      exact irrInv_inv (KU_comm c) γ.1
  }
  have hf2 : f ^ 2 = 1 := by
    apply Equiv.ext
    intro γ
    apply Subtype.ext
    exact irrInv_inv (KU_comm c) γ.1
  have hodd : Odd (Fintype.card O) := by
    have h := KU_orbit_odd c β
    simpa [O] using h
  rcases exists_fixed_of_involution_odd_card f hf2 hodd with ⟨γ, hγfix⟩
  refine ⟨γ.1, γ.2, ?_⟩
  exact congrArg Subtype.val hγfix

/-! ## Kernel of an irreducible character -/

/-- A finite-order linear endomorphism whose trace equals the dimension is the
identity. -/
private theorem finite_order_eq_one_of_trace_eq_finrank
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {n : ℕ} (hn : n ≠ 0) (hpow : f ^ n = 1)
    (htrace : LinearMap.trace ℂ V f = (Module.finrank ℂ V : ℂ)) :
    f = 1 := by
  classical
  let m : f.Eigenvalues → ℝ :=
    fun μ => (Module.finrank ℂ (f.eigenspace (μ : ℂ)) : ℝ)
  have htrace_one :
      LinearMap.trace ℂ V f =
        ∑ μ : f.Eigenvalues, (μ : ℂ) * (m μ : ℂ) := by
    simpa [m] using
      (Theory.Representation.trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := 1) hn hpow)
  have htrace_zero :
      (Module.finrank ℂ V : ℂ) =
        ∑ μ : f.Eigenvalues, (m μ : ℂ) := by
    have h0 :=
      Theory.Representation.trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := 0) hn hpow
    simpa [m, LinearMap.trace_id] using h0
  have hsum_complex :
      ∑ μ : f.Eigenvalues, (μ : ℂ) * (m μ : ℂ) =
        ∑ μ : f.Eigenvalues, (1 : ℂ) * (m μ : ℂ) := by
    rw [← htrace_one, htrace, htrace_zero]
    simp
  have hsum_real :
      ∑ μ : f.Eigenvalues, (μ : ℂ).re * m μ =
        ∑ μ : f.Eigenvalues, (1 : ℝ) * m μ := by
    have h := congrArg Complex.re hsum_complex
    simpa [Complex.re_sum, Complex.re_mul_ofReal] using h
  have hle :
      ∀ μ ∈ (Finset.univ : Finset f.Eigenvalues),
        (μ : ℂ).re * m μ ≤ (1 : ℝ) * m μ := by
    intro μ hμ
    have hμpow : (μ : ℂ) ^ n = 1 :=
      Theory.Representation.eigenvalue_pow_eq_one_of_pow_eq_one hpow μ.property
    have hnorm : ‖(μ : ℂ)‖ = 1 := by
      have hpowAbs : ‖(μ : ℂ)‖ ^ n = (1 : ℝ) := by
        simpa [hμpow] using (norm_pow (μ : ℂ) n).symm
      have habs_pow : |(‖(μ : ℂ)‖ : ℝ) ^ n| = 1 := by
        rw [hpowAbs, abs_one]
      have habs : |(‖(μ : ℂ)‖ : ℝ)| = 1 :=
        (abs_pow_eq_one (‖(μ : ℂ)‖ : ℝ) hn).mp habs_pow
      simpa [abs_of_nonneg (norm_nonneg (μ : ℂ))] using habs
    have hre_le : (μ : ℂ).re ≤ 1 := by
      simpa [hnorm] using Complex.re_le_norm (μ : ℂ)
    exact mul_le_mul_of_nonneg_right hre_le (by positivity : 0 ≤ m μ)
  have heq_each :
      ∀ μ : f.Eigenvalues, (μ : ℂ).re * m μ = (1 : ℝ) * m μ := by
    intro μ
    exact (Finset.sum_eq_sum_iff_of_le hle).mp (by simpa using hsum_real) μ
      (Finset.mem_univ μ)
  have heigen_eq_one : ∀ μ : f.Eigenvalues, (μ : ℂ) = 1 := by
    intro μ
    have hpos_nat : 0 < Module.finrank ℂ (f.eigenspace (μ : ℂ)) := by
      have hμ : f.HasEigenvalue (μ : ℂ) :=
        Module.End.hasEigenvalue_of_hasGenEigenvalue μ.property
      rcases hμ.exists_hasEigenvector with ⟨v, hv⟩
      rw [Module.finrank_pos_iff_exists_ne_zero]
      refine ⟨⟨v, ?_⟩, ?_⟩
      · rw [Module.End.mem_eigenspace_iff]
        exact hv.apply_eq_smul
      · intro hzero
        have hvzero : v = 0 := by
          simpa using congrArg Subtype.val hzero
        exact hv.2 hvzero
    have hpos : 0 < m μ := by
      dsimp [m]
      exact_mod_cast hpos_nat
    have hre_eq : (μ : ℂ).re = 1 := by
      have h := heq_each μ
      nlinarith
    have hμpow : (μ : ℂ) ^ n = 1 :=
      Theory.Representation.eigenvalue_pow_eq_one_of_pow_eq_one hpow μ.property
    have hnorm : ‖(μ : ℂ)‖ = 1 := by
      have hpowAbs : ‖(μ : ℂ)‖ ^ n = (1 : ℝ) := by
        simpa [hμpow] using (norm_pow (μ : ℂ) n).symm
      have habs_pow : |(‖(μ : ℂ)‖ : ℝ) ^ n| = 1 := by
        rw [hpowAbs, abs_one]
      have habs : |(‖(μ : ℂ)‖ : ℝ)| = 1 :=
        (abs_pow_eq_one (‖(μ : ℂ)‖ : ℝ) hn).mp habs_pow
      simpa [abs_of_nonneg (norm_nonneg (μ : ℂ))] using habs
    have hnormSq : (μ : ℂ).re * (μ : ℂ).re + (μ : ℂ).im * (μ : ℂ).im = 1 := by
      have h := Complex.normSq_eq_norm_sq (μ : ℂ)
      rw [Complex.normSq_apply, hnorm] at h
      norm_num at h
      exact h
    have him_sq : (μ : ℂ).im * (μ : ℂ).im = 0 := by
      nlinarith
    have him : (μ : ℂ).im = 0 := mul_self_eq_zero.mp him_sq
    exact Complex.ext (by simp [hre_eq]) (by simp [him])
  have htop :
      f.eigenspace (1 : ℂ) = ⊤ := by
    have hsemi : f.IsSemisimple :=
      Theory.Representation.end_isSemisimple_of_pow_eq_one f hn hpow
    have hiSup :=
      Theory.Representation.eigenspace_iSup_eq_top_over_eigenvalues (f := f) hsemi
    apply top_unique
    rw [← hiSup]
    refine iSup_le ?_
    intro μ
    simp [heigen_eq_one μ]
  ext v
  have hv : v ∈ f.eigenspace (1 : ℂ) := by
    rw [htop]
    exact Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff] at hv
  simpa using hv

/-- Acting trivially at `g` is equivalent to the character keeping its degree
at `g`. -/
private lemma rep_apply_eq_one_iff_char_eq_degree {G : Type u} [Group G] [Fintype G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    ρ g = 1 ↔ ρ.character g = ρ.character 1 := by
  constructor
  · intro h
    simp [Representation.character, h]
  · intro h
    have hn : orderOf g ≠ 0 := Nat.ne_of_gt (orderOf_pos g)
    have hpow : (ρ g) ^ orderOf g = 1 := by
      rw [← MonoidHom.map_pow, pow_orderOf_eq_one, MonoidHom.map_one]
    have htrace : LinearMap.trace ℂ V (ρ g) = (Module.finrank ℂ V : ℂ) := by
      have h' := h.trans (Representation.char_one ρ)
      simpa [Representation.character] using h'
    exact finite_order_eq_one_of_trace_eq_finrank (ρ g) hn hpow htrace

/-- An element lies in the kernel of an irreducible character exactly when the
character keeps its degree there. -/
private lemma mem_charKernel_of_irr_iff {G : Type u} [Group G] [Fintype G]
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) (g : G) :
    g ∈ charKernel (isCharacter_of_isIrreducibleCharacter hχ) ↔ χ g = χ 1 := by
  classical
  have hdef : charKernel (isCharacter_of_isIrreducibleCharacter hχ) =
      (Classical.choose (Classical.choose_spec
        (isCharacter_of_isIrreducibleCharacter hχ))).ker := rfl
  have hρ : χ = (Classical.choose (Classical.choose_spec
        (isCharacter_of_isIrreducibleCharacter hχ))).character :=
    Classical.choose_spec (Classical.choose_spec (isCharacter_of_isIrreducibleCharacter hχ))
  rw [hdef]
  rw [MonoidHom.mem_ker]
  rw [rep_apply_eq_one_iff_char_eq_degree]
  rw [← hρ]

/-- A subgroup lies in the kernel of an irreducible character exactly when the
character keeps its degree on the subgroup. -/
private lemma le_charKernel_of_irr_iff {G : Type u} [Group G] [Fintype G]
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) (A : Subgroup G) :
    A ≤ charKernel (isCharacter_of_isIrreducibleCharacter hχ) ↔
      ∀ a : A, χ (a : G) = χ 1 := by
  constructor
  · intro hA a
    exact (mem_charKernel_of_irr_iff hχ (a : G)).1 (hA a.2)
  · intro hA a ha
    exact (mem_charKernel_of_irr_iff hχ a).2 (hA ⟨a, ha⟩)

/-- A self-inverse linear character of an odd-order finite group is trivial. -/
private lemma linearChar_self_inverse_eq_one {K : Type u} [Group K] [Fintype K]
    (hodd : Nat.Coprime 2 (Nat.card K)) {β : ClassFunction K}
    (hβ : IsLinearCharacter β) (hfix : ∀ k : K, β k = β k⁻¹) :
    ∀ k : K, β k = 1 := by
  intro k
  let φ : K →* ℂˣ := linearCharHom hβ
  have hβφ : ∀ x : K, ((φ x : ℂˣ) : ℂ) = β x := linearCharHom_apply hβ
  have hsq : ((φ k : ℂˣ) : ℂ) ^ 2 = 1 := by
    have h1 : β k * β k = 1 := by
      calc
        β k * β k = β k * β k⁻¹ := by rw [hfix k]
        _ = 1 := by
          rw [linearChar_inv hβ k]
          exact mul_inv_cancel₀ (linearChar_ne_zero hβ k)
    calc
      ((φ k : ℂˣ) : ℂ) ^ 2 = β k * β k := by rw [hβφ]; ring
      _ = 1 := h1
  have hsqUnits : (φ k) ^ 2 = 1 := Units.ext (by simpa using hsq)
  have hdvd2 : orderOf (φ k) ∣ 2 := orderOf_dvd_of_pow_eq_one hsqUnits
  have hpow : (φ k) ^ orderOf k = 1 := by
    calc
      (φ k) ^ orderOf k = φ (k ^ orderOf k) := by rw [map_pow]
      _ = φ 1 := by rw [pow_orderOf_eq_one]
      _ = 1 := map_one φ
  have hdvd : orderOf (φ k) ∣ orderOf k := orderOf_dvd_of_pow_eq_one hpow
  have hoddk : Nat.Coprime 2 (orderOf k) :=
    hodd.coprime_dvd_right (orderOf_dvd_natCard k)
  have hcop : Nat.Coprime (orderOf (φ k)) 2 :=
    Nat.Coprime.of_dvd_left hdvd (Nat.Coprime.symm hoddk)
  have hord1 : orderOf (φ k) = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd2
  have hφ1 : φ k = 1 := orderOf_eq_one_iff.mp hord1
  calc
    β k = ((φ k : ℂˣ) : ℂ) := (hβφ k).symm
    _ = 1 := congrArg (fun z : ℂˣ => (z : ℂ)) hφ1

/-- Restriction of an irreducible character of the odd group `U` to `K` has an
irreducible constituent of odd multiplicity (local version of Lemma 19's
`exists_odd_multiplicity_restrict`, stated directly on the restriction
function to avoid the opaque `restrictChar`). -/
private lemma exists_odd_multiplicity_restrict_char (c : Hyp11 G) [Hyp11KData c] (α : Irr (↥c.U)) :
    ∃ β : IrrBG19 (↥(KU c)), ∃ m : ℕ, Odd m ∧
      (m : ℂ) = scalarProduct (↥(KU c)) (fun k : ↥(KU c) => α.1 (k : ↥c.U)) β.1 := by
  classical
  let K0 : Subgroup (↥c.U) := KU c
  let φ : ClassFunction (↥K0) := fun k : ↥K0 => α.1 (k : ↥c.U)
  have hφchar : IsCharacter φ := by
    simpa [φ] using isCharacter_restrict K0 (isCharacter_of_isIrreducibleCharacter α.2)
  have hφgen : IsGeneralizedCharacter φ :=
    ⟨φ, 0, hφchar, isCharacter_zero, by ext x; simp⟩
  have hK0odd : Nat.Coprime 2 (Nat.card (↥K0)) := by
    have hdiv : Nat.card (↥K0) ∣ Nat.card (↥c.U) := K0.card_subgroup_dvd_card
    exact (U_coprime_two c).coprime_dvd_right hdiv
  have hcoeff (ν : IrrBG19 (↥K0)) : ∃ m : ℕ,
      (m : ℂ) = scalarProduct (↥K0) φ ν.1 := by
    rcases scalarProduct_irr_char_nat (χ := ν.1) (ψ := φ) ν.2 hφchar with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    calc
      (r : ℂ) = scalarProduct (↥K0) ν.1 φ := hr
      _ = star (scalarProduct (↥K0) ν.1 φ) := by
            rw [hr.symm]
            simp
      _ = scalarProduct (↥K0) φ ν.1 := scalarProduct_conj ν.1 φ
  let m : IrrBG19 (↥K0) → ℕ := fun ν => Classical.choose (hcoeff ν)
  have hm (ν : IrrBG19 (↥K0)) : (m ν : ℂ) = scalarProduct (↥K0) φ ν.1 :=
    Classical.choose_spec (hcoeff ν)
  have hdeg (ν : IrrBG19 (↥K0)) : ∃ d : ℕ, Odd d ∧ (d : ℂ) = ν.1 1 :=
    irr_degree_odd hK0odd ν
  let d : IrrBG19 (↥K0) → ℕ := fun ν => Classical.choose (hdeg ν)
  have hd (ν : IrrBG19 (↥K0)) : Odd (d ν) ∧ (d ν : ℂ) = ν.1 1 :=
    Classical.choose_spec (hdeg ν)
  rcases irr_degree_odd (U_coprime_two c) α with ⟨a, haOdd, ha⟩
  have hsum1 : φ 1 = ∑ ν : IrrBG19 (↥K0), (m ν : ℂ) * (d ν : ℂ) := by
    have h := classFunction_eq_sum_irr_coeffs (G := ↥K0) hφgen (1 : ↥K0)
    rw [h]
    refine Finset.sum_congr rfl ?_
    intro ν hν
    rw [hm ν, (hd ν).2]
  have hsum1' : (a : ℂ) = ∑ ν : IrrBG19 (↥K0), (m ν : ℂ) * (d ν : ℂ) := by
    calc
      (a : ℂ) = α.1 1 := ha
      _ = φ 1 := rfl
      _ = ∑ ν : IrrBG19 (↥K0), (m ν : ℂ) * (d ν : ℂ) := hsum1
  by_contra hnone
  push_neg at hnone
  have hEvenProd : ∀ ν : IrrBG19 (↥K0), Even (m ν * d ν) := by
    intro ν
    have hEvenM : Even (m ν) := by
      by_contra hOdd
      exact (hnone ν (m ν) (Nat.not_even_iff_odd.mp hOdd)) (hm ν)
    exact Even.mul_right hEvenM (d ν)
  have hEvenSum : Even (∑ ν : IrrBG19 (↥K0), m ν * d ν) := by
    exact Finset.even_sum (fun ν : IrrBG19 (↥K0) => m ν * d ν) (by intro ν hν; exact hEvenProd ν)
  have hsumNat : (∑ ν : IrrBG19 (↥K0), (m ν : ℂ) * (d ν : ℂ)) =
      ((∑ ν : IrrBG19 (↥K0), m ν * d ν : ℕ) : ℂ) := by
    norm_num
  have hNatEq : a = ∑ ν : IrrBG19 (↥K0), m ν * d ν := by
    exact_mod_cast (hsum1'.trans hsumNat)
  have hEvenA : Even a := by
    rw [hNatEq]
    exact hEvenSum
  exact (Nat.not_even_iff_odd.mpr haOdd) hEvenA

/-- If a reflection of `S \ S0` fixes `α ∈ Irr(U)`, then `K` lies in the kernel
of `α` (the kernel of any representation affording `α`). -/
private lemma fixed_reflection_ker_core (c : Hyp11 G) [Hyp11KData c] {x : G}
    (hxS : x ∈ (c.S : Subgroup G)) (hxnot : x ∉ (c.S0 : Subgroup G))
    (α : Irr (↥c.U)) (hfix : conjIrrS c hxS α = α) :
    c.K ≤ (charKernel (isCharacter_of_isIrreducibleCharacter α.2)).map
      (Subgroup.subtype c.U) := by
  classical
  let K0 : Subgroup (↥c.U) := KU c
  have hK0odd : Nat.Coprime 2 (Nat.card (↥K0)) := by
    have hdiv : Nat.card (↥K0) ∣ Nat.card (↥c.U) := K0.card_subgroup_dvd_card
    exact (U_coprime_two c).coprime_dvd_right hdiv
  have hK0comm : IsMulCommutative (↥K0) := KU_comm c
  let φ : ClassFunction (↥K0) := fun k : ↥K0 => α.1 (k : ↥c.U)
  have hφchar : IsCharacter φ := by
    simpa [φ] using isCharacter_restrict K0 (isCharacter_of_isIrreducibleCharacter α.2)
  rcases exists_odd_multiplicity_restrict_char c α with ⟨β0, m, hmOdd, hm⟩
  have hmne : m ≠ 0 := by
    rcases hmOdd with ⟨k, rfl⟩
    omega
  have hβ0 : scalarProduct (↥K0) φ β0.1 ≠ 0 := by
    intro h0
    have hm0 : (m : ℂ) = 0 := by
      rw [hm]
      exact h0
    exact hmne (by exact_mod_cast hm0)
  let : MulDistribMulAction (↥c.U) (↥K0) := KU_action c
  let : MulAction (↥c.U) (IrrBG19 (↥K0)) := KU_irr_action c
  rcases exists_self_inverse_in_orbit c hxS hxnot α hfix β0 hβ0 with ⟨γ, hγO, hγinv⟩
  have hγlin : IsLinearCharacter γ.1 := irr_linear_of_comm hK0comm γ
  have hγfixval : ∀ k : ↥K0, γ.1 k = γ.1 k⁻¹ := by
    intro k
    have h' := congrFun (congrArg Subtype.val hγinv) k
    rw [irrInv_apply hK0comm] at h'
    exact h'.symm
  have hγtriv : ∀ k : ↥K0, γ.1 k = 1 :=
    linearChar_self_inverse_eq_one hK0odd hγlin hγfixval
  have hδtriv (δ : IrrBG19 (↥K0))
      (hδ : scalarProduct (↥K0) φ δ.1 ≠ 0) : δ.1 = (1 : ClassFunction (↥K0)) := by
    have hδO : δ ∈ MulAction.orbit (↥c.U) β0 :=
      constituents_conjugate c α β0 hβ0 δ hδ
    have hOrbEq : MulAction.orbit (↥c.U) β0 = MulAction.orbit (↥c.U) γ :=
      MulAction.orbit_eq_iff.2 (MulAction.mem_orbit_symm.mp hγO)
    have hδγ : δ ∈ MulAction.orbit (↥c.U) γ := by
      rwa [hOrbEq] at hδO
    rcases (MulAction.mem_orbit_iff.mp hδγ) with ⟨u, rfl⟩
    ext k
    change γ.1 (u⁻¹ • k) = 1
    exact hγtriv (u⁻¹ • k)
  have hφgen : IsGeneralizedCharacter φ :=
    ⟨φ, 0, hφchar, isCharacter_zero, by ext x; simp⟩
  have hsum (k : ↥K0) : φ k = ∑ δ : IrrBG19 (↥K0),
      scalarProduct (↥K0) φ δ.1 * δ.1 k := by
    simpa using (classFunction_eq_sum_irr_coeffs (G := ↥K0) (φ := φ) hφgen k)
  have hconst : ∀ k : ↥K0, φ k = φ (1 : ↥K0) := by
    intro k
    rw [hsum k, hsum 1]
    refine Finset.sum_congr rfl ?_
    intro δ hδ
    by_cases hc : scalarProduct (↥K0) φ δ.1 = 0
    · simp [hc]
    · rw [hδtriv δ hc]
      simp
  intro k hk
  rw [Subgroup.mem_map]
  refine ⟨⟨k, K_le_U c hk⟩, ?_, rfl⟩
  rw [mem_charKernel_of_irr_iff α.2 ⟨k, K_le_U c hk⟩]
  have hkK0 : (⟨k, K_le_U c hk⟩ : ↥c.U) ∈ K0 := by
    change (⟨k, K_le_U c hk⟩ : ↥c.U) ∈ (c.K : Subgroup G).subgroupOf c.U
    rw [Subgroup.mem_subgroupOf]
    simpa using hk
  have hc := hconst ⟨⟨k, K_le_U c hk⟩, hkK0⟩
  simpa [φ] using hc

/-- Evaluating the restriction at `1` gives the degree. -/
private lemma restrictU_one_local (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (ν : ClassFunction (↥c.H0)) :
    restrictU c h12 ν (1 : ↥c.U) = ν (1 : ↥c.H0) := by
  change ν ⟨(1 : G), (h12.U_normal_in_H0).1 (1 : ↥c.U).2⟩ = ν (1 : ↥c.H0)
  congr 1

/-- If `K ≤ ker α`, every `S0`-conjugate of `α` takes the value `α(1)` on
`K`. -/
private lemma s0Orbit_mem_charKernel_value (c : Hyp11 G) [Hyp11KData c] (α : Irr (↥c.U))
    (hKle : c.K ≤ (charKernel (isCharacter_of_isIrreducibleCharacter α.2)).map
      (Subgroup.subtype c.U))
    {k : G} (hk : k ∈ c.K) :
    ∀ α' : Irr (↥c.U), α' ∈ s0Orbit c α →
      α'.1 ⟨k, K_le_U c hk⟩ = α'.1 (1 : ↥c.U) := by
  classical
  intro α' hα'
  rcases (Finset.mem_image.mp hα') with ⟨g, hg, hEq⟩
  have hkU : k ∈ (c.U : Subgroup G) := K_le_U c hk
  have hmem : ⟨k, hkU⟩ ∈ charKernel (isCharacter_of_isIrreducibleCharacter α.2) := by
    rcases (Subgroup.mem_map.mp (hKle hk)) with ⟨u, hu, hEqU⟩
    have hu' : u = ⟨k, hkU⟩ := by
      apply Subtype.ext
      exact hEqU
    rwa [hu'] at hu
  have hval : α.1 ⟨k, hkU⟩ = α.1 (1 : ↥c.U) :=
    (mem_charKernel_of_irr_iff α.2 ⟨k, hkU⟩).1 hmem
  have hgcen : (g : G) * k * (g : G)⁻¹ = k := by
    have hkg : (g : G) * k = k * (g : G) :=
      (Subgroup.mem_centralizer_iff.mp (S0_centralizes_K c hk)) (g : G) g.2
    calc
      (g : G) * k * (g : G)⁻¹ = k * (g : G) * (g : G)⁻¹ := by rw [hkg]
      _ = k := by group
  have hval' : (conjIrrS c (c.S0_le_S g.2) α).1 ⟨k, hkU⟩ = α.1 (1 : ↥c.U) := by
    change α.1 ⟨(g : G) * (k : G) * (g : G)⁻¹,
      S_normalizes_U c (g : G) (c.S0_le_S g.2) (k : G) hkU⟩ = α.1 (1 : ↥c.U)
    have hsub : (⟨(g : G) * (k : G) * (g : G)⁻¹,
        S_normalizes_U c (g : G) (c.S0_le_S g.2) (k : G) hkU⟩ : ↥c.U) = ⟨k, hkU⟩ := by
      apply Subtype.ext
      exact hgcen
    rw [hsub]
    exact hval
  have hone' : (conjIrrS c (c.S0_le_S g.2) α).1 (1 : ↥c.U) = α.1 (1 : ↥c.U) := by
    change α.1 ⟨(g : G) * (1 : G) * (g : G)⁻¹,
      S_normalizes_U c (g : G) (c.S0_le_S g.2) (1 : G) c.U.one_mem⟩ = α.1 (1 : ↥c.U)
    have hsub : (⟨(g : G) * (1 : G) * (g : G)⁻¹,
        S_normalizes_U c (g : G) (c.S0_le_S g.2) (1 : G) c.U.one_mem⟩ : ↥c.U) = (1 : ↥c.U) := by
      apply Subtype.ext
      simp
    rw [hsub]
  rw [← hEq, hval', hone']

/-- If `K ≤ ker α`, then `K ≤ ker μ` for every `μ` in the `Λ`-orbit of `α`
(the orbit members restrict to the same `S0`-sum on `U`). -/
private lemma orbit_mem_kernel_le_of_orbitOfAlpha (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (α : Irr (↥c.U)) (μ : Irr (↥c.H0))
    (hOrbit : orbit c.H0 c.U μ.1 = orbitOfAlpha c h12 hSC α)
    (hKle : c.K ≤ (charKernel (isCharacter_of_isIrreducibleCharacter α.2)).map
      (Subgroup.subtype c.U)) :
    c.K ≤ (charKernel (isCharacter_of_isIrreducibleCharacter μ.2)).map
      (Subgroup.subtype c.H0) := by
  classical
  have hres : restrictU c h12 μ.1 = ∑ α' ∈ s0Orbit c α, α'.1 := by
    exact (orbitOfAlpha_spec c h12 hSC α).2 μ.1 (by
      have hself : μ.1 ∈ orbit c.H0 c.U μ.1 := orbit_self_mem c.H0 c.U μ.1
      rwa [← hOrbit])
  intro k hk
  rw [Subgroup.mem_map]
  refine ⟨⟨k, (U_le_H0 c) (K_le_U c hk)⟩, ?_, rfl⟩
  rw [mem_charKernel_of_irr_iff μ.2 ⟨k, (U_le_H0 c) (K_le_U c hk)⟩]
  have hkU : k ∈ (c.U : Subgroup G) := K_le_U c hk
  have hres_k := congrFun hres ⟨k, hkU⟩
  have hres_1 := congrFun hres (1 : ↥c.U)
  have hsum_k : (∑ α' ∈ s0Orbit c α, α'.1) ⟨k, hkU⟩ =
      (∑ α' ∈ s0Orbit c α, α'.1 (1 : ↥c.U)) := by
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro α' hα'
    exact s0Orbit_mem_charKernel_value c α hKle hk α' hα'
  have hμk : μ.1 ⟨k, (U_le_H0 c) (K_le_U c hk)⟩ = μ.1 (1 : ↥c.H0) := by
    calc
      μ.1 ⟨k, (U_le_H0 c) (K_le_U c hk)⟩ = restrictU c h12 μ.1 ⟨k, hkU⟩ := by
        change μ.1 ⟨(k : G), (h12.U_normal_in_H0).1 hkU⟩ = μ.1 ⟨k, (U_le_H0 c) (K_le_U c hk)⟩
        congr 1
      _ = (∑ α' ∈ s0Orbit c α, α'.1) ⟨k, hkU⟩ := hres_k
      _ = (∑ α' ∈ s0Orbit c α, α'.1 (1 : ↥c.U)) := hsum_k
      _ = (∑ α' ∈ s0Orbit c α, α'.1) (1 : ↥c.U) := by simp
      _ = restrictU c h12 μ.1 (1 : ↥c.U) := hres_1.symm
      _ = μ.1 (1 : ↥c.H0) := restrictU_one_local c h12 μ.1
  exact hμk

/-! ## Local orbit-conjugation facts (`s`-conjugation maps `Λ`-orbits) -/

/-- `s·(s·x·s⁻¹)·s⁻¹ = x` for the involution `s`. -/
private lemma s_conj_sq_local (c : Hyp11 G) [Hyp11KData c] (x : G) :
    c.s * (c.s * x * c.s⁻¹) * c.s⁻¹ = x := by
  have hs2 : c.s * c.s = 1 := by simpa [pow_two] using c.s_involution.2
  calc
    c.s * (c.s * x * c.s⁻¹) * c.s⁻¹ = (c.s * c.s) * x * (c.s⁻¹ * c.s⁻¹) := by group
    _ = x := by
      have hs2' : c.s⁻¹ * c.s⁻¹ = 1 := by
        rw [← mul_inv_rev]
        rw [hs2]
        simp
      rw [hs2, hs2']
      simp

/-- Conjugation by `s` is an involution on `H0`. -/
private lemma conjMonoidHom_conjMonoidHom_local (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (x : ↥c.H0) :
    (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12)
      (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) x) : ↥c.H0) = x := by
  apply Subtype.ext
  exact s_conj_sq_local c (x : G)

/-- `s` is an involution, so conjugation by `s` is an involution on class
functions: `(ν^s)^s = ν`. -/
private lemma conjChar_conjChar_local (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (ν : ClassFunction (↥c.H0)) :
    conjChar c.H0 (s_normalizes_H0 c h12)
      (conjChar c.H0 (s_normalizes_H0 c h12) ν) = ν := by
  classical
  ext x
  simp [conjChar]
  rw [conjMonoidHom_conjMonoidHom_local c h12 x]

/-- The `s`-conjugate of a `Λ`-character is again a `Λ`-character
(`s` normalizes `U`). -/
private noncomputable def conjLambda_local (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (l : LambdaHom c.H0 c.U) : LambdaHom c.H0 c.U := by
  classical
  refine ⟨l.1.comp (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12)), ?_⟩
  intro u hu
  change l.1 (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) u) = 1
  exact l.2 (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) u) (by
    change c.s * (u : G) * c.s⁻¹ ∈ c.U
    exact s_normalizes_U c hu)

/-- Conjugation by `s` maps the orbit of `ν^s` into the orbit of `ν`. -/
private lemma orbit_conjChar_subset_local (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {ν : ClassFunction (↥c.H0)}
    (μ : ClassFunction (↥c.H0))
    (hμ : μ ∈ orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν)) :
    conjChar c.H0 (s_normalizes_H0 c h12) μ ∈ orbit c.H0 c.U ν := by
  classical
  rcases (Finset.mem_image.mp hμ) with ⟨l, hl, rfl⟩
  refine Finset.mem_image.mpr ⟨conjLambda_local c h12 l, Finset.mem_univ _, ?_⟩
  ext x
  change (LambdaChar (conjLambda_local c h12 l).1 * ν) x =
    (conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l.1 *
      conjChar c.H0 (s_normalizes_H0 c h12) ν)) x
  simp [conjChar, conjLambda_local, LambdaChar]
  have hx : (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) x : ↥c.H0) =
      ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩ := rfl
  rw [hx]
  have hx' : (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12)
      ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩ : ↥c.H0) = x := by
    apply Subtype.ext
    exact s_conj_sq_local c (x : G)
  rw [hx']

/-- Conjugation by `s` maps the orbit of `ν` into the orbit of `ν^s`. -/
private lemma orbit_subset_conjChar_local (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {ν : ClassFunction (↥c.H0)}
    (μ : ClassFunction (↥c.H0))
    (hμ : μ ∈ orbit c.H0 c.U ν) :
    conjChar c.H0 (s_normalizes_H0 c h12) μ ∈
      orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν) := by
  classical
  rcases (Finset.mem_image.mp hμ) with ⟨l, hl, rfl⟩
  refine Finset.mem_image.mpr ⟨conjLambda_local c h12 l, Finset.mem_univ _, ?_⟩
  ext x
  change (LambdaChar (conjLambda_local c h12 l).1 * conjChar c.H0 (s_normalizes_H0 c h12) ν) x =
    (conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l.1 * ν)) x
  simp [conjChar, conjLambda_local, LambdaChar]

/-- Conjugation by `s` maps orbits to orbits. -/
private lemma orbit_conjChar_eq_local (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (ν : ClassFunction (↥c.H0)) :
    orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν) =
      (orbit c.H0 c.U ν).image (fun μ =>
        conjChar c.H0 (s_normalizes_H0 c h12) μ) := by
  classical
  apply Finset.ext
  intro μ
  constructor
  · intro hμ
    refine Finset.mem_image.mpr
      ⟨conjChar c.H0 (s_normalizes_H0 c h12) μ,
        orbit_conjChar_subset_local c h12 μ hμ, conjChar_conjChar_local c h12 μ⟩
  · intro hμ
    rcases (Finset.mem_image.mp hμ) with ⟨a, ha, rfl⟩
    exact orbit_subset_conjChar_local c h12 a ha

/-- If `ν^s ∈ orbit ν`, the whole orbit is `s`-invariant. -/
private lemma orbit_sInvariant_of_mem (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {ν : ClassFunction (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν ∈ orbit c.H0 c.U ν) :
    ∀ ξ ∈ orbit c.H0 c.U ν,
      conjChar c.H0 (s_normalizes_H0 c h12) ξ ∈ orbit c.H0 c.U ν := by
  classical
  have hOrbEq : orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν) =
      orbit c.H0 c.U ν := orbit_eq_of_mem' c hνs
  have hImage : orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν) =
      (orbit c.H0 c.U ν).image (fun μ =>
        conjChar c.H0 (s_normalizes_H0 c h12) μ) :=
    orbit_conjChar_eq_local c h12 ν
  have hEq : (orbit c.H0 c.U ν).image (fun μ =>
        conjChar c.H0 (s_normalizes_H0 c h12) μ) = orbit c.H0 c.U ν := by
    rw [← hImage, hOrbEq]
  intro ξ hξ
  have hξ' : conjChar c.H0 (s_normalizes_H0 c h12) ξ ∈
      (orbit c.H0 c.U ν).image (fun μ =>
        conjChar c.H0 (s_normalizes_H0 c h12) μ) :=
    Finset.mem_image.mpr ⟨ξ, hξ, rfl⟩
  rwa [hEq] at hξ'

/-- Members of a `Λ`-orbit avoiding `B(χ)` have equal multiplicity in
`χ|_{H0}`. -/
private lemma orbit_mem_scalarProduct_eq (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {χ : ClassFunction G} (hχ : IsClassFunction χ)
    {μ ν : Irr (↥c.H0)}
    (hν : ν.1 ∈ orbit c.H0 c.U μ.1)
    (hμB0 : scalarProduct G χ (tildeNu c h12 μ) = 0)
    (hνB0 : scalarProduct G χ (tildeNu c h12 ν) = 0) :
    scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) ν.1 =
      scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) μ.1 := by
  classical
  let χH0 : ClassFunction (↥c.H0) := fun y : ↥c.H0 => χ (y : G)
  have hcoeff : scalarProduct (↥c.H0) χH0 ν.1 =
      scalarProduct G χ (inducedClassFunction c.H0 (ν.1 - μ.1)) +
        scalarProduct (↥c.H0) χH0 μ.1 := by
    calc
      scalarProduct (↥c.H0) χH0 ν.1 = scalarProduct G χ (inducedClassFunction c.H0 ν.1) := by
        rw [scalarProduct_restrict_induced c.H0 hχ ν.1]
      _ = scalarProduct G χ (inducedClassFunction c.H0 (ν.1 - μ.1) +
            inducedClassFunction c.H0 μ.1) := by
            have hsub : inducedClassFunction c.H0 (ν.1 - μ.1) +
                inducedClassFunction c.H0 μ.1 = inducedClassFunction c.H0 ν.1 := by
              have h := inducedClassFunction_sub c.H0 ν.1 μ.1
              rw [h]
              abel
            rw [hsub]
      _ = scalarProduct G χ (inducedClassFunction c.H0 (ν.1 - μ.1)) +
            scalarProduct G χ (inducedClassFunction c.H0 μ.1) := by
            rw [scalarProduct_add_right]
      _ = scalarProduct G χ (inducedClassFunction c.H0 (ν.1 - μ.1)) +
            scalarProduct (↥c.H0) χH0 μ.1 := by
            rw [scalarProduct_restrict_induced c.H0 hχ μ.1]
  have hind := tildeNu_ind c h12 (μ := ν) (ν := μ) hν
  have hsp0 : scalarProduct G χ (inducedClassFunction c.H0 (ν.1 - μ.1)) = 0 := by
    rw [hind, scalarProduct_sub_right, hνB0, hμB0]
    simp
  calc
    scalarProduct (↥c.H0) χH0 ν.1 =
        scalarProduct G χ (inducedClassFunction c.H0 (ν.1 - μ.1)) +
          scalarProduct (↥c.H0) χH0 μ.1 := hcoeff
    _ = scalarProduct (↥c.H0) χH0 μ.1 := by rw [hsp0]; simp

/-- Members of a `Λ`-orbit have the same degree. -/
private lemma orbit_mem_degree_eq (c : Hyp11 G) [Hyp11KData c]
    {ν μ : ClassFunction (↥c.H0)} (hμ : μ ∈ orbit c.H0 c.U ν) : μ 1 = ν 1 := by
  classical
  rcases (Finset.mem_image.mp hμ) with ⟨l, hl, rfl⟩
  simp [LambdaChar]

/-- The degree of an irreducible character is a positive natural number. -/
private lemma irr_one_pos {H : Type u} [Group H] [Fintype H] (ν : Irr H) :
    (0 : ℝ) < (ν.1 1).re := by
  classical
  rcases ν.2 with ⟨n, ρ, hρ, hEq⟩
  have hnon : Nontrivial (Fin n → ℂ) := Subrepresentation.irreducible_module_nontrivial (ρ := ρ)
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    have hsub : Subsingleton (Fin 0 → ℂ) := by
      refine ⟨fun f g => ?_⟩
      ext x
      exact IsEmpty.elim (inferInstance : IsEmpty (Fin 0)) x
    exact (not_subsingleton_iff_nontrivial.mpr hnon) hsub
  have hν1 : ν.1 1 = (n : ℂ) := by
    rw [hEq, Representation.char_one, Module.finrank_pi, Fintype.card_fin]
  rw [hν1]
  norm_num
  exact_mod_cast hn

/-! ## Local mod-2 parity core (`B(χ)` members have odd multiplicity)

For `χ ∈ ±Irr(G)`, `ν ∈ Irr(H0)`, let `a_ν = (χ|_{H0},ν)` and
`e_ν = (χ,ν̃)_G`.  The paper's Lemma 2.4 gives `χ ≡ Σ_ν e_ν·ν (mod 2)` on
`U`; the Fourier expansion gives `χ = Σ_ν a_ν·ν`, so
`Σ_ν (a_ν−e_ν)·ν ≡ 0 (mod 2)` on `U`.  Since `a_ν−e_ν` is constant on each
`Λ`-orbit and the restrictions of distinct orbits to `U` are disjoint sums
of irreducible characters of the odd group `U`, Lemma 1.8 forces
`|Λν|·(a_ν−e_ν)` to be even.  This is used for singleton orbits (where
`a_ν−e_ν` itself is even). -/

/-- Character values of an irreducible character are algebraic integers. -/
private lemma char_value_isIntegral_local {H : Type u} [Group H] [Fintype H]
    (ν : Irr H) (g : H) : IsIntegral ℤ (ν.1 g) := by
  rcases ν.2 with ⟨n, ρ, hρ, hνeq⟩
  simpa [hνeq] using character_value_isIntegral ρ g

/-- `±1` are algebraic integers. -/
private lemma pm_one_isIntegral_local {c : ℂ} (h : c = 1 ∨ c = -1) : IsIntegral ℤ c := by
  rcases h with h1 | hm1
  · rw [h1]
    exact isIntegral_one
  · rw [hm1]
    exact IsIntegral.neg isIntegral_one

/-- `±x ≡ x (mod 2)` for an algebraic integer `x`. -/
private lemma pm_one_mul_congr_local {c x : ℂ} (h : c = 1 ∨ c = -1)
    (hx : IsIntegral ℤ x) : CongruentModTwo (c * x) x := by
  rcases h with h1 | hm1
  · rw [h1]
    simpa using CongruentModTwo.refl x
  · rw [hm1]
    refine ⟨-x, hx.neg, by ring⟩

/-- Pointwise mod-2 congruence over a finset. -/
private lemma sum_congr_of_mem_local {α : Type u} {s : Finset α} {f g : α → ℂ}
    (h : ∀ a ∈ s, CongruentModTwo (f a) (g a)) :
    CongruentModTwo (∑ a ∈ s, f a) (∑ a ∈ s, g a) := by
  classical
  have h' : ∀ a : s, CongruentModTwo (f a.1) (g a.1) := fun a => h a.1 a.2
  have hsum : CongruentModTwo (∑ a : s, f a.1) (∑ a : s, g a.1) :=
    CongruentModTwo.sum h'
  rw [← Finset.sum_attach s f, ← Finset.sum_attach s g]
  exact hsum

/-- `(χ|_{H0},μ) − (χ,μ̃)` is constant on each `Λ`-orbit. -/
private lemma mult_minus_tilde_orbit_eq (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {χ : ClassFunction G} (hχ : IsClassFunction χ)
    {μ ν : Irr (↥c.H0)} (hμ : μ.1 ∈ orbit c.H0 c.U ν.1) :
    scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) μ.1 -
        scalarProduct G χ (tildeNu c h12 μ) =
      scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) ν.1 -
        scalarProduct G χ (tildeNu c h12 ν) := by
  classical
  have hind := tildeNu_ind c h12 (μ := μ) (ν := ν) hμ
  have hspInd : scalarProduct G χ (inducedClassFunction c.H0 (μ.1 - ν.1)) =
      scalarProduct G χ (tildeNu c h12 μ) - scalarProduct G χ (tildeNu c h12 ν) := by
    rw [hind]
    rw [scalarProduct_sub_right]
  have hspRest : scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) μ.1 -
        scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) ν.1 =
      scalarProduct G χ (inducedClassFunction c.H0 (μ.1 - ν.1)) := by
    calc
      scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) μ.1 -
          scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) ν.1
          = scalarProduct G χ (inducedClassFunction c.H0 μ.1) -
              scalarProduct G χ (inducedClassFunction c.H0 ν.1) := by
              rw [← scalarProduct_restrict_induced c.H0 hχ μ.1,
                ← scalarProduct_restrict_induced c.H0 hχ ν.1]
      _ = scalarProduct G χ (inducedClassFunction c.H0 μ.1 -
            inducedClassFunction c.H0 ν.1) := by
            rw [scalarProduct_sub_right]
      _ = scalarProduct G χ (inducedClassFunction c.H0 (μ.1 - ν.1)) := by
            rw [inducedClassFunction_sub]
  have hmain : scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) μ.1 -
        scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) ν.1 =
      scalarProduct G χ (tildeNu c h12 μ) - scalarProduct G χ (tildeNu c h12 ν) := by
    rw [hspRest, hspInd]
  linear_combination hmain

/-- `±Irr(G)` characters are generalized characters. -/
private lemma isGeneralizedCharacter_of_isPMIrr_local {G : Type u} [Group G] [Fintype G]
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) : IsGeneralizedCharacter χ := by
  rcases hχ with hχ | hχ
  · exact ⟨χ, 0, isCharacter_of_isIrreducibleCharacter hχ, isCharacter_zero,
      by ext x; simp⟩
  · exact ⟨0, -χ, isCharacter_zero, isCharacter_of_isIrreducibleCharacter hχ,
      by ext x; simp⟩

/-- Lemma 2.4 on `U`: `χ(u) ≡ Σ_ν e_ν·ν(u) (mod 2)` for all `u ∈ U`,
where `e_ν = (χ,ν̃)_G` (zero outside `B(χ)`). -/
private lemma mult_minus_tilde_sum_congr (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (χ : ClassFunction G) (hχ : IsPMIrr G χ) (u : ↥c.U) :
    CongruentModTwo
      (∑ ν : Irr (↥c.H0),
        (scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) ν.1 -
          scalarProduct G χ (tildeNu c h12 ν)) * ν.1 ⟨(u : G), (U_le_H0 c) u.2⟩) 0 := by
  classical
  let χH0 : ClassFunction (↥c.H0) := fun y : ↥c.H0 => χ (y : G)
  let uH0 : ↥c.H0 := ⟨(u : G), (U_le_H0 c) u.2⟩
  have hχH0g : IsGeneralizedCharacter χH0 :=
    isGeneralizedCharacter_restrict c.H0 (isGeneralizedCharacter_of_isPMIrr_local hχ)
  have hfourier : χ (u : G) = ∑ ν : Irr (↥c.H0),
      scalarProduct (↥c.H0) χH0 ν.1 * ν.1 uH0 := by
    simpa [χH0, uH0] using
      classFunction_eq_sum_irr_coeffs (G := ↥c.H0) (φ := χH0) hχH0g uH0
  have h24 : CongruentModTwo (χ (u : G))
      (∑ ν ∈ BOf c h12 χ, ν.1 uH0) := by
    have h := (lemma_2_4 c h12 hχ).2 u (U_le_H0 c u.2)
    simpa [uH0] using h
  have hsubset (ν : Irr (↥c.H0)) (hν : ν ∈ BOf c h12 χ) :
      CongruentModTwo (scalarProduct G χ (tildeNu c h12 ν) * ν.1 uH0) (ν.1 uH0) :=
    pm_one_mul_congr_local (BOf_scalar_eq_pm_one c h12 hχ hν)
      (char_value_isIntegral_local ν uH0)
  have hfull : (∑ ν : Irr (↥c.H0),
        scalarProduct G χ (tildeNu c h12 ν) * ν.1 uH0) =
      ∑ ν ∈ BOf c h12 χ, scalarProduct G χ (tildeNu c h12 ν) * ν.1 uH0 := by
    symm
    exact Finset.sum_subset (Finset.subset_univ (BOf c h12 χ)) (by
      intro ν hνuniv hνnot
      have hz : scalarProduct G χ (tildeNu c h12 ν) = 0 := by
        by_contra hne
        exact hνnot ((BOf_mem_iff c h12 χ ν).2 hne)
      simp [hz])
  have hBfull : CongruentModTwo
      (∑ ν : Irr (↥c.H0), scalarProduct G χ (tildeNu c h12 ν) * ν.1 uH0)
      (∑ ν ∈ BOf c h12 χ, ν.1 uH0) := by
    rw [hfull]
    exact sum_congr_of_mem_local hsubset
  have hcong : CongruentModTwo
      (∑ ν : Irr (↥c.H0), scalarProduct G χ (tildeNu c h12 ν) * ν.1 uH0)
      (χ (u : G)) :=
    hBfull.trans h24.symm
  have hcong' : CongruentModTwo
      (∑ ν : Irr (↥c.H0), scalarProduct G χ (tildeNu c h12 ν) * ν.1 uH0)
      (∑ ν : Irr (↥c.H0), scalarProduct (↥c.H0) χH0 ν.1 * ν.1 uH0) := by
    rw [hfourier] at hcong
    simpa [χH0] using hcong
  have hsub := CongruentModTwo.sub
    (CongruentModTwo.refl
      (∑ ν : Irr (↥c.H0), scalarProduct (↥c.H0) χH0 ν.1 * ν.1 uH0))
    hcong'
  have hsumEq : (∑ ν : Irr (↥c.H0),
        (scalarProduct (↥c.H0) χH0 ν.1 - scalarProduct G χ (tildeNu c h12 ν)) *
          ν.1 uH0) =
      (∑ ν : Irr (↥c.H0), scalarProduct (↥c.H0) χH0 ν.1 * ν.1 uH0) -
        (∑ ν : Irr (↥c.H0), scalarProduct G χ (tildeNu c h12 ν) * ν.1 uH0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro ν hν
    ring
  simpa [χH0, uH0, hsumEq] using hsub

/-- The sum of the values of the irreducible characters in the fiber of a
representative is the orbit sum of that representative. -/
private lemma orbit_sum_fiber_eq_orbitSum_local (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {ι : Type u} [Fintype ι] (rep : ι → ClassFunction (↥c.H0))
    (hrep_irr : ∀ i : ι, IsIrreducibleCharacter (rep i))
    (hrep : ∀ ν : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
      ∃! i : ι, ν.1 ∈ orbit c.H0 c.U (rep i))
    (i : ι) (x : ↥c.H0) :
    (∑ ν ∈ Finset.univ.filter (fun ν : Irr (↥c.H0) => Classical.choose (hrep ν) = i), ν.1 x) =
      orbitSum c.H0 c.U (rep i) x := by
  classical
  change (∑ ν ∈ Finset.univ.filter (fun ν : Irr (↥c.H0) => Classical.choose (hrep ν) = i), ν.1 x) =
    ∑ μ ∈ orbit c.H0 c.U (rep i), μ x
  symm
  refine Finset.sum_bij (fun μ hμ =>
      (⟨μ, orbit_mem_isIrreducible c.H0 c.U (hrep_irr i) hμ⟩ :
        Irr (↥c.H0))) ?_ ?_ ?_ ?_
  · intro μ hμ
    have hgi : Classical.choose
        (hrep ⟨μ, orbit_mem_isIrreducible c.H0 c.U (hrep_irr i) hμ⟩) = i := by
      exact ((Classical.choose_spec
        (hrep ⟨μ, orbit_mem_isIrreducible c.H0 c.U (hrep_irr i) hμ⟩)).2 i hμ).symm
    simp [hgi]
  · intro a ha b hb hEq
    exact congrArg Subtype.val hEq
  · intro ν hν
    have hmem : ν.1 ∈ orbit c.H0 c.U (rep (Classical.choose (hrep ν))) :=
      (Classical.choose_spec (hrep ν)).1
    have hgi : Classical.choose (hrep ν) = i := (Finset.mem_filter.mp hν).2
    have hνi : ν.1 ∈ orbit c.H0 c.U (rep i) := by rwa [hgi] at hmem
    refine ⟨ν.1, hνi, ?_⟩
    exact Subtype.ext rfl
  · intro μ hμ
    rfl

/-- Regrouping the coefficients of the orbit representatives: the sum over
`ν` of `a(i(ν))·ν(x)` equals the sum over the representatives `i` of
`a i` times the orbit sum `r(Λ rep i)(x)`. -/
private lemma rep_coeff_sum_eq_orbit_sums_local (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {ι : Type u} [Fintype ι] (rep : ι → ClassFunction (↥c.H0))
    (hrep_irr : ∀ i : ι, IsIrreducibleCharacter (rep i))
    (hrep : ∀ ν : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
      ∃! i : ι, ν.1 ∈ orbit c.H0 c.U (rep i))
    (a : ι → ℂ) (x : ↥c.H0) :
    (∑ ν : Irr (↥c.H0), a (Classical.choose (hrep ν)) * ν.1 x) =
      ∑ i : ι, a i * orbitSum c.H0 c.U (rep i) x := by
  classical
  have hfib : (∑ ν : Irr (↥c.H0), a (Classical.choose (hrep ν)) * ν.1 x) =
      ∑ i : ι, ∑ ν ∈ Finset.univ.filter (fun ν : Irr (↥c.H0) => Classical.choose (hrep ν) = i),
        a (Classical.choose (hrep ν)) * ν.1 x := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (g := fun ν : Irr (↥c.H0) => Classical.choose (hrep ν))
      (f := fun ν => a (Classical.choose (hrep ν)) * ν.1 x)
      (by intro ν hν; simp)
  rw [hfib]
  refine Finset.sum_congr rfl ?_
  intro i hi
  calc
    (∑ ν ∈ Finset.univ.filter (fun ν : Irr (↥c.H0) => Classical.choose (hrep ν) = i),
        a (Classical.choose (hrep ν)) * ν.1 x)
        = (∑ ν ∈ Finset.univ.filter (fun ν : Irr (↥c.H0) => Classical.choose (hrep ν) = i),
            a i * ν.1 x) := by
          refine Finset.sum_congr rfl ?_
          intro ν hν
          have hgi : Classical.choose (hrep ν) = i := (Finset.mem_filter.mp hν).2
          rw [hgi]
    _ = a i * (∑ ν ∈ Finset.univ.filter (fun ν : Irr (↥c.H0) => Classical.choose (hrep ν) = i), ν.1 x) := by
          rw [Finset.mul_sum]
    _ = a i * orbitSum c.H0 c.U (rep i) x := by
          rw [orbit_sum_fiber_eq_orbitSum_local c h12 rep hrep_irr hrep i x]

/-- An `S0`-orbit is determined by any one of its members. -/
private lemma s0Orbit_eq_of_mem_local (c : Hyp11 G) [Hyp11KData c] {α β : Irr (↥c.U)}
    (hβ : β ∈ s0Orbit c α) : s0Orbit c β = s0Orbit c α := by
  classical
  rcases Finset.mem_image.mp hβ with ⟨r, hr, rfl⟩
  apply Finset.ext
  intro γ
  constructor
  · intro hγ
    rcases Finset.mem_image.mp hγ with ⟨g, hg, rfl⟩
    refine Finset.mem_image.mpr
      ⟨⟨(r : G) * (g : G), (c.S0 : Subgroup G).mul_mem r.2 g.2⟩,
        Finset.mem_univ _, ?_⟩
    have hEq : conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).mul_mem r.2 g.2)) α =
        conjIrrS c (c.S0_le_S g.2) (conjIrrS c (c.S0_le_S r.2) α) :=
      conjIrrS_mul c (c.S0_le_S r.2) (c.S0_le_S g.2) α
    exact hEq
  · intro hγ
    rcases Finset.mem_image.mp hγ with ⟨g, hg, rfl⟩
    have hrinv : (r : G)⁻¹ * (g : G) ∈ (c.S0 : Subgroup G) :=
      (c.S0 : Subgroup G).mul_mem ((c.S0 : Subgroup G).inv_mem r.2) g.2
    refine Finset.mem_image.mpr
      ⟨⟨(r : G)⁻¹ * (g : G), hrinv⟩, Finset.mem_univ _, ?_⟩
    have hEq : conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).mul_mem r.2 hrinv)) α =
        conjIrrS c (c.S0_le_S hrinv) (conjIrrS c (c.S0_le_S r.2) α) :=
      conjIrrS_mul c (c.S0_le_S r.2) (c.S0_le_S hrinv) α
    calc
      conjIrrS c (c.S0_le_S hrinv) (conjIrrS c (c.S0_le_S r.2) α)
          = conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).mul_mem r.2 hrinv)) α := hEq.symm
      _ = conjIrrS c (c.S0_le_S g.2) α := by
            congr 1
            group

/-- An `S0`-orbit contains its base character. -/
private lemma s0Orbit_self_mem_local (c : Hyp11 G) [Hyp11KData c] (α : Irr (↥c.U)) :
    α ∈ s0Orbit c α := by
  refine Finset.mem_image.mpr ⟨(1 : ↥(c.S0 : Subgroup G)), Finset.mem_univ _, ?_⟩
  exact conjIrrS_one c α

/-- Restriction commutes with conjugation by `s`. -/
private lemma restrictU_conjChar_local (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (ν : ClassFunction (↥c.H0)) :
    restrictU c h12 (conjChar c.H0 (s_normalizes_H0 c h12) ν) =
      conjChar c.U (fun x : ↥c.U => S_normalizes_U c c.s c.s_mem_S x.1 x.2)
        (restrictU c h12 ν) := by
  funext u
  simp [restrictU, conjChar, conjMonoidHom, conjIrrS]

/-- Conjugating the `S0`-orbit sum of `α` by `s` gives the `S0`-orbit sum
of `α^s`. -/
private lemma s0Orbit_conjIrrS_local (c : Hyp11 G) [Hyp11KData c] (hSC : Section3Hyp c)
    (α : Irr (↥c.U)) :
    conjChar c.U (fun x : ↥c.U => S_normalizes_U c c.s c.s_mem_S x.1 x.2)
        (∑ β ∈ s0Orbit c α, β.1) =
      ∑ β ∈ s0Orbit c (conjIrrS c c.s_mem_S α), β.1 := by
  classical
  let hs : ∀ x : ↥c.U, c.s * (x : G) * c.s⁻¹ ∈ c.U :=
    fun x => S_normalizes_U c c.s c.s_mem_S x.1 x.2
  let f : Irr (↥c.U) → Irr (↥c.U) := fun β => conjIrrS c c.s_mem_S β
  have hInj : Set.InjOn f ↑(s0Orbit c α) := by
    intro β hβ γ hγ hEq
    exact conjIrrS_injective c c.s_mem_S hEq
  have himage : (s0Orbit c α).image f = s0Orbit c (conjIrrS c c.s_mem_S α) := by
    ext γ
    constructor
    · intro hγ
      rcases Finset.mem_image.mp hγ with ⟨β, hβ, rfl⟩
      rcases Finset.mem_image.mp hβ with ⟨g, hg, rfl⟩
      have hconj : c.s⁻¹ * (g : G) * c.s ∈ (c.S0 : Subgroup G) := by
        simpa using S_conj_mem_S0 c ((c.S : Subgroup G).inv_mem c.s_mem_S) g.2
      have hgS : (g : G) ∈ (c.S : Subgroup G) := c.S0_le_S g.2
      have hconjS : c.s⁻¹ * (g : G) * c.s ∈ (c.S : Subgroup G) :=
        c.S0_le_S hconj
      refine Finset.mem_image.mpr
        ⟨⟨c.s⁻¹ * (g : G) * c.s, hconj⟩, Finset.mem_univ _, ?_⟩
      change conjIrrS c hconjS (conjIrrS c c.s_mem_S α) = f (conjIrrS c hgS α)
      calc
        conjIrrS c hconjS (conjIrrS c c.s_mem_S α)
            = conjIrrS c ((c.S : Subgroup G).mul_mem c.s_mem_S hconjS) α := by
              exact (conjIrrS_mul c c.s_mem_S hconjS α).symm
        _ = conjIrrS c ((c.S : Subgroup G).mul_mem
              hgS c.s_mem_S) α := by
              congr 1
              group
        _ = f (conjIrrS c hgS α) :=
              conjIrrS_mul c hgS c.s_mem_S α
    · intro hγ
      rcases Finset.mem_image.mp hγ with ⟨g, hg, rfl⟩
      have hconj : c.s * (g : G) * c.s⁻¹ ∈ (c.S0 : Subgroup G) :=
        S_conj_mem_S0 c c.s_mem_S g.2
      have hgS : (g : G) ∈ (c.S : Subgroup G) := c.S0_le_S g.2
      have hconjS : c.s * (g : G) * c.s⁻¹ ∈ (c.S : Subgroup G) :=
        c.S0_le_S hconj
      refine Finset.mem_image.mpr
        ⟨conjIrrS c hconjS α, ?_, ?_⟩
      · exact Finset.mem_image.mpr
          ⟨⟨c.s * (g : G) * c.s⁻¹, hconj⟩, Finset.mem_univ _, rfl⟩
      · change f (conjIrrS c hconjS α) = conjIrrS c hgS (conjIrrS c c.s_mem_S α)
        calc
          f (conjIrrS c hconjS α)
              = conjIrrS c ((c.S : Subgroup G).mul_mem hconjS c.s_mem_S) α := by
                  exact (conjIrrS_mul c hconjS c.s_mem_S α).symm
          _ = conjIrrS c ((c.S : Subgroup G).mul_mem c.s_mem_S hgS) α := by
                  congr 1
                  group
          _ = conjIrrS c hgS (conjIrrS c c.s_mem_S α) :=
                  conjIrrS_mul c c.s_mem_S hgS α
  funext u
  simp [conjChar, conjMonoidHom]
  change (∑ β ∈ s0Orbit c α, (f β).1 u) =
    ∑ β ∈ s0Orbit c (conjIrrS c c.s_mem_S α), β.1 u
  rw [← himage, Finset.sum_image hInj]

set_option maxHeartbeats 1000000 in
/-- `(χ|_{H0},ν)` is an integer for `χ ∈ ±Irr(G)`. -/
private lemma restrict_scalarProduct_int_local (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    (rep : ClassFunction (↥c.H0)) (hrep : IsIrreducibleCharacter rep) :
    ∃ a : ℤ, scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) rep = (a : ℂ) := by
  classical
  have hχH0 : IsGeneralizedCharacter (fun y : ↥c.H0 => χ (y : G)) :=
    isGeneralizedCharacter_restrict c.H0 (isGeneralizedCharacter_of_isPMIrr_local hχ)
  rcases multiplicity_int hrep (fun y : ↥c.H0 => χ (y : G)) hχH0 with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hrev : star (scalarProduct (↥c.H0) rep (fun y : ↥c.H0 => χ (y : G))) =
      scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) rep := by
    unfold scalarProduct
    simp [map_sum, map_mul, map_star, mul_comm, mul_left_comm, mul_assoc]
  rw [← hrev, ha]
  simp

/-- A sum over a sigma of finsets equals the double sum over the attached
finsets. -/
private lemma sigma_finset_sum_eq {ι : Type u} [Fintype ι] {α : ι → Type u}
    (t : ∀ i, Finset (α i)) (f : (i : ι) → α i → ℂ) :
    (∑ p : Σ i : ι, {x : α i // x ∈ t i}, f p.1 (p.2 : α p.1)) =
      ∑ i : ι, ∑ x ∈ (t i).attach, f i (x : α i) := by
  classical
  calc
    (∑ p : Σ i : ι, {x : α i // x ∈ t i}, f p.1 (p.2 : α p.1))
        = ∑ p ∈ (Finset.univ : Finset (Σ i : ι, {x : α i // x ∈ t i})),
            f p.1 (p.2 : α p.1) := rfl
    _ = ∑ p ∈ (Finset.univ : Finset ι).sigma (fun i : ι => (t i).attach),
            f p.1 (p.2 : α p.1) := by
            congr 1
    _ = ∑ i : ι, ∑ x ∈ (t i).attach, f i (x : α i) := by
            rw [Finset.sum_sigma]

set_option maxHeartbeats 1000000 in
/-- For every `ν`, `|Λν|·((χ|_{H0},ν) − (χ,ν̃))` is even. -/
private lemma mult_minus_tilde_mul_card_even (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (χ : ClassFunction G) (hχ : IsPMIrr G χ)
    (ν : Irr (↥c.H0)) :
    CongruentModTwo
      (((orbit c.H0 c.U ν.1).card : ℂ) *
        (scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) ν.1 -
          scalarProduct G χ (tildeNu c h12 ν))) 0 := by
  classical
  rcases exists_orbit_reps c h12 with ⟨ι, hι, rep, hrep_irr, hrep⟩
  let : Fintype ι := hι
  let repIrr : ι → Irr (↥c.H0) := fun i => ⟨rep i, hrep_irr i⟩
  let α_i : ι → Irr (↥c.U) := fun i =>
    Classical.choose (orbit_is_orbitOfAlpha c h12 hSC (repIrr i))
  have hOrbit_i (i : ι) : orbit c.H0 c.U (rep i) = orbitOfAlpha c h12 hSC (α_i i) :=
    Classical.choose_spec (orbit_is_orbitOfAlpha c h12 hSC (repIrr i))
  let d : Irr (↥c.H0) → ℂ := fun ξ =>
    scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) ξ.1 -
      scalarProduct G χ (tildeNu c h12 ξ)
  have hd_const {ξ η : Irr (↥c.H0)} (hξη : ξ.1 ∈ orbit c.H0 c.U η.1) : d ξ = d η :=
    mult_minus_tilde_orbit_eq c h12
      (isClassFunction_of_isGeneralizedCharacter (isGeneralizedCharacter_of_isPMIrr_local hχ)) hξη
  let I : Type u := Σ i : ι, s0Orbit c (α_i i)
  let β : I → ClassFunction (↥c.U) := fun p => (p.2 : Irr (↥c.U)).1
  let cc : I → ℂ := fun p =>
    d (repIrr p.1) * ((orbit c.H0 c.U (rep p.1)).card : ℂ)
  have hβirr : ∀ p : I, IsIrreducibleCharacter (β p) := fun p => (p.2 : Irr (↥c.U)).2
  have hβdist : Pairwise fun p q : I => β p ≠ β q := by
    intro p q hpq
    intro hEq
    cases p with
    | mk i β0 =>
      cases q with
      | mk j γ0 =>
        have hEqIrr : (β0 : Irr (↥c.U)) = (γ0 : Irr (↥c.U)) := by
          apply Subtype.ext
          simpa [β] using hEq
        have hmemP : (β0 : Irr (↥c.U)) ∈ s0Orbit c (α_i i) := β0.2
        have hmemQ : (γ0 : Irr (↥c.U)) ∈ s0Orbit c (α_i j) := γ0.2
        have hmemQ' : (β0 : Irr (↥c.U)) ∈ s0Orbit c (α_i j) := by
          simpa [hEqIrr] using hmemQ
        have hOrb : s0Orbit c (α_i i) = s0Orbit c (α_i j) :=
          (s0Orbit_eq_of_mem_local c hmemP).symm.trans (s0Orbit_eq_of_mem_local c hmemQ')
        have hOAlpha : orbitOfAlpha c h12 hSC (α_i i) = orbitOfAlpha c h12 hSC (α_i j) := by
          apply orbitOfAlpha_unique c h12 hSC (α_i j) (orbitOfAlpha c h12 hSC (α_i i))
          constructor
          · rcases orbitOfAlpha_spec c h12 hSC (α_i i) with ⟨⟨μ, hL⟩, hres⟩
            exact ⟨μ, hL⟩
          · intro ξ hξ
            have hresp := (orbitOfAlpha_spec c h12 hSC (α_i i)).2 ξ hξ
            rw [hOrb] at hresp
            exact hresp
        have hOrbitEq : orbit c.H0 c.U (rep i) = orbit c.H0 c.U (rep j) := by
          rw [hOrbit_i i, hOAlpha, hOrbit_i j]
        have hmemRep : rep i ∈ orbit c.H0 c.U (rep j) := by
          rw [← hOrbitEq]
          exact orbit_self_mem c.H0 c.U (rep i)
        have hij : i = j := by
          have huni := Classical.choose_spec (hrep ⟨rep i, hrep_irr i⟩)
          exact ((huni.2 i (orbit_self_mem c.H0 c.U (rep i))).trans
            (huni.2 j hmemRep).symm)
        subst hij
        have hβγ : β0 = γ0 := Subtype.ext hEqIrr
        exact hpq (congrArg (Sigma.mk i) hβγ)
  have hcval : ∀ p : I, IsIntegral ℤ (cc p) := by
    intro p
    have hd_int : IsIntegral ℤ (d (repIrr p.1)) := by
      have ha : IsIntegral ℤ
          (scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) (rep p.1)) := by
        rcases restrict_scalarProduct_int_local c h12 hχ (rep p.1) (hrep_irr p.1) with ⟨a, ha⟩
        rw [ha]
        exact isIntegral_intCast a
      have he : IsIntegral ℤ (scalarProduct G χ (tildeNu c h12 (repIrr p.1))) := by
        by_cases hB : repIrr p.1 ∈ BOf c h12 χ
        · rcases BOf_scalar_eq_pm_one c h12 hχ hB with h1 | hm1
          · rw [h1]
            exact isIntegral_one
          · rw [hm1]
            exact IsIntegral.neg isIntegral_one
        · have hz : scalarProduct G χ (tildeNu c h12 (repIrr p.1)) = 0 :=
            by
            by_contra hne
            exact hB ((BOf_mem_iff c h12 χ (repIrr p.1)).2 hne)
          rw [hz]
          exact isIntegral_zero
      exact ha.sub he
    have hcard_int : IsIntegral ℤ ((orbit c.H0 c.U (rep p.1)).card : ℂ) :=
      isIntegral_natCast (orbit c.H0 c.U (rep p.1)).card
    simpa [cc] using hd_int.mul hcard_int
  have h0 : ∀ b : ↥c.U, CongruentModTwo (∑ p : I, cc p * β p b) 0 := by
    intro b
    let uH0 : ↥c.H0 := ⟨(b : G), (U_le_H0 c) b.2⟩
    have hsumCongr := mult_minus_tilde_sum_congr c h12 χ hχ b
    have horbit (i : ι) : orbitSum c.H0 c.U (rep i) uH0 =
        ((orbit c.H0 c.U (rep i)).card : ℂ) *
          (∑ α' ∈ s0Orbit c (α_i i), α'.1 b) := by
      have hspec := (orbitOfAlpha_spec c h12 hSC (α_i i)).2
      calc
        orbitSum c.H0 c.U (rep i) uH0
            = ∑ μ ∈ orbit c.H0 c.U (rep i), μ uH0 := rfl
        _ = ∑ μ ∈ orbitOfAlpha c h12 hSC (α_i i), μ uH0 := by rw [hOrbit_i i]
        _ = ∑ μ ∈ orbitOfAlpha c h12 hSC (α_i i),
            (∑ α' ∈ s0Orbit c (α_i i), α'.1) b := by
              refine Finset.sum_congr rfl ?_
              intro μ hμ
              have hres := hspec μ hμ
              change μ uH0 = (∑ α' ∈ s0Orbit c (α_i i), α'.1) b
              have hU : μ uH0 = restrictU c h12 μ b := by
                unfold restrictU
                congr 1
              rw [hU, hres]
        _ = ((orbitOfAlpha c h12 hSC (α_i i)).card : ℂ) *
              (∑ α' ∈ s0Orbit c (α_i i), α'.1 b) := by
              rw [Finset.sum_const]
              simp
        _ = ((orbit c.H0 c.U (rep i)).card : ℂ) *
              (∑ α' ∈ s0Orbit c (α_i i), α'.1 b) := by
              rw [hOrbit_i i]
    have hEq : (∑ p : I, cc p * β p b) = ∑ ν : Irr (↥c.H0), d ν * ν.1 uH0 := by
      calc
        (∑ p : I, cc p * β p b)
            = ∑ i : ι, ∑ α' ∈ s0Orbit c (α_i i),
                d (repIrr i) * ((orbit c.H0 c.U (rep i)).card : ℂ) * α'.1 b := by
                classical
                have hsumI : (∑ p : I, cc p * β p b) =
                    ∑ i : ι, ∑ α' ∈ (s0Orbit c (α_i i)).attach,
                      d (repIrr i) * ((orbit c.H0 c.U (rep i)).card : ℂ) *
                        (α' : Irr (↥c.U)).1 b := by
                  simpa [I, cc, β] using
                    (sigma_finset_sum_eq (ι := ι)
                      (α := fun i : ι => Irr (↥c.U))
                      (t := fun i : ι => s0Orbit c (α_i i))
                      (f := fun i β => d (repIrr i) *
                        ((orbit c.H0 c.U (rep i)).card : ℂ) * β.1 b))
                rw [hsumI]
                refine Finset.sum_congr rfl ?_
                intro i hi
                exact Finset.sum_attach (s0Orbit c (α_i i))
                  (fun x : Irr (↥c.U) =>
                    d (repIrr i) * ((orbit c.H0 c.U (rep i)).card : ℂ) * x.1 b)
        _ = ∑ i : ι, d (repIrr i) * orbitSum c.H0 c.U (rep i) uH0 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              calc
                (∑ α' ∈ s0Orbit c (α_i i),
                    d (repIrr i) * ((orbit c.H0 c.U (rep i)).card : ℂ) * α'.1 b)
                    = (d (repIrr i) * ((orbit c.H0 c.U (rep i)).card : ℂ)) *
                        (∑ α' ∈ s0Orbit c (α_i i), α'.1 b) := by
                        rw [← Finset.mul_sum]
                _ = d (repIrr i) * orbitSum c.H0 c.U (rep i) uH0 := by
                        rw [horbit i]
                        ring
        _ = ∑ ν : Irr (↥c.H0), d ν * ν.1 uH0 := by
              have hmain := rep_coeff_sum_eq_orbit_sums_local c h12 rep hrep_irr hrep
                (fun i : ι => d (repIrr i)) uH0
              rw [← hmain]
              refine Finset.sum_congr rfl ?_
              intro ν hν
              have hmem : ν.1 ∈ orbit c.H0 c.U (rep (Classical.choose (hrep ν))) :=
                (Classical.choose_spec (hrep ν)).1
              have hmem' : (repIrr (Classical.choose (hrep ν))).1 ∈
                  orbit c.H0 c.U ν.1 := by
                have horb := orbit_eq_of_mem' c hmem
                have hself := orbit_self_mem c.H0 c.U (rep (Classical.choose (hrep ν)))
                rw [← horb] at hself
                exact hself
              rw [hd_const hmem']
    have hcong' : CongruentModTwo (∑ p : I, cc p * β p b) (∑ ν : Irr (↥c.H0), d ν * ν.1 uH0) :=
      CongruentModTwo.of_eq hEq
    exact hcong'.trans hsumCongr
  have h18 := lemma_1_8 (B := ↥c.U) (U_coprime_two c) (I := I) (β := β) (c := cc)
    hβirr hβdist hcval h0
  have hself : α_i (Classical.choose (hrep ν)) ∈
      s0Orbit c (α_i (Classical.choose (hrep ν))) :=
    s0Orbit_self_mem_local c (α_i (Classical.choose (hrep ν)))
  have hcong : CongruentModTwo
      (d (repIrr (Classical.choose (hrep ν))) *
        ((orbit c.H0 c.U (rep (Classical.choose (hrep ν)))).card : ℂ)) 0 := by
    simpa [cc, β] using
      h18 ⟨Classical.choose (hrep ν),
        ⟨α_i (Classical.choose (hrep ν)), hself⟩⟩
  have hmem : ν.1 ∈ orbit c.H0 c.U (rep (Classical.choose (hrep ν))) :=
    (Classical.choose_spec (hrep ν)).1
  have hcardEq : (orbit c.H0 c.U ν.1).card = (orbit c.H0 c.U (rep (Classical.choose (hrep ν)))).card := by
    rw [orbit_eq_of_mem' c hmem]
  have hdEq : d ν = d (repIrr (Classical.choose (hrep ν))) := hd_const hmem
  simpa [d, hcardEq, hdEq, mul_comm, mul_left_comm, mul_assoc] using hcong

/-! ## Bad-case killers: an `s`-invariant orbit contained in `B(χ)` cannot
have all members with zero multiplicity in `χ|_{H0}` -/

/-- A finset of cardinality two containing two distinct elements is the pair
of those elements. -/
private lemma finset_pair_eq_of_card_two_local {α : Type u} [DecidableEq α]
    {s : Finset α} {a b : α} (hcard : s.card = 2) (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) : s = {a, b} := by
  classical
  have hsub : ({a, b} : Finset α) ⊆ s := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  refine Finset.Subset.antisymm ?_ hsub
  intro x hx
  by_contra hxnot
  have hxne_a : x ≠ a := by
    intro hEq
    apply hxnot
    simp [hEq]
  have hxne_b : x ≠ b := by
    intro hEq
    apply hxnot
    simp [hEq]
  have hsub3 : ({a, b, x} : Finset α) ⊆ s := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hx
  have hcard3 : ({a, b, x} : Finset α).card = 3 := by
    simp [hab, hxne_a, hxne_b, hxne_a.symm, hxne_b.symm]
  have hle : 3 ≤ s.card := by
    calc
      3 = ({a, b, x} : Finset α).card := hcard3.symm
      _ ≤ s.card := Finset.card_le_card hsub3
  omega

/-- Conjugation by `s` fixes the value of every `H0`-character at the central
involution `t` (because `s` fixes `t`). -/
private lemma conjChar_apply_tH0_eq_local (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (ν : ClassFunction (↥c.H0)) :
    conjChar c.H0 (s_normalizes_H0 c h12) ν (tH0 c) = ν (tH0 c) := by
  change ν (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) (tH0 c)) = ν (tH0 c)
  congr 1
  apply Subtype.ext
  change c.s * c.t * c.s⁻¹ = c.t
  exact s_conj_t c

/-- Conjugation by `s` is injective on class functions of `H0`. -/
private lemma conjChar_injective_local (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {φ ψ : ClassFunction (↥c.H0)}
    (h : conjChar c.H0 (s_normalizes_H0 c h12) φ =
      conjChar c.H0 (s_normalizes_H0 c h12) ψ) : φ = ψ := by
  calc
    φ = conjChar c.H0 (s_normalizes_H0 c h12)
        (conjChar c.H0 (s_normalizes_H0 c h12) φ) :=
          (conjChar_conjChar_local c h12 φ).symm
    _ = conjChar c.H0 (s_normalizes_H0 c h12)
        (conjChar c.H0 (s_normalizes_H0 c h12) ψ) := by rw [h]
    _ = ψ := conjChar_conjChar_local c h12 ψ

/-- Two signed irreducibles with a nonzero scalar product are equal up to the
sign of the coefficient. -/
private lemma signed_irr_eq_smul_of_pairing_ne_local {G : Type u} [Group G] [Fintype G]
    {χ ψ : ClassFunction G} (hχ : IsPMIrr G χ)
    (hψ : IsIrreducibleCharacter ψ)
    (hne : scalarProduct G χ ψ ≠ 0) :
    χ = scalarProduct G χ ψ • ψ := by
  classical
  have hχg : IsGeneralizedCharacter χ := isGeneralizedCharacter_of_isPMIrr_local hχ
  have hχself : scalarProduct G χ χ = 1 := by
    rcases hχ with hχ | hχneg
    · exact scalarProduct_irreducible_self hχ
    · have h' : scalarProduct G (-χ) (-χ) = 1 := scalarProduct_irreducible_self hχneg
      rw [scalarProduct_neg_left, scalarProduct_neg_right] at h'
      simpa using h'
  rcases norm_one_signed_irreducible hχg hχself with ⟨ψ₀, hψ₀, hχeq⟩
  have hψ₀eq : ψ₀ = ψ := by
    by_contra h
    rcases hχeq with hχeq | hχeq
    · have h' : scalarProduct G χ ψ = 0 := by
        rw [hχeq]
        simpa [scalarProduct_irr_ite hψ₀ hψ, h]
      exact hne h'
    · have h' : scalarProduct G χ ψ = 0 := by
        rw [hχeq]
        rw [scalarProduct_neg_left]
        simpa [scalarProduct_irr_ite hψ₀ hψ, h]
      exact hne h'
  rcases hχeq with hχeq | hχeq
  · have h1 : scalarProduct G χ ψ = 1 := by
      rw [hχeq, hψ₀eq]
      exact scalarProduct_irreducible_self hψ
    rw [h1, hχeq, hψ₀eq]
    simp
  · have h1 : scalarProduct G χ ψ = -1 := by
      rw [hχeq, hψ₀eq]
      rw [scalarProduct_neg_left]
      simp [scalarProduct_irreducible_self hψ]
    rw [h1, hχeq, hψ₀eq]
    simp

/-- Since `ν ∈ B(χ)` and `ν^s ≠ ν`, `ν̃` is a signed irreducible and
`χ = (χ,ν̃) • ν̃` pointwise. -/
private lemma chi_eq_smul_tildeNu_local (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hνB : ν ∈ BOf c h12 χ) :
    χ = scalarProduct G χ (tildeNu c h12 ν) • tildeNu c h12 ν := by
  classical
  have hgen : IsGeneralizedCharacter (tildeNu c h12 ν) :=
    tildeNu_isGeneralized c h12 ν
  have hnorm : normSq G (tildeNu c h12 ν) = 1 := by
    rw [tildeNu_norm c h12 ν]
    simp [hνs]
  have hnorm1 : scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν) = 1 := by
    simpa [normSq] using hnorm
  rcases norm_one_signed_irreducible hgen hnorm1 with ⟨ψ, hψ, hψeq⟩
  have hne : scalarProduct G χ (tildeNu c h12 ν) ≠ 0 := by
    exact (BOf_mem_iff c h12 χ ν).1 hνB
  rcases hψeq with hψeq | hψeq
  · have hne' : scalarProduct G χ ψ ≠ 0 := by simpa [hψeq] using hne
    have hEq := signed_irr_eq_smul_of_pairing_ne_local (hχ := hχ) (hψ := hψ) hne'
    simpa [hψeq] using hEq
  · have hne' : scalarProduct G χ (-ψ) ≠ 0 := by simpa [hψeq] using hne
    have hEq := signed_irr_eq_smul_of_pairing_ne_local (hχ := hχ) (hψ := hψ)
      (by
        have h' : scalarProduct G χ (-ψ) = -scalarProduct G χ ψ := by
          rw [scalarProduct_neg_right]
        have h'' : scalarProduct G χ ψ ≠ 0 := by
          intro h0
          apply hne'
          rw [h', h0]
          norm_num
        exact h''
      )
    have h'' : scalarProduct G χ (tildeNu c h12 ν) • tildeNu c h12 ν =
        scalarProduct G χ ψ • ψ := by
      rw [hψeq]
      rw [scalarProduct_neg_right]
      simp [smul_neg, neg_smul, neg_neg]
    calc
      χ = scalarProduct G χ ψ • ψ := hEq
      _ = scalarProduct G χ (tildeNu c h12 ν) • tildeNu c h12 ν := h''.symm

/-- In a two-element `Λ`-orbit `{ν, l·ν}` with `ν^s = l·ν`, the multiplier
evaluates to `−1` at the involution `t`. -/
private lemma lambda_mover_eval_t_neg_one (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {ν : Irr (↥c.H0)} {l : LambdaHom c.H0 c.U}
    (hl : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = LambdaChar l.1 * ν.1)
    (hcard : (orbit c.H0 c.U ν.1).card = 2)
    (hνsne : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1) :
    (l.1 (tH0 c) : ℂ) = -1 := by
  classical
  let t0 : ↥c.H0 := tH0 c
  have htnotU : (t0 : G) ∉ c.U := t_not_mem_U c
  have hsum : ∑ l' : LambdaHom c.H0 c.U, (l'.1 t0 : ℂ) = 0 :=
    dual_sum_zero c.H0 c.U (U_normal_subgroupOf c h12) (lambda_hcomm c h12) t0 htnotU
  have horbitSumAll : orbitSumAll c.H0 c.U ν.1 t0 = 0 := by
    calc
      orbitSumAll c.H0 c.U ν.1 t0
          = ∑ l' : LambdaHom c.H0 c.U, ((l'.1 t0 : ℂ) * ν.1 t0) := rfl
      _ = (∑ l' : LambdaHom c.H0 c.U, (l'.1 t0 : ℂ)) * ν.1 t0 := by
            rw [Finset.sum_mul]
      _ = 0 * ν.1 t0 := by rw [hsum]
      _ = 0 := by simp
  have hstab_card : 0 < (Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
      LambdaChar s.1 * ν.1 = ν.1)).card := by
    exact Finset.card_pos.mpr ⟨1, one_mem_stab c.H0 c.U ν.1⟩
  have hmem_l : LambdaChar l.1 * ν.1 ∈ orbit c.H0 c.U ν.1 :=
    Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩
  have hνmem : ν.1 ∈ orbit c.H0 c.U ν.1 := orbit_self_mem c.H0 c.U ν.1
  have hne : ν.1 ≠ LambdaChar l.1 * ν.1 := by
    intro hEq
    exact hνsne (hl.trans hEq.symm)
  have horbit_pair : orbit c.H0 c.U ν.1 = {ν.1, LambdaChar l.1 * ν.1} :=
    finset_pair_eq_of_card_two_local hcard hνmem hmem_l hne
  have horbitSum : orbitSum c.H0 c.U ν.1 t0 = ν.1 t0 * (1 + (l.1 t0 : ℂ)) := by
    calc
      orbitSum c.H0 c.U ν.1 t0
          = ∑ μ ∈ orbit c.H0 c.U ν.1, μ t0 := rfl
      _ = ν.1 t0 + (LambdaChar l.1 * ν.1) t0 := by
            rw [horbit_pair]
            rw [Finset.sum_insert (by simpa using hne)]
            simp
      _ = ν.1 t0 * (1 + (l.1 t0 : ℂ)) := by
            simp [LambdaChar]
            ring
  have hmain : ((Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
      LambdaChar s.1 * ν.1 = ν.1)).card : ℂ) *
        (ν.1 t0 * (1 + (l.1 t0 : ℂ))) = 0 := by
    have h := orbitSumAll_eq_card_stab c.H0 c.U ν.1 t0
    rw [horbitSum] at h
    rw [horbitSumAll] at h
    exact h.symm
  have hstab_ne : ((Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
      LambdaChar s.1 * ν.1 = ν.1)).card : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hstab_card)
  have hνt_ne : ν.1 (tH0 c) ≠ 0 :=
    char_apply_central_ne_zero (G := ↥c.H0) (t := tH0 c)
      (by simpa [tH0] using t_central_H0' c) (t_H0_sq c) ν.2
  have hmul : 1 + (l.1 t0 : ℂ) = 0 := by
    have h' : ν.1 t0 * (1 + (l.1 t0 : ℂ)) = 0 :=
      (mul_eq_zero.mp hmain).resolve_left hstab_ne
    exact (mul_eq_zero.mp h').resolve_left (by simpa [t0] using hνt_ne)
  have hlt : (l.1 (tH0 c) : ℂ) = -1 := by
    have h1 : 1 + (l.1 (tH0 c) : ℂ) = 0 := by simpa [t0] using hmul
    have h2 : 1 = - (l.1 (tH0 c) : ℂ) := add_eq_zero_iff_eq_neg.mp h1
    have h3 : -1 = (l.1 (tH0 c) : ℂ) := by simpa using congrArg Neg.neg h2
    exact h3.symm
  simpa [t0] using hlt

/-- `[H0 : U] = |S0|`: the map `S0 → H0/U`, `r ↦ rU` is a bijection. -/
private lemma U_index_eq_S0_card_local (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) :
    (c.U.subgroupOf c.H0).index = Nat.card (c.S0 : Subgroup G) := by
  classical
  let K : Subgroup (↥c.H0) := c.U.subgroupOf c.H0
  have hKnormal : K.Normal := U_normal_subgroupOf c h12
  let f : ↥c.S0 → ↥c.H0 ⧸ K := fun r =>
    (QuotientGroup.mk (⟨(r : G), S0_le_H0 c r.2⟩ : ↥c.H0) : ↥c.H0 ⧸ K)
  have hinj : Function.Injective f := by
    intro r₁ r₂ hEq
    unfold f at hEq
    have hf1 : f (r₁ * r₂⁻¹) = 1 := by
      unfold f
      have hsub : (⟨((r₁ * r₂⁻¹ : ↥c.S0) : G), S0_le_H0 c ((r₁ * r₂⁻¹ : ↥c.S0)).2⟩ : ↥c.H0) =
          (⟨(r₁ : G), S0_le_H0 c r₁.2⟩ : ↥c.H0) * (⟨(r₂ : G), S0_le_H0 c r₂.2⟩ : ↥c.H0)⁻¹ := by
        apply Subtype.ext
        rfl
      rw [hsub, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hEq]
      simp
    have hU : ((r₁ * r₂⁻¹ : ↥c.S0) : G) ∈ c.U := by
      let y : ↥c.H0 := ⟨((r₁ * r₂⁻¹ : ↥c.S0) : G), S0_le_H0 c ((r₁ * r₂⁻¹ : ↥c.S0)).2⟩
      have hk : y ∈ K := by
        exact (QuotientGroup.eq_one_iff y).1 (by
          simpa [f, y] using hf1)
      exact Subgroup.mem_subgroupOf.mp hk
    have hEq' : (r₁ * r₂⁻¹ : ↥c.S0) = 1 := by
      apply Subtype.ext
      exact U_inter_S0_eq_bot c hU ((r₁ * r₂⁻¹ : ↥c.S0)).2
    apply Subtype.ext
    exact mul_inv_eq_one.mp (congrArg (fun z : ↥c.S0 => (z : G)) hEq')
  have hsurj : Function.Surjective f := by
    intro q
    rcases QuotientGroup.mk'_surjective K q with ⟨x, hx⟩
    rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u, r, hxEq⟩
    refine ⟨r, ?_⟩
    have huH0 : (u : G) ∈ c.H0 := by
      exact (le_sup_left : c.U ≤ c.U ⊔ (c.S0 : Subgroup G)) u.2
    let uH0 : ↥c.H0 := ⟨(u : G), huH0⟩
    let rH0 : ↥c.H0 := ⟨(r : G), S0_le_H0 c r.2⟩
    have hxEq'' : x = uH0 * rH0 := by
      apply Subtype.ext
      exact hxEq
    have huK : uH0 ∈ K := by
      exact Subgroup.mem_subgroupOf.mpr u.2
    have hmk : (QuotientGroup.mk x : ↥c.H0 ⧸ K) = QuotientGroup.mk rH0 := by
      rw [hxEq'', QuotientGroup.mk_mul]
      have hu1 : (QuotientGroup.mk uH0 : ↥c.H0 ⧸ K) = 1 := by
        exact (QuotientGroup.eq_one_iff uH0).mpr huK
      rw [hu1, one_mul]
    unfold f
    exact hmk.symm.trans hx
  have hcard : Nat.card (↥c.H0 ⧸ K) = Nat.card (↥c.S0) := by
    exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm
  calc
    (c.U.subgroupOf c.H0).index = Nat.card (↥c.H0 ⧸ K) := by
      exact Subgroup.index_eq_card K
    _ = Nat.card (↥c.S0) := hcard

/-- Every `Λ`-orbit of an irreducible character of `H0` has 2-power
cardinality. -/
private lemma orbit_card_is_pow_two_local (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (ν : Irr (↥c.H0)) : ∃ k : ℕ, (orbit c.H0 c.U ν.1).card = 2 ^ k := by
  classical
  have hmain := orbit_card_mul_stab c.H0 c.U ν.1
  have hΛ : Fintype.card (LambdaHom c.H0 c.U) = (c.U.subgroupOf c.H0).index := by
    simpa using lambda_card_eq_index c h12
  have hdvd : (orbit c.H0 c.U ν.1).card ∣ (c.U.subgroupOf c.H0).index := by
    refine ⟨(Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
      LambdaChar s.1 * ν.1 = ν.1)).card, ?_⟩
    rw [← hΛ]
    rw [hmain]
  have hdvd' : (orbit c.H0 c.U ν.1).card ∣ 2 ^ c.m := by
    have hindex : (c.U.subgroupOf c.H0).index = 2 ^ c.m := by
      rw [U_index_eq_S0_card_local c h12]
      exact S0_nat_card c
    rwa [hindex] at hdvd
  rcases (Nat.dvd_prime_pow Nat.prime_two).1 hdvd' with ⟨k, _hk, hk⟩
  exact ⟨k, hk⟩

/-- `(χ|_{H0},ν)` is a natural number for `χ ∈ Irr(G)`. -/
private lemma restrict_mult_nat (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (χ : Irr G)
    (ν : Irr (↥c.H0)) : ∃ r : ℕ,
      (r : ℂ) = scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ.1 (y : G)) ν.1 := by
  classical
  let χH0 : ClassFunction (↥c.H0) := fun y : ↥c.H0 => χ.1 (y : G)
  have hχH0 : IsCharacter χH0 :=
    isCharacter_restrict c.H0 (isCharacter_of_isIrreducibleCharacter χ.2)
  rcases scalarProduct_irr_char_nat (χ := ν.1) (ψ := χH0) ν.2 hχH0 with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  calc
    (r : ℂ) = scalarProduct (↥c.H0) ν.1 χH0 := hr
    _ = star (scalarProduct (↥c.H0) ν.1 χH0) := by
          rw [hr.symm]
          simp
    _ = scalarProduct (↥c.H0) χH0 ν.1 := scalarProduct_conj ν.1 χH0

set_option maxHeartbeats 1000000 in
/-- No `Λ`-orbit contained in `B(χ)` can contain a member with zero
multiplicity in `χ|_{H0}`. -/
private lemma orbit_subset_BOf_zero_mult_false (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (χ : Irr G) {ν : Irr (↥c.H0)}
    (hνB : ν ∈ BOf c h12 χ.1)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈ orbit c.H0 c.U ν.1)
    (hLsubB : ∀ μ : Irr (↥c.H0), μ.1 ∈ orbit c.H0 c.U ν.1 → μ ∈ BOf c h12 χ.1)
    (haν0 : scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ.1 (y : G)) ν.1 = 0) :
    False := by
  classical
  let L : Finset (ClassFunction (↥c.H0)) := orbit c.H0 c.U ν.1
  let a : Irr (↥c.H0) → ℂ := fun ξ =>
    scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ.1 (y : G)) ξ.1
  let e : Irr (↥c.H0) → ℂ := fun ξ => scalarProduct G χ.1 (tildeNu c h12 ξ)
  have hχpm : IsPMIrr G χ.1 := Or.inl χ.2
  have hBle : (BOf c h12 χ.1).card ≤ 3 := theorem_3_2 c h12 hSC hχpm
  have hLleB : L.card ≤ (BOf c h12 χ.1).card := by
    -- L = orbit ν.1 embeds into BOf via (orbit_mem_isIrreducible)
    let f : {μ : ClassFunction (↥c.H0) // μ ∈ L} → Irr (↥c.H0) := fun μ =>
      ⟨μ.1, orbit_mem_isIrreducible c.H0 c.U ν.2 μ.2⟩
    have hinj : Function.Injective f := by
      intro x y hEq
      rcases x with ⟨x, hx⟩
      rcases y with ⟨y, hy⟩
      change (⟨x, orbit_mem_isIrreducible c.H0 c.U ν.2 hx⟩ : Irr (↥c.H0)) =
          ⟨y, orbit_mem_isIrreducible c.H0 c.U ν.2 hy⟩ at hEq
      cases hEq
      rfl
    have hmem : ∀ μ : {μ : ClassFunction (↥c.H0) // μ ∈ L}, f μ ∈ BOf c h12 χ.1 := by
      intro μ
      exact hLsubB (f μ) μ.2
    calc
      L.card = Fintype.card {μ : ClassFunction (↥c.H0) // μ ∈ L} := by
            simpa using (Fintype.card_coe L).symm
      _ ≤ Fintype.card (BOf c h12 χ.1) := by
            refine Fintype.card_le_of_injective (f := fun μ : {μ // μ ∈ L} => ⟨f μ, hmem μ⟩) ?_
            intro x y hEq
            exact hinj (Subtype.ext
              (congrArg (fun z : BOf c h12 χ.1 => (z : ClassFunction (↥c.H0))) hEq))
      _ = (BOf c h12 χ.1).card := Fintype.card_coe (BOf c h12 χ.1)
  have hLle : L.card ≤ 3 := le_trans hLleB hBle
  rcases orbit_card_is_pow_two_local c h12 ν with ⟨k, hk⟩
  have hk_le : k ≤ 1 := by
    by_contra hknot
    have h2 : 2 ≤ k := by omega
    have h4 : 4 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) h2
    have hL4 : 4 ≤ L.card := by
      change 4 ≤ (orbit c.H0 c.U ν.1).card
      rwa [← hk] at h4
    omega
  have hLcard : L.card = 1 ∨ L.card = 2 := by
    have hkEq : k = 0 ∨ k = 1 := by omega
    rcases hkEq with hk0 | hk1
    · left
      rw [hk0] at hk
      simpa [L] using hk
    · right
      rw [hk1] at hk
      simpa [L] using hk
  rcases hLcard with hL1 | hL2
  · -- singleton orbit: parity kills it
    have hpar := mult_minus_tilde_mul_card_even c h12 hSC χ.1 hχpm ν
    have hd : CongruentModTwo (a ν - e ν) 0 := by
      have h' : CongruentModTwo ((L.card : ℂ) * (a ν - e ν)) 0 := by
        simpa [a, e, L] using hpar
      rw [hL1] at h'
      simpa using h'
    have hde : CongruentModTwo (0 - e ν) 0 := by simpa [a, haν0] using hd
    rcases BOf_scalar_eq_pm_one c h12 hχpm hνB with he1 | hem1
    · have hc : CongruentModTwo (1 : ℂ) 0 := by
        have hneg := CongruentModTwo.neg hde
        simpa [e, he1] using hneg
      exact (CongruentModTwo.not_zero_of_odd_nat (n := 1) (by norm_num))
        (by simpa using hc.symm)
    · have hc : CongruentModTwo (1 : ℂ) 0 := by
        simpa [e, hem1] using hde
      exact (CongruentModTwo.not_zero_of_odd_nat (n := 1) (by norm_num))
        (by simpa using hc.symm)
  · -- two-element orbit
    by_cases hfix : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1
    · -- fixed member: the two tildes are disjoint, but χ occurs in both
      have hνx : ν.1 ∈ L := orbit_self_mem c.H0 c.U ν.1
      have hpos : 0 < (L.erase ν.1).card := by
        rw [Finset.card_erase_of_mem hνx, hL2]
        norm_num
      obtain ⟨a, ha_erase⟩ := Finset.card_pos.mp hpos
      have ha_ne : a ≠ ν.1 := (Finset.mem_erase.mp ha_erase).1
      have haL : a ∈ L := (Finset.mem_erase.mp ha_erase).2
      let μ0 : Irr (↥c.H0) := ⟨a, orbit_mem_isIrreducible c.H0 c.U ν.2 haL⟩
      have hμ0L : μ0.1 ∈ L := haL
      have hμ0ν : μ0 ≠ ν := by
        intro hEq
        apply ha_ne
        exact congrArg Subtype.val hEq
      have hμ0B : μ0 ∈ BOf c h12 χ.1 := hLsubB μ0 hμ0L
      have hνs_ne_μ0 : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ μ0.1 := by
        rw [hfix]
        change ↑ν ≠ a
        exact ha_ne.symm
      have hνμ0 : ν.1 ≠ μ0.1 := by
        intro hEq
        apply hμ0ν
        apply Subtype.ext
        exact hEq.symm
      have hdisj : Theory.Character.Disjoint (tildeNu c h12 μ0) (tildeNu c h12 ν) :=
        tildeNu_disjoint c h12 (μ := μ0) (ν := ν) hμ0L hνμ0 hνs_ne_μ0
      have hχν : scalarProduct G χ.1 (tildeNu c h12 ν) ≠ 0 :=
        (BOf_mem_iff c h12 χ.1 ν).1 hνB
      have hχμ : scalarProduct G χ.1 (tildeNu c h12 μ0) ≠ 0 :=
        (BOf_mem_iff c h12 χ.1 μ0).1 hμ0B
      exact hχν (hdisj χ.1 χ.2 hχμ)
    · -- non-fixed member: `ν^s = l·ν` with `l(t) = -1`; `(vi)` gives a
      -- contradiction at `t`
      rcases Finset.mem_image.mp hνs with ⟨l, hl, hEq⟩
      have hlt := lambda_mover_eval_t_neg_one c h12 hEq.symm hL2 hfix
      let νs : Irr (↥c.H0) := conjIrr c h12 ν
      have hνsB : νs ∈ BOf c h12 χ.1 := hLsubB νs (by
        have hmem : (conjIrr c h12 ν).1 ∈ orbit c.H0 c.U ν.1 := by
          simpa [conjIrr_coe] using hνs
        simpa [νs, L] using hmem)
      have hνssne : conjChar c.H0 (s_normalizes_H0 c h12) νs.1 ≠ νs.1 := by
        have hνs_coe : νs.1 = conjChar c.H0 (s_normalizes_H0 c h12) ν.1 := by
          simpa [νs, conjIrr_coe]
        rw [hνs_coe]
        change conjChar c.H0 (s_normalizes_H0 c h12)
          (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) ≠
            conjChar c.H0 (s_normalizes_H0 c h12) ν.1
        rw [conjChar_conjChar_local c h12 ν.1]
        exact fun h => hfix h.symm
      have hνscard : (orbit c.H0 c.U νs.1).card = 2 := by
        have hνs_coe : νs.1 = conjChar c.H0 (s_normalizes_H0 c h12) ν.1 := by
          simpa [νs, conjIrr_coe]
        rw [hνs_coe]
        rw [orbit_conjChar_eq_local c h12 ν]
        rw [Finset.card_image_of_injOn]
        · simpa [L] using hL2
        · intro x hx y hy hEq'
          exact conjChar_injective_local c h12 hEq'
      have hνsL : ¬ ((orbit c.H0 c.U νs.1).card = 4 ∧
          conjChar c.H0 (s_normalizes_H0 c h12) νs.1 ∈ orbit c.H0 c.U νs.1) := by
        intro h
        omega
      have hnt : tildeNu c h12 ν c.t = 2 * ν.1 (tH0 c) :=
        tildeNu_at_t c h12 hfix
          (by
            intro h
            have hcard2 : (orbit c.H0 c.U ν.1).card = 2 := by simpa [L] using hL2
            have hcard4 : (orbit c.H0 c.U ν.1).card = 4 := h.1
            omega)
      have hnst : tildeNu c h12 νs c.t = 2 * νs.1 (tH0 c) := by
        have h := tildeNu_at_t c h12 hνssne hνsL
        simpa [νs] using h
      have he : scalarProduct G χ.1 (tildeNu c h12 ν) = 1 ∨
          scalarProduct G χ.1 (tildeNu c h12 ν) = -1 :=
        BOf_scalar_eq_pm_one c h12 hχpm hνB
      let ee : ℂ := scalarProduct G χ.1 (tildeNu c h12 ν)
      have hχt1 : χ.1 c.t = ee * (2 * ν.1 (tH0 c)) := by
        have hchi := chi_eq_smul_tildeNu_local c h12 hχpm hfix hνB
        have h' := congrFun hchi c.t
        simpa [ee, smul_eq_mul, hnt] using h'
      have hχt2 : χ.1 c.t = ee * (2 * νs.1 (tH0 c)) := by
        have hchi := chi_eq_smul_tildeNu_local c h12 hχpm hνssne hνsB
        have h' := congrFun hchi c.t
        have heeq : scalarProduct G χ.1 (tildeNu c h12 νs) = ee := by
          simpa [ee, νs, tildeNu_invariance c h12 ν]
        simpa [ee, smul_eq_mul, heeq, hnst] using h'
      have hνst : νs.1 (tH0 c) = -ν.1 (tH0 c) := by
        have hval : (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) (tH0 c) =
            -ν.1 (tH0 c) := by
          calc
            (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) (tH0 c)
                = (LambdaChar l.1 * ν.1) (tH0 c) := by rw [hEq]
            _ = (l.1 (tH0 c) : ℂ) * ν.1 (tH0 c) := by simp [LambdaChar]
            _ = -1 * ν.1 (tH0 c) := by rw [hlt]
            _ = -ν.1 (tH0 c) := by ring
        simpa [νs, conjIrr_coe] using hval
      have hνt0 : ν.1 (tH0 c) = 0 := by
        have hcomb : ee * (2 * ν.1 (tH0 c)) = ee * (2 * νs.1 (tH0 c)) :=
          hχt1.symm.trans hχt2
        have hcomb' : ee * (2 * ν.1 (tH0 c)) = ee * (2 * (-ν.1 (tH0 c))) := by
          simpa [hνst] using hcomb
        have hmain : (4 : ℂ) * ee * ν.1 (tH0 c) = 0 := by
          calc
            (4 : ℂ) * ee * ν.1 (tH0 c)
                = ee * (2 * ν.1 (tH0 c)) - ee * (2 * (-ν.1 (tH0 c))) := by ring
            _ = 0 := by rw [hcomb']; ring
        have hee_ne : ee ≠ 0 := by
          rcases he with h | h <;> simp [ee, h]
        have h1 : ee * ν.1 (tH0 c) = 0 := by
          have h2 : (4 : ℂ) * (ee * ν.1 (tH0 c)) = 0 := by
            simpa [mul_assoc] using hmain
          exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
        exact (mul_eq_zero.mp h1).resolve_left hee_ne
      have hνt_ne : ν.1 (tH0 c) ≠ 0 :=
        char_apply_central_ne_zero (G := ↥c.H0) (t := tH0 c)
          (by simpa [tH0] using t_central_H0' c) (t_H0_sq c) ν.2
      exact hνt_ne hνt0

/-- If `ν ∈ B(χ)` with `ν^s ∈ Λν`, then some member of its `Λ`-orbit has
nonzero multiplicity in `χ|_{H0}`. -/
private lemma exists_positive_multiplicity_in_orbit (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (χ : Irr G) {ν : Irr (↥c.H0)}
    (hνB : ν ∈ BOf c h12 χ.1)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈ orbit c.H0 c.U ν.1) :
    ∃ μ : Irr (↥c.H0), μ.1 ∈ orbit c.H0 c.U ν.1 ∧
      scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ.1 (y : G)) μ.1 ≠ 0 := by
  classical
  let a : Irr (↥c.H0) → ℂ := fun ξ =>
    scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ.1 (y : G)) ξ.1
  let e : Irr (↥c.H0) → ℂ := fun ξ => scalarProduct G χ.1 (tildeNu c h12 ξ)
  have hχpm : IsPMIrr G χ.1 := Or.inl χ.2
  by_cases haν : a ν ≠ 0
  · exact ⟨ν, orbit_self_mem c.H0 c.U ν.1, haν⟩
  · have haν0 : a ν = 0 := by
      by_contra h
      exact haν h
    by_cases hLsubB : ∀ μ : Irr (↥c.H0), μ.1 ∈ orbit c.H0 c.U ν.1 →
        μ ∈ BOf c h12 χ.1
    · exfalso
      exact orbit_subset_BOf_zero_mult_false c h12 hSC χ hνB hνs hLsubB haν0
    · push_neg at hLsubB
      rcases hLsubB with ⟨μ, hμL, hμBnot⟩
      have heμ : e μ = 0 := by
        by_contra hne
        exact hμBnot ((BOf_mem_iff c h12 χ.1 μ).2 hne)
      rcases BOf_scalar_eq_pm_one c h12 hχpm hνB with he1 | hem1
      · have hd := mult_minus_tilde_orbit_eq c h12
          (isClassFunction_of_isGeneralizedCharacter
            (isGeneralizedCharacter_of_isPMIrr_local hχpm)) hμL
        have haμ : a μ = -1 := by
          -- aμ - eμ = aν - eν = 0 - 1
          have h' : a μ - e μ = a ν - e ν := by simpa [a, e] using hd
          simpa [a, e, heμ, haν0, he1] using h'
        have haμ_ne : a μ ≠ 0 := by
          intro h0
          rcases restrict_mult_nat c h12 χ μ with ⟨r, hr⟩
          have hc : (r : ℂ) = (-1 : ℂ) := by
            rw [hr]
            simpa [a] using haμ
          have hre : (r : ℝ) = -1 := by exact_mod_cast hc
          have hnonneg : 0 ≤ (r : ℝ) := by exact_mod_cast (Nat.zero_le r)
          nlinarith
        exact ⟨μ, hμL, by simpa [a] using haμ_ne⟩
      · have hd := mult_minus_tilde_orbit_eq c h12
          (isClassFunction_of_isGeneralizedCharacter
            (isGeneralizedCharacter_of_isPMIrr_local hχpm)) hμL
        have haμ : a μ = 1 := by
          have h' : a μ - e μ = a ν - e ν := by simpa [a, e] using hd
          simpa [a, e, heμ, haν0, hem1] using h'
        have haμ_ne : a μ ≠ 0 := by
          intro h0
          rcases restrict_mult_nat c h12 χ μ with ⟨r, hr⟩
          have hc : (r : ℂ) = (1 : ℂ) := by
            rw [hr]
            simpa [a] using haμ
          have hr1 : r = 1 := by exact_mod_cast hc
          have hr0c : (r : ℂ) = 0 := by
            rw [hr]
            simpa [a] using h0
          have hr0 : r = 0 := by exact_mod_cast hr0c
          omega
        exact ⟨μ, hμL, by simpa [a] using haμ_ne⟩

/-- If every constituent of `χ|_{H0}` with nonzero multiplicity had
`K ≤ ker`, then `χ` would be constant on `K`, contradicting `hK`. -/
private lemma exists_constituent_not_in_kernel (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (χ : Irr G) (hK : ¬ c.K ≤ charKernel (isCharacter_of_isIrreducibleCharacter χ.2)) :
    ∃ μ : Irr (↥c.H0),
      scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ.1 (y : G)) μ.1 ≠ 0 ∧
        ¬ c.K ≤ (charKernel (isCharacter_of_isIrreducibleCharacter μ.2)).map
          (Subgroup.subtype c.H0) := by
  classical
  by_contra h
  let a : Irr (↥c.H0) → ℂ := fun ξ =>
    scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ.1 (y : G)) ξ.1
  have hKle : ∀ μ : Irr (↥c.H0), a μ ≠ 0 →
      c.K ≤ (charKernel (isCharacter_of_isIrreducibleCharacter μ.2)).map
        (Subgroup.subtype c.H0) := by
    intro μ hne
    by_contra hnot
    exact h ⟨μ, hne, hnot⟩
  let χH0 : ClassFunction (↥c.H0) := fun y : ↥c.H0 => χ.1 (y : G)
  have hχH0g : IsGeneralizedCharacter χH0 :=
    isGeneralizedCharacter_restrict c.H0
      (isGeneralizedCharacter_of_isPMIrr_local (Or.inl χ.2))
  have hconst : ∀ k : G, k ∈ c.K → χ.1 k = χ.1 1 := by
    intro k hk
    let kH : ↥c.H0 := ⟨k, U_le_H0 c (K_le_U c hk)⟩
    have hfourier_k : χ.1 k = ∑ ν : Irr (↥c.H0), a ν * ν.1 kH := by
      have h := classFunction_eq_sum_irr_coeffs (G := ↥c.H0) (φ := χH0) hχH0g kH
      simpa [a, χH0, kH] using h
    have hfourier_1 : χ.1 1 = ∑ ν : Irr (↥c.H0), a ν * ν.1 (1 : ↥c.H0) := by
      have h := classFunction_eq_sum_irr_coeffs (G := ↥c.H0) (φ := χH0) hχH0g (1 : ↥c.H0)
      simpa [a, χH0] using h
    rw [hfourier_k, hfourier_1]
    refine Finset.sum_congr rfl ?_
    intro ν hν
    by_cases hne : a ν = 0
    · simp [hne]
    · have hνk : ν.1 kH = ν.1 (1 : ↥c.H0) := by
        have hmem := hKle ν hne hk
        rcases Subgroup.mem_map.mp hmem with ⟨u, hu, hEq⟩
        have huEq : u = kH := by
          apply Subtype.ext
          exact hEq
        have hu' : u ∈ charKernel (isCharacter_of_isIrreducibleCharacter ν.2) := hu
        rw [huEq] at hu'
        exact (mem_charKernel_of_irr_iff ν.2 kH).1 hu'
      rw [hνk]
  apply hK
  rw [le_charKernel_of_irr_iff χ.2 c.K]
  intro k
  exact hconst (k : G) k.2

/-- The sum of degrees over the `Irr(H0)` members of a `Λ`-orbit equals the
orbit sum of degrees. -/
private lemma sum_irr_orbit_degree_eq (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (μ : Irr (↥c.H0)) :
    (∑ ν ∈ Finset.univ.filter (fun ν : Irr (↥c.H0) =>
        ν.1 ∈ orbit c.H0 c.U μ.1), ν.1 1) =
      ∑ μ0 ∈ orbit c.H0 c.U μ.1, μ0 1 := by
  classical
  symm
  refine Finset.sum_bij (fun μ0 hμ0 =>
      (⟨μ0, orbit_mem_isIrreducible c.H0 c.U μ.2 hμ0⟩ : Irr (↥c.H0))) ?_ ?_ ?_ ?_
  · intro μ0 hμ0
    simp [hμ0]
  · intro a ha b hb hEq
    exact congrArg Subtype.val hEq
  · intro ν hν
    have hmem : ν.1 ∈ orbit c.H0 c.U μ.1 := (Finset.mem_filter.mp hν).2
    refine ⟨ν.1, hmem, ?_⟩
    exact Subtype.ext rfl
  · intro μ0 hμ0
    rfl

/-- `s`-conjugation of `H0`-irreducibles sends the `Λ`-orbit of `α` to the
`Λ`-orbit of `α^s`. -/
private lemma orbit_conjIrr_eq_orbitOfAlpha (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (α : Irr (↥c.U)) (μ : Irr (↥c.H0))
    (hOrbit : orbit c.H0 c.U μ.1 = orbitOfAlpha c h12 hSC α) :
    orbit c.H0 c.U (conjIrr c h12 μ).1 =
      orbitOfAlpha c h12 hSC (conjIrrS c c.s_mem_S α) := by
  classical
  apply orbitOfAlpha_unique c h12 hSC (conjIrrS c c.s_mem_S α)
  constructor
  · exact ⟨conjIrr c h12 μ, rfl⟩
  · intro ν hν
    have hνOrb : ν ∈ orbit c.H0 c.U (conjIrr c h12 μ).1 := hν
    have hνOrb' : ν ∈ orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) μ.1) := by
      simpa [conjIrr_coe] using hνOrb
    have hIm := orbit_conjChar_eq_local c h12 μ.1
    rcases Finset.mem_image.mp (by simpa [hIm] using hνOrb') with ⟨ξ, hξ, hEq⟩
    calc
      restrictU c h12 ν = restrictU c h12 (conjChar c.H0 (s_normalizes_H0 c h12) ξ) := by
            rw [← hEq]
      _ =
          conjChar c.U (fun x : ↥c.U =>
            S_normalizes_U c c.s c.s_mem_S x.1 x.2) (restrictU c h12 ξ) :=
            restrictU_conjChar_local c h12 ξ
      _ = conjChar c.U (fun x : ↥c.U =>
            S_normalizes_U c c.s c.s_mem_S x.1 x.2) (∑ β ∈ s0Orbit c α, β.1) := by
            rw [(orbitOfAlpha_spec c h12 hSC α).2 ξ (by simpa [← hOrbit] using hξ)]
      _ = ∑ β ∈ s0Orbit c (conjIrrS c c.s_mem_S α), β.1 :=
            s0Orbit_conjIrrS_local c hSC α

/-- If the orbit of `ν` is `s`-invariant, so is the orbit of `ν^s`. -/
private lemma orbit_sInvariant_of_conj_orbit (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {ν : ClassFunction (↥c.H0)}
    (hInv : ∀ ξ ∈ orbit c.H0 c.U ν,
      conjChar c.H0 (s_normalizes_H0 c h12) ξ ∈ orbit c.H0 c.U ν) :
    ∀ ξ ∈ orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν),
      conjChar c.H0 (s_normalizes_H0 c h12) ξ ∈
        orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν) := by
  classical
  intro ξ hξ
  have hEq : orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν) =
      (orbit c.H0 c.U ν).image (fun μ =>
        conjChar c.H0 (s_normalizes_H0 c h12) μ) :=
    orbit_conjChar_eq_local c h12 ν
  have hξ' : ξ ∈ (orbit c.H0 c.U ν).image (fun μ =>
      conjChar c.H0 (s_normalizes_H0 c h12) μ) := by
    simpa [hEq] using hξ
  rcases Finset.mem_image.mp hξ' with ⟨η, hη, rfl⟩
  have htarget : conjChar c.H0 (s_normalizes_H0 c h12)
      (conjChar c.H0 (s_normalizes_H0 c h12) η) ∈
      (orbit c.H0 c.U ν).image (fun μ =>
        conjChar c.H0 (s_normalizes_H0 c h12) μ) := by
    refine Finset.mem_image.mpr ⟨conjChar c.H0 (s_normalizes_H0 c h12) η,
      hInv η hη, ?_⟩
    rw [conjChar_conjChar_local c h12 η]
  simpa [hEq] using htarget

/-- `(φ, ψ^s) = (φ^s, ψ)` for arbitrary class functions of `H0`. -/
private lemma s_inv_normalizes_H0_local (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (y : ↥c.H0) : c.s⁻¹ * (y : G) * c.s ∈ c.H0 := by
  have hsq : c.s⁻¹ = c.s := by
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using c.s_involution.2)
  have hx : c.s * (y : G) * c.s⁻¹ ∈ c.H0 := s_normalizes_H0 c h12 y
  simpa [hsq] using hx

private lemma scalarProduct_conjChar_eq_local (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (φ ψ : ClassFunction (↥c.H0)) :
    scalarProduct (↥c.H0) φ (conjChar c.H0 (s_normalizes_H0 c h12) ψ) =
      scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) φ) ψ := by
  classical
  unfold scalarProduct
  congr 1
  refine Finset.sum_bij
    (fun x : ↥c.H0 => fun _ : x ∈ (Finset.univ : Finset (↥c.H0)) =>
      ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩) ?_ ?_ ?_ ?_
  · intro x hx
    simp
  · intro a ha b hb hEq
    apply Subtype.ext
    have hEq' : c.s * (a : G) * c.s⁻¹ = c.s * (b : G) * c.s⁻¹ := congrArg Subtype.val hEq
    have hss : c.s * c.s = 1 := by simpa [pow_two] using c.s_involution.2
    have hs' : c.s⁻¹ = c.s := inv_eq_of_mul_eq_one_right hss
    calc
      (a : G) = 1 * (a : G) * 1 := by simp
      _ = (c.s * c.s) * (a : G) * (c.s * c.s) := by rw [hss]
      _ = c.s * (c.s * (a : G) * c.s⁻¹) * c.s := by
            rw [hs']
            group
      _ = c.s * (c.s * (b : G) * c.s⁻¹) * c.s := by rw [hEq']
      _ = (b : G) := by
            calc
              c.s * (c.s * (b : G) * c.s⁻¹) * c.s = c.s * (c.s * (b : G) * c.s) * c.s := by rw [hs']
              _ = (c.s * c.s) * (b : G) * (c.s * c.s) := by group
              _ = 1 * (b : G) * 1 := by rw [hss]
              _ = (b : G) := by simp
  · intro y hy
    refine ⟨⟨c.s⁻¹ * (y : G) * c.s, s_inv_normalizes_H0_local c h12 y⟩, by simp, ?_⟩
    apply Subtype.ext
    have hss : c.s * c.s = 1 := by simpa [pow_two] using c.s_involution.2
    have hs' : c.s⁻¹ = c.s := inv_eq_of_mul_eq_one_right hss
    calc
      c.s * (c.s⁻¹ * (y : G) * c.s) * c.s⁻¹ = c.s * (c.s * (y : G) * c.s⁻¹) * c.s⁻¹ := by
            rw [hs']
      _ = (y : G) := by
            rw [hs']
            calc
              c.s * (c.s * (y : G) * c.s) * c.s = (c.s * c.s) * (y : G) * (c.s * c.s) := by group
              _ = 1 * (y : G) * 1 := by rw [hss]
              _ = (y : G) := by simp
  · intro x hx
    have hss : c.s * c.s = 1 := by simpa [pow_two] using c.s_involution.2
    have hs' : c.s⁻¹ = c.s := inv_eq_of_mul_eq_one_right hss
    simp only [conjChar]
    congr 1
    apply congrArg (φ : ↥c.H0 → ℂ)
    apply Subtype.ext
    change (x : G) = c.s * (c.s * (x : G) * c.s⁻¹) * c.s⁻¹
    rw [hs']
    have hmain : c.s * (c.s * (x : G) * c.s) * c.s = (x : G) := by
      calc
        c.s * (c.s * (x : G) * c.s) * c.s = (c.s * c.s) * (x : G) * (c.s * c.s) := by group
        _ = 1 * (x : G) * 1 := by rw [hss]
        _ = (x : G) := by simp
    rw [hmain]

/-- Restriction multiplicities are invariant under `s`-conjugation: the
restricted irreducible character `χ|_{H0}` is an `s`-class function. -/
private lemma restrict_scalarProduct_conjChar_eq (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (χ : Irr G) (ν : ClassFunction (↥c.H0)) :
    scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ.1 (y : G))
        (conjChar c.H0 (s_normalizes_H0 c h12) ν) =
      scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ.1 (y : G)) ν := by
  classical
  let φ : ClassFunction (↥c.H0) := fun y : ↥c.H0 => χ.1 (y : G)
  have hφcls : IsClassFunction χ.1 :=
    isCharacter_isClassFunction (isCharacter_of_isIrreducibleCharacter χ.2)
  have hself : conjChar c.H0 (s_normalizes_H0 c h12) φ = φ := by
    funext y
    change χ.1 (c.s * (y : G) * c.s⁻¹) = χ.1 (y : G)
    exact hφcls (y : G) c.s
  calc
    scalarProduct (↥c.H0) φ (conjChar c.H0 (s_normalizes_H0 c h12) ν) =
        scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) φ) ν :=
          scalarProduct_conjChar_eq_local c h12 φ ν
    _ = scalarProduct (↥c.H0) φ ν := by rw [hself]

/-- Lemma 3.6: if `χ ∈ Irr(G)` with `B(χ)` not empty and `K ⊄ Ker(χ)`, and
`ν^s ∈ Λν` for every `ν ∈ B(χ)`, then for some `α ∈ Irr(U)`,
`K ⊄ Ker(α)` and `χ(1) > 2m·α(1)`. -/
public theorem lemma_3_6 (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (χ : Irr G) (hB : (BOf c h12 χ.1).Nonempty)
    (hK : ¬ c.K ≤ charKernel (isCharacter_of_isIrreducibleCharacter χ.2))
    (hνs : ∀ ν : Irr (↥c.H0), ν ∈ BOf c h12 χ.1 →
      conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈ orbit c.H0 c.U ν.1) :
    ∃ α : Irr (↥c.U),
      ¬ c.K ≤ (charKernel (isCharacter_of_isIrreducibleCharacter α.2)).map
          (Subgroup.subtype c.U) ∧
        (2 * (c.U.subgroupOf c.H0).index : ℝ) * (α.1 1).re < (χ.1 1).re := by
  classical
  let a : Irr (↥c.H0) → ℂ := fun ξ =>
    scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ.1 (y : G)) ξ.1
  let χH0 : ClassFunction (↥c.H0) := fun y : ↥c.H0 => χ.1 (y : G)
  have hχH0g : IsGeneralizedCharacter χH0 :=
    isGeneralizedCharacter_restrict c.H0
      (isGeneralizedCharacter_of_isPMIrr_local (Or.inl χ.2))
  have hχcls : IsClassFunction χ.1 :=
    isCharacter_isClassFunction (isCharacter_of_isIrreducibleCharacter χ.2)
  rcases exists_constituent_not_in_kernel c h12 χ hK with ⟨μ, hμne, hKμ⟩
  rcases orbit_is_orbitOfAlpha c h12 hSC μ with ⟨α, hOrbit⟩
  have hKα : ¬ c.K ≤ (charKernel (isCharacter_of_isIrreducibleCharacter α.2)).map
      (Subgroup.subtype c.U) := by
    intro hle
    exact hKμ (orbit_mem_kernel_le_of_orbitOfAlpha c h12 hSC α μ hOrbit hle)
  have hα_moved : ∀ x : G, ∀ hxS : x ∈ (c.S : Subgroup G),
      x ∉ (c.S0 : Subgroup G) → conjIrrS c hxS α ≠ α := by
    intro x hxS hxnot hfix
    exact hKα (fixed_reflection_ker_core c hxS hxnot α hfix)
  have hstab_le : stabilizerS c α ≤ (c.S0 : Subgroup G) := by
    intro x hx
    by_contra hxnot
    exact hα_moved (x : G) hx.1 hxnot hx.2
  have hNotInv1 : ¬ (∀ ν : ClassFunction (↥c.H0),
      ν ∈ orbitOfAlpha c h12 hSC α →
        conjChar c.H0 (s_normalizes_H0 c h12) ν ∈ orbitOfAlpha c h12 hSC α) := by
    intro hfixed
    exact ((orbitOfAlpha_fixed_iff c h12 hSC α).mp hfixed) hstab_le
  let μs : Irr (↥c.H0) := conjIrr c h12 μ
  let αs : Irr (↥c.U) := conjIrrS c c.s_mem_S α
  have hμs_coe : μs.1 = conjChar c.H0 (s_normalizes_H0 c h12) μ.1 := by
    simpa [μs, conjIrr_coe]
  have hOrbit2 : orbit c.H0 c.U μs.1 = orbitOfAlpha c h12 hSC αs := by
    simpa [μs, αs] using orbit_conjIrr_eq_orbitOfAlpha c h12 hSC α μ hOrbit
  have hOrbit_ne : orbit c.H0 c.U μs.1 ≠ orbit c.H0 c.U μ.1 := by
    intro hEq
    have hμs_in : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 ∈
        orbit c.H0 c.U μ.1 := by
      have hmem : μs.1 ∈ orbit c.H0 c.U μ.1 := by
        rw [← hEq]
        exact orbit_self_mem c.H0 c.U μs.1
      simpa [hμs_coe] using hmem
    have hInv1 := orbit_sInvariant_of_mem c h12 hμs_in
    have hfixed : ∀ ν : ClassFunction (↥c.H0),
        ν ∈ orbitOfAlpha c h12 hSC α →
          conjChar c.H0 (s_normalizes_H0 c h12) ν ∈ orbitOfAlpha c h12 hSC α := by
      intro ν hν
      have hν' : ν ∈ orbit c.H0 c.U μ.1 := by simpa [hOrbit] using hν
      have hc := hInv1 ν hν'
      simpa [hOrbit] using hc
    exact hNotInv1 hfixed
  have hOrbit1_notB : ∀ ν : Irr (↥c.H0), ν.1 ∈ orbit c.H0 c.U μ.1 →
      ν ∉ BOf c h12 χ.1 := by
    intro ν hν hνB
    have hfixν := hνs ν hνB
    have horbit_eq : orbit c.H0 c.U ν.1 = orbit c.H0 c.U μ.1 :=
      orbit_eq_of_mem' c hν
    have hμs_in_orbitν : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 ∈
        orbit c.H0 c.U ν.1 :=
      orbit_sInvariant_of_mem c h12 hfixν μ.1 (by
        rw [horbit_eq]
        exact orbit_self_mem c.H0 c.U μ.1)
    have hμs_in_orbitμ : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 ∈
        orbit c.H0 c.U μ.1 := by
      rwa [horbit_eq] at hμs_in_orbitν
    have hInv1 := orbit_sInvariant_of_mem c h12 hμs_in_orbitμ
    have hfixed : ∀ ξ : ClassFunction (↥c.H0),
        ξ ∈ orbitOfAlpha c h12 hSC α →
          conjChar c.H0 (s_normalizes_H0 c h12) ξ ∈ orbitOfAlpha c h12 hSC α := by
      intro ξ hξ
      have hξ' : ξ ∈ orbit c.H0 c.U μ.1 := by simpa [hOrbit] using hξ
      have hc := hInv1 ξ hξ'
      simpa [hOrbit] using hc
    exact hNotInv1 hfixed
  have hOrbit2_notB : ∀ ν : Irr (↥c.H0), ν.1 ∈ orbit c.H0 c.U μs.1 →
      ν ∉ BOf c h12 χ.1 := by
    intro ν hν hνB
    have hfixν := hνs ν hνB
    have horbit_eq : orbit c.H0 c.U ν.1 = orbit c.H0 c.U μs.1 :=
      orbit_eq_of_mem' c hν
    have hμ_in_orbitν : conjChar c.H0 (s_normalizes_H0 c h12) μs.1 ∈
        orbit c.H0 c.U ν.1 :=
      orbit_sInvariant_of_mem c h12 hfixν μs.1 (by
        rw [horbit_eq]
        exact orbit_self_mem c.H0 c.U μs.1)
    have hμ_in_orbitμs : conjChar c.H0 (s_normalizes_H0 c h12) μs.1 ∈
        orbit c.H0 c.U μs.1 := by
      rwa [horbit_eq] at hμ_in_orbitν
    have hInv2 : ∀ ξ ∈ orbit c.H0 c.U μs.1,
        conjChar c.H0 (s_normalizes_H0 c h12) ξ ∈ orbit c.H0 c.U μs.1 :=
      orbit_sInvariant_of_mem c h12 hμ_in_orbitμs
    have hInv1 : ∀ ξ ∈ orbit c.H0 c.U μ.1,
        conjChar c.H0 (s_normalizes_H0 c h12) ξ ∈ orbit c.H0 c.U μ.1 := by
      have hInv := orbit_sInvariant_of_conj_orbit c h12 hInv2
      have hOrbEq : orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) μs.1) =
          orbit c.H0 c.U μ.1 := by
        rw [show conjChar c.H0 (s_normalizes_H0 c h12) μs.1 = μ.1 by
          simpa [hμs_coe] using (conjChar_conjChar_local c h12 μ.1)]
      intro ξ hξ
      have hc := hInv ξ (by simpa [hOrbEq] using hξ)
      simpa [hOrbEq] using hc
    have hfixed : ∀ ξ : ClassFunction (↥c.H0),
        ξ ∈ orbitOfAlpha c h12 hSC α →
          conjChar c.H0 (s_normalizes_H0 c h12) ξ ∈ orbitOfAlpha c h12 hSC α := by
      intro ξ hξ
      have hξ' : ξ ∈ orbit c.H0 c.U μ.1 := by simpa [hOrbit] using hξ
      have hc := hInv1 ξ hξ'
      simpa [hOrbit] using hc
    exact hNotInv1 hfixed
  rcases restrict_mult_nat c h12 χ μ with ⟨r0, hr0⟩
  have hr0_ne : r0 ≠ 0 := by
    intro h
    apply hμne
    rw [← hr0]
    exact_mod_cast h
  have hr0_pos : 0 < r0 := Nat.pos_of_ne_zero hr0_ne
  have hμB0 : scalarProduct G χ.1 (tildeNu c h12 μ) = 0 := by
    by_contra hne
    exact hOrbit1_notB μ (orbit_self_mem c.H0 c.U μ.1)
      ((BOf_mem_iff c h12 χ.1 μ).2 hne)
  have hMult1 (ν : Irr (↥c.H0)) (hν : ν.1 ∈ orbit c.H0 c.U μ.1) :
      a ν = (r0 : ℂ) := by
    have hνB0 : scalarProduct G χ.1 (tildeNu c h12 ν) = 0 := by
      by_contra hne
      exact hOrbit1_notB ν hν ((BOf_mem_iff c h12 χ.1 ν).2 hne)
    have hsp := orbit_mem_scalarProduct_eq c h12 (hχ := hχcls)
      (μ := μ) (ν := ν) hν hμB0 hνB0
    have hEq : a ν = a μ := by simpa [a] using hsp
    calc
      a ν = a μ := hEq
      _ = (r0 : ℂ) := hr0.symm
  have hμsB0 : scalarProduct G χ.1 (tildeNu c h12 μs) = 0 := by
    by_contra hne
    exact hOrbit2_notB μs (orbit_self_mem c.H0 c.U μs.1)
      ((BOf_mem_iff c h12 χ.1 μs).2 hne)
  have hEqBase : a μs = a μ := by
    simpa [a, μs, hμs_coe] using
      restrict_scalarProduct_conjChar_eq c h12 χ μ.1
  have hMult2 (ν : Irr (↥c.H0)) (hν : ν.1 ∈ orbit c.H0 c.U μs.1) :
      a ν = (r0 : ℂ) := by
    have hνB0 : scalarProduct G χ.1 (tildeNu c h12 ν) = 0 := by
      by_contra hne
      exact hOrbit2_notB ν hν ((BOf_mem_iff c h12 χ.1 ν).2 hne)
    have hsp := orbit_mem_scalarProduct_eq c h12 (hχ := hχcls)
      (μ := μs) (ν := ν) hν hμsB0 hνB0
    have hEq : a ν = a μs := by simpa [a] using hsp
    calc
      a ν = a μs := hEq
      _ = a μ := hEqBase
      _ = (r0 : ℂ) := hr0.symm
  rcases hB with ⟨ν0, hν0B⟩
  rcases exists_positive_multiplicity_in_orbit c h12 hSC χ (ν := ν0) hν0B (hνs ν0 hν0B) with
    ⟨ξ, hξOrbit, hξne⟩
  have hξ_not1 : ξ.1 ∉ orbit c.H0 c.U μ.1 := by
    intro hξ1
    have hOrbEq : orbit c.H0 c.U ξ.1 = orbit c.H0 c.U μ.1 :=
      orbit_eq_of_mem' c hξ1
    have hν0_in_ξ : ν0.1 ∈ orbit c.H0 c.U ξ.1 := by
      rw [orbit_eq_of_mem' c hξOrbit]
      exact orbit_self_mem c.H0 c.U ν0.1
    exact hOrbit1_notB ν0 (by simpa [hOrbEq] using hν0_in_ξ) hν0B
  have hξ_not2 : ξ.1 ∉ orbit c.H0 c.U μs.1 := by
    intro hξ2
    have hOrbEq : orbit c.H0 c.U ξ.1 = orbit c.H0 c.U μs.1 :=
      orbit_eq_of_mem' c hξ2
    have hν0_in_ξ : ν0.1 ∈ orbit c.H0 c.U ξ.1 := by
      rw [orbit_eq_of_mem' c hξOrbit]
      exact orbit_self_mem c.H0 c.U ν0.1
    exact hOrbit2_notB ν0 (by simpa [hOrbEq] using hν0_in_ξ) hν0B
  rcases restrict_mult_nat c h12 χ ξ with ⟨rξ, hrξ⟩
  have hrξ_ne : rξ ≠ 0 := by
    intro h
    apply hξne
    rw [← hrξ]
    exact_mod_cast h
  have hrξ_pos : 0 < rξ := Nat.pos_of_ne_zero hrξ_ne
  let f : Irr (↥c.H0) → ℂ := fun ν => a ν * ν.1 1
  let L1 : Finset (Irr (↥c.H0)) :=
    Finset.univ.filter (fun ν : Irr (↥c.H0) => ν.1 ∈ orbit c.H0 c.U μ.1)
  let L2 : Finset (Irr (↥c.H0)) :=
    Finset.univ.filter (fun ν : Irr (↥c.H0) => ν.1 ∈ orbit c.H0 c.U μs.1)
  let Rest : Finset (Irr (↥c.H0)) :=
    Finset.univ.filter (fun ν : Irr (↥c.H0) =>
      ν.1 ∉ orbit c.H0 c.U μ.1 ∧ ν.1 ∉ orbit c.H0 c.U μs.1)
  have hξRest : ξ ∈ Rest := by
    simp [Rest, hξ_not1, hξ_not2]
  have hχ1 : χ.1 1 = ∑ ν : Irr (↥c.H0), f ν := by
    have h := classFunction_eq_sum_irr_coeffs (G := ↥c.H0) (φ := χH0) hχH0g (1 : ↥c.H0)
    simpa [f, a, χH0] using h
  have hsumL1 : (∑ ν ∈ L1, f ν) =
      (r0 : ℂ) * (∑ μ0 ∈ orbit c.H0 c.U μ.1, μ0 1) := by
    calc
      (∑ ν ∈ L1, f ν) = ∑ ν ∈ L1, (r0 : ℂ) * ν.1 1 := by
            refine Finset.sum_congr rfl ?_
            intro ν hν
            have hfν : f ν = (r0 : ℂ) * ν.1 1 := by
              unfold f
              rw [hMult1 ν (Finset.mem_filter.mp hν).2]
            rw [hfν]
      _ = (r0 : ℂ) * (∑ ν ∈ L1, ν.1 1) := by rw [← Finset.mul_sum]
      _ = (r0 : ℂ) * (∑ μ0 ∈ orbit c.H0 c.U μ.1, μ0 1) := by
            rw [sum_irr_orbit_degree_eq c h12 μ]
  have hsumL2 : (∑ ν ∈ L2, f ν) =
      (r0 : ℂ) * (∑ μ0 ∈ orbit c.H0 c.U μs.1, μ0 1) := by
    calc
      (∑ ν ∈ L2, f ν) = ∑ ν ∈ L2, (r0 : ℂ) * ν.1 1 := by
            refine Finset.sum_congr rfl ?_
            intro ν hν
            have hfν : f ν = (r0 : ℂ) * ν.1 1 := by
              unfold f
              rw [hMult2 ν (Finset.mem_filter.mp hν).2]
            rw [hfν]
      _ = (r0 : ℂ) * (∑ ν ∈ L2, ν.1 1) := by rw [← Finset.mul_sum]
      _ = (r0 : ℂ) * (∑ μ0 ∈ orbit c.H0 c.U μs.1, μ0 1) := by
            rw [sum_irr_orbit_degree_eq c h12 μs]
  have hsplit1 : (∑ ν : Irr (↥c.H0), f ν) =
      (∑ ν ∈ L1, f ν) +
        (∑ ν ∈ Finset.univ.filter (fun ν : Irr (↥c.H0) =>
          ν.1 ∉ orbit c.H0 c.U μ.1), f ν) := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ)
      (p := fun ν : Irr (↥c.H0) => ν.1 ∈ orbit c.H0 c.U μ.1) (f := f)]
  have hsplit2 : (∑ ν ∈ Finset.univ.filter (fun ν : Irr (↥c.H0) =>
        ν.1 ∉ orbit c.H0 c.U μ.1), f ν) =
      (∑ ν ∈ L2, f ν) + (∑ ν ∈ Rest, f ν) := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ.filter (fun ν : Irr (↥c.H0) =>
        ν.1 ∉ orbit c.H0 c.U μ.1))
      (p := fun ν : Irr (↥c.H0) => ν.1 ∈ orbit c.H0 c.U μs.1) (f := f)]
    have hL2eq : (Finset.univ.filter (fun ν : Irr (↥c.H0) =>
        ν.1 ∉ orbit c.H0 c.U μ.1)).filter
          (fun ν : Irr (↥c.H0) => ν.1 ∈ orbit c.H0 c.U μs.1) = L2 := by
      ext ν
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, L2]
      constructor
      · intro h
        exact h.2
      · intro h
        refine ⟨?_, h⟩
        intro h1
        exact hOrbit_ne (by
          have heq1 : orbit c.H0 c.U ν.1 = orbit c.H0 c.U μ.1 := orbit_eq_of_mem' c h1
          have heq2 : orbit c.H0 c.U ν.1 = orbit c.H0 c.U μs.1 := orbit_eq_of_mem' c h
          exact heq2.symm.trans heq1)
    have hRestEq : (Finset.univ.filter (fun ν : Irr (↥c.H0) =>
        ν.1 ∉ orbit c.H0 c.U μ.1)).filter
          (fun ν : Irr (↥c.H0) => ν.1 ∉ orbit c.H0 c.U μs.1) = Rest := by
      ext ν
      simp [Rest, and_assoc, and_left_comm, and_comm]
    rw [hL2eq, hRestEq]
  have hsum_decomp : (∑ ν : Irr (↥c.H0), f ν) =
      (∑ ν ∈ L1, f ν) + (∑ ν ∈ L2, f ν) + (∑ ν ∈ Rest, f ν) := by
    rw [hsplit1, hsplit2]
    abel
  have hdeg1 : (∑ μ0 ∈ orbit c.H0 c.U μ.1, μ0 1) =
      ((c.U.subgroupOf c.H0).index : ℂ) * α.1 1 := by
    rw [hOrbit]
    exact orbitOfAlpha_degree_sum c h12 hSC α
  have hdeg2 : (∑ μ0 ∈ orbit c.H0 c.U μs.1, μ0 1) =
      ((c.U.subgroupOf c.H0).index : ℂ) * αs.1 1 := by
    rw [hOrbit2]
    exact orbitOfAlpha_degree_sum c h12 hSC αs
  have hdegαs : αs.1 1 = α.1 1 := by
    simp [αs, conjIrrS, conjChar]
  let mR : ℝ := (c.U.subgroupOf c.H0).index
  let d : ℝ := (α.1 1).re
  let rR : ℝ := r0
  have hL1re : (∑ ν ∈ L1, f ν).re = rR * mR * d := by
    have hsum : (∑ ν ∈ L1, f ν) =
        (r0 : ℂ) * (((c.U.subgroupOf c.H0).index : ℂ) * α.1 1) := by
      rw [hsumL1, hdeg1]
    rw [hsum]
    simp [Complex.mul_re, mR, d, rR]
    ring
  have hL2re : (∑ ν ∈ L2, f ν).re = rR * mR * d := by
    have hsum : (∑ ν ∈ L2, f ν) =
        (r0 : ℂ) * (((c.U.subgroupOf c.H0).index : ℂ) * αs.1 1) := by
      rw [hsumL2, hdeg2]
    rw [hsum]
    simp [Complex.mul_re, hdegαs, mR, d, rR]
    ring
  have hRest_nonneg : ∀ ν : Irr (↥c.H0), ν ∈ Rest → 0 ≤ (f ν).re := by
    intro ν hν
    rcases restrict_mult_nat c h12 χ ν with ⟨r, hr⟩
    have hf : (f ν).re = (r : ℝ) * (ν.1 1).re := by
      unfold f
      have hEq : a ν = (r : ℂ) := by simpa [a] using hr.symm
      rw [hEq]
      simp [Complex.mul_re]
    rw [hf]
    exact mul_nonneg (by exact_mod_cast (Nat.zero_le r)) (le_of_lt (irr_one_pos ν))
  have hfξpos : 0 < (f ξ).re := by
    have hf : (f ξ).re = (rξ : ℝ) * (ξ.1 1).re := by
      unfold f
      have hEq : a ξ = (rξ : ℂ) := by simpa [a] using hrξ.symm
      rw [hEq]
      simp [Complex.mul_re]
    rw [hf]
    exact mul_pos (by exact_mod_cast hrξ_pos) (irr_one_pos ξ)
  have hRest_lower : (f ξ).re ≤ (∑ ν ∈ Rest, f ν).re := by
    rw [← Finset.add_sum_erase Rest f hξRest]
    rw [Complex.add_re, Complex.re_sum]
    have hnon : 0 ≤ (∑ ν ∈ Rest.erase ξ, (f ν).re) := by
      refine Finset.sum_nonneg ?_
      intro ν hν
      exact hRest_nonneg ν (Finset.mem_of_mem_erase hν)
    nlinarith
  have hsumRest_pos : 0 < (∑ ν ∈ Rest, f ν).re :=
    lt_of_lt_of_le hfξpos hRest_lower
  have hre_sum : (χ.1 1).re =
      (∑ ν ∈ L1, f ν).re + (∑ ν ∈ L2, f ν).re + (∑ ν ∈ Rest, f ν).re := by
    have h := congrArg Complex.re (hχ1.trans hsum_decomp)
    simpa [Complex.add_re, Complex.re_sum] using h
  have hindex_pos : 0 < mR := by
    dsimp [mR]
    exact_mod_cast (Nat.pos_of_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := c.U.subgroupOf c.H0)))
  have hdeg_pos : 0 < d := irr_one_pos α
  have hlt : 2 * mR * d < (χ.1 1).re := by
    have hge : 2 * mR * d ≤ (∑ ν ∈ L1, f ν).re + (∑ ν ∈ L2, f ν).re := by
      rw [hL1re, hL2re]
      have hR1 : (1 : ℝ) ≤ rR := by
        dsimp [rR]
        exact_mod_cast (Nat.succ_le_of_lt hr0_pos)
      have hmul_nonneg : 0 ≤ mR * d :=
        mul_nonneg (le_of_lt hindex_pos) (le_of_lt hdeg_pos)
      have hprod : mR * d ≤ rR * (mR * d) := by nlinarith
      nlinarith
    nlinarith
  refine ⟨α, hKα, ?_⟩
  simpa [mR, d] using hlt

end Section3

end CFSG.BenderGlauberman

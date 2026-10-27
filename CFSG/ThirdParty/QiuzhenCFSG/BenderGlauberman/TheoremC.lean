module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Coherence
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Coherence
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Lemma24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Lemma25
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Lemma25Core
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Remark31
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Remark31
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Lemma33
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Lemma33
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Lemma34
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Lemma34
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Theorem32
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Theorem32
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Lemma36
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section4.Theorem43
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Hyp12OfHyp11
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Remark35
import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.TheoremBProof
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Basic
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Clifford
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Trace
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_1

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Theorem C

This module owns `BenderGlauberman.theorem_C`; `MainStatements.lean` is the
thin public wrapper that re-exports it.

The proof follows the paper's two-case structure:

* `|S| ≥ 8` (paper L851--L977): the character-theoretic argument using the
  proved §2/§3 chain, equations (1)--(7), Lemmas 2.5 and 3.6, and the
  Frobenius degree contradiction.
* `|S| = 4` (paper L1200--L1236): the proved Section-4 component
  classification and reciprocal-degree contradiction.
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

section TheoremC

variable {G : Type u} [Group G] [Finite G]

/-- Hypothesis 1.2 is reconstructed from Hypothesis 1.1 by the reviewed
constructor in `Hyp12OfHyp11`. -/
private noncomputable def theoremC_hyp12 (c : Hyp11 G) [Hyp11KData c] : Hyp12 c :=
  hyp12_of_hyp11 c

/-- Every element of `K₁` is inverted by `t₁` (K-data accessor
`K1_inverted`, repaired in commit 91b4718). -/
private theorem theoremC_K1_inverted (c : Hyp11 G) [Hyp11KData c] {x : G} (hx : x ∈ c.K1) :
    c.t1 * x * c.t1⁻¹ = x⁻¹ := by
  exact c.K1_inverted x hx

/-- Every element of `K₂` is inverted by `t₂` (K-data accessor
`K2_inverted`). -/
private theorem theoremC_K2_inverted (c : Hyp11 G) [Hyp11KData c] {x : G} (hx : x ∈ c.K2) :
    c.t2 * x * c.t2⁻¹ = x⁻¹ := by
  exact c.K2_inverted x hx

/-- Every element of `K = K₁ ∩ K₂` is inverted by `t₁`. -/
private theorem theoremC_K_inverted_by_t1 (c : Hyp11 G) [Hyp11KData c] {x : G} (hx : x ∈ c.K) :
    c.t1 * x * c.t1⁻¹ = x⁻¹ := by
  exact c.K1_inverted x (Subgroup.mem_inf.mp hx).1

/-- Every element of `K = K₁ ∩ K₂` is inverted by `t₂`. -/
private theorem theoremC_K_inverted_by_t2 (c : Hyp11 G) [Hyp11KData c] {x : G} (hx : x ∈ c.K) :
    c.t2 * x * c.t2⁻¹ = x⁻¹ := by
  exact c.K2_inverted x (Subgroup.mem_inf.mp hx).2

/-- Every odd-order subgroup of `H` lies in the odd core `U = O(H)`
(`H = U·S` with `S` a 2-group, so `H/U` is a 2-group). -/
private lemma theoremC_odd_le_U (c : Hyp11 G) [Hyp11KData c] (X : Subgroup G)
    (hXH : X ≤ c.H) (hXodd : Nat.Coprime 2 (Nat.card ↥X)) : X ≤ c.U := by
  intro x hx
  have hxH : x ∈ c.H := hXH hx
  have hUleH : c.U ≤ c.H :=
    SetLike.le_def.1 (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H))
  let BH : Subgroup ↥c.H := (c.U : Subgroup G).subgroupOf c.H
  have : BH.Normal := (Subgroup.normal_subgroupOf_iff hUleH).2 (by
    intro h b hb hh
    exact U_normal_in_H c hh hb)
  let q : ↥c.H →* (↥c.H ⧸ BH) := QuotientGroup.mk' BH
  let xH : ↥c.H := ⟨x, hxH⟩
  have hHset : (↑c.H : Set G) = (c.U : Set G) * (↑(c.S : Subgroup G) : Set G) := by
    rw [← c.H_eq_US]
    exact Subgroup.coe_mul_of_right_le_normalizer_left c.U (c.S : Subgroup G)
      (S_le_normalizer_U c)
  have hx' : x ∈ (c.U : Set G) * (↑(c.S : Subgroup G) : Set G) := by
    rw [← hHset]
    exact hxH
  rcases hx' with ⟨u, hu, s, hs, hEq⟩
  let uH : ↥c.H := ⟨u, hUleH hu⟩
  let sH : ↥c.H := ⟨s, S_le_H c hs⟩
  have hEqH : xH = uH * sH := by
    apply Subtype.ext
    simpa [uH, sH] using hEq.symm
  have hqEq : q xH = q sH := by
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
  have hqpow : q xH ^ (2 ^ (c.m + 1)) = 1 := by
    rw [hqEq, ← map_pow, hs_pow, map_one]
  have hdvd2 : orderOf (q xH) ∣ 2 ^ (c.m + 1) :=
    orderOf_dvd_of_pow_eq_one hqpow
  have hxpow1 : xH ^ orderOf x = 1 := by
    apply Subtype.ext
    change (x : G) ^ orderOf x = 1
    exact pow_orderOf_eq_one x
  have hqpowx : q xH ^ orderOf x = 1 := by
    have hq : q (xH ^ orderOf x) = 1 := by
      simpa using congrArg q hxpow1
    simpa [map_pow] using hq
  have hdvdx : orderOf (q xH) ∣ orderOf x := orderOf_dvd_of_pow_eq_one hqpowx
  have hord_dvd : orderOf x ∣ Nat.card ↥X :=
    Subgroup.orderOf_dvd_natCard X hx
  have hodd : Nat.Coprime 2 (orderOf x) :=
    hXodd.coprime_dvd_right hord_dvd
  have hcop3 : Nat.Coprime (orderOf x) 2 := hodd.symm
  have hcop4 : Nat.Coprime (orderOf x) (2 ^ (c.m + 1)) :=
    Nat.Coprime.pow_right (c.m + 1) hcop3
  have hcopq : Nat.Coprime (orderOf (q xH)) (2 ^ (c.m + 1)) :=
    Nat.Coprime.coprime_dvd_left hdvdx hcop4
  have hord1 : orderOf (q xH) = 1 := Nat.Coprime.eq_one_of_dvd hcopq hdvd2
  have hq1 : q xH = 1 := orderOf_eq_one_iff.mp hord1
  have hxHmem : xH ∈ BH := by
    rw [← QuotientGroup.ker_mk' BH]
    exact MonoidHom.mem_ker.mpr hq1
  exact Subgroup.mem_subgroupOf.mp hxHmem

/-- `K₁ ≤ U`. -/
private lemma theoremC_K1_le_U (c : Hyp11 G) [Hyp11KData c] : c.K1 ≤ c.U :=
  theoremC_odd_le_U c c.K1 c.K1_le_H c.K1_odd

/-- `K₂ ≤ U`. -/
private lemma theoremC_K2_le_U (c : Hyp11 G) [Hyp11KData c] : c.K2 ≤ c.U :=
  theoremC_odd_le_U c c.K2 c.K2_le_H c.K2_odd

/-- `U = O(H)` has odd order. -/
private lemma theoremC_U_coprime_two (c : Hyp11 G) [Hyp11KData c] : Nat.Coprime 2 (Nat.card ↥c.U) := by
  have h1 : Nat.card ↥c.U = Nat.card (pPrimeCore 2 c.H) := by
    dsimp [Hyp11.U]
    rw [oddCoreOf]
    exact Subgroup.card_map_of_injective (f := c.H.subtype)
      (K := pPrimeCore 2 c.H) (Subgroup.subtype_injective c.H)
  rw [h1]
  exact pPrimeCore_coprime_card (p := 2) (G := c.H)

/-- `K = K₁ ∩ K₂` has odd order. -/
private lemma theoremC_K_odd (c : Hyp11 G) [Hyp11KData c] : Nat.Coprime 2 (Nat.card ↥c.K) := by
  have hdiv : Nat.card ↥c.K ∣ Nat.card ↥c.K1 :=
    Subgroup.card_dvd_of_le (inf_le_left : c.K ≤ c.K1)
  exact c.K1_odd.coprime_dvd_right hdiv

/-- `K ≤ U`. -/
private lemma theoremC_K_le_U (c : Hyp11 G) [Hyp11KData c] : c.K ≤ c.U := by
  have hK1 : c.K ≤ c.K1 := inf_le_left
  have hKH : c.K ≤ c.H := le_trans hK1 c.K1_le_H
  have hKodd := theoremC_K_odd c
  exact theoremC_odd_le_U c c.K hKH hKodd

/-- `U = O(H)` lies in `H`. -/
private lemma theoremC_U_le_H (c : Hyp11 G) [Hyp11KData c] : c.U ≤ c.H :=
  SetLike.le_def.1 (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H))

omit [Finite G] in
/-- Conjugating a power by an element that inverts the base inverts the power. -/
private lemma theoremC_inverted_power {t x : G} (h : t * x * t⁻¹ = x⁻¹) (n : ℤ) :
    t * x ^ n * t⁻¹ = (x ^ n)⁻¹ := by
  have hc : (MulAut.conj t) (x ^ n) = ((MulAut.conj t) x) ^ n := by
    rw [map_zpow]
  calc
    t * x ^ n * t⁻¹ = (MulAut.conj t) (x ^ n) := by
      simp [MulAut.conj_apply]
    _ = (MulAut.conj t) x ^ n := hc
    _ = (x⁻¹) ^ n := by
      change (t * x * t⁻¹) ^ n = (x⁻¹) ^ n
      rw [h]
    _ = (x ^ n)⁻¹ := by rw [inv_zpow]

/-- An odd-order element of `U` inverted by `t₁` lies in `K₁` (maximality). -/
private lemma theoremC_mem_K1_of_inverted (c : Hyp11 G) [Hyp11KData c] {x : G}
    (hxU : x ∈ c.U) (hxinv : c.t1 * x * c.t1⁻¹ = x⁻¹) : x ∈ c.K1 := by
  let X : Subgroup G := Subgroup.zpowers x
  have hXU : X ≤ c.U := Subgroup.zpowers_le.mpr hxU
  have hXH : X ≤ c.H := hXU.trans (theoremC_U_le_H c)
  have hXodd : Nat.Coprime 2 (Nat.card ↥X) := by
    have hdiv : Nat.card ↥X ∣ Nat.card ↥c.U := Subgroup.card_dvd_of_le hXU
    exact (theoremC_U_coprime_two c).coprime_dvd_right hdiv
  have hXinv : IsInvertedBy c.t1 X := by
    intro y hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
    exact theoremC_inverted_power hxinv n
  exact c.K1_maximal X hXH hXodd hXinv (Subgroup.mem_zpowers x)

/-- `K₂` is exactly the set of elements of `U` inverted by `t₂`. -/
private lemma theoremC_K2_eq_invertedElements (c : Hyp11 G) [Hyp11KData c] :
    (c.K2 : Set G) = invertedElements c.U c.t2 := by
  ext x
  constructor
  · intro hx
    rw [invertedElements]
    exact ⟨theoremC_K2_le_U c hx, c.K2_inverted x hx⟩
  · intro hx
    rw [invertedElements] at hx
    rcases hx with ⟨hxU, hxinv⟩
    let X : Subgroup G := Subgroup.zpowers x
    have hXU : X ≤ c.U := Subgroup.zpowers_le.mpr hxU
    have hXH : X ≤ c.H := hXU.trans (theoremC_U_le_H c)
    have hXodd : Nat.Coprime 2 (Nat.card ↥X) := by
      have hdiv : Nat.card ↥X ∣ Nat.card ↥c.U := Subgroup.card_dvd_of_le hXU
      exact (theoremC_U_coprime_two c).coprime_dvd_right hdiv
    have hXinv : IsInvertedBy c.t2 X := by
      intro y hy
      rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
      exact theoremC_inverted_power hxinv n
    exact c.K2_maximal X hXH hXodd hXinv (Subgroup.mem_zpowers x)

/-- `K₂` is abelian and normal in `U` (Fact 1.5(iii)). -/
public lemma theoremC_K2_abelian_normal (c : Hyp11 G) [Hyp11KData c] :
    IsMulCommutative (↥c.K2) ∧ IsNormalIn c.K2 c.U := by
  have h := fact_1_5_iii_inverted_subgroup_abelian_normal
    (X := c.U) (s := c.t2) c.t2_involution (theoremC_U_coprime_two c)
    (by
      intro x hx
      exact S_normalizes_U c c.t2 c.t2_mem_S x hx)
    (theoremC_K2_eq_invertedElements c)
  exact ⟨h.1, h.2.1⟩

/-- `B = C_U(S)` lies inside `U`. -/
public lemma theoremC_B_le_U (c : Hyp11 G) [Hyp11KData c] : c.B ≤ c.U := by
  intro b hb
  have hb1 : b ∈ c.B1 := by
    have hb' : b ∈ c.B1 ⊓ c.B2 := by simpa [Hyp11.B] using hb
    exact (inf_le_left : c.B1 ⊓ c.B2 ≤ c.B1) hb'
  unfold Hyp11.B1 centralizerIn at hb1
  exact (inf_le_left : c.U ⊓ Subgroup.centralizer ({c.t1} : Set G) ≤ c.U) hb1

/-- `|B|` is odd (`B ≤ U` and `U` is a `2'`-group). -/
private lemma theoremC_B_card_odd (c : Hyp11 G) [Hyp11KData c] : Odd (Nat.card c.B) := by
  have hcopU : Nat.Coprime 2 (Nat.card (↥c.U)) := theoremC_U_coprime_two c
  have hoddU : Odd (Nat.card (↥c.U)) := Nat.coprime_two_left.mp hcopU
  have hcard : Nat.card c.B ∣ Nat.card (↥c.U) := by
    have hEq : Nat.card ↥(c.B.subgroupOf c.U) = Nat.card ↥c.B := by
      exact Nat.card_congr {
        toFun := fun x : ↥(c.B.subgroupOf c.U) =>
          ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
        invFun := fun y : ↥c.B =>
          ⟨⟨(y : G), theoremC_B_le_U c y.2⟩, Subgroup.mem_subgroupOf.mpr y.2⟩
        left_inv := by intro x; apply Subtype.ext; rfl
        right_inv := by intro y; apply Subtype.ext; rfl }
    have h := Subgroup.card_mul_index (c.B.subgroupOf c.U)
    rw [hEq] at h
    exact ⟨(c.B.subgroupOf c.U).index, by rw [← h]⟩
  exact Odd.of_dvd_nat hoddU hcard

/-- `b ∈ B` commutes with `t₁`. -/
public lemma theoremC_mem_B1_of_mem_B (c : Hyp11 G) [Hyp11KData c] {b : G} (hbB : b ∈ c.B) :
    b ∈ c.B1 := by
  have hb' : b ∈ c.B1 ⊓ c.B2 := by simpa [Hyp11.B] using hbB
  exact (inf_le_left : c.B1 ⊓ c.B2 ≤ c.B1) hb'

/-- `b ∈ B` commutes with `t₂`. -/
public lemma theoremC_mem_B2_of_mem_B (c : Hyp11 G) [Hyp11KData c] {b : G} (hbB : b ∈ c.B) :
    b ∈ c.B2 := by
  have hb' : b ∈ c.B1 ⊓ c.B2 := by simpa [Hyp11.B] using hbB
  exact (inf_le_right : c.B1 ⊓ c.B2 ≤ c.B2) hb'

/-- `B₁ = C_U(t₁)` lies in `U`. -/
public lemma theoremC_B1_le_U (c : Hyp11 G) [Hyp11KData c] : c.B1 ≤ c.U := by
  intro x hx
  unfold Hyp11.B1 centralizerIn at hx
  exact (inf_le_left : c.U ⊓ Subgroup.centralizer ({c.t1} : Set G) ≤ c.U) hx

/-- `x ∈ B1` is fixed by `t₁`. -/
public lemma theoremC_fixed_by_t1_of_mem_B1 (c : Hyp11 G) [Hyp11KData c] {x : G} (hx : x ∈ c.B1) :
    c.t1 * x * c.t1⁻¹ = x := by
  unfold Hyp11.B1 centralizerIn at hx
  have hcomm : c.t1 * x = x * c.t1 :=
    (Subgroup.mem_centralizer_iff).1 hx.2 c.t1 (by simp)
  calc
    c.t1 * x * c.t1⁻¹ = (x * c.t1) * c.t1⁻¹ := by rw [hcomm]
    _ = x := by group

/-- `x ∈ B2` is fixed by `t₂`. -/
public lemma theoremC_fixed_by_t2_of_mem_B2 (c : Hyp11 G) [Hyp11KData c] {x : G} (hx : x ∈ c.B2) :
    c.t2 * x * c.t2⁻¹ = x := by
  unfold Hyp11.B2 centralizerIn at hx
  have hcomm : c.t2 * x = x * c.t2 :=
    (Subgroup.mem_centralizer_iff).1 hx.2 c.t2 (by simp)
  calc
    c.t2 * x * c.t2⁻¹ = (x * c.t2) * c.t2⁻¹ := by rw [hcomm]
    _ = x := by group

/-- The commutator of `x ∈ U` with `y ∈ K₂` lies in `K₂` (normality). -/
private lemma theoremC_commutator_mem_K2_of_mem_K2 (c : Hyp11 G) [Hyp11KData c] {x y : G}
    (hxU : x ∈ c.U) (hyK2 : y ∈ c.K2) : ⁅x, y⁆ ∈ c.K2 := by
  have hK2norm : IsNormalIn c.K2 c.U := (theoremC_K2_abelian_normal c).2
  have hyU : y ∈ c.U := theoremC_K2_le_U c hyK2
  have hconj : x * y * x⁻¹ ∈ c.K2 := hK2norm.2 x hxU y hyK2
  exact c.K2.mul_mem hconj (c.K2.inv_mem hyK2)

/-- If `t₁` fixes `x` and inverts `k ∈ K`, then `t₁` inverts `[x,k]`. -/
private lemma theoremC_t1_inverts_comm_of_fixed_and_K (c : Hyp11 G) [Hyp11KData c] {x k : G}
    (hxU : x ∈ c.U) (hxfix : c.t1 * x * c.t1⁻¹ = x) (hkK : k ∈ c.K) :
    c.t1 * ⁅x, k⁆ * c.t1⁻¹ = (⁅x, k⁆)⁻¹ := by
  have hkK1 : k ∈ c.K1 := by
    change k ∈ c.K1 ⊓ c.K2 at hkK
    exact (Subgroup.mem_inf.mp hkK).1
  have hkK2 : k ∈ c.K2 := by
    change k ∈ c.K1 ⊓ c.K2 at hkK
    exact (Subgroup.mem_inf.mp hkK).2
  have hmemK2 : ⁅x, k⁆ ∈ c.K2 := theoremC_commutator_mem_K2_of_mem_K2 c hxU hkK2
  have hK2abel : IsMulCommutative (↥c.K2) := (theoremC_K2_abelian_normal c).1
  have hcomm : k * ⁅x, k⁆ = ⁅x, k⁆ * k := by
    have hz : (⟨k, hkK2⟩ : ↥c.K2) * ⟨⁅x, k⁆, hmemK2⟩ =
        ⟨⁅x, k⁆, hmemK2⟩ * ⟨k, hkK2⟩ := by
      exact mul_comm' (a := (⟨k, hkK2⟩ : ↥c.K2)) (b := (⟨⁅x, k⁆, hmemK2⟩ : ↥c.K2))
    exact congrArg (fun z : ↥c.K2 => (z : G)) hz
  have hcomm_inv : k⁻¹ * (⁅x, k⁆)⁻¹ = (⁅x, k⁆)⁻¹ * k⁻¹ := by
    calc
      k⁻¹ * (⁅x, k⁆)⁻¹ = (⁅x, k⁆ * k)⁻¹ := by group
      _ = (k * ⁅x, k⁆)⁻¹ := by rw [hcomm]
      _ = (⁅x, k⁆)⁻¹ * k⁻¹ := by group
  have hkx : ⁅k, x⁆ = (⁅x, k⁆)⁻¹ := by
    exact (commutatorElement_inv x k).symm
  have hEq : ⁅x, k⁻¹⁆ = (⁅x, k⁆)⁻¹ := by
    calc
      ⁅x, k⁻¹⁆ = k⁻¹ * ⁅k, x⁆ * k := by rw [commutatorElement_inv_right]
      _ = k⁻¹ * (⁅x, k⁆)⁻¹ * k := by rw [hkx]
      _ = (⁅x, k⁆)⁻¹ := by
        rw [hcomm_inv]
        group
  calc
    c.t1 * ⁅x, k⁆ * c.t1⁻¹
        = ⁅c.t1 * x * c.t1⁻¹, c.t1 * k * c.t1⁻¹⁆ := by
            rw [conjugate_commutatorElement]
    _ = ⁅x, k⁻¹⁆ := by rw [hxfix, theoremC_K1_inverted c hkK1]
    _ = (⁅x, k⁆)⁻¹ := hEq

/-- If `t₁` fixes `x`, then `[x, K] ≤ K`. -/
private lemma theoremC_commutator_mem_K_of_fixed (c : Hyp11 G) [Hyp11KData c] {x k : G}
    (hxU : x ∈ c.U) (hxfix : c.t1 * x * c.t1⁻¹ = x) (hkK : k ∈ c.K) :
    ⁅x, k⁆ ∈ c.K := by
  have hmemK2 : ⁅x, k⁆ ∈ c.K2 :=
    theoremC_commutator_mem_K2_of_mem_K2 c hxU (by
      change k ∈ c.K1 ⊓ c.K2 at hkK
      exact (Subgroup.mem_inf.mp hkK).2)
  have hxinv := theoremC_t1_inverts_comm_of_fixed_and_K c hxU hxfix hkK
  have hK1 : ⁅x, k⁆ ∈ c.K1 :=
    theoremC_mem_K1_of_inverted c (theoremC_K2_le_U c hmemK2) hxinv
  exact Subgroup.mem_inf.mpr ⟨hK1, hmemK2⟩

/-- `[B1 ∩ K2, B] ≤ B1 ∩ K2`. -/
private lemma theoremC_A_comm_B_le_A (c : Hyp11 G) [Hyp11KData c] :
    ⁅c.B1 ⊓ c.K2, c.B⁆ ≤ c.B1 ⊓ c.K2 := by
  rw [Subgroup.commutator_le]
  intro a ha b hbB
  have haA : a ∈ c.B1 ⊓ c.K2 := ha
  have haB1 : a ∈ c.B1 := (Subgroup.mem_inf.mp haA).1
  have haK2 : a ∈ c.K2 := (Subgroup.mem_inf.mp haA).2
  have hbB1 : b ∈ c.B1 := theoremC_mem_B1_of_mem_B c hbB
  have haU : a ∈ c.U := theoremC_K2_le_U c haK2
  have hbU : b ∈ c.U := theoremC_B_le_U c hbB
  have hU : ⁅a, b⁆ ∈ c.U := by
    change a * b * a⁻¹ * b⁻¹ ∈ c.U
    exact c.U.mul_mem (c.U.mul_mem (c.U.mul_mem haU hbU) (c.U.inv_mem haU))
      (c.U.inv_mem hbU)
  have hK2 : ⁅a, b⁆ ∈ c.K2 := by
    have hbaK2 : ⁅b, a⁆ ∈ c.K2 :=
      theoremC_commutator_mem_K2_of_mem_K2 c hbU haK2
    have hEq : ⁅a, b⁆ = (⁅b, a⁆)⁻¹ := (commutatorElement_inv b a).symm
    rw [hEq]
    exact c.K2.inv_mem hbaK2
  have hfix_comm : c.t1 * ⁅a, b⁆ * c.t1⁻¹ = ⁅a, b⁆ := by
    calc
      c.t1 * ⁅a, b⁆ * c.t1⁻¹
          = ⁅c.t1 * a * c.t1⁻¹, c.t1 * b * c.t1⁻¹⁆ := by
              rw [conjugate_commutatorElement]
      _ = ⁅a, b⁆ := by
        rw [theoremC_fixed_by_t1_of_mem_B1 c haB1,
          theoremC_fixed_by_t1_of_mem_B1 c hbB1]
  have hcomm : c.t1 * ⁅a, b⁆ = ⁅a, b⁆ * c.t1 := by
    calc
      c.t1 * ⁅a, b⁆ = (c.t1 * ⁅a, b⁆ * c.t1⁻¹) * c.t1 := by group
      _ = ⁅a, b⁆ * c.t1 := by rw [hfix_comm]
  have hcent : ⁅a, b⁆ ∈ Subgroup.centralizer ({c.t1} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    simp at hs
    rw [hs]
    exact hcomm
  have hB1 : ⁅a, b⁆ ∈ c.B1 := by
    unfold Hyp11.B1 centralizerIn
    exact Subgroup.mem_inf.mpr ⟨hU, hcent⟩
  exact Subgroup.mem_inf.mpr ⟨hB1, hK2⟩

/-- `[B1 ∩ K2, K] ≤ K`. -/
private lemma theoremC_A_comm_K_le_K (c : Hyp11 G) [Hyp11KData c] :
    ⁅c.B1 ⊓ c.K2, c.K⁆ ≤ c.K := by
  rw [Subgroup.commutator_le]
  intro a ha k hkK
  have haB1 : a ∈ c.B1 := (Subgroup.mem_inf.mp ha).1
  have haU : a ∈ c.U := theoremC_K2_le_U c (Subgroup.mem_inf.mp ha).2
  exact theoremC_commutator_mem_K_of_fixed c haU
    (theoremC_fixed_by_t1_of_mem_B1 c haB1) hkK

/-- `[B, K] ≤ K`. -/
private lemma theoremC_B_comm_K_le_K (c : Hyp11 G) [Hyp11KData c] : ⁅c.B, c.K⁆ ≤ c.K := by
  rw [Subgroup.commutator_le]
  intro b hbB k hkK
  have hbB1 : b ∈ c.B1 := theoremC_mem_B1_of_mem_B c hbB
  exact theoremC_commutator_mem_K_of_fixed c (theoremC_B_le_U c hbB)
    (theoremC_fixed_by_t1_of_mem_B1 c hbB1) hkK

/-- `A = B₁ ∩ K₂` normalizes `N = A ⊔ B' ⊔ K`. -/
private lemma theoremC_A_normalizes_N (c : Hyp11 G) [Hyp11KData c] :
    c.B1 ⊓ c.K2 ≤
      Subgroup.normalizer ((((c.B1 ⊓ c.K2) ⊔ ⁅c.B, c.B⁆) ⊔ c.K : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha n hn
  let A : Subgroup G := c.B1 ⊓ c.K2
  let B : Subgroup G := c.B
  let B' : Subgroup G := ⁅B, B⁆
  let K : Subgroup G := c.K
  let N : Subgroup G := A ⊔ B' ⊔ K
  change a ∈ A at ha
  change n ∈ N at hn
  have hAN : A ≤ N := (le_sup_left : A ≤ A ⊔ B').trans (le_sup_left : A ⊔ B' ≤ N)
  have hB'N : B' ≤ N := (le_sup_right : B' ≤ A ⊔ B').trans (le_sup_left : A ⊔ B' ≤ N)
  have hKN : K ≤ N := le_sup_right
  have hAB' : ⁅A, B'⁆ ≤ A := by
    have hB'leB : B' ≤ B := Subgroup.commutator_le_self B
    exact (Subgroup.commutator_mono le_rfl hB'leB).trans (by
      simpa [A, B] using theoremC_A_comm_B_le_A c)
  have hAK : ⁅A, K⁆ ≤ K := by simpa [A, K] using theoremC_A_comm_K_le_K c
  have hni : n ∈ ⨆ i : Fin 3, (![A, B', K] : Fin 3 → Subgroup G) i := by
    simpa [A, B', K, N] using hn
  refine Subgroup.iSup_induction' (S := ![A, B', K])
    (C := fun z _hz => a * z * a⁻¹ ∈ N) ?_ ?_ ?_ hni
  · intro i z hz
    fin_cases i
    · have hmem : a * z * a⁻¹ ∈ A := A.mul_mem (A.mul_mem ha hz) (A.inv_mem ha)
      exact hAN hmem
    · have hmemAB : ⁅a, z⁆ ∈ A := (Subgroup.commutator_le.mp hAB') a ha z hz
      have hEq : a * z * a⁻¹ = ⁅a, z⁆ * z := by
        change a * z * a⁻¹ = (a * z * a⁻¹ * z⁻¹) * z
        group
      rw [hEq]
      exact N.mul_mem (hAN hmemAB) (hB'N hz)
    · have hmemAK : ⁅a, z⁆ ∈ K := (Subgroup.commutator_le.mp hAK) a ha z hz
      have hEq : a * z * a⁻¹ = ⁅a, z⁆ * z := by
        change a * z * a⁻¹ = (a * z * a⁻¹ * z⁻¹) * z
        group
      rw [hEq]
      exact N.mul_mem (hKN hmemAK) (hKN hz)
  · simp
  · intro x y _hx _hy ihx ihy
    have hEq : a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
    rw [hEq]
    exact N.mul_mem ihx ihy

/-- `B` normalizes `N = A ⊔ B' ⊔ K`. -/
private lemma theoremC_B_normalizes_N (c : Hyp11 G) [Hyp11KData c] :
    c.B ≤ Subgroup.normalizer ((((c.B1 ⊓ c.K2) ⊔ ⁅c.B, c.B⁆) ⊔ c.K : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro b hb n hn
  let A : Subgroup G := c.B1 ⊓ c.K2
  let B : Subgroup G := c.B
  let B' : Subgroup G := ⁅B, B⁆
  let K : Subgroup G := c.K
  let N : Subgroup G := A ⊔ B' ⊔ K
  change b ∈ B at hb
  change n ∈ N at hn
  have hAN : A ≤ N := (le_sup_left : A ≤ A ⊔ B').trans (le_sup_left : A ⊔ B' ≤ N)
  have hB'N : B' ≤ N := (le_sup_right : B' ≤ A ⊔ B').trans (le_sup_left : A ⊔ B' ≤ N)
  have hKN : K ≤ N := le_sup_right
  have hBA : ⁅B, A⁆ ≤ A := by
    rw [Subgroup.commutator_comm B A]
    simpa [A, B] using theoremC_A_comm_B_le_A c
  have hBK : ⁅B, K⁆ ≤ K := by simpa [B, K] using theoremC_B_comm_K_le_K c
  have hni : n ∈ ⨆ i : Fin 3, (![A, B', K] : Fin 3 → Subgroup G) i := by
    simpa [A, B', K, N] using hn
  refine Subgroup.iSup_induction' (S := ![A, B', K])
    (C := fun z _hz => b * z * b⁻¹ ∈ N) ?_ ?_ ?_ hni
  · intro i z hz
    fin_cases i
    · have hmemBA : ⁅b, z⁆ ∈ A := (Subgroup.commutator_le.mp hBA) b hb z hz
      have hEq : b * z * b⁻¹ = ⁅b, z⁆ * z := by
        change b * z * b⁻¹ = (b * z * b⁻¹ * z⁻¹) * z
        group
      rw [hEq]
      exact N.mul_mem (hAN hmemBA) (hAN hz)
    · have hbNorm : b ∈ Subgroup.normalizer ((B' : Subgroup G) : Set G) :=
        Subgroup.normalizer_commutator_ge_left B B hb
      have hconj : b * z * b⁻¹ ∈ B' := by
        rw [Subgroup.mem_normalizer_iff] at hbNorm
        exact (hbNorm z).1 hz
      exact hB'N hconj
    · have hmemBK : ⁅b, z⁆ ∈ K := (Subgroup.commutator_le.mp hBK) b hb z hz
      have hEq : b * z * b⁻¹ = ⁅b, z⁆ * z := by
        change b * z * b⁻¹ = (b * z * b⁻¹ * z⁻¹) * z
        group
      rw [hEq]
      exact N.mul_mem (hKN hmemBK) (hKN hz)
  · simp
  · intro x y _hx _hy ihx ihy
    have hEq : b * (x * y) * b⁻¹ = (b * x * b⁻¹) * (b * y * b⁻¹) := by group
    rw [hEq]
    exact N.mul_mem ihx ihy

/-- `K` normalizes `N = A ⊔ B' ⊔ K`. -/
private lemma theoremC_K_normalizes_N (c : Hyp11 G) [Hyp11KData c] :
    c.K ≤ Subgroup.normalizer ((((c.B1 ⊓ c.K2) ⊔ ⁅c.B, c.B⁆) ⊔ c.K : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro k hk n hn
  let A : Subgroup G := c.B1 ⊓ c.K2
  let B : Subgroup G := c.B
  let B' : Subgroup G := ⁅B, B⁆
  let K : Subgroup G := c.K
  let N : Subgroup G := A ⊔ B' ⊔ K
  change k ∈ K at hk
  change n ∈ N at hn
  have hAN : A ≤ N := (le_sup_left : A ≤ A ⊔ B').trans (le_sup_left : A ⊔ B' ≤ N)
  have hB'N : B' ≤ N := (le_sup_right : B' ≤ A ⊔ B').trans (le_sup_left : A ⊔ B' ≤ N)
  have hKN : K ≤ N := le_sup_right
  have hKA : ⁅K, A⁆ ≤ K := by
    rw [Subgroup.commutator_comm K A]
    simpa [A, K] using theoremC_A_comm_K_le_K c
  have hKB : ⁅K, B⁆ ≤ K := by
    rw [Subgroup.commutator_comm K B]
    simpa [B, K] using theoremC_B_comm_K_le_K c
  have hni : n ∈ ⨆ i : Fin 3, (![A, B', K] : Fin 3 → Subgroup G) i := by
    simpa [A, B', K, N] using hn
  refine Subgroup.iSup_induction' (S := ![A, B', K])
    (C := fun z _hz => k * z * k⁻¹ ∈ N) ?_ ?_ ?_ hni
  · intro i z hz
    fin_cases i
    · have hmemKA : ⁅k, z⁆ ∈ K := (Subgroup.commutator_le.mp hKA) k hk z hz
      have hEq : k * z * k⁻¹ = ⁅k, z⁆ * z := by
        change k * z * k⁻¹ = (k * z * k⁻¹ * z⁻¹) * z
        group
      rw [hEq]
      exact N.mul_mem (hKN hmemKA) (hAN hz)
    · have hmemKB : ⁅k, z⁆ ∈ K := by
        have hB'leB : B' ≤ B := Subgroup.commutator_le_self B
        have hKB' : ⁅K, B'⁆ ≤ K := (Subgroup.commutator_mono le_rfl hB'leB).trans hKB
        exact (Subgroup.commutator_le.mp hKB') k hk z hz
      have hEq : k * z * k⁻¹ = ⁅k, z⁆ * z := by
        change k * z * k⁻¹ = (k * z * k⁻¹ * z⁻¹) * z
        group
      rw [hEq]
      exact N.mul_mem (hKN hmemKB) (hB'N hz)
    · have hmem : k * z * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk hz) (K.inv_mem hk)
      exact hKN hmem
  · simp
  · intro x y _hx _hy ihx ihy
    have hEq : k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) := by group
    rw [hEq]
    exact N.mul_mem ihx ihy

/-- `N = A ⊔ B' ⊔ K` is normal in `U`. -/
private lemma theoremC_N_normal_in_U (c : Hyp11 G) [Hyp11KData c]
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K)) :
    IsNormalIn ((c.B1 ⊓ c.K2) ⊔ ⁅c.B, c.B⁆ ⊔ c.K) c.U := by
  let A : Subgroup G := c.B1 ⊓ c.K2
  let B : Subgroup G := c.B
  let B' : Subgroup G := ⁅B, B⁆
  let K : Subgroup G := c.K
  let N : Subgroup G := A ⊔ B' ⊔ K
  have hA_norm : A ≤ Subgroup.normalizer ((N : Subgroup G) : Set G) := by
    simpa [A, B, B', K, N] using theoremC_A_normalizes_N c
  have hB_norm : B ≤ Subgroup.normalizer ((N : Subgroup G) : Set G) := by
    simpa [A, B, B', K, N] using theoremC_B_normalizes_N c
  have hK_norm : K ≤ Subgroup.normalizer ((N : Subgroup G) : Set G) := by
    simpa [A, B, B', K, N] using theoremC_K_normalizes_N c
  have hUnorm : c.U ≤ Subgroup.normalizer ((N : Subgroup G) : Set G) := by
    rw [hU]
    exact sup_le hA_norm (sup_le hB_norm hK_norm)
  refine ⟨?_, ?_⟩
  · have hA_U : A ≤ c.U := by
      intro x hx
      exact theoremC_B1_le_U c (Subgroup.mem_inf.mp hx).1
    have hB_U : B ≤ c.U := theoremC_B_le_U c
    have hB'_U : B' ≤ c.U := (Subgroup.commutator_le_self B).trans hB_U
    have hK_U : K ≤ c.U := theoremC_K_le_U c
    exact sup_le (sup_le hA_U hB'_U) hK_U
  · intro u hu n hn
    exact (Subgroup.le_normalizer_iff.mp hUnorm) u hu n hn

/-- `U' = ⁅U,U⁆ ≤ A ⊔ B' ⊔ K`. -/
private lemma theoremC_Uprime_le_N (c : Hyp11 G) [Hyp11KData c]
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K)) :
    ⁅c.U, c.U⁆ ≤ (c.B1 ⊓ c.K2) ⊔ ⁅c.B, c.B⁆ ⊔ c.K := by
  let A : Subgroup G := c.B1 ⊓ c.K2
  let B : Subgroup G := c.B
  let B' : Subgroup G := ⁅B, B⁆
  let K : Subgroup G := c.K
  let N : Subgroup G := A ⊔ B' ⊔ K
  have hNnorm : IsNormalIn N c.U := by
    simpa [A, B, B', K, N] using theoremC_N_normal_in_U c hU
  have hAN : A ≤ N := (le_sup_left : A ≤ A ⊔ B').trans (le_sup_left : A ⊔ B' ≤ N)
  have hB'N : B' ≤ N := (le_sup_right : B' ≤ A ⊔ B').trans (le_sup_left : A ⊔ B' ≤ N)
  have hKN : K ≤ N := le_sup_right
  have hAA : ⁅A, A⁆ ≤ A := Subgroup.commutator_le_self A
  have hAB : ⁅A, B⁆ ≤ A := by simpa [A, B] using theoremC_A_comm_B_le_A c
  have hAK : ⁅A, K⁆ ≤ K := by simpa [A, K] using theoremC_A_comm_K_le_K c
  have hBA : ⁅B, A⁆ ≤ A := by
    rw [Subgroup.commutator_comm B A]
    exact hAB
  have hBB : ⁅B, B⁆ ≤ B' := le_rfl
  have hBK : ⁅B, K⁆ ≤ K := by simpa [B, K] using theoremC_B_comm_K_le_K c
  have hKA : ⁅K, A⁆ ≤ K := by
    rw [Subgroup.commutator_comm K A]
    exact hAK
  have hKB : ⁅K, B⁆ ≤ K := by
    rw [Subgroup.commutator_comm K B]
    exact hBK
  have hKK : ⁅K, K⁆ ≤ K := Subgroup.commutator_le_self K
  have baseA : ∀ z : G, z ∈ A → ∀ y : G, y ∈ c.U → ⁅z, y⁆ ∈ N := by
    intro z hz y hy
    have hyi : y ∈ ⨆ i : Fin 3, (![A, B, K] : Fin 3 → Subgroup G) i := by
      simpa [A, B, K, hU, sup_assoc] using hy
    refine Subgroup.iSup_induction' (S := ![A, B, K])
      (C := fun w _hw => ⁅z, w⁆ ∈ N) ?_ ?_ ?_ hyi
    · intro i w hw
      fin_cases i
      · exact hAN ((Subgroup.commutator_le.mp hAA) z hz w hw)
      · exact hAN ((Subgroup.commutator_le.mp hAB) z hz w hw)
      · exact hKN ((Subgroup.commutator_le.mp hAK) z hz w hw)
    · simp
    · intro v w hv _hw hzv hzw
      have hEq : ⁅z, v * w⁆ = ⁅z, v⁆ * v * ⁅z, w⁆ * v⁻¹ :=
        commutatorElement_mul_right_eq_mul_conj z v w
      rw [hEq]
      have hvU : v ∈ c.U := by
        simpa [A, B, K, hU, sup_assoc] using hv
      exact (by
        simpa [mul_assoc] using N.mul_mem hzv (hNnorm.2 v hvU ⁅z, w⁆ hzw))
  have baseB : ∀ z : G, z ∈ B → ∀ y : G, y ∈ c.U → ⁅z, y⁆ ∈ N := by
    intro z hz y hy
    have hyi : y ∈ ⨆ i : Fin 3, (![A, B, K] : Fin 3 → Subgroup G) i := by
      simpa [A, B, K, hU, sup_assoc] using hy
    refine Subgroup.iSup_induction' (S := ![A, B, K])
      (C := fun w _hw => ⁅z, w⁆ ∈ N) ?_ ?_ ?_ hyi
    · intro i w hw
      fin_cases i
      · exact hAN ((Subgroup.commutator_le.mp hBA) z hz w hw)
      · exact hB'N ((Subgroup.commutator_le.mp hBB) z hz w hw)
      · exact hKN ((Subgroup.commutator_le.mp hBK) z hz w hw)
    · simp
    · intro v w hv _hw hzv hzw
      have hEq : ⁅z, v * w⁆ = ⁅z, v⁆ * v * ⁅z, w⁆ * v⁻¹ :=
        commutatorElement_mul_right_eq_mul_conj z v w
      rw [hEq]
      have hvU : v ∈ c.U := by
        simpa [A, B, K, hU, sup_assoc] using hv
      exact (by
        simpa [mul_assoc] using N.mul_mem hzv (hNnorm.2 v hvU ⁅z, w⁆ hzw))
  have baseK : ∀ z : G, z ∈ K → ∀ y : G, y ∈ c.U → ⁅z, y⁆ ∈ N := by
    intro z hz y hy
    have hyi : y ∈ ⨆ i : Fin 3, (![A, B, K] : Fin 3 → Subgroup G) i := by
      simpa [A, B, K, hU, sup_assoc] using hy
    refine Subgroup.iSup_induction' (S := ![A, B, K])
      (C := fun w _hw => ⁅z, w⁆ ∈ N) ?_ ?_ ?_ hyi
    · intro i w hw
      fin_cases i
      · exact hKN ((Subgroup.commutator_le.mp hKA) z hz w hw)
      · exact hKN ((Subgroup.commutator_le.mp hKB) z hz w hw)
      · exact hKN ((Subgroup.commutator_le.mp hKK) z hz w hw)
    · simp
    · intro v w hv _hw hzv hzw
      have hEq : ⁅z, v * w⁆ = ⁅z, v⁆ * v * ⁅z, w⁆ * v⁻¹ :=
        commutatorElement_mul_right_eq_mul_conj z v w
      rw [hEq]
      have hvU : v ∈ c.U := by
        simpa [A, B, K, hU, sup_assoc] using hv
      exact (by
        simpa [mul_assoc] using N.mul_mem hzv (hNnorm.2 v hvU ⁅z, w⁆ hzw))
  have main : ∀ x y : G, x ∈ c.U → y ∈ c.U → ⁅x, y⁆ ∈ N := by
    intro x y hx hy
    have hxi : x ∈ ⨆ i : Fin 3, (![A, B, K] : Fin 3 → Subgroup G) i := by
      simpa [A, B, K, hU, sup_assoc] using hx
    have hxres : ∀ y : G, y ∈ c.U → ⁅x, y⁆ ∈ N := by
      refine Subgroup.iSup_induction' (S := ![A, B, K])
        (C := fun w _hw => ∀ y : G, y ∈ c.U → ⁅w, y⁆ ∈ N) ?_ ?_ ?_ hxi
      · intro i w hw y hy
        fin_cases i
        · exact baseA w hw y hy
        · exact baseB w hw y hy
        · exact baseK w hw y hy
      · intro y _hy
        simp
      · intro v w hv _hw ihv ihw y hy
        have hEq : ⁅v * w, y⁆ = v * ⁅w, y⁆ * v⁻¹ * ⁅v, y⁆ :=
          commutatorElement_mul_left_eq_conj_mul v w y
        rw [hEq]
        have hvU : v ∈ c.U := by
          simpa [A, B, K, hU, sup_assoc] using hv
        have hnorm : v * ⁅w, y⁆ * v⁻¹ ∈ N :=
          hNnorm.2 v hvU ⁅w, y⁆ (ihw y hy)
        exact (by
          simpa [mul_assoc] using N.mul_mem hnorm (ihv y hy))
    exact hxres y hy
  exact Subgroup.commutator_le.mpr (by
    intro x hx y hy
    exact main x y hx hy)

/-- Every element of `N = A ⊔ B' ⊔ K` has the normal form `a·b'·k`.
This uses only the normalizations `B' ≤ N_G(A)`, `B' ≤ N_G(K)` and
`K ≤ N_G(A)` (the last from `A,K ≤ K₂` abelian). -/
private lemma theoremC_mem_N_decompose (c : Hyp11 G) [Hyp11KData c] {x : G}
    (hx : x ∈ (c.B1 ⊓ c.K2) ⊔ ⁅c.B, c.B⁆ ⊔ c.K) :
    ∃ a ∈ c.B1 ⊓ c.K2, ∃ bp ∈ ⁅c.B, c.B⁆, ∃ k ∈ c.K, a * bp * k = x := by
  let A : Subgroup G := c.B1 ⊓ c.K2
  let B : Subgroup G := c.B
  let B' : Subgroup G := ⁅B, B⁆
  let K : Subgroup G := c.K
  have hB'leB : B' ≤ B := Subgroup.commutator_le_self B
  have hB'normA : B' ≤ Subgroup.normalizer (A : Set G) := by
    have hBnormA : B ≤ Subgroup.normalizer (A : Set G) := by
      apply (Subgroup.le_normalizer_iff_commutator_le_left (H := B) (K := A)).2
      exact theoremC_A_comm_B_le_A c
    exact hB'leB.trans hBnormA
  have hB'normK : B' ≤ Subgroup.normalizer (K : Set G) := by
    have hBnormK : B ≤ Subgroup.normalizer (K : Set G) := by
      apply (Subgroup.le_normalizer_iff_commutator_le_left (H := B) (K := K)).2
      rw [Subgroup.commutator_comm K B]
      exact theoremC_B_comm_K_le_K c
    exact hB'leB.trans hBnormK
  have hKnormA : K ≤ Subgroup.normalizer (A : Set G) := by
    apply (Subgroup.le_normalizer_iff (H := K) (K := A)).2
    intro k hk a ha
    have hkK2 : k ∈ c.K2 := by
      change k ∈ c.K1 ⊓ c.K2 at hk
      exact (Subgroup.mem_inf.mp hk).2
    have haK2 : a ∈ c.K2 := (Subgroup.mem_inf.mp ha).2
    have hK2abel : IsMulCommutative (↥c.K2) := (theoremC_K2_abelian_normal c).1
    have hz : (⟨k, hkK2⟩ : ↥c.K2) * ⟨a, haK2⟩ = ⟨a, haK2⟩ * ⟨k, hkK2⟩ := by
      exact mul_comm' (a := (⟨k, hkK2⟩ : ↥c.K2)) (b := (⟨a, haK2⟩ : ↥c.K2))
    have hcomm : k * a = a * k := congrArg (fun z : ↥c.K2 => (z : G)) hz
    have hEq : k * a * k⁻¹ = a := by
      calc
        k * a * k⁻¹ = (a * k) * k⁻¹ := by rw [hcomm]
        _ = a := by group
    rw [hEq]
    exact ha
  have hAK_eq : (↑(A ⊔ K) : Set G) = (A : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A K hKnormA
  have hB'_normAK : B' ≤ Subgroup.normalizer ((A ⊔ K : Subgroup G) : Set G) :=
    (le_inf hB'normA hB'normK).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup A K)
  have hBK_sup_eq : (↑(B' ⊔ (A ⊔ K)) : Set G) =
      (B' : Set G) * (↑(A ⊔ K) : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right B' (A ⊔ K) hB'_normAK
  have hxcar : x ∈ (B' : Set G) * (↑(A ⊔ K) : Set G) := by
    have hx' : x ∈ B' ⊔ (A ⊔ K) := by
      change x ∈ (A ⊔ B') ⊔ K at hx
      simpa only [sup_assoc, sup_left_comm, sup_comm] using hx
    rw [← hBK_sup_eq]
    exact hx'
  rcases hxcar with ⟨bp, hbpB', ak, hakAK, hxeq⟩
  have hakcar : ak ∈ (A : Set G) * (K : Set G) := by
    have hak' : ak ∈ A ⊔ K := by
      simpa [A, K] using hakAK
    rwa [← hAK_eq]
  rcases hakcar with ⟨a, haA, k, hkK, hakeq⟩
  have hakeq' : a * k = ak := by simpa using hakeq
  refine ⟨bp * a * bp⁻¹, ?_, bp, hbpB', k, hkK, ?_⟩
  · have hnorm := (Subgroup.le_normalizer_iff.mp hB'normA) bp hbpB' a haA
    exact hnorm
  · calc
      (bp * a * bp⁻¹) * bp * k = bp * a * k := by group
      _ = bp * (a * k) := by group
      _ = bp * ak := by rw [hakeq']
      _ = x := hxeq

/-- `β(1)² ≤ |B|` for `β ∈ Irr(B)`: from `⟨β,β⟩ = 1` and one term of the
sum of squared absolute values. -/
private lemma theoremC_irr_degree_sq_le_card {B : Type u} [Group B] [Fintype B]
    {β : ClassFunction B} (hβ : IsIrreducibleCharacter β) :
    (β 1).re ^ 2 ≤ (Nat.card B : ℝ) := by
  classical
  rcases irr_one_int (H := B) ⟨β, hβ⟩ with ⟨a, ha⟩
  have hsp : scalarProduct B β β = 1 := scalarProduct_irreducible_self hβ
  unfold scalarProduct at hsp
  have hcard_ne : (Nat.card B : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := B)).ne'
  have hsum : (∑ x : B, β x * star (β x)) = (Nat.card B : ℂ) := by
    calc
      (∑ x : B, β x * star (β x))
          = (Nat.card B : ℂ) *
              ((Nat.card B : ℂ)⁻¹ * (∑ x : B, β x * star (β x))) := by
              rw [← mul_assoc, mul_inv_cancel₀ hcard_ne, one_mul]
      _ = (Nat.card B : ℂ) * 1 := by rw [hsp]
      _ = (Nat.card B : ℂ) := by simp
  have hterm (x : B) : (β x * star (β x)).re = Complex.normSq (β x) := by
    simp [Complex.normSq]
  have hsumR : (∑ x : B, Complex.normSq (β x)) = (Nat.card B : ℝ) := by
    have hre : (∑ x : B, (β x * star (β x)).re) = (Nat.card B : ℝ) := by
      have h := congrArg Complex.re hsum
      simpa using h
    rw [← hre]
    exact Finset.sum_congr rfl (fun x hx => (hterm x).symm)
  have hβ1sq : (β 1).re ^ 2 = Complex.normSq (β 1) := by
    have hβa : β 1 = (a : ℂ) := by simpa using ha
    have h : (↑a : ℂ).re * (↑a : ℂ).re = Complex.normSq (↑a : ℂ) := by
      norm_num [Complex.normSq]
    simp [hβa, pow_two]
  have hnonneg : ∀ x : B, 0 ≤ Complex.normSq (β x) := fun x => Complex.normSq_nonneg _
  have hsum_nonneg : 0 ≤ ∑ x : B, Complex.normSq (β x) :=
    Finset.sum_nonneg (fun x hx => hnonneg x)
  have hle1 : Complex.normSq (β 1) ≤ ∑ x : B, Complex.normSq (β x) :=
    Finset.single_le_sum (fun x hx => hnonneg x) (Finset.mem_univ (1 : B))
  rwa [← hβ1sq, hsumR] at hle1

/-- For a character `θ` of a finite group `B`,
`θ(1)² ≤ |B|·(θ,θ)`: from `Σ|θ(b)|² = |B|·⟨θ,θ⟩` and one term. -/
private lemma theoremC_char_degree_sq_le_card_mul_norm {B : Type u} [Group B] [Fintype B]
    {θ : ClassFunction B} (hθ : IsCharacter θ) :
    (θ 1).re ^ 2 ≤ (Nat.card B : ℝ) * (normSq B θ).re := by
  classical
  rcases hθ with ⟨n, ρ, hθeq⟩
  have hθ1 : θ 1 = (n : ℂ) := by
    rw [hθeq, Representation.char_one]
    rw [Module.finrank_pi, Fintype.card_fin]
  have hθ1sq : (θ 1).re ^ 2 = Complex.normSq (θ 1) := by
    rw [hθ1]
    rw [pow_two]
    norm_num [Complex.normSq]
  have hcard_ne : (Nat.card B : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := B)).ne'
  have hnsp : normSq B θ = (Nat.card B : ℂ)⁻¹ * (∑ b : B, θ b * star (θ b)) := by
    rfl
  have hsumC : (∑ b : B, θ b * star (θ b)) = (Nat.card B : ℂ) * normSq B θ := by
    calc
      (∑ b : B, θ b * star (θ b))
          = (Nat.card B : ℂ) *
              ((Nat.card B : ℂ)⁻¹ * (∑ b : B, θ b * star (θ b))) := by
              rw [← mul_assoc, mul_inv_cancel₀ hcard_ne, one_mul]
      _ = (Nat.card B : ℂ) * normSq B θ := by rw [hnsp]
  have hterm (b : B) : (θ b * star (θ b)).re = Complex.normSq (θ b) := by
    simp [Complex.normSq]
  have hsumR : (∑ b : B, Complex.normSq (θ b)) =
      (Nat.card B : ℝ) * (normSq B θ).re := by
    have hre := congrArg Complex.re hsumC
    have hL : ((∑ b : B, θ b * star (θ b)) : ℂ).re =
        ∑ b : B, Complex.normSq (θ b) := by
      simp [Complex.normSq]
    have hR : ((Nat.card B : ℂ) * normSq B θ).re =
        (Nat.card B : ℝ) * (normSq B θ).re := by
      rw [Complex.mul_re]
      simp
    rw [hL, hR] at hre
    exact hre
  have hnonneg : ∀ b : B, 0 ≤ Complex.normSq (θ b) := fun b => Complex.normSq_nonneg _
  have hle1 : Complex.normSq (θ 1) ≤ ∑ b : B, Complex.normSq (θ b) :=
    Finset.single_le_sum (fun b hb => hnonneg b) (Finset.mem_univ (1 : B))
  rwa [← hθ1sq, hsumR] at hle1

omit [Finite G] in
/-- If `r` centralizes `a`, then `r²` centralizes `a`. -/
private lemma sq_centralizes_of_centralizes {r a : G} (h : r * a * r⁻¹ = a) :
    (r ^ 2) * a * (r ^ 2)⁻¹ = a := by
  calc
    (r ^ 2) * a * (r ^ 2)⁻¹ = r * (r * a * r⁻¹) * r⁻¹ := by
      rw [pow_two]
      group
    _ = a := by
      rw [h]
      exact h

omit [Finite G] in
/-- If `r` inverts `a`, then `r²` centralizes `a`. -/
private lemma sq_centralizes_of_inverts {r a : G} (h : r * a * r⁻¹ = a⁻¹) :
    (r ^ 2) * a * (r ^ 2)⁻¹ = a := by
  calc
    (r ^ 2) * a * (r ^ 2)⁻¹ = r * (r * a * r⁻¹) * r⁻¹ := by
      rw [pow_two]
      group
    _ = a := by
      rw [h]
      calc
        r * a⁻¹ * r⁻¹ = (r * a * r⁻¹)⁻¹ := by group
        _ = (a⁻¹)⁻¹ := by rw [h]
        _ = a := by simp

omit [Finite G] in
/-- An element centralized by a generator is centralized by its powers. -/
private lemma centralizes_zpowers_of_centralized {r a : G}
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

/-- `t₁·t₂` centralizes `K`. -/
private lemma theoremC_r0_centralizes_K (c : Hyp11 G) [Hyp11KData c] {k : G} (hk : k ∈ c.K) :
    (c.t1 * c.t2) * k * (c.t1 * c.t2)⁻¹ = k := by
  have h1 := theoremC_K_inverted_by_t1 c hk
  have h2 := theoremC_K_inverted_by_t2 c hk
  calc
    (c.t1 * c.t2) * k * (c.t1 * c.t2)⁻¹
        = c.t1 * ((c.t2 * k * c.t2⁻¹) * c.t1⁻¹) := by group
    _ = c.t1 * (k⁻¹ * c.t1⁻¹) := by rw [h2]
    _ = c.t1 * k⁻¹ * c.t1⁻¹ := by group
    _ = (c.t1 * k * c.t1⁻¹)⁻¹ := by group
    _ = (k⁻¹)⁻¹ := by rw [h1]
    _ = k := by simp

/-- `S0 = ⟨t₁·t₂⟩` centralizes `K`. -/
public lemma theoremC_S0_centralizes_K (c : Hyp11 G) [Hyp11KData c] {k : G} (hk : k ∈ c.K) :
    k ∈ Subgroup.centralizer ((c.S0 : Subgroup G) : Set G) := by
  have hr0 := theoremC_r0_centralizes_K c hk
  have hz : k ∈ Subgroup.centralizer
      ((Subgroup.zpowers (c.t1 * c.t2) : Subgroup G) : Set G) :=
    centralizes_zpowers_of_centralized hr0
  simpa [c.S0_eq_zpowers] using hz

/-- Every reflection of `S \ S0` is `t₁` or `t₂` up to an element of `S0`. -/
private lemma theoremC_reflection_t1S0_or_t2S0 (c : Hyp11 G) [Hyp11KData c] {x : G}
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
private lemma theoremC_reflection_inverts_K (c : Hyp11 G) [Hyp11KData c] {x k : G}
    (hxS : x ∈ (c.S : Subgroup G)) (hxnot : x ∉ (c.S0 : Subgroup G))
    (hk : k ∈ c.K) : x * k * x⁻¹ = k⁻¹ := by
  rcases theoremC_reflection_t1S0_or_t2S0 c hxS hxnot with hx1 | hx2
  · have hrS0 : c.t1 * x ∈ (c.S0 : Subgroup G) := hx1
    let r : G := c.t1 * x
    have hx_eq : x = c.t1 * r := by
      dsimp [r]
      have ht1sq : c.t1 * c.t1 = 1 := by
        simpa [pow_two] using c.t1_involution.2
      calc
        x = (c.t1 * c.t1) * x := by rw [ht1sq]; simp
        _ = c.t1 * (c.t1 * x) := by group
    have hkcen : k ∈ Subgroup.centralizer ((c.S0 : Subgroup G) : Set G) :=
      theoremC_S0_centralizes_K c hk
    have hkr0 : (c.t1 * x) * k = k * (c.t1 * x) :=
      (Subgroup.mem_centralizer_iff.mp hkcen) (c.t1 * x) hrS0
    have hkr : (c.t1 * x) * k * (c.t1 * x)⁻¹ = k := by
      rw [hkr0]
      group
    have h1 := theoremC_K_inverted_by_t1 c hk
    calc
      x * k * x⁻¹ = (c.t1 * r) * k * (c.t1 * r)⁻¹ := by rw [hx_eq]
      _ = c.t1 * (r * k * r⁻¹) * c.t1⁻¹ := by group
      _ = c.t1 * k * c.t1⁻¹ := by rw [hkr]
      _ = k⁻¹ := h1
  · have hrS0 : c.t2 * x ∈ (c.S0 : Subgroup G) := hx2
    let r : G := c.t2 * x
    have hx_eq : x = c.t2 * r := by
      dsimp [r]
      have ht2sq : c.t2 * c.t2 = 1 := by
        simpa [pow_two] using c.t2_involution.2
      calc
        x = (c.t2 * c.t2) * x := by rw [ht2sq]; simp
        _ = c.t2 * (c.t2 * x) := by group
    have hkcen : k ∈ Subgroup.centralizer ((c.S0 : Subgroup G) : Set G) :=
      theoremC_S0_centralizes_K c hk
    have hkr0 : (c.t2 * x) * k = k * (c.t2 * x) :=
      (Subgroup.mem_centralizer_iff.mp hkcen) (c.t2 * x) hrS0
    have hkr : (c.t2 * x) * k * (c.t2 * x)⁻¹ = k := by
      rw [hkr0]
      group
    have h2 := theoremC_K_inverted_by_t2 c hk
    calc
      x * k * x⁻¹ = (c.t2 * r) * k * (c.t2 * r)⁻¹ := by rw [hx_eq]
      _ = c.t2 * (r * k * r⁻¹) * c.t2⁻¹ := by group
      _ = c.t2 * k * c.t2⁻¹ := by rw [hkr]
      _ = k⁻¹ := h2

/-- The chosen involution `s ∈ S \ S0` inverts `K`. -/
private lemma theoremC_s_inverts_K (c : Hyp11 G) [Hyp11KData c] {k : G} (hk : k ∈ c.K) :
    c.s * k * c.s⁻¹ = k⁻¹ :=
  theoremC_reflection_inverts_K c c.s_mem_S c.s_not_mem_S0 hk

/-! ## Equation (3) character-side infrastructure: reflection-fixed
characters kill `K`

For `α ∈ Irr(U)` fixed by a reflection `x ∈ S \ S0`, every element of
`K` is inverted by `x`, so `α|_K` is inversion-invariant.  Since `K` is
abelian of odd order, the irreducible constituents of `α|_K` lie in a
single `U`-orbit (Clifford), the orbit is `U`-stable under complex
conjugation and has odd cardinality, and the resulting self-inverse
constituent is the trivial character.  Hence `K ≤ ker α`.

The constituent machinery below mirrors the landed
`Section3.Lemma36` development, which is private to that module and not
on the allowed import list; it is reimplemented here with theorem-local
names. -/

/-- `K₁` is exactly the set of elements of `U` inverted by `t₁`. -/
private lemma theoremC_K1_eq_invertedElements (c : Hyp11 G) [Hyp11KData c] :
    (c.K1 : Set G) = invertedElements c.U c.t1 := by
  ext x
  constructor
  · intro hx
    rw [invertedElements]
    exact ⟨theoremC_K1_le_U c hx, c.K1_inverted x hx⟩
  · intro hx
    rw [invertedElements] at hx
    rcases hx with ⟨hxU, hxinv⟩
    let X : Subgroup G := Subgroup.zpowers x
    have hXU : X ≤ c.U := Subgroup.zpowers_le.mpr hxU
    have hXH : X ≤ c.H := hXU.trans (theoremC_U_le_H c)
    have hXodd : Nat.Coprime 2 (Nat.card ↥X) := by
      have hdiv : Nat.card ↥X ∣ Nat.card ↥c.U := Subgroup.card_dvd_of_le hXU
      exact (theoremC_U_coprime_two c).coprime_dvd_right hdiv
    have hXinv : IsInvertedBy c.t1 X := by
      intro y hy
      rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
      exact theoremC_inverted_power hxinv n
    exact c.K1_maximal X hXH hXodd hXinv (Subgroup.mem_zpowers x)

/-- `K₁ ⊴ U`. -/
private lemma theoremC_K1_normal_in_U (c : Hyp11 G) [Hyp11KData c] : IsNormalIn c.K1 c.U := by
  have h := fact_1_5_iii_inverted_subgroup_abelian_normal
    (X := c.U) (s := c.t1) c.t1_involution (theoremC_U_coprime_two c)
    (by
      intro x hx
      exact S_normalizes_U c c.t1 c.t1_mem_S x hx)
    (theoremC_K1_eq_invertedElements c)
  exact h.2.1

/-- `K = K₁ ∩ K₂ ⊴ U`. -/
private lemma theoremC_K_normal_in_U (c : Hyp11 G) [Hyp11KData c] : IsNormalIn c.K c.U := by
  have h1 := theoremC_K1_normal_in_U c
  have h2 := (theoremC_K2_abelian_normal c).2
  constructor
  · exact le_trans (inf_le_left : c.K ≤ c.K1) (theoremC_K1_le_U c)
  · intro h hh k hk
    rcases Subgroup.mem_inf.mp hk with ⟨hk1, hk2⟩
    have hc1 : h * k * h⁻¹ ∈ c.K1 := h1.2 h hh k hk1
    have hc2 : h * k * h⁻¹ ∈ c.K2 := h2.2 h hh k hk2
    change h * k * h⁻¹ ∈ c.K1 ⊓ c.K2
    exact Subgroup.mem_inf.mpr ⟨hc1, hc2⟩

/-- `K` as a subgroup of `U`. -/
private def theoremC_KU (c : Hyp11 G) [Hyp11KData c] : Subgroup (↥c.U) :=
  (c.K : Subgroup G).subgroupOf c.U

/-- `K ⊴ U`, as a subgroup-of-`U` normality. -/
private lemma theoremC_KU_normal (c : Hyp11 G) [Hyp11KData c] : (theoremC_KU c).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (theoremC_K_le_U c)).mpr ?_
  intro u hu
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hk
    exact (theoremC_K_normal_in_U c).2 u hu h hk
  · intro hk
    have h1 := (theoremC_K_normal_in_U c).2 u⁻¹ ((c.U).inv_mem hu) (u * h * u⁻¹) hk
    have hEq : u⁻¹ * (u * h * u⁻¹) * u = h := by group
    simpa [hEq, inv_inv] using h1

/-- `K` is abelian (Fact 1.5(iii) applied to `K₁`). -/
private lemma theoremC_KU_comm (c : Hyp11 G) [Hyp11KData c] : IsMulCommutative (↥(theoremC_KU c)) := by
  have hK1 : IsMulCommutative (↥(c.K1 : Subgroup G)) := by
    have h := fact_1_5_iii_inverted_subgroup_abelian_normal
      (X := c.U) (s := c.t1) c.t1_involution (theoremC_U_coprime_two c)
      (by
        intro x hx
        exact S_normalizes_U c c.t1 c.t1_mem_S x hx)
      (theoremC_K1_eq_invertedElements c)
    exact h.1
  rw [isMulCommutative_iff]
  intro a b
  apply Subtype.ext
  change (a : ↥c.U) * b = b * a
  apply Subtype.ext
  change ((a : ↥c.U) : G) * ((b : ↥c.U) : G) = ((b : ↥c.U) : G) * ((a : ↥c.U) : G)
  have ha : ((a : ↥c.U) : G) ∈ (c.K1 : Subgroup G) := by
    exact (inf_le_left : c.K ≤ c.K1) (Subgroup.mem_subgroupOf.mp a.2)
  have hb : ((b : ↥c.U) : G) ∈ (c.K1 : Subgroup G) := by
    exact (inf_le_left : c.K ≤ c.K1) (Subgroup.mem_subgroupOf.mp b.2)
  have hc := (isMulCommutative_iff.mp hK1)
      ⟨((a : ↥c.U) : G), ha⟩ ⟨((b : ↥c.U) : G), hb⟩
  exact congrArg Subtype.val hc

/-- In an abelian group every irreducible character is linear. -/
private lemma theoremC_irr_linear_of_comm {K : Type u} [Group K] [Fintype K]
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
    simp [Representation.character]

/-- The inverse (complex-conjugate) of a linear character of an abelian group. -/
@[reducible] private noncomputable def theoremC_irrInv {K : Type u} [Group K] [Fintype K]
    (hcomm : IsMulCommutative K) (β : IrrBG19 K) : IrrBG19 K :=
  letI : CommGroup K := { (inferInstance : Group K) with
    mul_comm := by
      intro a b
      exact (isMulCommutative_iff.mp hcomm) a b }
  let hlin : IsLinearCharacter β.1 := theoremC_irr_linear_of_comm hcomm β
  let φ : K →* ℂˣ := linearCharHom hlin
  ⟨fun k => (((φ.comp invMonoidHom) k : ℂˣ) : ℂ),
    (isLinearCharacter_of_hom (φ.comp invMonoidHom)).1⟩

/-- `theoremC_irrInv` is pointwise inversion. -/
private lemma theoremC_irrInv_apply {K : Type u} [Group K] [Fintype K]
    (hcomm : IsMulCommutative K) (β : IrrBG19 K) (k : K) :
    (theoremC_irrInv hcomm β).1 k = β.1 k⁻¹ := by
  rfl

/-- Inversion is an involution on `IrrBG19` of an abelian group. -/
private lemma theoremC_irrInv_inv {K : Type u} [Group K] [Fintype K]
    (hcomm : IsMulCommutative K) (β : IrrBG19 K) :
    theoremC_irrInv hcomm (theoremC_irrInv hcomm β) = β := by
  apply Subtype.ext
  ext k
  rw [theoremC_irrInv_apply hcomm, theoremC_irrInv_apply hcomm, inv_inv]

/-- Inversion does not change the multiplicity of a constituent in a character
fixed by inversion. -/
private lemma theoremC_scalarProduct_restrict_irrInv_eq {K : Type u} [Group K] [Fintype K]
    (hcomm : IsMulCommutative K) (α : ClassFunction K) (β : IrrBG19 K)
    (hfix : ∀ k : K, α k = α k⁻¹) :
    scalarProduct K α (theoremC_irrInv hcomm β).1 = scalarProduct K α β.1 := by
  unfold scalarProduct theoremC_irrInv
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
    change α k * star ((theoremC_irrInv hcomm β).1 k) = α k⁻¹ * star (β.1 k⁻¹)
    rw [theoremC_irrInv_apply hcomm]
    rw [hfix k]

/-- A reflection in `S \ S0` that fixes `α` makes `α` inversion-invariant on
`K`. -/
private lemma theoremC_restrict_alpha_inv_eq (c : Hyp11 G) [Hyp11KData c] {x : G}
    (hxS : x ∈ (c.S : Subgroup G)) (hxnot : x ∉ (c.S0 : Subgroup G))
    (α : Irr (↥c.U))
    (hfix : conjIrrS c hxS α = α) :
    ∀ k : ↥(theoremC_KU c),
      α.1 (k : ↥c.U) = α.1 ((k⁻¹ : ↥(theoremC_KU c)) : ↥c.U) := by
  intro k
  have hkG : ((k : ↥c.U) : G) ∈ c.K := by
    exact Subgroup.mem_subgroupOf.mp k.2
  have hinv : x * ((k : ↥c.U) : G) * x⁻¹ = ((k : ↥c.U) : G)⁻¹ :=
    theoremC_reflection_inverts_K c hxS hxnot hkG
  have hval : α.1 ⟨x * ((k : ↥c.U) : G) * x⁻¹,
      S_normalizes_U c x hxS ((k : ↥c.U) : G) (theoremC_K_le_U c hkG)⟩ = α.1 (k : ↥c.U) := by
    have hc := congrFun (congrArg Subtype.val hfix) (k : ↥c.U)
    exact hc
  rw [← hval]
  apply congrArg α.1
  apply Subtype.ext
  exact hinv

/-- Conjugation action of `U` on `K`. -/
@[reducible] private noncomputable instance theoremC_KU_action (c : Hyp11 G) [Hyp11KData c] :
    MulDistribMulAction (↥c.U) (↥(theoremC_KU c)) :=
  letI : (theoremC_KU c).Normal := theoremC_KU_normal c
  MulDistribMulAction.compHom (↥(theoremC_KU c))
    (MulAut.conjNormal (G := ↥c.U) (H := theoremC_KU c))

/-- Conjugation action of `U` on the irreducible characters of `K`. -/
@[reducible] private noncomputable instance theoremC_KU_irr_action (c : Hyp11 G) [Hyp11KData c] :
    MulAction (↥c.U) (IrrBG19 (↥(theoremC_KU c))) where
  smul s β := ⟨fun u => β.1 (s⁻¹ • u),
    isIrreducibleCharacter_congr
      (MulDistribMulAction.toMulEquiv (M := ↥(theoremC_KU c)) (G := ↥c.U) s⁻¹) β.2⟩
  one_smul β := by
    ext u
    change β.1 ((1 : ↥c.U)⁻¹ • u) = β.1 u
    simp
  mul_smul s t β := by
    ext u
    change β.1 (((s * t)⁻¹ : ↥c.U) • u) = β.1 (t⁻¹ • (s⁻¹ • u))
    rw [mul_inv_rev, mul_smul]

/-- The `U`-orbit of a character of `K` has odd cardinality. -/
private lemma theoremC_KU_orbit_odd (c : Hyp11 G) [Hyp11KData c] (β : IrrBG19 (↥(theoremC_KU c))) :
    Odd (Nat.card (MulAction.orbit (↥c.U) β)) := by
  let : MulDistribMulAction (↥c.U) (↥(theoremC_KU c)) := theoremC_KU_action c
  let : MulAction (↥c.U) (IrrBG19 (↥(theoremC_KU c))) := theoremC_KU_irr_action c
  have hcop : Nat.Coprime 2 (Nat.card (↥c.U)) := theoremC_U_coprime_two c
  have hdiv : Nat.card (MulAction.orbit (↥c.U) β) ∣ Nat.card (↥c.U) := by
    have hst : Fintype (MulAction.orbit (↥c.U) β) := by infer_instance
    have hstab : Fintype (MulAction.stabilizer (↥c.U) β) := by infer_instance
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (G := ↥c.U) (X := IrrBG19 (↥(theoremC_KU c))) β
    exact ⟨Nat.card (MulAction.stabilizer (↥c.U) β), by
      simpa [Nat.card_eq_fintype_card] using h.symm⟩
  have hcopOrbit : Nat.Coprime 2 (Nat.card (MulAction.orbit (↥c.U) β)) :=
    hcop.coprime_dvd_right hdiv
  exact Nat.coprime_two_left.mp hcopOrbit

/-- The character of an arbitrary finite-dimensional complex representation is
a `Theory.Character.IsCharacter`. -/
private lemma theoremC_isCharacter_of_representation {K : Type u} [Group K] [Fintype K]
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
  simp

/-- An irreducible finite-dimensional complex representation of an abelian
group gives an `IrrBG19` character (always linear). -/
private noncomputable def theoremC_charOfIrrRep {K : Type u} [CommGroup K] [Fintype K]
    {M : Type v} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (σ : Representation ℂ K M) (hσ : σ.IsIrreducible) : IrrBG19 K := by
  letI : Representation.IsIrreducible σ := hσ
  have hchar : IsCharacter σ.character := theoremC_isCharacter_of_representation σ
  have hnorm : scalarProductInv K σ.character σ.character = 1 := by
    have hnon : Nonempty (σ.Equiv σ) := ⟨Representation.Equiv.refl σ⟩
    simpa [scalarProductInv, hnon] using (Representation.char_orthonormal (ρ := σ) (σ := σ))
  exact ⟨σ.character, isIrreducibleCharacter_of_norm_one_inv hchar hnorm⟩

variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Clifford's theorem for `α|_K` at the character level: the restriction
character is the sum of the characters of the conjugate summands. -/
private lemma theoremC_clifford_restrict_char_sum (c : Hyp11 G) [Hyp11KData c] {H : Subgroup (↥c.U)} [H.Normal]
    (ρ : Representation ℂ (↥c.U) V) (hρ : ρ.IsIrreducible)
    (W : Subrepresentation (ρ.comp H.subtype)) (hW : W.toRepresentation.IsIrreducible) :
    ∃ (n : ℕ) (g : Fin n → ↥c.U),
      DirectSum.IsInternal
        (fun i : Fin n => (Theory.Representation.conjugateSubrepresentation ρ H W (g i)).toSubmodule) ∧
      (∀ i : Fin n,
        (Theory.Representation.conjugateSubrepresentation ρ H W (g i)).toRepresentation.IsIrreducible) ∧
      (∀ i : Fin n,
        Nonempty
          ((Theory.Representation.conjugateSubrepresentation ρ H W (g i)).toRepresentation ≃ₗ
            Theory.Representation.conjugateRep W.toRepresentation (g i))) ∧
      ∀ k : H, ρ.character (k : ↥c.U) =
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
  have hf : ∀ i : Fin n, Set.MapsTo (ρ (k : ↥c.U)) (N i) (N i) := by
    intro i x hx
    exact (Theory.Representation.conjugateSubrepresentation ρ H W (g i)).apply_mem_toSubmodule k hx
  have htr := LinearMap.trace_eq_sum_trace_restrict (R := ℂ) (M := V) (N := N) hsum' (f := ρ (k : ↥c.U)) hf
  change LinearMap.trace ℂ V (ρ (k : ↥c.U)) =
    ∑ i : Fin n, LinearMap.trace ℂ (N i) ((ρ (k : ↥c.U)).restrict (hf i))
  rw [htr]

/-- Clifford transitivity at character level: all irreducible constituents of
`α|_K` lie in the same `U`-orbit. -/
private lemma theoremC_constituents_conjugate (c : Hyp11 G) [Hyp11KData c] (α : Irr (↥c.U))
    (β : IrrBG19 (↥(theoremC_KU c)))
    (hβ : scalarProduct (↥(theoremC_KU c))
      (fun k : ↥(theoremC_KU c) => α.1 (k : ↥c.U)) β.1 ≠ 0) :
    ∀ γ : IrrBG19 (↥(theoremC_KU c)),
      scalarProduct (↥(theoremC_KU c))
        (fun k : ↥(theoremC_KU c) => α.1 (k : ↥c.U)) γ.1 ≠ 0 →
        γ ∈ MulAction.orbit (↥c.U) β := by
  classical
  rcases α.2 with ⟨n, ρ, hρ, hαeq⟩
  have : (theoremC_KU c).Normal := theoremC_KU_normal c
  have : Nontrivial (Fin n → ℂ) :=
    Subrepresentation.irreducible_module_nontrivial (ρ := ρ)
  rcases Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
      (ρ := ρ.comp (theoremC_KU c).subtype) with ⟨W, hW⟩
  rcases theoremC_clifford_restrict_char_sum c (H := theoremC_KU c) (ρ := ρ) hρ W hW with
    ⟨n0, g, hsum, hirr, hequiv, hchar⟩
  let : CommGroup (↥(theoremC_KU c)) := { (inferInstance : Group (↥(theoremC_KU c))) with
    mul_comm := by
      intro a b
      exact (isMulCommutative_iff.mp (theoremC_KU_comm c)) a b }
  let β0 : IrrBG19 (↥(theoremC_KU c)) := theoremC_charOfIrrRep W.toRepresentation hW
  let : MulDistribMulAction (↥c.U) (↥(theoremC_KU c)) := theoremC_KU_action c
  let : MulAction (↥c.U) (IrrBG19 (↥(theoremC_KU c))) := theoremC_KU_irr_action c
  have hchar' : ∀ k : ↥(theoremC_KU c), α.1 (k : ↥c.U) =
      ∑ i : Fin n0,
        ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation).character k := by
    intro k
    rw [hαeq]
    exact hchar k
  have hfun : (fun k : ↥(theoremC_KU c) => α.1 (k : ↥c.U)) =
      ∑ i : Fin n0,
        ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation).character := by
    funext k
    simpa using hchar' k
  have hsummand_orbit (i : Fin n0) :
      theoremC_charOfIrrRep
        ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation) (hirr i) ∈
        MulAction.orbit (↥c.U) β0 := by
    have hχi : theoremC_charOfIrrRep
        ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation) (hirr i) =
        (((g i : ↥c.U)⁻¹) • β0) := by
      apply Subtype.ext
      ext k
      have he := Classical.choice (hequiv i)
      have heRep := Theory.Representation.RepEquiv.toRepresentationEquiv he
      have hchars := Representation.char_iso heRep
      have hchar_smul : (((g i : ↥c.U)⁻¹) • β0).1 =
          fun u : ↥(theoremC_KU c) => β0.1 ((((g i : ↥c.U)⁻¹)⁻¹) • u) := rfl
      simp only [theoremC_charOfIrrRep, hchar_smul, inv_inv]
      rw [hchars]
      rfl
    rw [hχi]
    exact MulAction.mem_orbit β0 ((g i : ↥c.U)⁻¹)
  have all_mem (γ : IrrBG19 (↥(theoremC_KU c)))
      (hγ : scalarProduct (↥(theoremC_KU c))
        (fun k : ↥(theoremC_KU c) => α.1 (k : ↥c.U)) γ.1 ≠ 0) :
      γ ∈ MulAction.orbit (↥c.U) β0 := by
    have hsp_sum : scalarProduct (↥(theoremC_KU c))
        (fun k : ↥(theoremC_KU c) => α.1 (k : ↥c.U)) γ.1 =
        ∑ i : Fin n0, scalarProduct (↥(theoremC_KU c))
          ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation).character γ.1 := by
      rw [hfun, scalarProduct_sum_left]
    have hcoeff (i : Fin n0) :
        scalarProduct (↥(theoremC_KU c))
          ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation).character γ.1 =
          if (theoremC_charOfIrrRep
            ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation) (hirr i)).1 = γ.1
          then 1 else 0 := by
      have hχ : ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation).character =
          (theoremC_charOfIrrRep
            ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation) (hirr i)).1 := rfl
      rw [hχ]
      exact scalarProduct_irr_ite
        (theoremC_charOfIrrRep
          ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation) (hirr i)).2 γ.2
    have hex : ∃ i : Fin n0, (theoremC_charOfIrrRep
        ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation) (hirr i)).1 = γ.1 := by
      by_contra hnone
      push Not at hnone
      have hsp0 : scalarProduct (↥(theoremC_KU c))
          (fun k : ↥(theoremC_KU c) => α.1 (k : ↥c.U)) γ.1 = 0 := by
        rw [hsp_sum]
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hne' : (theoremC_charOfIrrRep
            ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation) (hirr i)).1 ≠ γ.1 := by
          intro h
          exact hnone i h
        rw [hcoeff i]
        exact if_neg hne'
      exact hγ hsp0
    rcases hex with ⟨i, hi⟩
    have hmem : theoremC_charOfIrrRep
        ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation) (hirr i) ∈
        MulAction.orbit (↥c.U) β0 := hsummand_orbit i
    have hiSub : theoremC_charOfIrrRep
        ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation) (hirr i) = γ :=
      Subtype.ext hi
    rwa [hiSub] at hmem
  intro γ hγ
  have hβorbit : β ∈ MulAction.orbit (↥c.U) β0 := all_mem β hβ
  have hγorbit : γ ∈ MulAction.orbit (↥c.U) β0 := all_mem γ hγ
  have hβ0orbit : β0 ∈ MulAction.orbit (↥c.U) β := MulAction.mem_orbit_symm.mp hβorbit
  have horbit : MulAction.orbit (↥c.U) β0 = MulAction.orbit (↥c.U) β :=
    MulAction.orbit_eq_iff.2 hβ0orbit
  rwa [← horbit]

/-- If a reflection fixes `α` and inverts `K`, inversion preserves the
occurring `U`-orbit of any constituent of `α|_K`. -/
private lemma theoremC_irrInv_orbit_mem (c : Hyp11 G) [Hyp11KData c] {x : G}
    (hxS : x ∈ (c.S : Subgroup G)) (hxnot : x ∉ (c.S0 : Subgroup G))
    (α : Irr (↥c.U)) (hfix : conjIrrS c hxS α = α) :
    letI : MulDistribMulAction (↥c.U) (↥(theoremC_KU c)) := theoremC_KU_action c
    letI : MulAction (↥c.U) (IrrBG19 (↥(theoremC_KU c))) := theoremC_KU_irr_action c
    ∀ (β : IrrBG19 (↥(theoremC_KU c))),
      scalarProduct (↥(theoremC_KU c))
        (fun k : ↥(theoremC_KU c) => α.1 (k : ↥c.U)) β.1 ≠ 0 →
    ∀ γ : IrrBG19 (↥(theoremC_KU c)), γ ∈ MulAction.orbit (↥c.U) β →
      theoremC_irrInv (theoremC_KU_comm c) γ ∈ MulAction.orbit (↥c.U) β := by
  classical
  intro β hβ γ hγ
  have hβinv : scalarProduct (↥(theoremC_KU c))
      (fun k : ↥(theoremC_KU c) => α.1 (k : ↥c.U))
      (theoremC_irrInv (theoremC_KU_comm c) β).1 ≠ 0 := by
    rw [theoremC_scalarProduct_restrict_irrInv_eq (theoremC_KU_comm c)
      (fun k : ↥(theoremC_KU c) => α.1 (k : ↥c.U)) β
      (theoremC_restrict_alpha_inv_eq c hxS hxnot α hfix)]
    exact hβ
  have hβinvO : theoremC_irrInv (theoremC_KU_comm c) β ∈ MulAction.orbit (↥c.U) β :=
    theoremC_constituents_conjugate c α β hβ (theoremC_irrInv (theoremC_KU_comm c) β) hβinv
  rcases (MulAction.mem_orbit_iff.mp hγ) with ⟨u, hu⟩
  have hcom : theoremC_irrInv (theoremC_KU_comm c) (u • β) = u • theoremC_irrInv (theoremC_KU_comm c) β := by
    apply Subtype.ext
    ext k
    rw [theoremC_irrInv_apply (theoremC_KU_comm c)]
    change (u • β).1 k⁻¹ = (theoremC_irrInv (theoremC_KU_comm c) β).1 (u⁻¹ • k)
    rw [theoremC_irrInv_apply (theoremC_KU_comm c)]
    change β.1 (u⁻¹ • k⁻¹) = β.1 ((u⁻¹ • k)⁻¹)
    rw [smul_inv' u⁻¹ k]
  rw [← hu, hcom]
  have hOrbEq : MulAction.orbit (↥c.U) (theoremC_irrInv (theoremC_KU_comm c) β) =
      MulAction.orbit (↥c.U) β :=
    MulAction.orbit_eq_iff.2 hβinvO
  rw [← hOrbEq]
  exact MulAction.mem_orbit (theoremC_irrInv (theoremC_KU_comm c) β) u

/-- The occurring `U`-orbit contains a self-inverse character. -/
private lemma theoremC_exists_self_inverse_in_orbit (c : Hyp11 G) [Hyp11KData c] {x : G}
    (hxS : x ∈ (c.S : Subgroup G)) (hxnot : x ∉ (c.S0 : Subgroup G))
    (α : Irr (↥c.U)) (hfix : conjIrrS c hxS α = α) :
    letI : MulDistribMulAction (↥c.U) (↥(theoremC_KU c)) := theoremC_KU_action c
    letI : MulAction (↥c.U) (IrrBG19 (↥(theoremC_KU c))) := theoremC_KU_irr_action c
    ∀ (β : IrrBG19 (↥(theoremC_KU c))),
      scalarProduct (↥(theoremC_KU c))
        (fun k : ↥(theoremC_KU c) => α.1 (k : ↥c.U)) β.1 ≠ 0 →
    ∃ γ : IrrBG19 (↥(theoremC_KU c)), γ ∈ MulAction.orbit (↥c.U) β ∧
      theoremC_irrInv (theoremC_KU_comm c) γ = γ := by
  classical
  intro β hβ
  let O : Set (IrrBG19 (↥(theoremC_KU c))) := MulAction.orbit (↥c.U) β
  let f : O ≃ O := {
    toFun := fun γ => ⟨theoremC_irrInv (theoremC_KU_comm c) γ.1,
      theoremC_irrInv_orbit_mem c hxS hxnot α hfix β hβ γ.1 γ.2⟩
    invFun := fun γ => ⟨theoremC_irrInv (theoremC_KU_comm c) γ.1,
      theoremC_irrInv_orbit_mem c hxS hxnot α hfix β hβ γ.1 γ.2⟩
    left_inv := by
      intro γ
      apply Subtype.ext
      exact theoremC_irrInv_inv (theoremC_KU_comm c) γ.1
    right_inv := by
      intro γ
      apply Subtype.ext
      exact theoremC_irrInv_inv (theoremC_KU_comm c) γ.1
  }
  have hf2 : f ^ 2 = 1 := by
    apply Equiv.ext
    intro γ
    apply Subtype.ext
    exact theoremC_irrInv_inv (theoremC_KU_comm c) γ.1
  have hodd : Odd (Fintype.card O) := by
    have h := theoremC_KU_orbit_odd c β
    simpa [O] using h
  rcases exists_fixed_of_involution_odd_card f hf2 hodd with ⟨γ, hγfix⟩
  refine ⟨γ.1, γ.2, ?_⟩
  exact congrArg Subtype.val hγfix

/-- A finite sum of `0/1` terms containing a `1` is nonzero. -/
private lemma theoremC_sum_ite_ne_zero_of_mem {n : ℕ} {t : Fin n → Prop}
    [DecidablePred t] (i0 : Fin n) (ht0 : t i0) :
    (∑ i : Fin n, if t i then (1 : ℂ) else 0) ≠ 0 := by
  classical
  have hsplit : (∑ i : Fin n, if t i then (1 : ℂ) else 0) =
      (1 : ℂ) + ∑ i ∈ (Finset.univ.erase i0), (if t i then (1 : ℂ) else 0) := by
    rw [← Finset.sum_erase_add (s := Finset.univ)
      (f := fun i => if t i then (1 : ℂ) else 0) (a := i0) (Finset.mem_univ i0)]
    rw [if_pos ht0]
    ring
  rw [hsplit]
  intro hz
  have hre := congrArg Complex.re hz
  rw [Complex.add_re, Complex.one_re] at hre
  norm_num at hre
  have hsum_re : (∑ i ∈ (Finset.univ.erase i0), (if t i then (1 : ℂ) else 0)).re =
      ∑ i ∈ (Finset.univ.erase i0), (if t i then (1 : ℂ) else 0).re := by
    simpa using (map_sum Complex.reAddGroupHom
      (fun i => (if t i then (1 : ℂ) else 0)) (Finset.univ.erase i0))
  have hnonneg : 0 ≤ (∑ i ∈ (Finset.univ.erase i0), (if t i then (1 : ℂ) else 0)).re := by
    rw [hsum_re]
    refine Finset.sum_nonneg ?_
    intro i hi
    by_cases h : t i
    · simp [h]
    · simp [h]
  nlinarith

/-- A self-inverse linear character of an odd-order abelian group is
trivial. -/
private lemma theoremC_self_inverse_linear_char_trivial {K : Type u} [Group K] [Fintype K]
    (hK2' : Nat.Coprime 2 (Nat.card K)) (hcomm : IsMulCommutative K)
    (γ : IrrBG19 K) (hγ : theoremC_irrInv hcomm γ = γ) :
    γ.1 = (1 : ClassFunction K) := by
  classical
  let : CommGroup K := { (inferInstance : Group K) with
    mul_comm := by
      intro a b
      exact (isMulCommutative_iff.mp hcomm) a b }
  have hlin : IsLinearCharacter γ.1 := theoremC_irr_linear_of_comm hcomm γ
  ext k
  have hval : γ.1 k = γ.1 k⁻¹ := by
    have hk := congrFun (congrArg Subtype.val hγ) k
    rw [theoremC_irrInv_apply hcomm] at hk
    exact hk.symm
  have hsq : (γ.1 k) ^ 2 = 1 := by
    calc
      (γ.1 k) ^ 2 = γ.1 k * γ.1 k := by ring
      _ = γ.1 k * γ.1 k⁻¹ := by rw [hval]
      _ = γ.1 (k * k⁻¹) := (linearChar_mul hlin k k⁻¹).symm
      _ = γ.1 1 := by rw [mul_inv_cancel]
      _ = 1 := hlin.2
  have hγpow : (γ.1 k) ^ Nat.card K = 1 := by
    have hφpow : ((linearCharHom hlin k : ℂˣ) : ℂ) ^ Nat.card K = 1 := by
      rw [← Units.val_pow_eq_pow_val]
      have hpow : (linearCharHom hlin k) ^ Nat.card K = 1 := by
        rw [← map_pow]
        have hkpow : k ^ Nat.card K = 1 := pow_card_eq_one' (G := K) (x := k)
        rw [hkpow, map_one]
      rw [hpow]
      simp
    rw [linearCharHom_apply hlin k] at hφpow
    exact hφpow
  have horder2 : orderOf (γ.1 k) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have horderK : orderOf (γ.1 k) ∣ Nat.card K := orderOf_dvd_of_pow_eq_one hγpow
  have hcop : Nat.Coprime (orderOf (γ.1 k)) (Nat.card K) :=
    hK2'.coprime_dvd_left horder2
  have hord1 : orderOf (γ.1 k) = 1 := Nat.Coprime.eq_one_of_dvd hcop horderK
  have hk1 : γ.1 k = 1 := orderOf_eq_one_iff.mp hord1
  simp [hk1]

/-- The trivial character of `K` as an irreducible character. -/
private noncomputable def theoremC_trivial_irr (c : Hyp11 G) [Hyp11KData c] :
    IrrBG19 (↥(theoremC_KU c)) :=
  ⟨(1 : ClassFunction (↥(theoremC_KU c))),
    (isLinearCharacter_of_hom (1 : ↥(theoremC_KU c) →* ℂˣ)).1⟩

/-- The `U`-orbit of the trivial character of `K` is a singleton. -/
private lemma theoremC_trivial_char_orbit_singleton (c : Hyp11 G) [Hyp11KData c] :
    MulAction.orbit (↥c.U) (theoremC_trivial_irr c) = {theoremC_trivial_irr c} := by
  classical
  let : MulDistribMulAction (↥c.U) (↥(theoremC_KU c)) := theoremC_KU_action c
  let : MulAction (↥c.U) (IrrBG19 (↥(theoremC_KU c))) := theoremC_KU_irr_action c
  apply Set.ext
  intro γ
  constructor
  · intro hγ
    rcases (MulAction.mem_orbit_iff.mp hγ) with ⟨u, hu⟩
    have hγeq : γ = theoremC_trivial_irr c := by
      apply Subtype.ext
      ext k
      change γ.1 k = (theoremC_trivial_irr c).1 k
      rw [← hu]
      rfl
    exact hγeq
  · intro hγ
    rw [hγ]
    exact MulAction.mem_orbit (theoremC_trivial_irr c) (1 : ↥c.U)

/-- Every irreducible constituent of `α|_K` is trivial when a reflection of
`S \ S0` fixes `α`. -/
private lemma theoremC_fixed_alpha_constituents_trivial (c : Hyp11 G) [Hyp11KData c] {x : G}
    (hxS : x ∈ (c.S : Subgroup G)) (hxnot : x ∉ (c.S0 : Subgroup G))
    (α : Irr (↥c.U)) (hfix : conjIrrS c hxS α = α) :
    letI : MulDistribMulAction (↥c.U) (↥(theoremC_KU c)) := theoremC_KU_action c
    letI : MulAction (↥c.U) (IrrBG19 (↥(theoremC_KU c))) := theoremC_KU_irr_action c
    ∀ β : IrrBG19 (↥(theoremC_KU c)),
      scalarProduct (↥(theoremC_KU c))
        (fun k : ↥(theoremC_KU c) => α.1 (k : ↥c.U)) β.1 ≠ 0 →
        β = theoremC_trivial_irr c := by
  classical
  intro β hβ
  have hKcard : Nat.card (↥(theoremC_KU c)) = Nat.card ↥c.K := by
    exact Nat.card_congr {
      toFun := fun u : ↥(theoremC_KU c) =>
        ⟨((u : ↥c.U) : G), Subgroup.mem_subgroupOf.mp u.2⟩
      invFun := fun k : ↥c.K =>
        ⟨⟨(k : G), theoremC_K_le_U c k.2⟩, Subgroup.mem_subgroupOf.mpr k.2⟩
      left_inv := by intro u; apply Subtype.ext; rfl
      right_inv := by intro k; apply Subtype.ext; rfl }
  have hKodd : Nat.Coprime 2 (Nat.card (↥(theoremC_KU c))) := by
    rw [hKcard]
    exact theoremC_K_odd c
  rcases theoremC_exists_self_inverse_in_orbit c hxS hxnot α hfix β hβ with ⟨γ, hγorbit, hγinv⟩
  have hγtriv : γ = theoremC_trivial_irr c := by
    apply Subtype.ext
    exact theoremC_self_inverse_linear_char_trivial hKodd (theoremC_KU_comm c) γ hγinv
  have hβ_in_γ : β ∈ MulAction.orbit (↥c.U) γ := MulAction.mem_orbit_symm.mp hγorbit
  have hβ_in_triv : β ∈ MulAction.orbit (↥c.U) (theoremC_trivial_irr c) := by
    rw [hγtriv] at hβ_in_γ
    exact hβ_in_γ
  have hsing := theoremC_trivial_char_orbit_singleton c
  rw [hsing] at hβ_in_triv
  simpa using hβ_in_triv

/-- A reflection in `S \ S0` fixing `α ∈ Irr(U)` forces `K ≤ ker α`: for
every `k ∈ K`, `α(k) = α(1)`.  This is the character-side implication
needed for equation (3) ("inverting `K`, each element of `S − S0` moves
`α`" — contrapositive). -/
private lemma theoremC_reflection_fixed_char_kills_K (c : Hyp11 G) [Hyp11KData c] {x : G}
    (hxS : x ∈ (c.S : Subgroup G)) (hxnot : x ∉ (c.S0 : Subgroup G))
    (α : Irr (↥c.U)) (hfix : conjIrrS c hxS α = α) :
    ∀ k : G, (hk : k ∈ c.K) →
      α.1 ⟨k, theoremC_K_le_U c hk⟩ = α.1 1 := by
  classical
  rcases α.2 with ⟨n, ρ, hρ, hαeq⟩
  have : (theoremC_KU c).Normal := theoremC_KU_normal c
  have : Nontrivial (Fin n → ℂ) :=
    Subrepresentation.irreducible_module_nontrivial (ρ := ρ)
  rcases Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
      (ρ := ρ.comp (theoremC_KU c).subtype) with ⟨W, hW⟩
  rcases theoremC_clifford_restrict_char_sum c (H := theoremC_KU c) (ρ := ρ) hρ W hW with
    ⟨n0, g, hsum, hirr, hequiv, hchar⟩
  let : MulDistribMulAction (↥c.U) (↥(theoremC_KU c)) := theoremC_KU_action c
  let : MulAction (↥c.U) (IrrBG19 (↥(theoremC_KU c))) := theoremC_KU_irr_action c
  let : CommGroup (↥(theoremC_KU c)) := { (inferInstance : Group (↥(theoremC_KU c))) with
    mul_comm := by
      intro a b
      exact (isMulCommutative_iff.mp (theoremC_KU_comm c)) a b }
  have hchar' : ∀ k0 : ↥(theoremC_KU c), α.1 (k0 : ↥c.U) =
      ∑ i : Fin n0,
        ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation).character k0 := by
    intro k0
    rw [hαeq]
    exact hchar k0
  have hfun : (fun k0 : ↥(theoremC_KU c) => α.1 (k0 : ↥c.U)) =
      ∑ i : Fin n0,
        ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation).character := by
    funext k0
    simpa using hchar' k0
  have hsummand_trivial (i : Fin n0) :
      ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation).character =
        (1 : ClassFunction (↥(theoremC_KU c))) := by
    let βi : IrrBG19 (↥(theoremC_KU c)) :=
      theoremC_charOfIrrRep
        ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation) (hirr i)
    have hβi : scalarProduct (↥(theoremC_KU c))
        (fun k0 : ↥(theoremC_KU c) => α.1 (k0 : ↥c.U)) βi.1 ≠ 0 := by
      have hsp : scalarProduct (↥(theoremC_KU c))
          (fun k0 : ↥(theoremC_KU c) => α.1 (k0 : ↥c.U)) βi.1 =
          ∑ j : Fin n0, (if (theoremC_charOfIrrRep
            ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g j)).toRepresentation) (hirr j)).1 = βi.1
            then (1 : ℂ) else 0) := by
        rw [hfun, scalarProduct_sum_left]
        refine Finset.sum_congr rfl ?_
        intro j hj
        have hχj : ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g j)).toRepresentation).character =
            (theoremC_charOfIrrRep
              ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g j)).toRepresentation) (hirr j)).1 := rfl
        rw [hχj]
        exact scalarProduct_irr_ite
          (theoremC_charOfIrrRep
            ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g j)).toRepresentation) (hirr j)).2
          βi.2
      rw [hsp]
      refine theoremC_sum_ite_ne_zero_of_mem i ?_
      change (theoremC_charOfIrrRep
        ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation) (hirr i)).1 =
        (theoremC_charOfIrrRep
          ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation) (hirr i)).1
      rfl
    have hβi_triv := theoremC_fixed_alpha_constituents_trivial c hxS hxnot α hfix βi hβi
    have hval : (theoremC_charOfIrrRep
        ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation) (hirr i)).1 =
        (1 : ClassFunction (↥(theoremC_KU c))) := by
      have hsub := congrArg Subtype.val hβi_triv
      simpa [βi, theoremC_trivial_irr] using hsub
    simpa [theoremC_charOfIrrRep] using hval
  intro k hk
  let kU : ↥(theoremC_KU c) :=
    ⟨⟨k, theoremC_K_le_U c hk⟩, Subgroup.mem_subgroupOf.mpr hk⟩
  have hαk : α.1 (kU : ↥c.U) = ∑ i : Fin n0,
      ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation).character kU :=
    hchar' kU
  have hsum : (∑ i : Fin n0,
      ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation).character kU) =
      (n0 : ℂ) := by
    calc
      (∑ i : Fin n0,
          ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation).character kU)
          = ∑ i : Fin n0, (1 : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hsummand_trivial i]
            rfl
      _ = (n0 : ℂ) := by simp
  have hα1 : α.1 (1 : ↥c.U) = (n0 : ℂ) := by
    have h1 := hchar (1 : ↥(theoremC_KU c))
    have hsum1 : (∑ i : Fin n0,
        ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation).character
          (1 : ↥(theoremC_KU c))) = (n0 : ℂ) := by
      calc
        (∑ i : Fin n0,
            ((Theory.Representation.conjugateSubrepresentation ρ (theoremC_KU c) W (g i)).toRepresentation).character
              (1 : ↥(theoremC_KU c)))
            = ∑ i : Fin n0, (1 : ℂ) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hsummand_trivial i]
              rfl
        _ = (n0 : ℂ) := by simp
    have hρ1 : ρ.character (1 : ↥c.U) = (n0 : ℂ) := by
      simpa using (h1.trans hsum1)
    rw [hαeq]
    simpa using hρ1
  have hEq : α.1 (kU : ↥c.U) = α.1 (1 : ↥c.U) :=
    (hαk.trans hsum).trans hα1.symm
  simpa [kU] using hEq

/-! ## Equation (3) degree bound: `2β(1)² ≤ |B|` for `β ≠ β̄`

For `β ∈ Irr(B)` with `β ≠ β̄`, the conjugate pair contributes two
distinct constituents to `θ = β + β̄`, so `⟨θ,θ⟩ = 2` and the
Cauchy--Schwarz bound `theoremC_char_degree_sq_le_card_mul_norm` gives
`4β(1)² ≤ 2|B|`.  The remaining self-conjugate case (`β = β̄`) is the
real-character-of-odd-group theorem (see the task card gap audit). -/

/-- The pointwise complex conjugate of an irreducible character is an
irreducible character: `β̄(g) = star (β g) = β g⁻¹` (the dual
representation). -/
private lemma theoremC_star_irr {B : Type u} [Group B] [Fintype B]
    {β : ClassFunction B} (hβ : IsIrreducibleCharacter β) :
    IsIrreducibleCharacter (fun b : B => star (β b)) := by
  classical
  have hcharβ : IsCharacter β := isCharacter_of_isIrreducibleCharacter hβ
  have hstar (b : B) : star (β b) = β b⁻¹ := star_char_eq_char_inv hcharβ b
  have hcharβbar : IsCharacter (fun b : B => star (β b)) := by
    rcases hβ with ⟨n, ρ, _hρ, hβeq⟩
    have hcharDual : IsCharacter ρ.dual.character :=
      theoremC_isCharacter_of_representation (K := B) (σ := ρ.dual)
    have hEq : (fun b : B => star (β b)) = ρ.dual.character := by
      ext b
      rw [hstar b, hβeq]
      exact (Representation.char_dual ρ b).symm
    rwa [← hEq] at hcharDual
  have hcard_ne : (Nat.card B : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := B)).ne'
  have hsum : (∑ b : B, star (β b) * star (β b⁻¹)) = (Nat.card B : ℂ) := by
    calc
      (∑ b : B, star (β b) * star (β b⁻¹))
          = ∑ b : B, β b⁻¹ * β b := by
              refine Finset.sum_congr rfl ?_
              intro b hb
              rw [hstar b, hstar b⁻¹]
              rw [inv_inv]
      _ = ∑ b : B, β b * β b⁻¹ := by
              symm
              refine Finset.sum_bij (fun b _ => b⁻¹) ?_ ?_ ?_ ?_
              · intro b hb
                simp
              · intro a ha b hb hab
                simpa using (inv_injective hab)
              · intro b hb
                refine ⟨b⁻¹, by simp, ?_⟩
                simp
              · intro b hb
                rw [inv_inv]
      _ = ∑ b : B, β b * star (β b) := by
              refine Finset.sum_congr rfl ?_
              intro b hb
              rw [← hstar b]
      _ = (Nat.card B : ℂ) := by
              have hsp := scalarProduct_irreducible_self (G := B) hβ
              unfold scalarProduct at hsp
              calc
                (∑ b : B, β b * star (β b))
                    = (Nat.card B : ℂ) *
                        ((Nat.card B : ℂ)⁻¹ * (∑ b : B, β b * star (β b))) := by
                        rw [← mul_assoc, mul_inv_cancel₀ hcard_ne, one_mul]
                _ = (Nat.card B : ℂ) * 1 := by rw [hsp]
                _ = (Nat.card B : ℂ) := by simp
  have hnorm : scalarProductInv B (fun b : B => star (β b))
      (fun b : B => star (β b)) = 1 := by
    unfold scalarProductInv
    rw [hsum]
    field_simp [hcard_ne]
  exact isIrreducibleCharacter_of_norm_one_inv hcharβbar hnorm

/-- Equation (3)'s degree bound for the non-self-conjugate case:
`2β(1)² ≤ |B|` whenever `β ≠ β̄`. -/
private lemma theoremC_two_beta_sq_le_card_of_ne_star {B : Type u} [Group B] [Fintype B]
    {β : ClassFunction B} (hβ : IsIrreducibleCharacter β)
    (hne : β ≠ fun b : B => star (β b)) :
    2 * (β 1).re ^ 2 ≤ (Nat.card B : ℝ) := by
  classical
  let βbar : ClassFunction B := fun b : B => star (β b)
  have hβbar : IsIrreducibleCharacter βbar := by
    dsimp [βbar]
    exact theoremC_star_irr hβ
  have hθ : IsCharacter (β + βbar) := by
    exact isCharacter_add (isCharacter_of_isIrreducibleCharacter hβ)
      (isCharacter_of_isIrreducibleCharacter hβbar)
  have hnorm : (normSq B (β + βbar)).re = 2 := by
    have horth : scalarProduct B β βbar = 0 :=
      scalarProduct_irreducible_orthogonal hβ hβbar (by simpa [βbar] using hne)
    have horth' : scalarProduct B βbar β = 0 :=
      scalarProduct_irreducible_orthogonal hβbar hβ (by
        intro hEq
        apply hne
        simpa [βbar] using hEq.symm)
    have hselfβ : scalarProduct B β β = 1 := scalarProduct_irreducible_self hβ
    have hselfβbar : scalarProduct B βbar βbar = 1 := scalarProduct_irreducible_self hβbar
    have hθθ : scalarProduct B (β + βbar) (β + βbar) = 2 := by
      rw [scalarProduct_add_left, scalarProduct_add_right, scalarProduct_add_right]
      rw [hselfβ, horth, horth', hselfβbar]
      norm_num
    have hθθre := congrArg Complex.re hθθ
    norm_num at hθθre
    simpa [normSq] using hθθre
  have hbnd := theoremC_char_degree_sq_le_card_mul_norm (B := B) (θ := β + βbar) hθ
  have hβbar1 : βbar 1 = β 1 := by
    dsimp [βbar]
    change star (β 1) = β 1
    rw [star_char_eq_char_inv (isCharacter_of_isIrreducibleCharacter hβ) 1]
    simp
  have hre : ((β + βbar) 1).re = 2 * (β 1).re := by
    change (β 1 + βbar 1).re = 2 * (β 1).re
    rw [hβbar1]
    rw [Complex.add_re]
    ring
  rw [hre, hnorm] at hbnd
  have hsq : (2 * (β 1).re) ^ 2 = 4 * (β 1).re ^ 2 := by ring
  rw [hsq] at hbnd
  nlinarith

/-- Odd-order real-character endpoint: an irreducible character of a finite
group of odd order equal to its complex conjugate is the principal
character (`Section1.proposition_1_1`). -/
private lemma theoremC_self_conj_irr_eq_principal {B : Type u} [Group B] [Fintype B]
    (hodd : Odd (Nat.card B)) {β : ClassFunction B} (hβ : IsIrreducibleCharacter β)
    (hself : β = Section1.conjugateCharacter β) :
    β = (1 : ClassFunction B) := by
  classical
  rcases hβ with ⟨n, ρ, hρ, hβeq⟩
  have hfixed : ρ.character = Section1.conjugateCharacter ρ.character := by
    calc
      ρ.character = β := hβeq.symm
      _ = Section1.conjugateCharacter β := hself
      _ = Section1.conjugateCharacter ρ.character := congrArg Section1.conjugateCharacter hβeq
  by_contra hne1
  have hne_principal : ρ.character ≠ Section1.principalCharacter B := by
    intro h
    apply hne1
    rw [hβeq, h]
    rfl
  have hne_fixed : ρ.character ≠ Section1.conjugateCharacter ρ.character :=
    Section1.proposition_1_1 hodd ρ hρ hne_principal
  exact hne_fixed hfixed

/-- Equation (3)'s degree bound: for a finite group `B` of odd order with
`|B| ≥ 2`, every `β ∈ Irr(B)` satisfies `2β(1)² ≤ |B|`.  The
self-conjugate case is the odd-order real-character endpoint; the
non-self-conjugate case is `theoremC_two_beta_sq_le_card_of_ne_star`. -/
private lemma theoremC_two_beta_sq_le_card {B : Type u} [Group B] [Fintype B]
    {β : ClassFunction B} (hβ : IsIrreducibleCharacter β)
    (hodd : Odd (Nat.card B)) (hB2 : 2 ≤ Nat.card B) :
    2 * (β 1).re ^ 2 ≤ (Nat.card B : ℝ) := by
  classical
  by_cases h1 : β = (1 : ClassFunction B)
  · have hβ1 : (β 1).re = 1 := by
      rw [h1]
      simp
    have hR : (2 : ℝ) ≤ (Nat.card B : ℝ) := by exact_mod_cast hB2
    simpa [hβ1] using hR
  · have hne_star : β ≠ fun b : B => star (β b) := by
      intro hstar
      have hself : β = Section1.conjugateCharacter β := by
        funext b
        exact congrFun hstar b
      have hprincipal := theoremC_self_conj_irr_eq_principal hodd hβ hself
      exact h1 hprincipal
    exact theoremC_two_beta_sq_le_card_of_ne_star hβ hne_star

/-! ## Equation (3): direct-product restriction-to-`B` irreducibility

The paper (refs/bender-glauberman-character.tex L875--L883) derives the
restriction-to-`B` irreducibility of `α ∈ Irr(U)` from (i) `α` fixed by
`t₁` or `t₂`, (ii) `K ≤ ker α`, and (iii) the Theorem-C decomposition
`U = (B₁∩K₂) × BK` — not from the Glauberman correspondence alone.  The
abstract core is: for an abelian factor `A`, every `φ ∈ Irr(A × B)`
restricts to an irreducible character of `B`.  The theorem-C instance
needs the internal direct product `U ≅ (B₁∩K₂) × B` (factoring out `K`),
which is not derivable from the `⊔`/`hUint` hypotheses alone (they give
only set-level decomposition plus `[A,B] ≤ A`, `[A,K] ≤ K`, `[B,K] ≤ K`);
the missing component is recorded as an explicit hypothesis `e` below. -/

/-- The multiplication equivalence supplied by the source's internal direct
product hypothesis `U = (B₁ ∩ K₂) × BK`. -/
private noncomputable def theoremC_internalDirectProductMulEquiv (c : Hyp11 G) [Hyp11KData c]
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (hUint : (c.B1 ⊓ c.K2) ⊓ (c.B ⊔ c.K) = ⊥)
    (hUcomm : ⁅c.B1 ⊓ c.K2, c.B ⊔ c.K⁆ = ⊥) :
    ↥(c.B1 ⊓ c.K2) × ↥(c.B ⊔ c.K) ≃* ↥c.U := by
  classical
  let A : Subgroup G := c.B1 ⊓ c.K2
  let C : Subgroup G := c.B ⊔ c.K
  have hAleU : A ≤ c.U := by
    intro a ha
    rw [hU]
    exact (le_sup_left : A ≤ A ⊔ C) ha
  have hCleU : C ≤ c.U := by
    intro x hx
    rw [hU]
    exact (le_sup_right : C ≤ A ⊔ C) hx
  have hAcentC : A ≤ Subgroup.centralizer (C : Set G) := by
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 (by
      simpa [A, C] using hUcomm)
  let f : ↥A × ↥C →* ↥c.U := {
    toFun := fun p => ⟨(p.1 : G) * (p.2 : G),
      c.U.mul_mem (hAleU p.1.2) (hCleU p.2.2)⟩
    map_one' := by
      apply Subtype.ext
      simp
    map_mul' := by
      intro p q
      apply Subtype.ext
      have hcomm : (p.2 : G) * (q.1 : G) = (q.1 : G) * (p.2 : G) := by
        exact (Subgroup.mem_centralizer_iff.mp (hAcentC q.1.2)) (p.2 : G) p.2.2
      change ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) =
        (p.1 : G) * (p.2 : G) * ((q.1 : G) * (q.2 : G))
      calc
        ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) =
            (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by group
        _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by rw [← hcomm]
        _ = (p.1 : G) * (p.2 : G) * ((q.1 : G) * (q.2 : G)) := by group }
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro p q hpq
    have hpq' : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) :=
      congrArg Subtype.val hpq
    have hcross : (q.1 : G)⁻¹ * (p.1 : G) = (q.2 : G) * (p.2 : G)⁻¹ := by
      calc
        (q.1 : G)⁻¹ * (p.1 : G) =
            (q.1 : G)⁻¹ * ((p.1 : G) * (p.2 : G)) * (p.2 : G)⁻¹ := by group
        _ = (q.1 : G)⁻¹ * ((q.1 : G) * (q.2 : G)) * (p.2 : G)⁻¹ := by rw [hpq']
        _ = (q.2 : G) * (p.2 : G)⁻¹ := by group
    have hleftA : (q.1 : G)⁻¹ * (p.1 : G) ∈ A :=
      A.mul_mem (A.inv_mem q.1.2) p.1.2
    have hrightC : (q.2 : G) * (p.2 : G)⁻¹ ∈ C :=
      C.mul_mem q.2.2 (C.inv_mem p.2.2)
    have hcrossInf : (q.1 : G)⁻¹ * (p.1 : G) ∈ A ⊓ C :=
      Subgroup.mem_inf.mpr ⟨hleftA, by rwa [hcross]⟩
    have hcrossOne : (q.1 : G)⁻¹ * (p.1 : G) = 1 := by
      have hbot : (q.1 : G)⁻¹ * (p.1 : G) ∈ (⊥ : Subgroup G) := by
        rw [show A ⊓ C = ⊥ by simpa [A, C] using hUint] at hcrossInf
        exact hcrossInf
      exact Subgroup.mem_bot.mp hbot
    apply Prod.ext
    · apply Subtype.ext
      have h := congrArg (fun z : G => (q.1 : G) * z) hcrossOne
      simpa [mul_assoc] using h
    · apply Subtype.ext
      have hrightOne : (q.2 : G) * (p.2 : G)⁻¹ = 1 := by rwa [← hcross]
      have h := congrArg (fun z : G => z * (p.2 : G)) hrightOne
      simpa [mul_assoc] using h.symm
  · intro u
    have hu : (u : G) ∈ A ⊔ C := by
      rw [← hU]
      exact u.2
    have hAnormC : A ≤ Subgroup.normalizer (C : Set G) :=
      hAcentC.trans (Subgroup.centralizer_le_normalizer (C : Set G))
    have hset : (↑(A ⊔ C) : Set G) = (A : Set G) * (C : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right A C hAnormC
    have hprod : (u : G) ∈ (A : Set G) * (C : Set G) := by
      rwa [← hset]
    rcases hprod with ⟨a, ha, x, hx, hax⟩
    refine ⟨(⟨a, ha⟩, ⟨x, hx⟩), ?_⟩
    apply Subtype.ext
    exact hax

/-- `A = B₁ ∩ K₂` is abelian (`A ≤ K₂`, Fact 1.5(iii)). -/
private lemma theoremC_A_abelian (c : Hyp11 G) [Hyp11KData c] : IsMulCommutative (↥(c.B1 ⊓ c.K2)) := by
  have hK2abel : IsMulCommutative (↥c.K2) := (theoremC_K2_abelian_normal c).1
  rw [isMulCommutative_iff]
  intro a b
  apply Subtype.ext
  change (a : G) * (b : G) = (b : G) * (a : G)
  have ha : (a : G) ∈ c.K2 := (Subgroup.mem_inf.mp a.2).2
  have hb : (b : G) ∈ c.K2 := (Subgroup.mem_inf.mp b.2).2
  have hc := (isMulCommutative_iff.mp hK2abel) ⟨(a : G), ha⟩ ⟨(b : G), hb⟩
  exact congrArg Subtype.val hc

/-- Abstract core: for an abelian factor `A`, an irreducible character of
the direct product `A × B` restricts to an irreducible character of `B`. -/
private lemma theoremC_irr_restrict_of_abelian_factor {A B : Type u} [Group A] [Group B]
    [Fintype A] [Fintype B] (hAcomm : IsMulCommutative A)
    {φ : ClassFunction (A × B)} (hφ : IsIrreducibleCharacter φ) :
    IsIrreducibleCharacter (fun b : B => φ (1, b)) := by
  classical
  rcases irreducibleCharacter_eq_prodChar φ hφ with ⟨χ, ψ, hprod⟩
  have hχlin : IsLinearCharacter χ.1 := theoremC_irr_linear_of_comm hAcomm χ
  have hχ1 : χ.1 1 = 1 := hχlin.2
  have hEq : (fun b : B => φ (1, b)) = ψ.1 := by
    ext b
    have hb : φ (1, b) = χ.1 1 * ψ.1 b := by
      have hc := congrFun hprod (1, b)
      simpa [prodChar] using hc.symm
    rw [hb, hχ1]
    simp
  simpa [hEq] using ψ.2

set_option backward.isDefEq.respectTransparency false in
/-- Restriction from the internal direct product
`U = (B₁ ∩ K₂) × BK` to its `BK` factor preserves irreducibility. -/
private lemma theoremC_internalProduct_restrict_BK_irr (c : Hyp11 G) [Hyp11KData c]
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (hUint : (c.B1 ⊓ c.K2) ⊓ (c.B ⊔ c.K) = ⊥)
    (hUcomm : ⁅c.B1 ⊓ c.K2, c.B ⊔ c.K⁆ = ⊥)
    (α : Irr (↥c.U)) :
    IsIrreducibleCharacter (fun x : ↥(c.B ⊔ c.K) =>
      α.1 ⟨(x : G), by
        rw [hU]
        exact (le_sup_right : c.B ⊔ c.K ≤ (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K)) x.2⟩) := by
  classical
  let A : Subgroup G := c.B1 ⊓ c.K2
  let C : Subgroup G := c.B ⊔ c.K
  let e : ↥A × ↥C ≃* ↥c.U :=
    theoremC_internalDirectProductMulEquiv c hU hUint hUcomm
  let φ : ClassFunction (↥A × ↥C) := fun p => α.1 (e p)
  have hφ : IsIrreducibleCharacter φ :=
    isIrreducibleCharacter_congr (e := e) (χ := α.1) α.2
  have hres := theoremC_irr_restrict_of_abelian_factor (A := ↥A) (B := ↥C)
    (theoremC_A_abelian c) hφ
  have hfun : (fun x : ↥C => φ (1, x)) =
      (fun x : ↥C => α.1 ⟨(x : G), by
        rw [hU]
        exact (le_sup_right : C ≤ A ⊔ C) x.2⟩) := by
    funext x
    dsimp [φ]
    have he : e (1, x) = ⟨(x : G), by
        rw [hU]
        exact (le_sup_right : C ≤ A ⊔ C) x.2⟩ := by
      apply Subtype.ext
      simp [e, theoremC_internalDirectProductMulEquiv]
    rw [he]
  simpa [A, C, hfun] using hres

/-- Every element of `BK = B ⊔ K` has the form `b·k`. -/
private lemma theoremC_BK_decompose_join (c : Hyp11 G) [Hyp11KData c] {x : G}
    (hx : x ∈ c.B ⊔ c.K) :
    ∃ b ∈ c.B, ∃ k ∈ c.K, b * k = x := by
  have hBnormK : c.B ≤ Subgroup.normalizer (c.K : Set G) := by
    apply (Subgroup.le_normalizer_iff (H := c.B) (K := c.K)).2
    intro b hb k hk
    have hmemBK : ⁅b, k⁆ ∈ c.K :=
      (Subgroup.commutator_le.mp (theoremC_B_comm_K_le_K c)) b hb k hk
    have hEq : b * k * b⁻¹ = ⁅b, k⁆ * k := by
      change b * k * b⁻¹ = (b * k * b⁻¹ * k⁻¹) * k
      group
    rw [hEq]
    exact c.K.mul_mem hmemBK hk
  have hset : (↑(c.B ⊔ c.K) : Set G) = (c.B : Set G) * (c.K : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right c.B c.K hBnormK
  have hxcar : x ∈ (c.B : Set G) * (c.K : Set G) := by
    rwa [← hset]
  rcases hxcar with ⟨b, hbB, k, hkK, hEq⟩
  exact ⟨b, hbB, k, hkK, hEq⟩

/-- Theorem-C instance of the direct-product restriction lemma: given the
internal direct product `U ≅ (B₁∩K₂) × B` (factoring `K`) with `B`
embedded as `{1} × B`, every `α ∈ Irr(U)` restricts to an irreducible
character of `B`.  The isomorphism `e` is the exact missing hypothesis:
the paper's `×` in `U = (B₁∩K₂) × BK` is not implied by `hU`/`hUint`
alone. -/
private lemma theoremC_direct_prod_restrict_B_irr (c : Hyp11 G) [Hyp11KData c]
    (e : ↥c.U ≃* (↥(c.B1 ⊓ c.K2) × ↥c.B))
    (heB : ∀ b : ↥c.B, e ⟨(b : G), theoremC_B_le_U c b.2⟩ = (1, b))
    (α : Irr (↥c.U)) :
    IsIrreducibleCharacter (fun b : ↥c.B => α.1 ⟨(b : G), theoremC_B_le_U c b.2⟩) := by
  classical
  let A : Subgroup G := c.B1 ⊓ c.K2
  let φ : ClassFunction (↥A × ↥c.B) := fun p => α.1 (e.symm p)
  have hφ : IsIrreducibleCharacter φ :=
    isIrreducibleCharacter_congr (e := e.symm) (χ := α.1) α.2
  have hres := theoremC_irr_restrict_of_abelian_factor (A := ↥A) (B := ↥c.B)
    (theoremC_A_abelian c) hφ
  have hfun : (fun b : ↥c.B => φ (1, b)) =
      (fun b : ↥c.B => α.1 ⟨(b : G), theoremC_B_le_U c b.2⟩) := by
    funext b
    dsimp [φ]
    have hsymm : e.symm (1, b) = ⟨(b : G), theoremC_B_le_U c b.2⟩ := by
      have h := congrArg e.symm (heB b)
      simpa using h.symm
    rw [hsymm]
  simpa [hfun] using hres

/-- The theorem-C decomposition `U = (B₁∩K₂) × BK` forces `Section3Hyp`:
`S'` centralizes `U`. -/
private theorem theoremC_section3Hyp (c : Hyp11 G) [Hyp11KData c]
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (_hUint : (c.B1 ⊓ c.K2) ⊓ (c.B ⊔ c.K) = ⊥) :
    Section3Hyp c := by
  let r0 : G := c.t1 * c.t2
  have hA : (c.B1 ⊓ c.K2) ≤
      Subgroup.centralizer ((SPrime c : Subgroup G) : Set G) := by
    intro x hx
    rcases Subgroup.mem_inf.mp hx with ⟨hxB1, hxK2⟩
    have ht1fix : c.t1 * (x : G) * c.t1⁻¹ = (x : G) := by
      unfold Hyp11.B1 centralizerIn at hxB1
      have hcomm : c.t1 * (x : G) = (x : G) * c.t1 :=
        (Subgroup.mem_centralizer_iff.mp hxB1.2) c.t1 (by simp)
      calc
        c.t1 * (x : G) * c.t1⁻¹ = (x : G) * (c.t1 * c.t1⁻¹) := by
          rw [hcomm]
          group
        _ = (x : G) := by simp
    have ht2inv : c.t2 * (x : G) * c.t2⁻¹ = (x : G)⁻¹ :=
      theoremC_K2_inverted c hxK2
    have ht1fix_inv : c.t1 * (x : G)⁻¹ * c.t1⁻¹ = (x : G)⁻¹ := by
      calc
        c.t1 * (x : G)⁻¹ * c.t1⁻¹ = (c.t1 * (x : G) * c.t1⁻¹)⁻¹ := by group
        _ = (x : G)⁻¹ := by rw [ht1fix]
    have hrconj : r0 * (x : G) * r0⁻¹ = (x : G)⁻¹ := by
      dsimp [r0]
      calc
        (c.t1 * c.t2) * (x : G) * (c.t1 * c.t2)⁻¹
            = c.t1 * ((c.t2 * (x : G) * c.t2⁻¹) * c.t1⁻¹) := by group
        _ = c.t1 * ((x : G)⁻¹ * c.t1⁻¹) := by rw [ht2inv]
        _ = c.t1 * (x : G)⁻¹ * c.t1⁻¹ := by group
        _ = (x : G)⁻¹ := by
          exact ht1fix_inv
    have hsq : (r0 ^ 2) * (x : G) * (r0 ^ 2)⁻¹ = (x : G) :=
      sq_centralizes_of_inverts hrconj
    exact centralizes_zpowers_of_centralized hsq
  have hB : c.B ≤ Subgroup.centralizer ((SPrime c : Subgroup G) : Set G) := by
    intro b hb
    have hb1 : b ∈ c.B1 := by
      have hb' : b ∈ c.B1 ⊓ c.B2 := by simpa [Hyp11.B] using hb
      exact (inf_le_left : c.B1 ⊓ c.B2 ≤ c.B1) hb'
    have hb2 : b ∈ c.B2 := by
      have hb' : b ∈ c.B1 ⊓ c.B2 := by simpa [Hyp11.B] using hb
      exact (inf_le_right : c.B1 ⊓ c.B2 ≤ c.B2) hb'
    have ht1fix : c.t1 * (b : G) * c.t1⁻¹ = (b : G) := by
      unfold Hyp11.B1 centralizerIn at hb1
      have hcomm : c.t1 * (b : G) = (b : G) * c.t1 :=
        (Subgroup.mem_centralizer_iff.mp hb1.2) c.t1 (by simp)
      calc
        c.t1 * (b : G) * c.t1⁻¹ = (b : G) * (c.t1 * c.t1⁻¹) := by
          rw [hcomm]
          group
        _ = (b : G) := by simp
    have ht2fix : c.t2 * (b : G) * c.t2⁻¹ = (b : G) := by
      unfold Hyp11.B2 centralizerIn at hb2
      have hcomm : c.t2 * (b : G) = (b : G) * c.t2 :=
        (Subgroup.mem_centralizer_iff.mp hb2.2) c.t2 (by simp)
      calc
        c.t2 * (b : G) * c.t2⁻¹ = (b : G) * (c.t2 * c.t2⁻¹) := by
          rw [hcomm]
          group
        _ = (b : G) := by simp
    have ht1fix_inv : c.t1 * (b : G)⁻¹ * c.t1⁻¹ = (b : G)⁻¹ := by
      calc
        c.t1 * (b : G)⁻¹ * c.t1⁻¹ = (c.t1 * (b : G) * c.t1⁻¹)⁻¹ := by group
        _ = (b : G)⁻¹ := by rw [ht1fix]
    have ht2fix_inv : c.t2 * (b : G)⁻¹ * c.t2⁻¹ = (b : G)⁻¹ := by
      calc
        c.t2 * (b : G)⁻¹ * c.t2⁻¹ = (c.t2 * (b : G) * c.t2⁻¹)⁻¹ := by group
        _ = (b : G)⁻¹ := by rw [ht2fix]
    have hrconj : r0 * (b : G) * r0⁻¹ = (b : G) := by
      dsimp [r0]
      calc
        (c.t1 * c.t2) * (b : G) * (c.t1 * c.t2)⁻¹
            = c.t1 * ((c.t2 * (b : G) * c.t2⁻¹) * c.t1⁻¹) := by group
        _ = c.t1 * ((b : G) * c.t1⁻¹) := by rw [ht2fix]
        _ = c.t1 * (b : G) * c.t1⁻¹ := by group
        _ = (b : G) := by
          exact ht1fix
    have hsq : (r0 ^ 2) * (b : G) * (r0 ^ 2)⁻¹ = (b : G) :=
      sq_centralizes_of_centralizes hrconj
    exact centralizes_zpowers_of_centralized hsq
  have hK : c.K ≤ Subgroup.centralizer ((SPrime c : Subgroup G) : Set G) := by
    intro k hk
    rcases Subgroup.mem_inf.mp hk with ⟨hk1, hk2⟩
    have ht1inv : c.t1 * (k : G) * c.t1⁻¹ = (k : G)⁻¹ :=
      theoremC_K1_inverted c hk1
    have ht2inv : c.t2 * (k : G) * c.t2⁻¹ = (k : G)⁻¹ :=
      theoremC_K2_inverted c hk2
    have hrconj : r0 * (k : G) * r0⁻¹ = (k : G) := by
      dsimp [r0]
      calc
        (c.t1 * c.t2) * (k : G) * (c.t1 * c.t2)⁻¹
            = c.t1 * ((c.t2 * (k : G) * c.t2⁻¹) * c.t1⁻¹) := by group
        _ = c.t1 * ((k : G)⁻¹ * c.t1⁻¹) := by rw [ht2inv]
        _ = c.t1 * (k : G)⁻¹ * c.t1⁻¹ := by group
        _ = (k : G) := by
          calc
            c.t1 * (k : G)⁻¹ * c.t1⁻¹ = (c.t1 * (k : G) * c.t1⁻¹)⁻¹ := by group
            _ = ((k : G)⁻¹)⁻¹ := by rw [ht1inv]
            _ = k := by simp
    have hsq : (r0 ^ 2) * (k : G) * (r0 ^ 2)⁻¹ = (k : G) :=
      sq_centralizes_of_centralizes hrconj
    exact centralizes_zpowers_of_centralized hsq
  have hUcent : c.U ≤ Subgroup.centralizer ((SPrime c : Subgroup G) : Set G) := by
    rw [hU]
    exact sup_le hA (sup_le hB hK)
  exact (Subgroup.le_centralizer_iff).mp hUcent

/-- The theorem-C hypotheses give `B ⊄ U'` (the paper's condition for
choosing `κ₁ ≠ 1_{H0}`).  The proof uses only the K-data from `Hyp11`:
`K₂` is abelian and normal in `U`, so `[A,B] ≤ A`, `[A,K] ≤ K` and
`[B,K] ≤ K`; hence `U' ≤ A ⊔ B' ⊔ K`, and the trivial intersection
`A ∩ BK = 1` separates `B ∩ U'` into `B'`. -/
private theorem theoremC_B_not_le_Uprime (c : Hyp11 G) [Hyp11KData c]
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (hUint : (c.B1 ⊓ c.K2) ⊓ (c.B ⊔ c.K) = ⊥)
    (hB' : ⁅c.B, c.B⁆ ≠ c.B) :
    ¬ c.B ≤ ⁅c.U, c.U⁆ := by
  intro hBle
  let A : Subgroup G := c.B1 ⊓ c.K2
  let B : Subgroup G := c.B
  let B' : Subgroup G := ⁅B, B⁆
  let K : Subgroup G := c.K
  let N : Subgroup G := A ⊔ B' ⊔ K
  have hUleN : ⁅c.U, c.U⁆ ≤ N := by
    simpa [A, B, B', K, N, sup_assoc] using theoremC_Uprime_le_N c hU
  have hBleN : B ≤ N := hBle.trans hUleN
  have hB'leB : B' ≤ B := Subgroup.commutator_le_self B
  apply hB'
  apply le_antisymm hB'leB
  intro b hbB
  have hbN : b ∈ N := hBleN hbB
  rcases theoremC_mem_N_decompose c (by simpa [A, B, B', K, N, sup_assoc] using hbN) with
    ⟨a, haA, bp, hbpB', k, hkK, hEq⟩
  have hEq' : a * bp * k = b := by simpa [mul_assoc] using hEq
  have haC : a ∈ c.B ⊔ c.K := by
    have ha_eq : a = b * k⁻¹ * bp⁻¹ := by
      have h1 : a * bp = b * k⁻¹ := by
        calc
          a * bp = (a * bp * k) * k⁻¹ := by group
          _ = b * k⁻¹ := by rw [hEq']
      calc
        a = (a * bp) * bp⁻¹ := by group
        _ = (b * k⁻¹) * bp⁻¹ := by rw [h1]
        _ = b * k⁻¹ * bp⁻¹ := by group
    rw [ha_eq]
    exact (c.B ⊔ c.K).mul_mem
      ((c.B ⊔ c.K).mul_mem
        ((le_sup_left : c.B ≤ c.B ⊔ c.K) hbB)
        ((c.B ⊔ c.K).inv_mem ((le_sup_right : c.K ≤ c.B ⊔ c.K) hkK)))
      ((c.B ⊔ c.K).inv_mem ((le_sup_left : c.B ≤ c.B ⊔ c.K) (hB'leB hbpB')))
  have hmemA_C : a ∈ (c.B1 ⊓ c.K2) ⊓ (c.B ⊔ c.K) :=
    Subgroup.mem_inf.mpr ⟨haA, haC⟩
  have ha1 : a = 1 := by
    have hbot : a ∈ (⊥ : Subgroup G) := by
      rw [hUint] at hmemA_C
      exact hmemA_C
    exact Subgroup.mem_bot.mp hbot
  have hEq1 : bp * k = b := by
    simpa [ha1] using hEq'
  have hBinterK : c.B ⊓ c.K = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    rcases Subgroup.mem_inf.mp hx with ⟨hxB, hxK⟩
    have hxBK : x ∈ c.B ⊔ c.K := (le_sup_left : c.B ≤ c.B ⊔ c.K) hxB
    have hxA : x ∈ c.B1 ⊓ c.K2 := by
      exact Subgroup.mem_inf.mpr ⟨(by
        have hb1 : x ∈ c.B1 := by
          have hb' : x ∈ c.B1 ⊓ c.B2 := by simpa [Hyp11.B] using hxB
          exact (inf_le_left : c.B1 ⊓ c.B2 ≤ c.B1) hb'
        exact hb1), (by
        have hk2 : x ∈ c.K2 := (inf_le_right : c.K1 ⊓ c.K2 ≤ c.K2) hxK
        exact hk2)⟩
    have hmem : x ∈ (c.B1 ⊓ c.K2) ⊓ (c.B ⊔ c.K) :=
      Subgroup.mem_inf.mpr ⟨hxA, hxBK⟩
    have hbot : x ∈ (⊥ : Subgroup G) := by
      rw [hUint] at hmem
      exact hmem
    exact Subgroup.mem_bot.mp hbot
  have hkB : k ∈ c.B := by
    have hk_eq : k = bp⁻¹ * b := by
      calc
        k = 1 * k := by simp
        _ = (bp⁻¹ * bp) * k := by simp
        _ = bp⁻¹ * (bp * k) := by group
        _ = bp⁻¹ * b := by rw [hEq1]
    rw [hk_eq]
    exact c.B.mul_mem (c.B.inv_mem (hB'leB hbpB')) hbB
  have hk1 : k = 1 := by
    have hmem : k ∈ c.B ⊓ c.K := Subgroup.mem_inf.mpr ⟨hkB, hkK⟩
    have hbot : k ∈ (⊥ : Subgroup G) := by
      rw [hBinterK] at hmem
      exact hmem
    exact Subgroup.mem_bot.mp hbot
  have hb_eq : bp = b := by
    simpa [hk1] using hEq1
  exact hb_eq ▸ hbpB'

/-- Lemma 3.6, specialized to the theorem-C situation as a direct application
of `BenderGlauberman.Section3.Lemma36.lemma_3_6`. -/
private theorem theoremC_lemma36 (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (χ : Irr G) (hB : (BOf c h12 χ.1).Nonempty)
    (hK : ¬ c.K ≤ charKernel (isCharacter_of_isIrreducibleCharacter χ.2))
    (hνs : ∀ ν : Irr (↥c.H0), ν ∈ BOf c h12 χ.1 →
      conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈ orbit c.H0 c.U ν.1) :
    ∃ α : Irr (↥c.U),
      ¬ c.K ≤ (charKernel (isCharacter_of_isIrreducibleCharacter α.2)).map
          (Subgroup.subtype c.U) ∧
        (2 * (c.U.subgroupOf c.H0).index : ℝ) * (α.1 1).re < (χ.1 1).re := by
  exact lemma_3_6 c h12 hSC χ hB hK hνs

/-- The integer degree consequence of Lemma 3.6 used for equation (7):
with `m = |H0 : U| ≥ 4`, the strict real bound `2m·a < b` on character
degrees gives `b ≥ 8a + 1`. -/
private lemma theoremC_lemma36_degree_bound {m a b : ℕ} (hm : 4 ≤ m) (_ha : 1 ≤ a)
    (h : (2 * m * a : ℝ) < (b : ℝ)) : 8 * a + 1 ≤ b := by
  have hnat : 2 * m * a < b := by exact_mod_cast h
  have h8 : 8 ≤ 2 * m := by omega
  have hmul : 8 * a ≤ 2 * m * a := by
    calc
      8 * a = (2 * 4) * a := by ring
      _ ≤ (2 * m) * a := Nat.mul_le_mul_right a h8
  omega

/-- In the `|S| = 4` case, `S0 = {1, t}` has order 2, so the generator
`t₁·t₂` of `S0` is the unique involution `t`. -/
private lemma theoremC_t1_mul_t2_eq_t_of_S4 (c : Hyp11 G) [Hyp11KData c]
    (hS4 : Nat.card (↥(c.S : Subgroup G)) = 4) : c.t1 * c.t2 = c.t := by
  have hS0card : Nat.card (↥(c.S0 : Subgroup G)) = 2 := by
    have h := c.S_index_two
    rw [hS4] at h
    omega
  have hmem : c.t1 * c.t2 ∈ c.S0 := by
    rw [c.S0_eq_zpowers]
    exact Subgroup.mem_zpowers (c.t1 * c.t2)
  let x : ↥(c.S0 : Subgroup G) := ⟨c.t1 * c.t2, hmem⟩
  have hx2 : x ^ 2 = 1 := by
    apply (orderOf_dvd_iff_pow_eq_one (x := x) (n := 2)).mp
    have hdvd : orderOf x ∣ Fintype.card ↥(c.S0 : Subgroup G) :=
      orderOf_dvd_card (G := ↥(c.S0 : Subgroup G)) (x := x)
    rwa [← Nat.card_eq_fintype_card, hS0card] at hdvd
  have hxne1 : x ≠ 1 := by
    intro hx1
    have hprod : c.t1 * c.t2 = 1 := by
      change (x : ↥(c.S0 : Subgroup G)) = (1 : ↥(c.S0 : Subgroup G)) at hx1
      exact congrArg Subtype.val hx1
    have hS0bot : c.S0 = ⊥ := by
      rw [c.S0_eq_zpowers, hprod]
      simp
    have hcard_bot : Nat.card (↥(⊥ : Subgroup G)) = 1 := by simp
    rw [hS0bot, hcard_bot] at hS0card
    norm_num at hS0card
  rcases (S0_sq_eq_one_iff c (x := x)).mp hx2 with hx1 | hxt
  · exact False.elim (hxne1 hx1)
  · exact congrArg Subtype.val hxt

/-- In the `|S| = 4` case, `B₁ ∩ K₂ = 1`: any element is fixed by `t₁` and
inverted by `t₂`, hence inverted by `t = t₁·t₂`; but `t` centralizes `U`
(`U ≤ H = C_G(t)`), so it is also fixed by `t`, forcing the element to have
order dividing 2, which is impossible in the odd group `U`. -/
private lemma theoremC_A_eq_bot_of_S4 (c : Hyp11 G) [Hyp11KData c]
    (hS4 : Nat.card (↥(c.S : Subgroup G)) = 4) : c.B1 ⊓ c.K2 = ⊥ := by
  apply le_bot_iff.mp
  intro a ha
  have haB1 : a ∈ c.B1 := (Subgroup.mem_inf.mp ha).1
  have haK2 : a ∈ c.K2 := (Subgroup.mem_inf.mp ha).2
  have haU : a ∈ c.U := theoremC_K2_le_U c haK2
  have haH : a ∈ c.H := theoremC_U_le_H c haU
  have ht : c.t1 * c.t2 = c.t := theoremC_t1_mul_t2_eq_t_of_S4 c hS4
  have hfix : c.t1 * a * c.t1⁻¹ = a := theoremC_fixed_by_t1_of_mem_B1 c haB1
  have hinv : c.t2 * a * c.t2⁻¹ = a⁻¹ := c.K2_inverted a haK2
  have haCent : a ∈ Subgroup.centralizer ({c.t} : Set G) := by
    rw [← c.H_eq_centralizer]
    exact haH
  have hcomm : c.t * a = a * c.t :=
    (Subgroup.mem_centralizer_iff).1 haCent c.t (by simp)
  have hcomm_t : c.t * a * c.t⁻¹ = a := by
    calc
      c.t * a * c.t⁻¹ = (a * c.t) * c.t⁻¹ := by rw [hcomm]
      _ = a := by group
  have hinv_t : c.t * a * c.t⁻¹ = a⁻¹ := by
    rw [← ht]
    calc
      (c.t1 * c.t2) * a * (c.t1 * c.t2)⁻¹
          = c.t1 * (c.t2 * a * c.t2⁻¹) * c.t1⁻¹ := by group
      _ = c.t1 * a⁻¹ * c.t1⁻¹ := by rw [hinv]
      _ = a⁻¹ := by
        calc
          c.t1 * a⁻¹ * c.t1⁻¹ = (c.t1 * a * c.t1⁻¹)⁻¹ := by group
          _ = a⁻¹ := by rw [hfix]
  have ha_eq : a = a⁻¹ := by
    calc
      a = c.t * a * c.t⁻¹ := hcomm_t.symm
      _ = a⁻¹ := hinv_t
  have ha2 : a ^ 2 = 1 := by
    rw [pow_two]
    calc
      a * a = a * a⁻¹ := by nth_rw 2 [ha_eq]
      _ = 1 := by group
  have hordU : orderOf a ∣ Nat.card ↥c.U := Subgroup.orderOf_dvd_natCard c.U haU
  have hcop2 : Nat.Coprime 2 (orderOf a) :=
    (theoremC_U_coprime_two c).coprime_dvd_right hordU
  have hcop : Nat.Coprime (orderOf a) 2 := hcop2.symm
  have hord2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using ha2)
  have hord1 : orderOf a = 1 := Nat.Coprime.eq_one_of_dvd hcop hord2
  exact orderOf_eq_one_iff.mp hord1

/-- The paper's `U = BK` in the `|S| = 4` case, from the theorem-C
decomposition and `B₁ ∩ K₂ = 1`. -/
private lemma theoremC_U_eq_BK_of_S4 (c : Hyp11 G) [Hyp11KData c]
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (hS4 : Nat.card (↥(c.S : Subgroup G)) = 4) : c.U = c.B ⊔ c.K := by
  have hA : c.B1 ⊓ c.K2 = ⊥ := theoremC_A_eq_bot_of_S4 c hS4
  simpa [hA] using hU

/-! ## The four-group `K ≠ 1` reduction

This argument is deliberately confined to `|S| = 4`: only here does
`theoremC_U_eq_BK_of_S4` turn `K = 1` into `U = B`. -/

@[reducible] private def theoremC_a5CentralizerFintype
    (x : alternatingGroup (Fin 5)) :
    Fintype (Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) := by
  letI : DecidablePred (fun y : alternatingGroup (Fin 5) =>
      y ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) := fun y =>
    decidable_of_iff (y * x = x * y)
      (Subgroup.mem_centralizer_singleton_iff (g := x) (k := y)).symm
  exact (Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))).instFintypeSubtypeMemOfDecidablePred

private def theoremC_a5CentralizerCard (x : alternatingGroup (Fin 5)) : ℕ :=
  ((Finset.univ : Finset (alternatingGroup (Fin 5))).filter fun y =>
    y * x = x * y).card

/-- Direct finite verification that an involution centralizer in `A₅` has
order four.  This uses ordinary kernel reduction (`decide`), not
compiled evaluation. -/
private theorem theoremC_a5_centralizer_finset_card_involution :
    ∀ x : alternatingGroup (Fin 5), x ≠ 1 → x ^ 2 = 1 →
      theoremC_a5CentralizerCard x = 4 := by
  decide

private theorem theoremC_a5_centralizer_card_involution :
    ∀ x : alternatingGroup (Fin 5), IsInvolution x →
      Nat.card (Subgroup.centralizer
        ({x} : Set (alternatingGroup (Fin 5)))) = 4 := by
  intro x hx
  let : DecidablePred (fun y : alternatingGroup (Fin 5) =>
      y ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) := fun y =>
    decidable_of_iff (y * x = x * y)
      (Subgroup.mem_centralizer_singleton_iff (g := x) (k := y)).symm
  let : Fintype (Subgroup.centralizer
      ({x} : Set (alternatingGroup (Fin 5)))) :=
    theoremC_a5CentralizerFintype x
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype]
  simpa [theoremC_a5CentralizerCard,
    Subgroup.mem_centralizer_singleton_iff] using
      theoremC_a5_centralizer_finset_card_involution x hx.1 hx.2

/-- A group equivalence with `A₅` transports `H = C_G(t)` to an involution
centralizer, so `|H| = 4`. -/
private theorem theoremC_H_card_eq_four_of_mulEquiv_a5 (c : Hyp11 G) [Hyp11KData c]
    (e : G ≃* alternatingGroup (Fin 5)) : Nat.card c.H = 4 := by
  have htin : IsInvolution (e c.t) := by
    refine ⟨?_, ?_⟩
    · intro h
      exact c.t_involution.1 (e.injective (by simpa using h))
    · simpa using congrArg e c.t_involution.2
  have hcardA5 : Nat.card (Subgroup.centralizer
      ({e c.t} : Set (alternatingGroup (Fin 5)))) = 4 :=
    theoremC_a5_centralizer_card_involution (e c.t) htin
  have hmap : e.mapSubgroup c.H = Subgroup.centralizer
      ({e c.t} : Set (alternatingGroup (Fin 5))) := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyeq⟩
      have hyc : y ∈ Subgroup.centralizer ({c.t} : Set G) := by
        rw [← c.H_eq_centralizer]
        exact hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
      have hxy : x = e y := by simpa using hyeq.symm
      rw [hxy]
      simpa using congrArg e hyc
    · intro hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      have hxe : e.symm x ∈ Subgroup.centralizer ({c.t} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        simpa using congrArg e.symm hx
      have hyH : e.symm x ∈ c.H := by
        simpa [c.H_eq_centralizer] using hxe
      apply Subgroup.mem_map.mpr
      refine ⟨e.symm x, hyH, ?_⟩
      simp
  calc
    Nat.card c.H = Nat.card (e.mapSubgroup c.H) :=
      (Subgroup.card_mapSubgroup c.H e).symm
    _ = Nat.card (Subgroup.centralizer
        ({e c.t} : Set (alternatingGroup (Fin 5)))) := by rw [hmap]
    _ = 4 := hcardA5

/-- `B' ≠ B` forces `B ≠ 1`. -/
private lemma theoremC_B_ne_bot (c : Hyp11 G) [Hyp11KData c] (hB' : ⁅c.B, c.B⁆ ≠ c.B) :
    c.B ≠ ⊥ := by
  intro hBbot
  have hBB : ⁅c.B, c.B⁆ ≤ c.B := Subgroup.commutator_le_self c.B
  have hBBbot : ⁅c.B, c.B⁆ = ⊥ := le_bot_iff.mp (by simp [hBbot])
  exact hB' (by simp [hBbot])

/-- If `U = BK`, then `K` is nontrivial.  Indeed, `K = 1` would give
`U = B`; Remark 3.5 and Theorem B then identify simple `G` with `A₅`, whose
involution centralizers have order four.  The odd subgroup `U ≤ H` would be
trivial, contradicting `B' ≠ B`. -/
private theorem theoremC_K_ne_one_of_U_eq_BK (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (hSC : Section3Hyp c)
    (hUBK : c.U = c.B ⊔ c.K)
    (hB' : ⁅c.B, c.B⁆ ≠ c.B)
    (hsimple : IsSimpleGroup G) : c.K ≠ ⊥ := by
  classical
  intro hKbot
  have hUB : c.U = c.B := by
    simpa [hKbot] using hUBK
  have hBne : c.B ≠ ⊥ := theoremC_B_ne_bot c hB'
  have hUneBot : c.U ≠ ⊥ := by
    intro hUbot
    apply hBne
    calc
      c.B = c.U := hUB.symm
      _ = ⊥ := hUbot
  have hUneTop : c.U ≠ ⊤ := by
    intro hUtop
    apply t_not_mem_U c
    rw [hUtop]
    exact Subgroup.mem_top c.t
  let : IsSimpleGroup G := hsimple
  have hUnormal : ¬ IsNormalIn c.U ⊤ := by
    intro hnormalIn
    have hnormal : c.U.Normal := by
      constructor
      intro u hu g
      exact hnormalIn.2 g (by trivial) u hu
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal c.U with hbot | htop
    · exact hUneBot hbot
    · exact hUneTop htop
  rcases remark_3_5 c h12 hSC hUB hUnormal with
    ⟨hNproper, hHN, hNclass⟩
  rcases theorem_B c (normalizerB c) hNproper hHN hNclass with ⟨eQ⟩
  have h2S : 2 ∣ Nat.card (↥(c.S : Subgroup G)) := by
    rw [S_nat_card c]
    exact dvd_mul_right 2 (2 ^ c.m)
  have h2G : 2 ∣ Nat.card G :=
    h2S.trans (c.S : Subgroup G).card_subgroup_dvd_card
  have hcore : pPrimeCore 2 G = ⊥ :=
    pPrimeCore_eq_bot_of_simple_of_even h2G
  let qcore : G ⧸ pPrimeCore 2 G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq (G := G) hcore).trans
      (QuotientGroup.quotientBot (G := G))
  let e : G ≃* alternatingGroup (Fin 5) := qcore.symm.trans eQ
  have hHcard : Nat.card c.H = 4 :=
    theoremC_H_card_eq_four_of_mulEquiv_a5 c e
  have hUdiv4 : Nat.card c.U ∣ 4 := by
    have hUdivH : Nat.card c.U ∣ Nat.card c.H :=
      Subgroup.card_dvd_of_le (theoremC_U_le_H c)
    rwa [hHcard] at hUdivH
  have hUcop4 : Nat.Coprime (Nat.card c.U) 4 := by
    simpa using Nat.Coprime.pow_right 2 (theoremC_U_coprime_two c).symm
  have hUcard : Nat.card c.U = 1 :=
    Nat.Coprime.eq_one_of_dvd hUcop4 hUdiv4
  have hUbot : c.U = ⊥ := Subgroup.card_eq_one.mp hUcard
  apply hBne
  calc
    c.B = c.U := hUB.symm
    _ = ⊥ := hUbot

/-- In the four-group branch, `U = BK`, so the preceding general endpoint
gives the required nontriviality of `K`. -/
private theorem theoremC_K_ne_one_of_S4 (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (hSC : Section3Hyp c)
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (hB' : ⁅c.B, c.B⁆ ≠ c.B)
    (hsimple : IsSimpleGroup G)
    (hS4 : Nat.card (↥(c.S : Subgroup G)) = 4) : c.K ≠ ⊥ := by
  exact theoremC_K_ne_one_of_U_eq_BK c h12 hSC
    (theoremC_U_eq_BK_of_S4 c hU hS4) hB' hsimple

/-- When `U = BK`, every element of `U` has the normal form `b·k` with
`b ∈ B`, `k ∈ K` (uses `B ≤ N_G(K)`, i.e. `[B,K] ≤ K`). -/
private lemma theoremC_BK_decompose (c : Hyp11 G) [Hyp11KData c] {x : G}
    (hUBK : c.U = c.B ⊔ c.K) (hxU : x ∈ c.U) :
    ∃ b ∈ c.B, ∃ k ∈ c.K, b * k = x := by
  have hxBK : x ∈ c.B ⊔ c.K := by rwa [← hUBK]
  have hBnormK : c.B ≤ Subgroup.normalizer (c.K : Set G) := by
    apply (Subgroup.le_normalizer_iff (H := c.B) (K := c.K)).2
    intro b hb k hk
    have hmemBK : ⁅b, k⁆ ∈ c.K :=
      (Subgroup.commutator_le.mp (theoremC_B_comm_K_le_K c)) b hb k hk
    have hEq : b * k * b⁻¹ = ⁅b, k⁆ * k := by
      change b * k * b⁻¹ = (b * k * b⁻¹ * k⁻¹) * k
      group
    rw [hEq]
    exact c.K.mul_mem hmemBK hk
  have hset : (↑(c.B ⊔ c.K) : Set G) = (c.B : Set G) * (c.K : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right c.B c.K hBnormK
  have hxcar : x ∈ (c.B : Set G) * (c.K : Set G) := by
    rwa [← hset]
  rcases hxcar with ⟨b, hbB, k, hkK, hEq⟩
  exact ⟨b, hbB, k, hkK, hEq⟩

/-- Uniqueness of the `BK` normal form when `B ∩ K = 1`. -/
private lemma theoremC_BK_decompose_unique (c : Hyp11 G) [Hyp11KData c]
    (hBinterK : c.B ⊓ c.K = ⊥) {b1 k1 b2 k2 : G}
    (hb1 : b1 ∈ c.B) (hk1 : k1 ∈ c.K) (hb2 : b2 ∈ c.B) (hk2 : k2 ∈ c.K)
    (h : b1 * k1 = b2 * k2) : b1 = b2 ∧ k1 = k2 := by
  have heq : b2⁻¹ * b1 = k2 * k1⁻¹ := by
    calc
      b2⁻¹ * b1 = b2⁻¹ * (b1 * k1) * k1⁻¹ := by group
      _ = b2⁻¹ * (b2 * k2) * k1⁻¹ := by rw [h]
      _ = k2 * k1⁻¹ := by group
  have hmemB : b2⁻¹ * b1 ∈ c.B := c.B.mul_mem (c.B.inv_mem hb2) hb1
  have hmemK : k2 * k1⁻¹ ∈ c.K := c.K.mul_mem hk2 (c.K.inv_mem hk1)
  have hmem : b2⁻¹ * b1 ∈ c.B ⊓ c.K :=
    Subgroup.mem_inf.mpr ⟨hmemB, by rwa [heq]⟩
  have hbot : b2⁻¹ * b1 ∈ (⊥ : Subgroup G) := by rwa [hBinterK] at hmem
  have hb1' : b2⁻¹ * b1 = 1 := Subgroup.mem_bot.mp hbot
  have hb_eq : b1 = b2 := by
    have h' := congrArg (fun z : G => b2 * z) hb1'
    simpa [mul_assoc] using h'
  have hk2' : k2 * k1⁻¹ = 1 := by rwa [heq] at hb1'
  have hk_eq : k2 = k1 := by
    have h' := congrArg (fun z : G => z * k1) hk2'
    simpa [mul_assoc] using h'
  exact ⟨hb_eq, hk_eq.symm⟩

/-- In the `|S| = 4` case, `B₁ = B`: an element of `U = BK` fixed by `t₁`
must have its `K`-component trivial (fixed by `t₁` and inverted by `t₁`). -/
private lemma theoremC_B1_eq_B_of_S4 (c : Hyp11 G) [Hyp11KData c]
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (hS4 : Nat.card (↥(c.S : Subgroup G)) = 4) : c.B1 = c.B := by
  apply le_antisymm ?_ (by intro b hb; exact theoremC_mem_B1_of_mem_B c hb)
  intro x hxB1
  have hxU : x ∈ c.U := theoremC_B1_le_U c hxB1
  have hUBK : c.U = c.B ⊔ c.K := theoremC_U_eq_BK_of_S4 c hU hS4
  rcases theoremC_BK_decompose c hUBK hxU with ⟨b, hbB, k, hkK, hEq⟩
  have hfix : c.t1 * x * c.t1⁻¹ = x := theoremC_fixed_by_t1_of_mem_B1 c hxB1
  have hbFix : c.t1 * b * c.t1⁻¹ = b :=
    theoremC_fixed_by_t1_of_mem_B1 c (theoremC_mem_B1_of_mem_B c hbB)
  have hkInv : c.t1 * k * c.t1⁻¹ = k⁻¹ :=
    c.K1_inverted k (Subgroup.mem_inf.mp hkK).1
  have hEq' : c.t1 * x * c.t1⁻¹ = b * k⁻¹ := by
    calc
      c.t1 * x * c.t1⁻¹ = c.t1 * (b * k) * c.t1⁻¹ := by rw [hEq]
      _ = (c.t1 * b * c.t1⁻¹) * (c.t1 * k * c.t1⁻¹) := by group
      _ = b * k⁻¹ := by rw [hbFix, hkInv]
  have hxk : b * k⁻¹ = b * k := by
    rw [← hEq', hfix, hEq]
  have hk_eq_inv : k⁻¹ = k := mul_left_cancel hxk
  have hk2 : k ^ 2 = 1 := by
    rw [pow_two]
    calc
      k * k = k * k⁻¹ := by rw [hk_eq_inv]
      _ = 1 := by group
  have hkU : k ∈ c.U := theoremC_K_le_U c hkK
  have hordU : orderOf k ∣ Nat.card ↥c.U := Subgroup.orderOf_dvd_natCard c.U hkU
  have hcop2 : Nat.Coprime 2 (orderOf k) :=
    (theoremC_U_coprime_two c).coprime_dvd_right hordU
  have hcop : Nat.Coprime (orderOf k) 2 := hcop2.symm
  have hord2 : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hk2)
  have hk1 : k = 1 := orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hord2)
  have hx_eq_b : x = b := by
    calc
      x = b * k := hEq.symm
      _ = b * 1 := by rw [hk1]
      _ = b := by simp
  simpa [hx_eq_b] using hbB

/-- In the `|S| = 4` case, `B₂ = B`, by the same fixed/inverted argument
with `t₂`. -/
private lemma theoremC_B2_eq_B_of_S4 (c : Hyp11 G) [Hyp11KData c]
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (hS4 : Nat.card (↥(c.S : Subgroup G)) = 4) : c.B2 = c.B := by
  apply le_antisymm ?_ (by intro b hb; exact theoremC_mem_B2_of_mem_B c hb)
  intro x hxB2
  have hxU : x ∈ c.U := by
    unfold Hyp11.B2 centralizerIn at hxB2
    exact (inf_le_left : c.U ⊓ Subgroup.centralizer ({c.t2} : Set G) ≤ c.U) hxB2
  have hUBK : c.U = c.B ⊔ c.K := theoremC_U_eq_BK_of_S4 c hU hS4
  rcases theoremC_BK_decompose c hUBK hxU with ⟨b, hbB, k, hkK, hEq⟩
  have hfix : c.t2 * x * c.t2⁻¹ = x := theoremC_fixed_by_t2_of_mem_B2 c hxB2
  have hbFix : c.t2 * b * c.t2⁻¹ = b :=
    theoremC_fixed_by_t2_of_mem_B2 c (theoremC_mem_B2_of_mem_B c hbB)
  have hkInv : c.t2 * k * c.t2⁻¹ = k⁻¹ :=
    c.K2_inverted k (Subgroup.mem_inf.mp hkK).2
  have hEq' : c.t2 * x * c.t2⁻¹ = b * k⁻¹ := by
    calc
      c.t2 * x * c.t2⁻¹ = c.t2 * (b * k) * c.t2⁻¹ := by rw [hEq]
      _ = (c.t2 * b * c.t2⁻¹) * (c.t2 * k * c.t2⁻¹) := by group
      _ = b * k⁻¹ := by rw [hbFix, hkInv]
  have hxk : b * k⁻¹ = b * k := by
    rw [← hEq', hfix, hEq]
  have hk_eq_inv : k⁻¹ = k := mul_left_cancel hxk
  have hk2 : k ^ 2 = 1 := by
    rw [pow_two]
    calc
      k * k = k * k⁻¹ := by rw [hk_eq_inv]
      _ = 1 := by group
  have hkU : k ∈ c.U := theoremC_K_le_U c hkK
  have hordU : orderOf k ∣ Nat.card ↥c.U := Subgroup.orderOf_dvd_natCard c.U hkU
  have hcop2 : Nat.Coprime 2 (orderOf k) :=
    (theoremC_U_coprime_two c).coprime_dvd_right hordU
  have hcop : Nat.Coprime (orderOf k) 2 := hcop2.symm
  have hord2 : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hk2)
  have hk1 : k = 1 := orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hord2)
  have hx_eq_b : x = b := by
    calc
      x = b * k := hEq.symm
      _ = b * 1 := by rw [hk1]
      _ = b := by simp
  simpa [hx_eq_b] using hbB

/-- `B ∩ K = 1` follows from the theorem-C trivial intersection. -/
private lemma theoremC_B_inter_K_bot (c : Hyp11 G) [Hyp11KData c]
    (hUint : (c.B1 ⊓ c.K2) ⊓ (c.B ⊔ c.K) = ⊥) :
    c.B ⊓ c.K = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  rcases Subgroup.mem_inf.mp hx with ⟨hxB, hxK⟩
  have hxBK : x ∈ c.B ⊔ c.K := (le_sup_left : c.B ≤ c.B ⊔ c.K) hxB
  have hxA : x ∈ c.B1 ⊓ c.K2 := by
    exact Subgroup.mem_inf.mpr ⟨(by
      have hb1 : x ∈ c.B1 := by
        have hb' : x ∈ c.B1 ⊓ c.B2 := by simpa [Hyp11.B] using hxB
        exact (inf_le_left : c.B1 ⊓ c.B2 ≤ c.B1) hb'
      exact hb1), (by
      have hk2 : x ∈ c.K2 := (inf_le_right : c.K1 ⊓ c.K2 ≤ c.K2) hxK
      exact hk2)⟩
  have hmem : x ∈ (c.B1 ⊓ c.K2) ⊓ (c.B ⊔ c.K) :=
    Subgroup.mem_inf.mpr ⟨hxA, hxBK⟩
  have hbot : x ∈ (⊥ : Subgroup G) := by
    rw [hUint] at hmem
    exact hmem
  exact Subgroup.mem_bot.mp hbot

/-- In the `|S| = 4` case, `|U| = |B|·|K|` via the bijective `BK`
multiplication map. -/
private lemma theoremC_U_card_eq_mul_of_S4 (c : Hyp11 G) [Hyp11KData c]
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (hUint : (c.B1 ⊓ c.K2) ⊓ (c.B ⊔ c.K) = ⊥)
    (hS4 : Nat.card (↥(c.S : Subgroup G)) = 4) :
    Nat.card (↥c.B) * Nat.card (↥c.K) = Nat.card (↥c.U) := by
  have hUBK : c.U = c.B ⊔ c.K := theoremC_U_eq_BK_of_S4 c hU hS4
  have hBinterK : c.B ⊓ c.K = ⊥ := theoremC_B_inter_K_bot c hUint
  let BS : Subgroup (↥c.U) := (c.B : Subgroup G).subgroupOf c.U
  let KS : Subgroup (↥c.U) := (c.K : Subgroup G).subgroupOf c.U
  let f : ↥BS × ↥KS → ↥c.U := fun p =>
    ⟨(p.1 : G) * (p.2 : G), by exact c.U.mul_mem (p.1 : ↥c.U).2 (p.2 : ↥c.U).2⟩
  have hf_inj : Function.Injective f := by
    intro p q hpq
    have hEqG : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) :=
      congrArg Subtype.val hpq
    rcases theoremC_BK_decompose_unique c hBinterK
      (p.1 : ↥BS).2 (p.2 : ↥KS).2 (q.1 : ↥BS).2 (q.2 : ↥KS).2 hEqG with ⟨hb, hk⟩
    apply Prod.ext
    · apply Subtype.ext
      have hbU : (p.1 : ↥c.U) = (q.1 : ↥c.U) := by
        apply Subtype.ext
        exact hb
      exact hbU
    · apply Subtype.ext
      have hkU : (p.2 : ↥c.U) = (q.2 : ↥c.U) := by
        apply Subtype.ext
        exact hk
      exact hkU
  have hf_surj : Function.Surjective f := by
    intro u
    rcases theoremC_BK_decompose c hUBK u.2 with ⟨b, hbB, k, hkK, hEq⟩
    have hbU : b ∈ c.U := theoremC_B_le_U c hbB
    have hkU : k ∈ c.U := theoremC_K_le_U c hkK
    refine ⟨(⟨⟨b, hbU⟩, hbB⟩, ⟨⟨k, hkU⟩, hkK⟩), ?_⟩
    apply Subtype.ext
    exact hEq
  let e : ↥BS × ↥KS ≃ ↥c.U := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hcardU : Nat.card (↥BS × ↥KS) = Nat.card (↥c.U) := Nat.card_congr e
  have hcardBS : Nat.card ↥BS = Nat.card (↥c.B) := by
    exact Nat.card_congr {
      toFun := fun x : ↥BS => ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
      invFun := fun y : ↥c.B =>
        ⟨⟨(y : G), theoremC_B_le_U c y.2⟩, Subgroup.mem_subgroupOf.mpr y.2⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  have hcardKS : Nat.card ↥KS = Nat.card (↥c.K) := by
    exact Nat.card_congr {
      toFun := fun x : ↥KS => ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
      invFun := fun y : ↥c.K =>
        ⟨⟨(y : G), theoremC_K_le_U c y.2⟩, Subgroup.mem_subgroupOf.mpr y.2⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  calc
    Nat.card (↥c.B) * Nat.card (↥c.K)
        = Nat.card ↥BS * Nat.card ↥KS := by rw [hcardBS, hcardKS]
    _ = Nat.card (↥BS × ↥KS) := (Nat.card_prod ↥BS ↥KS).symm
    _ = Nat.card (↥c.U) := hcardU

/-- In the `|S| = 4` case, `|U : B| = |K|`. -/
private lemma theoremC_index_B_eq_K_card_of_S4 (c : Hyp11 G) [Hyp11KData c]
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (hUint : (c.B1 ⊓ c.K2) ⊓ (c.B ⊔ c.K) = ⊥)
    (hS4 : Nat.card (↥(c.S : Subgroup G)) = 4) :
    (c.B.subgroupOf c.U).index = Nat.card (↥c.K) := by
  have hcard := theoremC_U_card_eq_mul_of_S4 c hU hUint hS4
  have hcardBS : Nat.card ↥(c.B.subgroupOf c.U) = Nat.card (↥c.B) := by
    exact Nat.card_congr {
      toFun := fun x : ↥(c.B.subgroupOf c.U) => ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
      invFun := fun y : ↥c.B =>
        ⟨⟨(y : G), theoremC_B_le_U c y.2⟩, Subgroup.mem_subgroupOf.mpr y.2⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  have hcm := Subgroup.card_mul_index (c.B.subgroupOf c.U)
  rw [hcardBS] at hcm
  have hpos : 0 < Nat.card (↥c.B) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (by
    calc
      Nat.card (↥c.B) * (c.B.subgroupOf c.U).index = Nat.card (↥c.U) := hcm
      _ = Nat.card (↥c.B) * Nat.card (↥c.K) := hcard.symm)

/-- In the `|S| = 4` case the two reflection-centralizer indices agree, so
`k₁ = k₂`; this is the case-3 input to Lemma 2.2. -/
private lemma theoremC_k1_eq_k2_of_S4 (c : Hyp11 G) [Hyp11KData c]
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (hS4 : Nat.card (↥(c.S : Subgroup G)) = 4) : c.k1 = c.k2 := by
  have hB1 : c.B1 = c.B := theoremC_B1_eq_B_of_S4 c hU hS4
  have hB2 : c.B2 = c.B := theoremC_B2_eq_B_of_S4 c hU hS4
  have hk1' : 2 * c.k1 = Nat.card (c.S0 : Subgroup G) *
      ((centralizerIn c.U c.t1).subgroupOf c.U).index := k1_eq c
  have hk2' : 2 * c.k2 = Nat.card (c.S0 : Subgroup G) *
      ((centralizerIn c.U c.t2).subgroupOf c.U).index := k2_eq c
  have heq : 2 * c.k1 = 2 * c.k2 := by
    calc
      2 * c.k1 = Nat.card (c.S0 : Subgroup G) *
          ((centralizerIn c.U c.t1).subgroupOf c.U).index := hk1'
      _ = Nat.card (c.S0 : Subgroup G) * (c.B.subgroupOf c.U).index := by
        change Nat.card (c.S0 : Subgroup G) * (c.B1.subgroupOf c.U).index = _
        rw [hB1]
      _ = Nat.card (c.S0 : Subgroup G) *
          ((centralizerIn c.U c.t2).subgroupOf c.U).index := by
        change _ = Nat.card (c.S0 : Subgroup G) * (c.B2.subgroupOf c.U).index
        rw [hB2]
      _ = 2 * c.k2 := hk2'.symm
  omega

/-- In the `|S| = 4` case, `k = k₁ + k₂ = 2|K|` (paper L1214). -/
private lemma theoremC_k_eq_two_mul_K_of_S4 (c : Hyp11 G) [Hyp11KData c]
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (hUint : (c.B1 ⊓ c.K2) ⊓ (c.B ⊔ c.K) = ⊥)
    (hS4 : Nat.card (↥(c.S : Subgroup G)) = 4) : c.k = 2 * Nat.card (↥c.K) := by
  have hS0card : Nat.card (c.S0 : Subgroup G) = 2 := by
    have h := c.S_index_two
    rw [hS4] at h
    omega
  have hB1 : c.B1 = c.B := theoremC_B1_eq_B_of_S4 c hU hS4
  have hB2 : c.B2 = c.B := theoremC_B2_eq_B_of_S4 c hU hS4
  have hindex : (c.B.subgroupOf c.U).index = Nat.card (↥c.K) :=
    theoremC_index_B_eq_K_card_of_S4 c hU hUint hS4
  have hk1' : 2 * c.k1 = Nat.card (c.S0 : Subgroup G) *
      ((centralizerIn c.U c.t1).subgroupOf c.U).index := k1_eq c
  have hk2' : 2 * c.k2 = Nat.card (c.S0 : Subgroup G) *
      ((centralizerIn c.U c.t2).subgroupOf c.U).index := k2_eq c
  have hk1 : c.k1 = Nat.card (↥c.K) := by
    have h' : 2 * c.k1 = 2 * Nat.card (↥c.K) := by
      rw [hk1', hS0card]
      congr 1
      change (c.B1.subgroupOf c.U).index = _
      rw [hB1]
      exact hindex
    exact Nat.mul_left_cancel (by norm_num : 0 < 2) h'
  have hk2 : c.k2 = Nat.card (↥c.K) := by
    have h' : 2 * c.k2 = 2 * Nat.card (↥c.K) := by
      rw [hk2', hS0card]
      congr 1
      change (c.B2.subgroupOf c.U).index = _
      rw [hB2]
      exact hindex
    exact Nat.mul_left_cancel (by norm_num : 0 < 2) h'
  rw [Hyp11.k, hk1, hk2]
  omega

/-! ## The Section-4 component containing `δκ₁`

The graph in `Section4.Basic` is now explicitly the induced graph on
`Delta`.  The following small infrastructure constructs its reachable
component; it is kept local because the main theorem only needs the
component containing the particular character `κ₁`. -/

private noncomputable def theoremC_deltaComponent (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (δ₀ : ClassFunction G) : Set (ClassFunction G) :=
  {δ | δ ∈ Delta c h12 ∧
    Relation.ReflTransGen (deltaAdjacent c h12) δ₀ δ}

private lemma theoremC_deltaAdjacent_symm (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {δ ε : ClassFunction G} (h : deltaAdjacent c h12 δ ε) :
    deltaAdjacent c h12 ε δ := by
  unfold BenderGlauberman.deltaAdjacent at h ⊢
  rcases h with ⟨hδ, hε, hne, hdis⟩
  exact ⟨hε, hδ, hne.symm, by
    intro h'
    apply hdis
    unfold Theory.Character.Disjoint at h' ⊢
    intro χ hχ hχδ
    by_contra hχε
    exact hχδ (h' χ hχ hχε)⟩

private lemma theoremC_reflTransGen_symm {α : Type*} {r : α → α → Prop}
    (hr : ∀ {a b}, r a b → r b a) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h₁ h₂ ih =>
      exact (Relation.ReflTransGen.single (hr h₂)).trans ih

private lemma theoremC_delta_finite (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) :
    (Delta c h12).Finite := by
  classical
  let f : Irr (↥c.H0) → ClassFunction G := fun ν => deltaNu c h12 ν
  have hrange : (Set.range f).Finite := by
    rw [show Set.range f = f '' (Set.univ : Set (Irr (↥c.H0))) by
      ext δ
      constructor
      · rintro ⟨ν, rfl⟩
        exact ⟨ν, Set.mem_univ _, rfl⟩
      · rintro ⟨ν, _, rfl⟩
        exact ⟨ν, rfl⟩]
    exact Set.Finite.image f Set.finite_univ
  apply hrange.subset
  intro δ hδ
  simp only [BenderGlauberman.Delta] at hδ
  rcases hδ with ⟨ν, _hνs, _hνt, rfl⟩
  exact ⟨ν, rfl⟩

private lemma theoremC_deltaComponent_isConnected (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {δ₀ : ClassFunction G} (hδ₀ : δ₀ ∈ Delta c h12) :
    IsConnectedComponent c h12 (theoremC_deltaComponent c h12 δ₀) := by
  classical
  let Δ0 := theoremC_deltaComponent c h12 δ₀
  have hmem₀ : δ₀ ∈ Δ0 := by
    change δ₀ ∈ Delta c h12 ∧ _
    exact ⟨hδ₀, Relation.ReflTransGen.refl⟩
  have hsub : Δ0 ⊆ Delta c h12 := by
    intro δ hδ
    change δ ∈ Delta c h12 ∧ _ at hδ
    exact hδ.1
  have hpath (δ : ClassFunction G) (hδ : δ ∈ Δ0) :
      Relation.ReflTransGen (deltaAdjacent c h12) δ₀ δ := by
    change δ ∈ Delta c h12 ∧ _ at hδ
    exact hδ.2
  unfold BenderGlauberman.IsConnectedComponent
  refine ⟨⟨δ₀, hmem₀⟩, hsub, ?_, ?_⟩
  · intro δ δ' hδ hδ'
    exact (theoremC_reflTransGen_symm (fun {a b} h =>
      theoremC_deltaAdjacent_symm c h12 h)
      (hpath δ hδ)).trans (hpath δ' hδ')
  · intro δ hδnot δ' hδ' hadj
    apply hδnot
    have hadj' := theoremC_deltaAdjacent_symm c h12 hadj
    change δ ∈ Delta c h12 ∧ _ at hadj
    exact ⟨hadj.1, (hpath δ' hδ').trans (Relation.ReflTransGen.single hadj')⟩

private lemma theoremC_deltaComponent_finite (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {δ₀ : ClassFunction G} :
    (theoremC_deltaComponent c h12 δ₀).Finite := by
  exact (theoremC_delta_finite c h12).subset (by
    intro δ hδ
    exact hδ.1)

/-- Every Section-4 difference character has degree zero: the two
`LambdaHom`-orbit representatives have the same value at the identity. -/
private lemma theoremC_deltaNu_one_eq_zero (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (ν : Irr (↥c.H0)) : deltaNu c h12 ν 1 = 0 := by
  classical
  rw [deltaNu_eq_induced]
  unfold inducedClassFunction
  simp [LambdaChar]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro x hx
  have hone (h : (1 : G) ∈ c.H0) : (⟨1, h⟩ : ↥c.H0) = 1 := by
    apply Subtype.ext
    simp
  simp [hone]

/-! ## Degree transport from a Section-4 vertex to its Glauberman
correspondent -/

/-- A finite-order complex endomorphism whose trace equals the dimension is
the identity. -/
private theorem theoremC_finite_order_eq_one_of_trace_eq_finrank
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
      (Theory.Representation.trace_pow_eq_sum_eigenvalues
        (f := f) (n := n) (k := 1) hn hpow)
  have htrace_zero :
      (Module.finrank ℂ V : ℂ) =
        ∑ μ : f.Eigenvalues, (m μ : ℂ) := by
    have h0 :=
      Theory.Representation.trace_pow_eq_sum_eigenvalues
        (f := f) (n := n) (k := 0) hn hpow
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
    intro μ _hμ
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
      rcases hμ.exists_hasEigenvector with ⟨w, hw⟩
      rw [Module.finrank_pos_iff_exists_ne_zero]
      refine ⟨⟨w, ?_⟩, ?_⟩
      · rw [Module.End.mem_eigenspace_iff]
        exact hw.apply_eq_smul
      · intro hzero
        have hwzero : w = 0 := by
          simpa using congrArg Subtype.val hzero
        exact hw.2 hwzero
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
    have hnormSq :
        (μ : ℂ).re * (μ : ℂ).re + (μ : ℂ).im * (μ : ℂ).im = 1 := by
      have h := Complex.normSq_eq_norm_sq (μ : ℂ)
      rw [Complex.normSq_apply, hnorm] at h
      norm_num at h
      exact h
    have him_sq : (μ : ℂ).im * (μ : ℂ).im = 0 := by
      nlinarith
    have him : (μ : ℂ).im = 0 := mul_self_eq_zero.mp him_sq
    exact Complex.ext (by simp [hre_eq]) (by simp [him])
  have htop : f.eigenspace (1 : ℂ) = ⊤ := by
    have hsemi : f.IsSemisimple :=
      Theory.Representation.end_isSemisimple_of_pow_eq_one f hn hpow
    have hiSup :=
      Theory.Representation.eigenspace_iSup_eq_top_over_eigenvalues
        (f := f) hsemi
    apply top_unique
    rw [← hiSup]
    refine iSup_le ?_
    intro μ
    simp [heigen_eq_one μ]
  ext w
  have hw : w ∈ f.eigenspace (1 : ℂ) := by
    rw [htop]
    exact Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff] at hw
  simpa using hw

private lemma theoremC_rep_eq_one_of_char_eq_degree
    {K : Type u} [Group K] [Fintype K] {n : ℕ}
    (ρ : Representation ℂ K (Fin n → ℂ)) (g : K)
    (h : ρ.character g = ρ.character 1) : ρ g = 1 := by
  have hn : orderOf g ≠ 0 := Nat.ne_of_gt (orderOf_pos g)
  have hpow : (ρ g) ^ orderOf g = 1 := by
    rw [← MonoidHom.map_pow, pow_orderOf_eq_one, MonoidHom.map_one]
  have htrace : LinearMap.trace ℂ (Fin n → ℂ) (ρ g) =
      (Module.finrank ℂ (Fin n → ℂ) : ℂ) := by
    have h' := h.trans (Representation.char_one ρ)
    simpa [Representation.character] using h'
  exact theoremC_finite_order_eq_one_of_trace_eq_finrank (ρ g) hn hpow htrace

/-- An irreducible character of `BK` that kills `K` remains irreducible on
the generating complement `B`. -/
private lemma theoremC_restrict_B_irreducible_of_K_kernel_in_BK (c : Hyp11 G) [Hyp11KData c]
    (γ : Irr (↥(c.B ⊔ c.K)))
    (hK : ∀ k : G, (hk : k ∈ c.K) →
      γ.1 ⟨k, (le_sup_right : c.K ≤ c.B ⊔ c.K) hk⟩ = γ.1 1) :
    IsIrreducibleCharacter (fun b : ↥c.B =>
      γ.1 ⟨(b : G), (le_sup_left : c.B ≤ c.B ⊔ c.K) b.2⟩) := by
  classical
  rcases γ.2 with ⟨n, ρ, hρ, hγ⟩
  let bToBK : ↥c.B →* ↥(c.B ⊔ c.K) := {
    toFun := fun b => ⟨(b : G), (le_sup_left : c.B ≤ c.B ⊔ c.K) b.2⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by intro a b; apply Subtype.ext; simp }
  let ρB : Representation ℂ (↥c.B) (Fin n → ℂ) := ρ.comp bToBK
  have hρB : Representation.IsIrreducible ρB := by
    let : Representation.IsIrreducible ρ := hρ
    let : Nontrivial (Fin n → ℂ) :=
      Subrepresentation.irreducible_module_nontrivial ρ
    refine { toNontrivial := inferInstance, eq_bot_or_eq_top := ?_ }
    intro W
    let WBK : Subrepresentation ρ := {
      toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro x v hv
        rcases theoremC_BK_decompose_join c x.2 with ⟨b, hb, k, hk, hbk⟩
        let bB : ↥c.B := ⟨b, hb⟩
        let bBK : ↥(c.B ⊔ c.K) :=
          ⟨b, (le_sup_left : c.B ≤ c.B ⊔ c.K) hb⟩
        let kBK : ↥(c.B ⊔ c.K) :=
          ⟨k, (le_sup_right : c.K ≤ c.B ⊔ c.K) hk⟩
        have hx : x = bBK * kBK := by
          apply Subtype.ext
          exact hbk.symm
        have hρk : ρ kBK = 1 := by
          apply theoremC_rep_eq_one_of_char_eq_degree ρ kBK
          rw [← hγ]
          exact hK k hk
        rw [hx, map_mul, hρk, mul_one]
        exact W.apply_mem_toSubmodule bB hv }
    rcases hρ.eq_bot_or_eq_top WBK with hbot | htop
    · left
      have hbSub := congrArg Subrepresentation.toSubmodule hbot
      change W.toSubmodule = (⊥ : Submodule ℂ (Fin n → ℂ)) at hbSub
      apply Subrepresentation.toSubmodule_injective
      exact hbSub
    · right
      have htSub := congrArg Subrepresentation.toSubmodule htop
      change W.toSubmodule = (⊤ : Submodule ℂ (Fin n → ℂ)) at htSub
      apply Subrepresentation.toSubmodule_injective
      exact htSub
  refine ⟨n, ρB, hρB, ?_⟩
  funext b
  simpa [ρB, bToBK, Representation.character] using congrFun hγ (bToBK b)

/-- Source-faithful equation-(3) restriction endpoint: after restricting an
irreducible character of the internal direct product `U = A × BK` to `BK`,
triviality on `K` lets it restrict irreducibly once more to `B`. -/
private lemma theoremC_internalProduct_restrict_B_irr (c : Hyp11 G) [Hyp11KData c]
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (hUint : (c.B1 ⊓ c.K2) ⊓ (c.B ⊔ c.K) = ⊥)
    (hUcomm : ⁅c.B1 ⊓ c.K2, c.B ⊔ c.K⁆ = ⊥)
    (α : Irr (↥c.U))
    (hK : ∀ k : G, (hk : k ∈ c.K) →
      α.1 ⟨k, theoremC_K_le_U c hk⟩ = α.1 1) :
    IsIrreducibleCharacter (fun b : ↥c.B =>
      α.1 ⟨(b : G), theoremC_B_le_U c b.2⟩) := by
  classical
  let γfun : ClassFunction (↥(c.B ⊔ c.K)) := fun x =>
    α.1 ⟨(x : G), by
      rw [hU]
      exact (le_sup_right : c.B ⊔ c.K ≤ (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K)) x.2⟩
  have hγ : IsIrreducibleCharacter γfun :=
    theoremC_internalProduct_restrict_BK_irr c hU hUint hUcomm α
  let γ : Irr (↥(c.B ⊔ c.K)) := ⟨γfun, hγ⟩
  have hγK : ∀ k : G, (hk : k ∈ c.K) →
      γ.1 ⟨k, (le_sup_right : c.K ≤ c.B ⊔ c.K) hk⟩ = γ.1 1 := by
    intro k hk
    change α.1 ⟨k, theoremC_K_le_U c hk⟩ = α.1 1
    exact hK k hk
  simpa [γ, γfun] using
    theoremC_restrict_B_irreducible_of_K_kernel_in_BK c γ hγK

/-- If `U = BK` and an irreducible character of `U` kills `K`, its
restriction to the complement `B` remains irreducible. -/
private lemma theoremC_restrict_B_irreducible_of_K_kernel (c : Hyp11 G) [Hyp11KData c]
    (hUBK : c.U = c.B ⊔ c.K) (α : Irr (↥c.U))
    (hK : ∀ k : G, (hk : k ∈ c.K) →
      α.1 ⟨k, theoremC_K_le_U c hk⟩ = α.1 1) :
    IsIrreducibleCharacter (fun b : ↥c.B =>
      α.1 ⟨(b : G), theoremC_B_le_U c b.2⟩) := by
  classical
  rcases α.2 with ⟨n, ρ, hρ, hα⟩
  let bToU : ↥c.B →* ↥c.U := {
    toFun := fun b => ⟨(b : G), theoremC_B_le_U c b.2⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by intro a b; apply Subtype.ext; simp }
  let ρB : Representation ℂ (↥c.B) (Fin n → ℂ) := ρ.comp bToU
  have hρB : Representation.IsIrreducible ρB := by
    let : Representation.IsIrreducible ρ := hρ
    let : Nontrivial (Fin n → ℂ) :=
      Subrepresentation.irreducible_module_nontrivial ρ
    refine { toNontrivial := inferInstance, eq_bot_or_eq_top := ?_ }
    intro W
    let WU : Subrepresentation ρ := {
      toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro u v hv
        rcases theoremC_BK_decompose c hUBK u.2 with ⟨b, hb, k, hk, hbk⟩
        let bB : ↥c.B := ⟨b, hb⟩
        let bU : ↥c.U := ⟨b, theoremC_B_le_U c hb⟩
        let kU : ↥c.U := ⟨k, theoremC_K_le_U c hk⟩
        have hu : u = bU * kU := by
          apply Subtype.ext
          exact hbk.symm
        have hρk : ρ kU = 1 := by
          apply theoremC_rep_eq_one_of_char_eq_degree ρ kU
          rw [← hα]
          exact hK k hk
        rw [hu, map_mul, hρk, mul_one]
        exact W.apply_mem_toSubmodule bB hv }
    rcases hρ.eq_bot_or_eq_top WU with hbot | htop
    · left
      have hbSub := congrArg Subrepresentation.toSubmodule hbot
      change W.toSubmodule = (⊥ : Submodule ℂ (Fin n → ℂ)) at hbSub
      apply Subrepresentation.toSubmodule_injective
      exact hbSub
    · right
      have htSub := congrArg Subrepresentation.toSubmodule htop
      change W.toSubmodule = (⊤ : Submodule ℂ (Fin n → ℂ)) at htSub
      apply Subrepresentation.toSubmodule_injective
      exact htSub
  refine ⟨n, ρB, hρB, ?_⟩
  funext b
  simpa [ρB, bToU, Representation.character] using congrFun hα (bToU b)

/-- In the Section-4 case `U = BK`, a Section-4 character `ν` and its
Glauberman correspondent `ν̂` have the same degree. -/
private lemma theoremC_nu_degree_eq_nuHat_degree_of_S4 (c : Hyp11 G) [Hyp11KData c]
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    (hUBK : c.U = c.B ⊔ c.K) {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1) :
    ν.1 1 = (nuHat c h12 ν).1 1 := by
  classical
  rcases exists_fixed_alpha_of_section4 c h12 hSC hS4 hνs hνt with
    ⟨α, hfix, hres⟩
  have hfix_t1 : conjIrrS c c.t1_mem_S α = α := by
    apply Subtype.ext
    funext u
    have h := congrFun (hfix ⟨c.t1, c.t1_mem_S⟩) u
    change α.1 ⟨c.t1 * (u : G) * c.t1⁻¹,
        S_normalizes_U c c.t1 c.t1_mem_S (u : G) u.2⟩ = α.1 u
    have harg : (⟨c.t1, c.t1_mem_S⟩ : ↥(c.S : Subgroup G)) • u =
        ⟨c.t1 * (u : G) * c.t1⁻¹,
          S_normalizes_U c c.t1 c.t1_mem_S (u : G) u.2⟩ := by
      apply Subtype.ext
      rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    rw [← harg]
    exact h
  have hK : ∀ k : G, (hk : k ∈ c.K) →
      α.1 ⟨k, theoremC_K_le_U c hk⟩ = α.1 1 :=
    theoremC_reflection_fixed_char_kills_K c c.t1_mem_S c.t1_not_mem_S0 α hfix_t1
  let αB : Irr (↥c.B) :=
    ⟨fun b : ↥c.B => α.1 ⟨(b : G), theoremC_B_le_U c b.2⟩,
      theoremC_restrict_B_irreducible_of_K_kernel c hUBK α hK⟩
  have hαB : αB = nuHat c h12 ν := by
    apply eq_of_congruent_irr
      (Nat.coprime_two_left.mpr (theoremC_B_card_odd c))
    intro b
    let bU : ↥c.U := ⟨(b : G), theoremC_B_le_U c b.2⟩
    have hbH0 : (b : G) ∈ c.H0 := U_le_H0 c (theoremC_B_le_U c b.2)
    have hresb := congrFun hres bU
    have hνeq : ν.1 ⟨(b : G), hbH0⟩ = α.1 bU := by
      simpa [restrictU, bU] using hresb
    change CongruentModTwo (α.1 bU) ((nuHat c h12 ν).1 b)
    rw [← hνeq]
    exact (nuHat_congruence c h12 hSC hS4 hνs hνt b hbH0).symm
  have hres1 := congrFun hres (1 : ↥c.U)
  have hνdegree : ν.1 1 = α.1 1 := by
    let oneH0 : ↥c.H0 :=
      ⟨(1 : G), (h12.U_normal_in_H0).1 c.U.one_mem⟩
    have hres1' : ν.1 oneH0 = α.1 1 := by
      simpa [restrictU, oneH0] using hres1
    have hone : oneH0 = 1 := by
      apply Subtype.ext
      rfl
    rw [hone] at hres1'
    exact hres1'
  have hαB1 := congrFun (congrArg Subtype.val hαB) (1 : ↥c.B)
  have hαBdegree : α.1 1 = (nuHat c h12 ν).1 1 := by
    let oneBU : ↥c.U :=
      ⟨((1 : ↥c.B) : G), theoremC_B_le_U c (1 : ↥c.B).2⟩
    have hαB1' : α.1 oneBU = (nuHat c h12 ν).1 1 := by
      change α.1 oneBU = (nuHat c h12 ν).1 1 at hαB1
      exact hαB1
    have hone : oneBU = 1 := by
      apply Subtype.ext
      simp [oneBU]
    rw [hone] at hαB1'
    exact hαB1'
  calc
    ν.1 1 = α.1 1 := hνdegree
    _ = (nuHat c h12 ν).1 1 := hαBdegree

/-- Conjugating an irreducible character of `B` preserves its degree. -/
private lemma theoremC_conjIrrB_degree (c : Hyp11 G) [Hyp11KData c] {g : G}
    (hg : ∀ b : ↥c.B, g * (b : G) * g⁻¹ ∈ c.B) (β : Irr (↥c.B)) :
    (conjIrrB c hg β).1 1 = β.1 1 := by
  change β.1 ⟨g * (1 : G) * g⁻¹, hg 1⟩ = β.1 1
  apply congrArg β.1
  apply Subtype.ext
  simp

/-- If two Section-4 Glauberman correspondents are normalizer-conjugate,
linearity of the first character transfers to the second. -/
private lemma theoremC_nu_degree_eq_one_of_nuHat_conj (c : Hyp11 G) [Hyp11KData c]
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    (hUBK : c.U = c.B ⊔ c.K) {κ ν : Irr (↥c.H0)}
    (hκs : conjChar c.H0 (s_normalizes_H0 c h12) κ.1 = κ.1)
    (hκt : κ.1 (tH0 c) = κ.1 1) (hκone : κ.1 1 = 1)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1) {g : G} (hg : g ∈ normalizerS c)
    (hconj : conjIrrB c (B_conj_mem_of_normalizerS c hg) (nuHat c h12 κ) =
      nuHat c h12 ν) :
    ν.1 1 = 1 := by
  have hκdegree := theoremC_nu_degree_eq_nuHat_degree_of_S4
    c h12 hSC hS4 hUBK hκs hκt
  have hνdegree := theoremC_nu_degree_eq_nuHat_degree_of_S4
    c h12 hSC hS4 hUBK hνs hνt
  have hconj1 := congrFun (congrArg Subtype.val hconj) (1 : ↥c.B)
  have hhat : (nuHat c h12 κ).1 1 = (nuHat c h12 ν).1 1 := by
    calc
      (nuHat c h12 κ).1 1 =
          (conjIrrB c (B_conj_mem_of_normalizerS c hg)
            (nuHat c h12 κ)).1 1 :=
        (theoremC_conjIrrB_degree c (B_conj_mem_of_normalizerS c hg)
          (nuHat c h12 κ)).symm
      _ = (nuHat c h12 ν).1 1 := hconj1
  calc
    ν.1 1 = (nuHat c h12 ν).1 1 := hνdegree
    _ = (nuHat c h12 κ).1 1 := hhat.symm
    _ = κ.1 1 := hκdegree.symm
    _ = 1 := hκone

/-- The usable Theorem-4.3 data for a nonsingleton component containing a
linear Section-4 vertex.  The returned vertices satisfy the Section-4
conditions and all have degree one. -/
private lemma theoremC_S4_nonsingleton_data (c : Hyp11 G) [Hyp11KData c]
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    (hUBK : c.U = c.B ⊔ c.K) [Fintype ↥(LambdaHom c.H0 c.U)]
    (κ : Irr (↥c.H0))
    (hκs : conjChar c.H0 (s_normalizes_H0 c h12) κ.1 = κ.1)
    (hκt : κ.1 (tH0 c) = κ.1 1) (hκone : κ.1 1 = 1)
    (Δ0 : Set (ClassFunction G)) (hcomp : IsConnectedComponent c h12 Δ0)
    (hκΔ0 : deltaNu c h12 κ ∈ Δ0) (hcard : Δ0.ncard ≠ 1) :
    ∃ ν1 ν2 ν3 : Irr (↥c.H0),
      deltaNu c h12 ν1 ∈ Δ0 ∧ deltaNu c h12 ν2 ∈ Δ0 ∧
      deltaNu c h12 ν3 ∈ Δ0 ∧
      ν1 ≠ ν2 ∧ ν2 ≠ ν3 ∧ ν1 ≠ ν3 ∧
      conjChar c.H0 (s_normalizes_H0 c h12) ν1.1 = ν1.1 ∧
      ν1.1 (tH0 c) = ν1.1 1 ∧ ν1.1 1 = 1 ∧
      conjChar c.H0 (s_normalizes_H0 c h12) ν2.1 = ν2.1 ∧
      ν2.1 (tH0 c) = ν2.1 1 ∧ ν2.1 1 = 1 ∧
      conjChar c.H0 (s_normalizes_H0 c h12) ν3.1 = ν3.1 ∧
      ν3.1 (tH0 c) = ν3.1 1 ∧ ν3.1 1 = 1 ∧
      ∃ χ1 χ2 χ3 χ4 : ClassFunction G,
        IsPMIrr G χ1 ∧ IsPMIrr G χ2 ∧ IsPMIrr G χ3 ∧ IsPMIrr G χ4 ∧
        scalarProduct G χ1 χ2 = 0 ∧ scalarProduct G χ1 χ3 = 0 ∧
        scalarProduct G χ1 χ4 = 0 ∧ scalarProduct G χ2 χ3 = 0 ∧
        scalarProduct G χ2 χ4 = 0 ∧ scalarProduct G χ3 χ4 = 0 ∧
        deltaNu c h12 ν1 = χ1 + χ2 + χ3 + χ4 ∧
        deltaNu c h12 ν2 = χ1 - χ2 + χ3 - χ4 ∧
        deltaNu c h12 ν3 = χ1 + χ2 - χ3 - χ4 ∧
        Δ0 = {deltaNu c h12 ν1, deltaNu c h12 ν2, deltaNu c h12 ν3} := by
  classical
  rcases theorem_4_3 c h12 hSC hS4 Δ0 hcomp hcard with
    ⟨ρ1, ρ2, ρ3, hρ1Δ0, hρ2Δ0, hρ3Δ0, _hρ12, _hρ23, _hρ13,
      χ1, χ2, χ3, χ4, hχ1, hχ2, hχ3, hχ4,
      hχ12, hχ13, hχ14, hχ23, hχ24, hχ34,
      hρ1dec, hρ2dec, hρ3dec, hset, hconj⟩
  have hρ1Δ : deltaNu c h12 ρ1 ∈ Delta c h12 := hcomp.2.1 hρ1Δ0
  have hρ2Δ : deltaNu c h12 ρ2 ∈ Delta c h12 := hcomp.2.1 hρ2Δ0
  have hρ3Δ : deltaNu c h12 ρ3 ∈ Delta c h12 := hcomp.2.1 hρ3Δ0
  change ∃ ν : Irr (↥c.H0),
    conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧
      ν.1 (tH0 c) = ν.1 1 ∧ deltaNu c h12 ρ1 = deltaNu c h12 ν at hρ1Δ
  change ∃ ν : Irr (↥c.H0),
    conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧
      ν.1 (tH0 c) = ν.1 1 ∧ deltaNu c h12 ρ2 = deltaNu c h12 ν at hρ2Δ
  change ∃ ν : Irr (↥c.H0),
    conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧
      ν.1 (tH0 c) = ν.1 1 ∧ deltaNu c h12 ρ3 = deltaNu c h12 ν at hρ3Δ
  rcases hρ1Δ with ⟨ν1, hν1s, hν1t, hρ1eq⟩
  rcases hρ2Δ with ⟨ν2, hν2s, hν2t, hρ2eq⟩
  rcases hρ3Δ with ⟨ν3, hν3s, hν3t, hρ3eq⟩
  have hν1Δ0 : deltaNu c h12 ν1 ∈ Δ0 := by
    rw [← hρ1eq]
    exact hρ1Δ0
  have hν2Δ0 : deltaNu c h12 ν2 ∈ Δ0 := by
    rw [← hρ2eq]
    exact hρ2Δ0
  have hν3Δ0 : deltaNu c h12 ν3 ∈ Δ0 := by
    rw [← hρ3eq]
    exact hρ3Δ0
  have hν12 : ν1 ≠ ν2 := by
    intro hEq
    apply _hρ12
    rw [hρ1eq, hρ2eq, hEq]
  have hν23 : ν2 ≠ ν3 := by
    intro hEq
    apply _hρ23
    rw [hρ2eq, hρ3eq, hEq]
  have hν13 : ν1 ≠ ν3 := by
    intro hEq
    apply _hρ13
    rw [hρ1eq, hρ3eq, hEq]
  rcases hconj κ ν1 hκΔ0 hν1Δ0 with ⟨g1, hg1, hconj1⟩
  rcases hconj κ ν2 hκΔ0 hν2Δ0 with ⟨g2, hg2, hconj2⟩
  rcases hconj κ ν3 hκΔ0 hν3Δ0 with ⟨g3, hg3, hconj3⟩
  have hν1one := theoremC_nu_degree_eq_one_of_nuHat_conj
    c h12 hSC hS4 hUBK hκs hκt hκone hν1s hν1t hg1 hconj1
  have hν2one := theoremC_nu_degree_eq_one_of_nuHat_conj
    c h12 hSC hS4 hUBK hκs hκt hκone hν2s hν2t hg2 hconj2
  have hν3one := theoremC_nu_degree_eq_one_of_nuHat_conj
    c h12 hSC hS4 hUBK hκs hκt hκone hν3s hν3t hg3 hconj3
  have hν1dec : deltaNu c h12 ν1 = χ1 + χ2 + χ3 + χ4 :=
    hρ1eq.symm.trans hρ1dec
  have hν2dec : deltaNu c h12 ν2 = χ1 - χ2 + χ3 - χ4 :=
    hρ2eq.symm.trans hρ2dec
  have hν3dec : deltaNu c h12 ν3 = χ1 + χ2 - χ3 - χ4 :=
    hρ3eq.symm.trans hρ3dec
  have hset' : Δ0 = {deltaNu c h12 ν1, deltaNu c h12 ν2,
      deltaNu c h12 ν3} := by
    rw [← hρ1eq, ← hρ2eq, ← hρ3eq]
    exact hset
  exact ⟨ν1, ν2, ν3, hν1Δ0, hν2Δ0, hν3Δ0, hν12, hν23, hν13,
    hν1s, hν1t, hν1one, hν2s, hν2t, hν2one, hν3s, hν3t, hν3one,
    χ1, χ2, χ3, χ4, hχ1, hχ2, hχ3, hχ4,
    hχ12, hχ13, hχ14, hχ23, hχ24, hχ34,
    hν1dec, hν2dec, hν3dec, hset'⟩

/-- Three distinct known members exhaust `B′(χ)`, whose cardinality is one
or three by Lemma 4.1(i). -/
private lemma theoremC_BPrime_eq_three (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    [Fintype ↥(LambdaHom c.H0 c.U)] {χ : ClassFunction G}
    (hχ : IsPMIrr G χ) {ν1 ν2 ν3 : Irr (↥c.H0)}
    (hν12 : ν1 ≠ ν2) (hν23 : ν2 ≠ ν3) (hν13 : ν1 ≠ ν3)
    (hν1 : ν1 ∈ BPrimeOf c h12 χ) (hν2 : ν2 ∈ BPrimeOf c h12 χ)
    (hν3 : ν3 ∈ BPrimeOf c h12 χ) :
    BPrimeOf c h12 χ = {ν1, ν2, ν3} := by
  classical
  have hsub : ({ν1, ν2, ν3} : Finset (Irr (↥c.H0))) ⊆
      BPrimeOf c h12 χ := by
    intro ν hν
    simp only [Finset.mem_insert, Finset.mem_singleton] at hν
    rcases hν with rfl | rfl | rfl
    · exact hν1
    · exact hν2
    · exact hν3
  have hthree : ({ν1, ν2, ν3} : Finset (Irr (↥c.H0))).card = 3 := by
    simp [hν12, hν23, hν13]
  have hcard : (BPrimeOf c h12 χ).card = 3 := by
    rcases (lemma_4_1 c h12 hSC hS4 hχ ⟨ν1, hν1⟩).1 with hcard | hcard
    · have hle := Finset.card_le_card hsub
      rw [hthree, hcard] at hle
      omega
    · exact hcard
  have heq : ({ν1, ν2, ν3} : Finset (Irr (↥c.H0))) =
      BPrimeOf c h12 χ :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hthree])
  exact heq.symm

/-- Lemma 4.1(ii) applied to the three signed Theorem-4.3 rows gives the
values `3, 1, 1, -1` when all three vertices are linear. -/
private lemma theoremC_S4_nonsingleton_t_values (c : Hyp11 G) [Hyp11KData c]
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    [Fintype ↥(LambdaHom c.H0 c.U)]
    {ν1 ν2 ν3 : Irr (↥c.H0)}
    (hν12 : ν1 ≠ ν2) (hν23 : ν2 ≠ ν3) (hν13 : ν1 ≠ ν3)
    (hν1s : conjChar c.H0 (s_normalizes_H0 c h12) ν1.1 = ν1.1)
    (hν1t : ν1.1 (tH0 c) = ν1.1 1) (hν1one : ν1.1 1 = 1)
    (hν2s : conjChar c.H0 (s_normalizes_H0 c h12) ν2.1 = ν2.1)
    (hν2t : ν2.1 (tH0 c) = ν2.1 1) (hν2one : ν2.1 1 = 1)
    (hν3s : conjChar c.H0 (s_normalizes_H0 c h12) ν3.1 = ν3.1)
    (hν3t : ν3.1 (tH0 c) = ν3.1 1) (hν3one : ν3.1 1 = 1)
    {χ1 χ2 χ3 χ4 : ClassFunction G}
    (hχ1 : IsPMIrr G χ1) (hχ2 : IsPMIrr G χ2)
    (hχ3 : IsPMIrr G χ3) (hχ4 : IsPMIrr G χ4)
    (hχ12 : scalarProduct G χ1 χ2 = 0)
    (hχ13 : scalarProduct G χ1 χ3 = 0)
    (hχ14 : scalarProduct G χ1 χ4 = 0)
    (hχ23 : scalarProduct G χ2 χ3 = 0)
    (hχ24 : scalarProduct G χ2 χ4 = 0)
    (hχ34 : scalarProduct G χ3 χ4 = 0)
    (hδ1 : deltaNu c h12 ν1 = χ1 + χ2 + χ3 + χ4)
    (hδ2 : deltaNu c h12 ν2 = χ1 - χ2 + χ3 - χ4)
    (hδ3 : deltaNu c h12 ν3 = χ1 + χ2 - χ3 - χ4) :
    χ1 c.t = 3 ∧ χ2 c.t = 1 ∧ χ3 c.t = 1 ∧ χ4 c.t = -1 := by
  classical
  have hzero_symm : ∀ {a b : ClassFunction G}, scalarProduct G a b = 0 →
      scalarProduct G b a = 0 := by
    intro a b hab
    calc
      scalarProduct G b a = star (scalarProduct G a b) :=
        (scalarProduct_star_comm a b).symm
      _ = 0 := by rw [hab]; simp
  have hχ21 := hzero_symm hχ12
  have hχ31 := hzero_symm hχ13
  have hχ41 := hzero_symm hχ14
  have hχ32 := hzero_symm hχ23
  have hχ42 := hzero_symm hχ24
  have hχ43 := hzero_symm hχ34
  have hχ11 := scalarProduct_self_eq_one_of_isPMIrr hχ1
  have hχ22 := scalarProduct_self_eq_one_of_isPMIrr hχ2
  have hχ33 := scalarProduct_self_eq_one_of_isPMIrr hχ3
  have hχ44 := scalarProduct_self_eq_one_of_isPMIrr hχ4
  have hp11 : scalarProduct G χ1 (deltaNu c h12 ν1) = 1 := by
    rw [hδ1, scalarProduct_add_right, scalarProduct_add_right,
      scalarProduct_add_right, hχ11, hχ12, hχ13, hχ14]
    norm_num
  have hp12 : scalarProduct G χ1 (deltaNu c h12 ν2) = 1 := by
    rw [hδ2, scalarProduct_sub_right, scalarProduct_add_right,
      scalarProduct_sub_right, hχ11, hχ12, hχ13, hχ14]
    norm_num
  have hp13 : scalarProduct G χ1 (deltaNu c h12 ν3) = 1 := by
    rw [hδ3, scalarProduct_sub_right, scalarProduct_sub_right,
      scalarProduct_add_right, hχ11, hχ12, hχ13, hχ14]
    norm_num
  have hp21 : scalarProduct G χ2 (deltaNu c h12 ν1) = 1 := by
    rw [hδ1, scalarProduct_add_right, scalarProduct_add_right,
      scalarProduct_add_right, hχ21, hχ22, hχ23, hχ24]
    norm_num
  have hp22 : scalarProduct G χ2 (deltaNu c h12 ν2) = -1 := by
    rw [hδ2, scalarProduct_sub_right, scalarProduct_add_right,
      scalarProduct_sub_right, hχ21, hχ22, hχ23, hχ24]
    norm_num
  have hp23 : scalarProduct G χ2 (deltaNu c h12 ν3) = 1 := by
    rw [hδ3, scalarProduct_sub_right, scalarProduct_sub_right,
      scalarProduct_add_right, hχ21, hχ22, hχ23, hχ24]
    norm_num
  have hp31 : scalarProduct G χ3 (deltaNu c h12 ν1) = 1 := by
    rw [hδ1, scalarProduct_add_right, scalarProduct_add_right,
      scalarProduct_add_right, hχ31, hχ32, hχ33, hχ34]
    norm_num
  have hp32 : scalarProduct G χ3 (deltaNu c h12 ν2) = 1 := by
    rw [hδ2, scalarProduct_sub_right, scalarProduct_add_right,
      scalarProduct_sub_right, hχ31, hχ32, hχ33, hχ34]
    norm_num
  have hp33 : scalarProduct G χ3 (deltaNu c h12 ν3) = -1 := by
    rw [hδ3, scalarProduct_sub_right, scalarProduct_sub_right,
      scalarProduct_add_right, hχ31, hχ32, hχ33, hχ34]
    norm_num
  have hp41 : scalarProduct G χ4 (deltaNu c h12 ν1) = 1 := by
    rw [hδ1, scalarProduct_add_right, scalarProduct_add_right,
      scalarProduct_add_right, hχ41, hχ42, hχ43, hχ44]
    norm_num
  have hp42 : scalarProduct G χ4 (deltaNu c h12 ν2) = -1 := by
    rw [hδ2, scalarProduct_sub_right, scalarProduct_add_right,
      scalarProduct_sub_right, hχ41, hχ42, hχ43, hχ44]
    norm_num
  have hp43 : scalarProduct G χ4 (deltaNu c h12 ν3) = -1 := by
    rw [hδ3, scalarProduct_sub_right, scalarProduct_sub_right,
      scalarProduct_add_right, hχ41, hχ42, hχ43, hχ44]
    norm_num
  have hmem11 : ν1 ∈ BPrimeOf c h12 χ1 :=
    (BPrime_mem_iff_scalar c h12 χ1 ν1).2 ⟨hν1s, hν1t, by rw [hp11]; norm_num⟩
  have hmem12 : ν2 ∈ BPrimeOf c h12 χ1 :=
    (BPrime_mem_iff_scalar c h12 χ1 ν2).2 ⟨hν2s, hν2t, by rw [hp12]; norm_num⟩
  have hmem13 : ν3 ∈ BPrimeOf c h12 χ1 :=
    (BPrime_mem_iff_scalar c h12 χ1 ν3).2 ⟨hν3s, hν3t, by rw [hp13]; norm_num⟩
  have hmem21 : ν1 ∈ BPrimeOf c h12 χ2 :=
    (BPrime_mem_iff_scalar c h12 χ2 ν1).2 ⟨hν1s, hν1t, by rw [hp21]; norm_num⟩
  have hmem22 : ν2 ∈ BPrimeOf c h12 χ2 :=
    (BPrime_mem_iff_scalar c h12 χ2 ν2).2 ⟨hν2s, hν2t, by rw [hp22]; norm_num⟩
  have hmem23 : ν3 ∈ BPrimeOf c h12 χ2 :=
    (BPrime_mem_iff_scalar c h12 χ2 ν3).2 ⟨hν3s, hν3t, by rw [hp23]; norm_num⟩
  have hmem31 : ν1 ∈ BPrimeOf c h12 χ3 :=
    (BPrime_mem_iff_scalar c h12 χ3 ν1).2 ⟨hν1s, hν1t, by rw [hp31]; norm_num⟩
  have hmem32 : ν2 ∈ BPrimeOf c h12 χ3 :=
    (BPrime_mem_iff_scalar c h12 χ3 ν2).2 ⟨hν2s, hν2t, by rw [hp32]; norm_num⟩
  have hmem33 : ν3 ∈ BPrimeOf c h12 χ3 :=
    (BPrime_mem_iff_scalar c h12 χ3 ν3).2 ⟨hν3s, hν3t, by rw [hp33]; norm_num⟩
  have hmem41 : ν1 ∈ BPrimeOf c h12 χ4 :=
    (BPrime_mem_iff_scalar c h12 χ4 ν1).2 ⟨hν1s, hν1t, by rw [hp41]; norm_num⟩
  have hmem42 : ν2 ∈ BPrimeOf c h12 χ4 :=
    (BPrime_mem_iff_scalar c h12 χ4 ν2).2 ⟨hν2s, hν2t, by rw [hp42]; norm_num⟩
  have hmem43 : ν3 ∈ BPrimeOf c h12 χ4 :=
    (BPrime_mem_iff_scalar c h12 χ4 ν3).2 ⟨hν3s, hν3t, by rw [hp43]; norm_num⟩
  have hB1 := theoremC_BPrime_eq_three c h12 hSC hS4 hχ1
    hν12 hν23 hν13 hmem11 hmem12 hmem13
  have hB2 := theoremC_BPrime_eq_three c h12 hSC hS4 hχ2
    hν12 hν23 hν13 hmem21 hmem22 hmem23
  have hB3 := theoremC_BPrime_eq_three c h12 hSC hS4 hχ3
    hν12 hν23 hν13 hmem31 hmem32 hmem33
  have hB4 := theoremC_BPrime_eq_three c h12 hSC hS4 hχ4
    hν12 hν23 hν13 hmem41 hmem42 hmem43
  have hv1 := (lemma_4_1 c h12 hSC hS4 hχ1 ⟨ν1, hmem11⟩).2.1
  have hv2 := (lemma_4_1 c h12 hSC hS4 hχ2 ⟨ν1, hmem21⟩).2.1
  have hv3 := (lemma_4_1 c h12 hSC hS4 hχ3 ⟨ν1, hmem31⟩).2.1
  have hv4 := (lemma_4_1 c h12 hSC hS4 hχ4 ⟨ν1, hmem41⟩).2.1
  rw [hB1] at hv1
  rw [hB2] at hv2
  rw [hB3] at hv3
  rw [hB4] at hv4
  have ht1 : χ1 c.t = 3 := by
    simp [hν12, hν23, hν13, hp11, hp12, hp13,
      hν1one, hν2one, hν3one] at hv1
    norm_num at hv1
    exact hv1
  have ht2 : χ2 c.t = 1 := by
    simp [hν12, hν23, hν13, hp21, hp22, hp23,
      hν1one, hν2one, hν3one] at hv2
    exact hv2
  have ht3 : χ3 c.t = 1 := by
    simp [hν12, hν23, hν13, hp31, hp32, hp33,
      hν1one, hν2one, hν3one] at hv3
    exact hv3
  have ht4 : χ4 c.t = -1 := by
    simp [hν12, hν23, hν13, hp41, hp42, hp43,
      hν1one, hν2one, hν3one] at hv4
    exact hv4
  exact ⟨ht1, ht2, ht3, ht4⟩

/-- Evaluating the three Theorem-4.3 sign rows at `1`, where every
`deltaNu` vanishes, determines all four signed degrees from the first. -/
private lemma theoremC_S4_nonsingleton_degree_relations (c : Hyp11 G) [Hyp11KData c]
    (h12 : Hyp12 c) {ν1 ν2 ν3 : Irr (↥c.H0)}
    {χ1 χ2 χ3 χ4 : ClassFunction G}
    (hδ1 : deltaNu c h12 ν1 = χ1 + χ2 + χ3 + χ4)
    (hδ2 : deltaNu c h12 ν2 = χ1 - χ2 + χ3 - χ4)
    (hδ3 : deltaNu c h12 ν3 = χ1 + χ2 - χ3 - χ4) :
    χ1 1 = -χ2 1 ∧ χ1 1 = -χ3 1 ∧ χ1 1 = χ4 1 := by
  have he1 := congrFun hδ1 (1 : G)
  have he2 := congrFun hδ2 (1 : G)
  have he3 := congrFun hδ3 (1 : G)
  rw [theoremC_deltaNu_one_eq_zero c h12 ν1] at he1
  rw [theoremC_deltaNu_one_eq_zero c h12 ν2] at he2
  rw [theoremC_deltaNu_one_eq_zero c h12 ν3] at he3
  simp only [Pi.add_apply, Pi.sub_apply] at he1 he2 he3
  constructor
  · have htwo : (2 : ℂ) * (χ1 1 + χ2 1) = 0 := by
      linear_combination -he1 - he3
    have hsum : χ1 1 + χ2 1 = 0 :=
      (mul_eq_zero.mp htwo).resolve_left (by norm_num)
    linear_combination hsum
  constructor
  · have htwo : (2 : ℂ) * (χ1 1 + χ3 1) = 0 := by
      linear_combination -he1 - he2
    have hsum : χ1 1 + χ3 1 = 0 :=
      (mul_eq_zero.mp htwo).resolve_left (by norm_num)
    linear_combination hsum
  · have htwo : (2 : ℂ) * (χ1 1 - χ4 1) = 0 := by
      linear_combination -he2 - he3
    have hdiff : χ1 1 - χ4 1 = 0 :=
      (mul_eq_zero.mp htwo).resolve_left (by norm_num)
    linear_combination hdiff



/-- In the `|S| ≥ 8` branch, `[H0 : U] = |S0| ≥ 4`. -/
private lemma theoremC_index_ge4 (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (hS8 : Nat.card (↥(c.S : Subgroup G)) ≠ 4) :
    4 ≤ (c.U.subgroupOf c.H0).index := by
  have hU := U_index_eq_S0_card c h12
  have hS0 := S0_nat_card c
  have hS := S_nat_card c
  have hm2 : 2 ≤ c.m := by
    by_contra hm
    have hmle : c.m ≤ 1 := by omega
    have hpow : 2 ^ c.m ≤ 2 := by
      exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hmle
    have hcard : Nat.card (↥(c.S : Subgroup G)) ≤ 4 := by
      rw [hS]
      nlinarith
    have hge : 4 ≤ Nat.card (↥(c.S : Subgroup G)) := by
      have hpow1 : 2 ≤ 2 ^ c.m := by
        have h1 : 2 ^ 1 ≤ 2 ^ c.m :=
          pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) c.one_le_m
        simpa using h1
      rw [hS]
      nlinarith
    exact hS8 (le_antisymm hcard hge)
  have h4 : 4 ≤ 2 ^ c.m := by
    have hpow : 2 ^ 2 ≤ 2 ^ c.m :=
      pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hm2
    norm_num at hpow ⊢
    exact hpow
  rw [hU, hS0]
  exact h4

/-- `Λ` contains a character whose square is nontrivial (used as `λ₃`). -/
private lemma theoremC_exists_lambda3 (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (hm : 4 ≤ (c.U.subgroupOf c.H0).index) :
    ∃ l : LambdaHom c.H0 c.U, l ^ 2 ≠ 1 := by
  classical
  have hcard : 4 ≤ Fintype.card (LambdaHom c.H0 c.U) := by
    rw [← Nat.card_eq_fintype_card, lambda_card_eq_index c h12]
    exact hm
  have htwo : (Finset.univ.filter (fun l : LambdaHom c.H0 c.U => l ^ 2 = 1)).card = 2 :=
    lambda_two_torsion_card c h12
  by_contra hnone
  push Not at hnone
  have hall : ∀ l : LambdaHom c.H0 c.U, l ^ 2 = 1 := hnone
  have hf : (Finset.univ.filter (fun l : LambdaHom c.H0 c.U => l ^ 2 = 1)) =
      (Finset.univ : Finset (LambdaHom c.H0 c.U)) := by
    ext l
    simp [hall l]
  rw [hf] at htwo
  simp at htwo
  omega

/-- The stabilizer of a linear `κ₁` in `Λ` is trivial, hence every
`κᵢ = λᵢ·κ₁` has full `Λ`-orbit. -/
private lemma theoremC_kappa_stab_one (c : Hyp11 G) [Hyp11KData c] (_h12 : Hyp12 c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1) :
    (Finset.univ.filter (fun l : LambdaHom c.H0 c.U => LambdaChar l.1 * κ1 = κ1)).card = 1 := by
  classical
  have hle : (Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
      LambdaChar l.1 * κ1 = κ1)) ≤ ({1} : Finset (LambdaHom c.H0 c.U)) := by
    intro l hl
    simp
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    apply Units.ext
    have hx := congrArg (fun f : ClassFunction (↥c.H0) => f x)
      (Finset.mem_filter.mp hl).2
    have hκnz : κ1 x ≠ 0 := linearChar_ne_zero hκ1lin x
    apply mul_right_cancel₀ hκnz
    simpa [LambdaChar] using hx
  have hge : 1 ≤ (Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
      LambdaChar l.1 * κ1 = κ1)).card := by
    exact Finset.card_pos.mpr ⟨1, by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ 1, ?_⟩
      have h1 : LambdaChar (1 : LambdaHom c.H0 c.U).1 =
          (1 : ClassFunction (↥c.H0)) := by
        ext x
        rfl
      rw [h1, one_mul]⟩
  have hlecard : (Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
      LambdaChar l.1 * κ1 = κ1)).card ≤ 1 := by
    simpa using Finset.card_le_card hle
  omega

/-- `|Λ·κᵢ| = [H0 : U]` for every `κᵢ = λᵢ·κ₁` with `κ₁` linear. -/
private lemma theoremC_kappa_orbit_card (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (l : LambdaHom c.H0 c.U) :
    (orbit c.H0 c.U (kappa c κ1 l)).card = (c.U.subgroupOf c.H0).index := by
  classical
  have h := orbit_card_mul_stab c.H0 c.U (kappa c κ1 l)
  rw [theoremC_kappa_stab_one c h12 (kappa_isLinear c h12 hκ1lin l), mul_one] at h
  rw [← Nat.card_eq_fintype_card, lambda_card_eq_index c h12] at h
  exact h

/-- The signed decomposition of `κ̃₁` and `κ̃₃`: `κ̃₁ = χ₁+χ₂` and
`κ̃₃ = χ₃` with `χᵢ ∈ ±Irr(G)` (equation (1) of the paper). -/
private lemma theoremC_kappa_decomp (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1S0 : ∀ x : ↥c.H0, (x : G) ∈ c.S0 → κ1 x = 1)
    (hκ1comm : ∀ x : ↥c.H0, (x : G) ∈ ⁅(c.S : Subgroup G), c.U⁆ → κ1 x = 1)
    (l3 : LambdaHom c.H0 c.U) (hl3 : l3 ^ 2 ≠ 1) :
    ∃ χ1 χ2 χ3 : ClassFunction G,
      IsPMIrr G χ1 ∧ IsPMIrr G χ2 ∧ IsPMIrr G χ3 ∧
        tildeNu c h12 ⟨κ1, hκ1lin.1⟩ = χ1 + χ2 ∧
        tildeNu c h12 ⟨kappa c κ1 l3, (kappa_isLinear c h12 hκ1lin l3).1⟩ = χ3 ∧
        scalarProduct G χ1 (tildeNu c h12 ⟨κ1, hκ1lin.1⟩) = 1 ∧
        scalarProduct G χ2 (tildeNu c h12 ⟨κ1, hκ1lin.1⟩) = 1 := by
  classical
  let κ1Irr : Irr (↥c.H0) := ⟨κ1, hκ1lin.1⟩
  let κ3Irr : Irr (↥c.H0) := ⟨kappa c κ1 l3, (kappa_isLinear c h12 hκ1lin l3).1⟩
  have hκ1fix : conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1 :=
    kappaOne_fixed_by_s c h12 hκ1lin hκ1S0 hκ1comm
  have hnorm1 : normSq G (tildeNu c h12 κ1Irr) = 2 := by
    have h := tildeNu_norm c h12 κ1Irr
    simpa [κ1Irr, hκ1fix] using h
  rcases signed_pair_decomp (tildeNu_isGeneralized c h12 κ1Irr) hnorm1 with
    ⟨ψ1, ψ2, hψ1, hψ2, hψ12, hcase⟩
  have hκ3s : conjChar c.H0 (s_normalizes_H0 c h12) (kappa c κ1 l3) ≠ kappa c κ1 l3 := by
    have hiff := kappa_conj_fixed_iff c h12 hκ1lin hκ1S0 hκ1comm l3
    intro hfix
    rcases hiff.mp hfix with h1 | h2
    · have hl3' : l3 ^ 2 = 1 := by
        rw [h1]
        simp
      exact hl3 hl3'
    · have hl3' : l3 ^ 2 = 1 := by
        rw [h2]
        exact lambdaTwo_sq_eq_one c h12
      exact hl3 hl3'
  have hχ3 : IsPMIrr G (tildeNu c h12 κ3Irr) :=
    signed_irr_of_nonfixed c h12 (by simpa [κ3Irr] using hκ3s)
  rcases hcase with hc1 | hc2 | hc3 | hc4
  · refine ⟨ψ1, -ψ2, tildeNu c h12 κ3Irr, Or.inl hψ1,
      Or.inr (by simpa using hψ2), hχ3, ?_, rfl, ?_, ?_⟩
    · simpa [hc1]
    · rw [hc1]
      simp [scalarProduct_sub_right, scalarProduct_irreducible_self hψ1,
        scalarProduct_irreducible_orthogonal hψ1 hψ2 hψ12]
    · rw [hc1]
      simp [scalarProduct_neg_left, scalarProduct_sub_right,
        scalarProduct_irreducible_orthogonal hψ2 hψ1 (Ne.symm hψ12),
        scalarProduct_irreducible_self hψ2]
  · refine ⟨ψ1, ψ2, tildeNu c h12 κ3Irr, Or.inl hψ1,
      Or.inl hψ2, hχ3, ?_, rfl, ?_, ?_⟩
    · simpa [hc2]
    · rw [hc2]
      simp [scalarProduct_add_right, scalarProduct_irreducible_self hψ1,
        scalarProduct_irreducible_orthogonal hψ1 hψ2 hψ12]
    · rw [hc2]
      simp [scalarProduct_add_right,
        scalarProduct_irreducible_orthogonal hψ2 hψ1 (Ne.symm hψ12),
        scalarProduct_irreducible_self hψ2]
  · refine ⟨-ψ1, -ψ2, tildeNu c h12 κ3Irr, Or.inr (by simpa using hψ1),
      Or.inr (by simpa using hψ2), hχ3, ?_, rfl, ?_, ?_⟩
    · simpa [hc3]
    · rw [hc3]
      simp [scalarProduct_neg_left, scalarProduct_sub_right,
        scalarProduct_neg_right, scalarProduct_irreducible_self hψ1,
        scalarProduct_irreducible_orthogonal hψ1 hψ2 hψ12]
    · rw [hc3]
      simp [scalarProduct_neg_left, scalarProduct_sub_right,
        scalarProduct_neg_right, scalarProduct_irreducible_orthogonal hψ2 hψ1 (Ne.symm hψ12),
        scalarProduct_irreducible_self hψ2]
  · refine ⟨-ψ1, ψ2, tildeNu c h12 κ3Irr, Or.inr (by simpa using hψ1),
      Or.inl hψ2, hχ3, ?_, rfl, ?_, ?_⟩
    · simpa [hc4]
    · rw [hc4]
      simp [scalarProduct_neg_left, scalarProduct_add_right,
        scalarProduct_neg_right, scalarProduct_irreducible_self hψ1,
        scalarProduct_irreducible_orthogonal hψ1 hψ2 hψ12]
    · rw [hc4]
      simp [scalarProduct_add_right,
        scalarProduct_neg_right,
        scalarProduct_irreducible_orthogonal hψ2 hψ1 (Ne.symm hψ12),
        scalarProduct_irreducible_self hψ2]

/-- Lemma 3.4 applied to `χ₃`: `B(χ₃) = {κ₃, κ₃ˢ}` and `χ₃(t) = ±2`
(equation (1) of the paper). -/
private lemma theoremC_chi3_facts (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (hSC : Section3Hyp c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1S0 : ∀ x : ↥c.H0, (x : G) ∈ c.S0 → κ1 x = 1)
    (hκ1comm : ∀ x : ↥c.H0, (x : G) ∈ ⁅(c.S : Subgroup G), c.U⁆ → κ1 x = 1)
    (l3 : LambdaHom c.H0 c.U) (hl3 : l3 ^ 2 ≠ 1)
    {χ3 : ClassFunction G} (hχ3eq : tildeNu c h12
      ⟨kappa c κ1 l3, (kappa_isLinear c h12 hκ1lin l3).1⟩ = χ3)
    (hχ3 : IsPMIrr G χ3) :
    BOf c h12 χ3 =
        {⟨kappa c κ1 l3, (kappa_isLinear c h12 hκ1lin l3).1⟩,
          conjIrr c h12 ⟨kappa c κ1 l3, (kappa_isLinear c h12 hκ1lin l3).1⟩} ∧
      (χ3 c.t = 2 ∨ χ3 c.t = -2) := by
  classical
  let κ3Irr : Irr (↥c.H0) :=
    ⟨kappa c κ1 l3, (kappa_isLinear c h12 hκ1lin l3).1⟩
  have hκ3s : conjChar c.H0 (s_normalizes_H0 c h12) κ3Irr.1 ≠ κ3Irr.1 := by
    have hiff := kappa_conj_fixed_iff c h12 hκ1lin hκ1S0 hκ1comm l3
    intro hfix
    rcases hiff.mp hfix with h1 | h2
    · have hl3' : l3 ^ 2 = 1 := by
        rw [h1]
        simp
      exact hl3 hl3'
    · have hl3' : l3 ^ 2 = 1 := by
        rw [h2]
        exact lambdaTwo_sq_eq_one c h12
      exact hl3 hl3'
  have hnorm : normSq G (tildeNu c h12 κ3Irr) = 1 := by
    have h := tildeNu_norm c h12 κ3Irr
    simpa [κ3Irr, hκ3s] using h
  have hself : scalarProduct G (tildeNu c h12 κ3Irr) (tildeNu c h12 κ3Irr) = 1 := by
    simpa [normSq] using hnorm
  have hκ3B : κ3Irr ∈ BOf c h12 χ3 := by
    rw [BOf_mem_iff]
    rw [hχ3eq, ← hχ3eq]
    exact ne_of_eq_of_ne hself (by norm_num)
  have hνL : conjChar c.H0 (s_normalizes_H0 c h12) κ3Irr.1 ∉ orbit c.H0 c.U κ3Irr.1 ∨
      (orbit c.H0 c.U κ3Irr.1).card = (c.U.subgroupOf c.H0).index := by
    right
    simpa [κ3Irr] using theoremC_kappa_orbit_card c h12 hκ1lin l3
  rcases lemma_3_4 c h12 hSC hχ3 hκ3B hκ3s hνL with ⟨hB, hT⟩
  constructor
  · simpa [κ3Irr] using hB
  · have hχ3t : χ3 c.t = 2 * κ3Irr.1 (tH0 c) := by
      rw [← hχ3eq, hT]
    have hκ1t : κ1 (tH0 c) = 1 :=
      hκ1S0 (tH0 c) (by simpa [tH0] using c.t_mem_S0)
    have hl3t : (l3.1 (tH0 c) : ℂ) = 1 ∨ (l3.1 (tH0 c) : ℂ) = -1 :=
      lambda_t_value_pm_one c l3
    have hκ3t : κ3Irr.1 (tH0 c) = 1 ∨ κ3Irr.1 (tH0 c) = -1 := by
      rcases hl3t with h1 | hm1
      · left
        change (kappa c κ1 l3) (tH0 c) = 1
        simp [kappa, LambdaChar, hκ1t, h1]
      · right
        change (kappa c κ1 l3) (tH0 c) = -1
        simp [kappa, LambdaChar, hκ1t, hm1]
    rcases hκ3t with h1 | hm1
    · left
      rw [hχ3t, h1]
      norm_num
    · right
      rw [hχ3t, hm1]
      norm_num

/-- `κ₁` (fixed by `s`) is not one of the pair `{ν, νˢ}` unless it equals
`ν`.  Used to extract the equation-(2) consequences of Lemmas 3.3/3.4. -/
private lemma theoremC_κ1_not_mem_pair (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1fix : conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1)
    {ν : Irr (↥c.H0)} (hνκ : ν ≠ ⟨κ1, hκ1lin.1⟩) :
    ⟨κ1, hκ1lin.1⟩ ∉ ({ν, conjIrr c h12 ν} : Finset (Irr (↥c.H0))) := by
  rw [Finset.mem_insert, Finset.mem_singleton]
  intro h
  rcases h with hEqν | hEqνs
  · exact hνκ hEqν.symm
  · apply hνκ
    apply Subtype.ext
    have hEq : κ1 = conjChar c.H0 (s_normalizes_H0 c h12) ν.1 := by
      simpa [conjIrr_coe] using congrArg Subtype.val hEqνs
    have hEq2 : conjChar c.H0 (s_normalizes_H0 c h12) κ1 = ν.1 := by
      have h := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hEq
      rw [conjChar_conjChar c h12 ν.1] at h
      exact h
    rw [hκ1fix] at hEq2
    exact hEq2.symm

/-- An `s`-fixed irreducible cannot be one of the conjugate pair generated
by an irreducible that is not fixed by `s`. -/
private lemma theoremC_fixed_Irr_not_mem_conj_pair
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {mu nu : Irr (↥c.H0)}
    (hmufix : conjChar c.H0 (s_normalizes_H0 c h12) mu.1 = mu.1)
    (hnunonfix : conjChar c.H0 (s_normalizes_H0 c h12) nu.1 ≠ nu.1) :
    mu ∉ ({nu, conjIrr c h12 nu} : Finset (Irr (↥c.H0))) := by
  rw [Finset.mem_insert, Finset.mem_singleton]
  intro hmem
  rcases hmem with hmunu | hmunus
  · apply hnunonfix
    simpa [hmunu] using hmufix
  · have hEq : mu.1 = conjChar c.H0 (s_normalizes_H0 c h12) nu.1 := by
      simpa [conjIrr_coe] using congrArg Subtype.val hmunus
    have hEq2 : conjChar c.H0 (s_normalizes_H0 c h12) mu.1 = nu.1 := by
      have h := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hEq
      rw [conjChar_conjChar c h12 nu.1] at h
      exact h
    apply hnunonfix
    calc
      conjChar c.H0 (s_normalizes_H0 c h12) nu.1 = mu.1 := hEq.symm
      _ = conjChar c.H0 (s_normalizes_H0 c h12) mu.1 := hmufix.symm
      _ = nu.1 := hEq2

/-- If `B(ψ)` contains an `s`-fixed member, every member's `s`-conjugate
lies in its `Λ`-orbit.  The nonfixed case follows from Lemma 3.4, since its
two-member alternative cannot contain the fixed member. -/
private lemma theoremC_BOf_conj_mem_orbit_of_fixed_member
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (hSC : Section3Hyp c)
    {psi : ClassFunction G} (hpsi : IsPMIrr G psi)
    {mu : Irr (↥c.H0)}
    (hmuB : mu ∈ BOf c h12 psi)
    (hmufix : conjChar c.H0 (s_normalizes_H0 c h12) mu.1 = mu.1) :
    ∀ nu : Irr (↥c.H0), nu ∈ BOf c h12 psi →
      conjChar c.H0 (s_normalizes_H0 c h12) nu.1 ∈ orbit c.H0 c.U nu.1 := by
  intro nu hnuB
  by_cases hnufix : conjChar c.H0 (s_normalizes_H0 c h12) nu.1 = nu.1
  · simpa [hnufix] using orbit_self_mem c.H0 c.U nu.1
  · by_contra hnot
    have h34 := lemma_3_4 c h12 hSC hpsi hnuB hnufix (Or.inl hnot)
    have hmupair : mu ∉ ({nu, conjIrr c h12 nu} : Finset (Irr (↥c.H0))) :=
      theoremC_fixed_Irr_not_mem_conj_pair c h12 hmufix hnufix
    exact hmupair (by simpa [h34.1] using hmuB)

/-- The `s`-conjugate of `λκ` is the `Λ`-translate indexed by
`λ⁻¹λ⁻¹`, hence lies in the same `Λ`-orbit whenever `κ` is `s`-fixed. -/
private lemma theoremC_kappa_conj_mem_orbit
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {kappa1 : ClassFunction (↥c.H0)}
    (hkappa1fix : conjChar c.H0 (s_normalizes_H0 c h12) kappa1 = kappa1)
    (l : LambdaHom c.H0 c.U) :
    conjChar c.H0 (s_normalizes_H0 c h12) (kappa c kappa1 l) ∈
      orbit c.H0 c.U (kappa c kappa1 l) := by
  classical
  have hconj : conjChar c.H0 (s_normalizes_H0 c h12) (kappa c kappa1 l) =
      kappa c kappa1 l⁻¹ := by
    unfold kappa
    ext x
    have hlamb := congrFun (LambdaChar_conj_eq_inv c h12 l) x
    have hkappa := congrFun hkappa1fix x
    simpa [conjChar, conjMonoidHom, LambdaChar] using
      congrArg₂ (· * ·) hlamb hkappa
  rw [hconj]
  refine Finset.mem_image.mpr ⟨l⁻¹ * l⁻¹, Finset.mem_univ _, ?_⟩
  ext x
  change
    ((l⁻¹ * l⁻¹).1 x : ℂ) * ((l.1 x : ℂ) * kappa1 x) =
      (l⁻¹).1 x * kappa1 x
  simp [mul_assoc]

/-- If `B(ψ)` is exactly a conjugate pair and the conjugate of its first
member lies in its `Λ`-orbit, the Lemma-3.6 orbit condition holds for both
members. -/
private lemma theoremC_BOf_pair_conj_mem_orbit
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {psi : ClassFunction G} {nu : Irr (↥c.H0)}
    (hB : BOf c h12 psi = {nu, conjIrr c h12 nu})
    (hconjL : conjChar c.H0 (s_normalizes_H0 c h12) nu.1 ∈
      orbit c.H0 c.U nu.1) :
    ∀ mu : Irr (↥c.H0), mu ∈ BOf c h12 psi →
      conjChar c.H0 (s_normalizes_H0 c h12) mu.1 ∈ orbit c.H0 c.U mu.1 := by
  intro mu hmu
  rw [hB] at hmu
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmu
  rcases hmu with hmunu | hmunus
  · subst mu
    exact hconjL
  · subst mu
    have horbitEq := orbit_eq_of_mem' c hconjL
    rw [conjIrr_coe, conjChar_conjChar c h12 nu.1, horbitEq]
    exact orbit_self_mem c.H0 c.U nu.1

/-- Equation (2), part 1: for every `ν ≠ κ₁` in `B(χ₁)`,
`|Λν| ≠ m`.  If `ν` is `s`-fixed this is Lemma 3.3 (else `|S| = 4`); if
`ν` is not `s`-fixed it is Lemma 3.4 (else `κ₁ ∈ {ν, νˢ}`). -/
private lemma theoremC_chi1_BOf_orbit_ne_m (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (hSC : Section3Hyp c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    {χ1 χ2 : ClassFunction G} (hχ1 : IsPMIrr G χ1)
    (_hκ1tilde : tildeNu c h12 ⟨κ1, hκ1lin.1⟩ = χ1 + χ2)
    (hpairκ1 : scalarProduct G χ1 (tildeNu c h12 ⟨κ1, hκ1lin.1⟩) = 1)
    (hκ1fix : conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1)
    (horbitκ1 : (orbit c.H0 c.U κ1).card = (c.U.subgroupOf c.H0).index)
    (hS8 : Nat.card (↥(c.S : Subgroup G)) ≠ 4)
    {ν : Irr (↥c.H0)} (hνB : ν ∈ BOf c h12 χ1) (hνκ : ν ≠ ⟨κ1, hκ1lin.1⟩) :
    (orbit c.H0 c.U ν.1).card ≠ (c.U.subgroupOf c.H0).index := by
  classical
  let κ1Irr : Irr (↥c.H0) := ⟨κ1, hκ1lin.1⟩
  have hκ1B : κ1Irr ∈ BOf c h12 χ1 := by
    rw [BOf_mem_iff]
    rw [hpairκ1]
    norm_num
  intro hcard
  by_cases hfix : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1
  · have h33 := lemma_3_3 c h12 hSC hχ1
      ⟨κ1Irr, ν, hκ1B, hνB, (by simpa [κ1Irr] using hνκ.symm),
        hκ1fix, hfix, horbitκ1, hcard⟩
    exact hS8 h33.2
  · have h34 := lemma_3_4 c h12 hSC hχ1 hνB hfix (Or.inr hcard)
    have hκ1not : κ1Irr ∉ ({ν, conjIrr c h12 ν} : Finset (Irr (↥c.H0))) :=
      theoremC_κ1_not_mem_pair c h12 hκ1lin hκ1fix hνκ
    exact hκ1not (by simpa [h34.1] using hκ1B)

/-- Equation (2), part 2 (partial): for `ν ≠ κ₁` in `B(χ₁)` with
`νˢ ≠ ν`, Lemma 3.4 forces `νˢ ∈ Λν`.  (The remaining bad case
`νˢ ∈ Λν`, `|Λν| ≠ m` is the gap recorded in the task card.) -/
private lemma theoremC_chi1_BOf_conj_mem_orbit (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (hSC : Section3Hyp c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    {χ1 χ2 : ClassFunction G} (hχ1 : IsPMIrr G χ1)
    (_hκ1tilde : tildeNu c h12 ⟨κ1, hκ1lin.1⟩ = χ1 + χ2)
    (hpairκ1 : scalarProduct G χ1 (tildeNu c h12 ⟨κ1, hκ1lin.1⟩) = 1)
    (hκ1fix : conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1)
    {ν : Irr (↥c.H0)} (hνB : ν ∈ BOf c h12 χ1) (hνκ : ν ≠ ⟨κ1, hκ1lin.1⟩)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1) :
    conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈ orbit c.H0 c.U ν.1 := by
  classical
  let κ1Irr : Irr (↥c.H0) := ⟨κ1, hκ1lin.1⟩
  have hκ1B : κ1Irr ∈ BOf c h12 χ1 := by
    rw [BOf_mem_iff]
    rw [hpairκ1]
    norm_num
  by_contra hnot
  have h34 := lemma_3_4 c h12 hSC hχ1 hνB hνs (Or.inl hnot)
  have hκ1not : κ1Irr ∉ ({ν, conjIrr c h12 ν} : Finset (Irr (↥c.H0))) :=
    theoremC_κ1_not_mem_pair c h12 hκ1lin hκ1fix hνκ
  exact hκ1not (by simpa [h34.1] using hκ1B)

/-- Remark-3.1 extraction used by equation (3).  If the `Λ`-orbit of
`ν` is `s`-stable but not full, its underlying `S₀`-orbit has two
members and one of the two distinguished reflections fixes a base
constituent `α ∈ Irr(U)`. -/
private lemma theoremC_reflection_fixed_data_of_conj_mem_orbit
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (hSC : Section3Hyp c)
    {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈
      orbit c.H0 c.U ν.1)
    (hcard : (orbit c.H0 c.U ν.1).card ≠
      (c.U.subgroupOf c.H0).index) :
    ∃ α : Irr (↥c.U),
      (conjIrrS c c.t1_mem_S α = α ∨ conjIrrS c c.t2_mem_S α = α) ∧
      restrictU c h12 ν.1 =
        (fun u : ↥c.U => α.1 u +
          (conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α).1 u) ∧
      ν.1 1 = 2 * α.1 1 := by
  classical
  rcases orbit_is_orbitOfAlpha c h12 hSC ν with ⟨α, hOrbit⟩
  have hs0card : (s0Orbit c α).card = 2 := by
    have hle : (s0Orbit c α).card ≤ 2 := s0Orbit_card_le_two c hSC α
    have hpos : 0 < (s0Orbit c α).card :=
      Finset.card_pos.mpr ⟨α, s0Orbit_self_mem c α⟩
    have hne1 : (s0Orbit c α).card ≠ 1 := by
      intro h1
      apply hcard
      rw [hOrbit, orbitOfAlpha_card c h12 hSC α, h1]
      simp
    omega
  have hfixedOrbit : ∀ ξ : ClassFunction (↥c.H0),
      ξ ∈ orbitOfAlpha c h12 hSC α →
      conjChar c.H0 (s_normalizes_H0 c h12) ξ ∈
        orbitOfAlpha c h12 hSC α := by
    intro ξ hξ
    have hξ' : ξ ∈ orbit c.H0 c.U ν.1 := by simpa [hOrbit] using hξ
    have hconj := orbit_subset_conjChar c h12 ξ hξ'
    have hOrbitConj : orbit c.H0 c.U
        (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) =
        orbit c.H0 c.U ν.1 := orbit_eq_of_mem' c hνs
    rw [hOrbitConj] at hconj
    simpa [hOrbit] using hconj
  have hnotle : ¬ stabilizerS c α ≤ (c.S0 : Subgroup G) :=
    (orbitOfAlpha_fixed_iff c h12 hSC α).mp hfixedOrbit
  have hreflection :
      conjIrrS c c.t1_mem_S α = α ∨ conjIrrS c c.t2_mem_S α = α := by
    rcases (stabilizerS_not_le_S0_iff c h12 hSC α).mp hnotle with
      hfull | hpair
    · omega
    · rcases hpair with ⟨_hcard2, hstab1 | hstab2⟩
      · left
        have ht1 : c.t1 ∈ stabilizerS c α := by
          rw [hstab1]
          exact SetLike.le_def.mp le_sup_right (Subgroup.mem_zpowers c.t1)
        rcases ht1 with ⟨ht1S, ht1fix⟩
        exact (conjIrrS_proof_irrel c c.t1_mem_S ht1S α).trans ht1fix
      · right
        have ht2 : c.t2 ∈ stabilizerS c α := by
          rw [hstab2]
          exact SetLike.le_def.mp le_sup_right (Subgroup.mem_zpowers c.t2)
        rcases ht2 with ⟨ht2S, ht2fix⟩
        exact (conjIrrS_proof_irrel c c.t2_mem_S ht2S α).trans ht2fix
  have hnotfixed :
      conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α ≠ α := by
    intro hfix
    have hsingleton := s0Orbit_eq_singleton_of_fixed c hSC α hfix
    rw [hsingleton] at hs0card
    norm_num at hs0card
  have hrestrict : restrictU c h12 ν.1 =
      fun u : ↥c.U => α.1 u +
        (conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α).1 u := by
    have hspec := (orbitOfAlpha_spec c h12 hSC α).2 ν.1 (by
      rw [← hOrbit]
      exact orbit_self_mem c.H0 c.U ν.1)
    rw [hspec]
    exact s0Orbit_sum_eq_α_add_r0_of_not_fixed c hSC α hnotfixed
  have hdegree : ν.1 1 = 2 * α.1 1 := by
    have h := congrFun hrestrict (1 : ↥c.U)
    rw [restrictU_one c h12 ν.1,
      conjIrrS_degree_eq c (c.S0_le_S (S0_generator_mem_S0 c)) α] at h
    calc
      ν.1 1 = α.1 1 + α.1 1 := h
      _ = 2 * α.1 1 := by ring
  exact ⟨α, hreflection, hrestrict, hdegree⟩

/-- Equation-(3) orbit data for every non-distinguished member of
`B(χ₁)`, including the exceptional nonfixed case allowed by Lemma 3.4. -/
private lemma theoremC_chi1_reflection_fixed_data
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (hSC : Section3Hyp c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    {χ1 χ2 : ClassFunction G} (hχ1 : IsPMIrr G χ1)
    (hκ1tilde : tildeNu c h12 ⟨κ1, hκ1lin.1⟩ = χ1 + χ2)
    (hpairκ1 : scalarProduct G χ1 (tildeNu c h12 ⟨κ1, hκ1lin.1⟩) = 1)
    (hκ1fix : conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1)
    (horbitκ1 : (orbit c.H0 c.U κ1).card = (c.U.subgroupOf c.H0).index)
    (hS8 : Nat.card (↥(c.S : Subgroup G)) ≠ 4)
    {ν : Irr (↥c.H0)} (hνB : ν ∈ BOf c h12 χ1)
    (hνκ : ν ≠ ⟨κ1, hκ1lin.1⟩) :
    ∃ α : Irr (↥c.U),
      (conjIrrS c c.t1_mem_S α = α ∨ conjIrrS c c.t2_mem_S α = α) ∧
      restrictU c h12 ν.1 =
        (fun u : ↥c.U => α.1 u +
          (conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α).1 u) ∧
      ν.1 1 = 2 * α.1 1 := by
  have hcard := theoremC_chi1_BOf_orbit_ne_m c h12 hSC hκ1lin hχ1 hκ1tilde
    hpairκ1 hκ1fix horbitκ1 hS8 hνB hνκ
  have hconj : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈
      orbit c.H0 c.U ν.1 := by
    by_cases hfix : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1
    · simpa [hfix] using orbit_self_mem c.H0 c.U ν.1
    · exact theoremC_chi1_BOf_conj_mem_orbit c h12 hSC hκ1lin hχ1 hκ1tilde
        hpairκ1 hκ1fix hνB hνκ hfix
  exact theoremC_reflection_fixed_data_of_conj_mem_orbit c h12 hSC hconj hcard

/-- `κ₂ = λ₂κ₁` is not in `B(χ₁)`: otherwise Lemma 3.3 forces `|S| = 4`. -/
private lemma theoremC_chi1_kappaTwo_not_mem (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (hSC : Section3Hyp c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1S0 : ∀ x : ↥c.H0, (x : G) ∈ c.S0 → κ1 x = 1)
    (hκ1comm : ∀ x : ↥c.H0, (x : G) ∈ ⁅(c.S : Subgroup G), c.U⁆ → κ1 x = 1)
    {χ1 : ClassFunction G} (hχ1 : IsPMIrr G χ1)
    (hκ1B : ⟨κ1, hκ1lin.1⟩ ∈ BOf c h12 χ1)
    (hκ1fix : conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1)
    (horbitκ1 : (orbit c.H0 c.U κ1).card = (c.U.subgroupOf c.H0).index)
    (hS8 : Nat.card (↥(c.S : Subgroup G)) ≠ 4) :
    ⟨kappa c κ1 (lambdaTwo c h12),
      (kappa_isLinear c h12 hκ1lin (lambdaTwo c h12)).1⟩ ∉ BOf c h12 χ1 := by
  classical
  let κ2Irr : Irr (↥c.H0) :=
    ⟨kappa c κ1 (lambdaTwo c h12), (kappa_isLinear c h12 hκ1lin (lambdaTwo c h12)).1⟩
  intro hκ2B
  have hκ2fix : conjChar c.H0 (s_normalizes_H0 c h12) (kappa c κ1 (lambdaTwo c h12)) =
      kappa c κ1 (lambdaTwo c h12) :=
    (kappa_conj_fixed_iff c h12 hκ1lin hκ1S0 hκ1comm (lambdaTwo c h12)).mpr (Or.inr rfl)
  have hκ2orb : (orbit c.H0 c.U (kappa c κ1 (lambdaTwo c h12))).card =
      (c.U.subgroupOf c.H0).index :=
    theoremC_kappa_orbit_card c h12 hκ1lin (lambdaTwo c h12)
  have hne : (⟨κ1, hκ1lin.1⟩ : Irr (↥c.H0)) ≠ κ2Irr := by
    intro hEq
    have hEq' := congrArg Subtype.val hEq
    have hκ2 : kappa c κ1 (lambdaTwo c h12) = LambdaChar (lambdaTwo c h12).1 * κ1 := rfl
    dsimp [κ2Irr] at hEq'
    rw [hκ2] at hEq'
    apply lambdaTwo_ne_one c h12
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    apply Units.ext
    have hx := congrFun hEq' x
    have hκnz : (κ1 x : ℂ) ≠ 0 := linearChar_ne_zero hκ1lin x
    exact mul_right_cancel₀ hκnz (by simpa [LambdaChar] using hx.symm)
  have h33 := lemma_3_3 c h12 hSC hχ1
    ⟨(⟨κ1, hκ1lin.1⟩ : Irr (↥c.H0)), κ2Irr, hκ1B, hκ2B, hne, hκ1fix, hκ2fix,
      horbitκ1, hκ2orb⟩
  exact hS8 h33.2

/-! ## Group-order infrastructure for the cardinality-three endpoint -/

private lemma card_dvd_index_of_normal_disjoint
    {K B U : Subgroup G} (hKN : IsNormalIn K U) (hBU : B ≤ U)
    (hBK : B ⊓ K = ⊥) :
    Nat.card (↥K) ∣ (B.subgroupOf U).index := by
  let KU : Subgroup (↥U) := K.subgroupOf U
  let BU : Subgroup (↥U) := B.subgroupOf U
  have hKU_norm : KU.Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hKN.1).mpr ?_
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact hKN.2 u hu k hk
    · intro hk
      have hk' := hKN.2 u⁻¹ (U.inv_mem hu) (u * k * u⁻¹) hk
      have hEq : u⁻¹ * (u * k * u⁻¹) * u = k := by group
      simpa [hEq, inv_inv] using hk'
  have hdisj : Disjoint BU KU := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    have hxB : (x : G) ∈ B :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).1
    have hxK : (x : G) ∈ K :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).2
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hBK]
      exact Subgroup.mem_inf.mpr ⟨hxB, hxK⟩
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hxbot))
  let J : Subgroup (↥U) := BU ⊔ KU
  have hnormz : BU ≤ Subgroup.normalizer KU := by
    rw [(Subgroup.normalizer_eq_top_iff.mpr hKU_norm)]
    exact le_top
  have hcoe : (↑J : Set (↥U)) = (↑BU : Set (↥U)) * (↑KU : Set (↥U)) := by
    change (↑(BU ⊔ KU) : Set (↥U)) = (↑BU : Set (↥U)) * (↑KU : Set (↥U))
    exact Subgroup.coe_mul_of_left_le_normalizer_right BU KU hnormz
  let f : ↥BU × ↥KU → ↥J := fun p =>
    ⟨(p.1 : ↥U) * (p.2 : ↥U), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf_inj : Function.Injective f := by
    intro p q hpq
    apply Subgroup.mul_injective_of_disjoint hdisj
    exact congrArg Subtype.val hpq
  have hf_surj : Function.Surjective f := by
    intro j
    have hj : (j : ↥U) ∈ (↑BU : Set (↥U)) * (↑KU : Set (↥U)) := by
      rw [← hcoe]
      exact j.2
    rcases hj with ⟨b, hb, k, hk, hbk⟩
    refine ⟨(⟨b, hb⟩, ⟨k, hk⟩), ?_⟩
    apply Subtype.ext
    exact hbk
  have hcardJ : Nat.card (↥J) = Nat.card (↥BU) * Nat.card (↥KU) := by
    calc
      Nat.card (↥J) = Nat.card (↥BU × ↥KU) :=
        (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm
      _ = Nat.card (↥BU) * Nat.card (↥KU) := Nat.card_prod _ _
  have hJdvd : Nat.card (↥J) ∣ Nat.card (↥U) := J.card_subgroup_dvd_card
  have hcardBU : Nat.card (↥BU) = Nat.card (↥B) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBU).toEquiv
  have hcardKU : Nat.card (↥KU) = Nat.card (↥K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN.1).toEquiv
  have hUcard : Nat.card (↥BU) * BU.index = Nat.card (↥U) :=
    Subgroup.card_mul_index BU
  rcases hJdvd with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  have hpos : 0 < Nat.card (↥BU) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    Nat.card (↥BU) * BU.index = Nat.card (↥U) := hUcard
    _ = Nat.card (↥J) * q := hq
    _ = (Nat.card (↥BU) * Nat.card (↥KU)) * q := by rw [hcardJ]
    _ = Nat.card (↥BU) * (Nat.card (↥K) * q) := by
      rw [hcardKU, Nat.mul_assoc]

omit [Finite G] in
private lemma inf_eq_bot_of_fixed_inverted_odd
    {t : G} {B K : Subgroup G}
    (hfix : ∀ x : G, x ∈ B → t * x * t⁻¹ = x)
    (hinv : ∀ x : G, x ∈ K → t * x * t⁻¹ = x⁻¹)
    (hodd : Nat.Coprime 2 (Nat.card (↥K))) : B ⊓ K = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hxB : x ∈ B := (Subgroup.mem_inf.mp hx).1
  have hxK : x ∈ K := (Subgroup.mem_inf.mp hx).2
  have hxeq : x = x⁻¹ := (hfix x hxB).symm.trans (hinv x hxK)
  have hx2 : x ^ 2 = 1 := by
    rw [pow_two]
    calc
      x * x = x * x⁻¹ := by nth_rw 2 [hxeq]
      _ = 1 := mul_inv_cancel x
  have hordK : orderOf x ∣ Nat.card (↥K) := Subgroup.orderOf_dvd_natCard K hxK
  have hcop : Nat.Coprime (orderOf x) 2 :=
    (hodd.coprime_dvd_right hordK).symm
  have hord2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hord2)

private lemma theoremC_B1_inf_K_eq_bot (c : Hyp11 G) [Hyp11KData c] : c.B1 ⊓ c.K = ⊥ :=
  inf_eq_bot_of_fixed_inverted_odd
    (fun _x hx => theoremC_fixed_by_t1_of_mem_B1 c hx)
    (fun x hx => c.K1_inverted x (Subgroup.mem_inf.mp hx).1)
    (theoremC_K_odd c)

private lemma theoremC_B2_inf_K_eq_bot (c : Hyp11 G) [Hyp11KData c] : c.B2 ⊓ c.K = ⊥ :=
  inf_eq_bot_of_fixed_inverted_odd
    (fun _x hx => theoremC_fixed_by_t2_of_mem_B2 c hx)
    (fun x hx => c.K2_inverted x (Subgroup.mem_inf.mp hx).2)
    (theoremC_K_odd c)

private lemma theoremC_two_mul_K_card_dvd_k
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (hm : 4 ≤ (c.U.subgroupOf c.H0).index) :
    2 * Nat.card (↥c.K) ∣ c.k := by
  have hB2U : c.B2 ≤ c.U := by
    intro x hx
    unfold Hyp11.B2 centralizerIn at hx
    exact (inf_le_left : c.U ⊓ Subgroup.centralizer ({c.t2} : Set G) ≤ c.U) hx
  have hKdvdI1 : Nat.card (↥c.K) ∣ (c.B1.subgroupOf c.U).index :=
    card_dvd_index_of_normal_disjoint (theoremC_K_normal_in_U c)
      (theoremC_B1_le_U c) (theoremC_B1_inf_K_eq_bot c)
  have hKdvdI2 : Nat.card (↥c.K) ∣ (c.B2.subgroupOf c.U).index :=
    card_dvd_index_of_normal_disjoint (theoremC_K_normal_in_U c)
      hB2U (theoremC_B2_inf_K_eq_bot c)
  have hKdvd2k1 : Nat.card (↥c.K) ∣ 2 * c.k1 := by
    rw [k1_eq c]
    exact dvd_mul_of_dvd_right hKdvdI1 (Nat.card (↥c.S0))
  have hKdvd2k2 : Nat.card (↥c.K) ∣ 2 * c.k2 := by
    rw [k2_eq c]
    exact dvd_mul_of_dvd_right hKdvdI2 (Nat.card (↥c.S0))
  have hcopK2 : Nat.Coprime (Nat.card (↥c.K)) 2 := (theoremC_K_odd c).symm
  have hKdvdK1 : Nat.card (↥c.K) ∣ c.k1 := hcopK2.dvd_of_dvd_mul_left hKdvd2k1
  have hKdvdK2 : Nat.card (↥c.K) ∣ c.k2 := hcopK2.dvd_of_dvd_mul_left hKdvd2k2
  have hKdvdK : Nat.card (↥c.K) ∣ c.k := by
    rw [Hyp11.k]
    exact Nat.dvd_add hKdvdK1 hKdvdK2
  have hindexpow : (c.U.subgroupOf c.H0).index = 2 ^ c.m := by
    rw [U_index_eq_S0_card c h12, S0_nat_card c]
  have hmne : c.m ≠ 0 := by
    intro hm0
    rw [hindexpow, hm0] at hm
    norm_num at hm
  have h2index : 2 ∣ (c.U.subgroupOf c.H0).index := by
    rw [hindexpow]
    exact dvd_pow_self 2 hmne
  have h2k : 2 ∣ c.k := h2index.trans (m_dvd_k c h12)
  exact (theoremC_K_odd c).mul_dvd_of_dvd_of_dvd h2k hKdvdK

private lemma theoremC_card_lt_kernel_of_frobenius
    {X K B : Subgroup G}
    (hFrob : IsFrobeniusGroupWithKernel X K)
    (hBX : B ≤ X) (hBK : B ⊓ K = ⊥) :
    Nat.card (↥B) < Nat.card (↥K) := by
  unfold IsFrobeniusGroupWithKernel at hFrob
  rcases hFrob with ⟨hKN, hfree, hK⟩
  let : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK
  rcases exists_ne (1 : K) with ⟨k0, hk0⟩
  have hk0G : (k0 : G) ≠ 1 := fun hk => hk0 (Subtype.ext hk)
  let f : B → K := fun b =>
    ⟨(b : G) * (k0 : G) * (b : G)⁻¹,
      hKN.2 (b : G) (hBX b.2) (k0 : G) k0.2⟩
  have hf_inj : Function.Injective f := by
    intro b1 b2 heq
    have heqG : (b1 : G) * (k0 : G) * (b1 : G)⁻¹ =
        (b2 : G) * (k0 : G) * (b2 : G)⁻¹ := congrArg Subtype.val heq
    let x : G := (b2 : G)⁻¹ * (b1 : G)
    have hxB : x ∈ B := B.mul_mem (B.inv_mem b2.2) b1.2
    have hxX : x ∈ X := hBX hxB
    have hxfix : x * (k0 : G) * x⁻¹ = (k0 : G) := by
      dsimp [x]
      calc
        (b2 : G)⁻¹ * (b1 : G) * (k0 : G) * ((b2 : G)⁻¹ * (b1 : G))⁻¹ =
            (b2 : G)⁻¹ * ((b1 : G) * (k0 : G) * (b1 : G)⁻¹) * (b2 : G) := by group
        _ = (b2 : G)⁻¹ * ((b2 : G) * (k0 : G) * (b2 : G)⁻¹) * (b2 : G) := by rw [heqG]
        _ = (k0 : G) := by group
    have hxK : x ∈ K := by
      by_contra hxnot
      exact hfree x hxX hxnot (k0 : G) k0.2
        hk0G hxfix
    have hxinf : x ∈ B ⊓ K := Subgroup.mem_inf.mpr ⟨hxB, hxK⟩
    have hx1 : x = 1 := by
      rw [hBK] at hxinf
      exact Subgroup.mem_bot.mp hxinf
    apply Subtype.ext
    dsimp [x] at hx1
    exact (inv_mul_eq_one.mp hx1).symm
  have hone_not : (1 : K) ∉ Set.range f := by
    rintro ⟨b, hb⟩
    have hbG : (b : G) * (k0 : G) * (b : G)⁻¹ = 1 := congrArg Subtype.val hb
    have hk01 : (k0 : G) = 1 := by
      calc
        (k0 : G) = (b : G)⁻¹ * ((b : G) * (k0 : G) * (b : G)⁻¹) * (b : G) := by group
        _ = 1 := by rw [hbG]; group
    exact hk0 (Subtype.ext hk01)
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_injective_of_notMem f hf_inj hone_not

private lemma theoremC_B_le_centralizer_S0 (c : Hyp11 G) [Hyp11KData c] :
    c.B ≤ Subgroup.centralizer ((c.S0 : Subgroup G) : Set G) := by
  rw [Subgroup.le_centralizer_iff, c.S0_eq_zpowers, Subgroup.zpowers_le]
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hb1 : b ∈ c.B1 :=
    (inf_le_left : c.B1 ⊓ c.B2 ≤ c.B1) hb
  have hb2 : b ∈ c.B2 :=
    (inf_le_right : c.B1 ⊓ c.B2 ≤ c.B2) hb
  unfold Hyp11.B1 centralizerIn at hb1
  unfold Hyp11.B2 centralizerIn at hb2
  have h1 : c.t1 * b = b * c.t1 :=
    (Subgroup.mem_centralizer_iff.mp hb1.2) c.t1 (by simp)
  have h2 : c.t2 * b = b * c.t2 :=
    (Subgroup.mem_centralizer_iff.mp hb2.2) c.t2 (by simp)
  calc
    b * (c.t1 * c.t2) = (b * c.t1) * c.t2 := by group
    _ = (c.t1 * b) * c.t2 := by rw [h1]
    _ = c.t1 * (b * c.t2) := by group
    _ = c.t1 * (c.t2 * b) := by rw [h2]
    _ = (c.t1 * c.t2) * b := by group

private lemma theoremC_U_le_centralizer_S0_of_eq_BK (c : Hyp11 G) [Hyp11KData c]
    (hKcent : c.K ≤ Subgroup.centralizer ((c.S0 : Subgroup G) : Set G))
    (hUBK : c.U = c.B ⊔ c.K) :
    c.U ≤ Subgroup.centralizer ((c.S0 : Subgroup G) : Set G) := by
  rw [hUBK]
  exact sup_le (theoremC_B_le_centralizer_S0 c) hKcent

private noncomputable def theoremC_H0_mulEquiv_prod_of_eq_BK
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (hKcent : c.K ≤ Subgroup.centralizer ((c.S0 : Subgroup G) : Set G))
    (hUBK : c.U = c.B ⊔ c.K) :
    ↥c.U × ↥(c.S0 : Subgroup G) ≃* ↥c.H0 := by
  classical
  have hUcent : c.U ≤ Subgroup.centralizer ((c.S0 : Subgroup G) : Set G) :=
    theoremC_U_le_centralizer_S0_of_eq_BK c hKcent hUBK
  let f : ↥c.U × ↥(c.S0 : Subgroup G) →* ↥c.H0 := {
    toFun := fun p => ⟨(p.1 : G) * (p.2 : G),
      c.H0.mul_mem (U_le_H0 c p.1.2) (S0_le_H0 c p.2.2)⟩
    map_one' := by
      apply Subtype.ext
      simp
    map_mul' := by
      intro p q
      apply Subtype.ext
      have hcomm : (p.2 : G) * (q.1 : G) = (q.1 : G) * (p.2 : G) := by
        exact (Subgroup.mem_centralizer_iff.mp (hUcent q.1.2)) (p.2 : G) p.2.2
      change ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) =
        ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
      calc
        ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) =
            (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by group
        _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by rw [← hcomm]
        _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by group }
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro p q hpq
    have hval : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) :=
      congrArg Subtype.val hpq
    have hcross : (q.1 : G)⁻¹ * (p.1 : G) = (q.2 : G) * (p.2 : G)⁻¹ := by
      calc
        (q.1 : G)⁻¹ * (p.1 : G) =
            (q.1 : G)⁻¹ * ((p.1 : G) * (p.2 : G)) * (p.2 : G)⁻¹ := by group
        _ = (q.1 : G)⁻¹ * ((q.1 : G) * (q.2 : G)) * (p.2 : G)⁻¹ := by rw [hval]
        _ = (q.2 : G) * (p.2 : G)⁻¹ := by group
    have hcrossU : (q.1 : G)⁻¹ * (p.1 : G) ∈ c.U :=
      c.U.mul_mem (c.U.inv_mem q.1.2) p.1.2
    have hcrossS0 : (q.1 : G)⁻¹ * (p.1 : G) ∈ (c.S0 : Subgroup G) := by
      rw [hcross]
      exact c.S0.mul_mem q.2.2 (c.S0.inv_mem p.2.2)
    have hcrossOne : (q.1 : G)⁻¹ * (p.1 : G) = 1 :=
      U_inter_S0_eq_bot c hcrossU hcrossS0
    have hu : p.1 = q.1 := by
      apply Subtype.ext
      calc
        (p.1 : G) = (q.1 : G) * ((q.1 : G)⁻¹ * (p.1 : G)) := by group
        _ = (q.1 : G) := by rw [hcrossOne]; simp
    have hr : p.2 = q.2 := by
      apply Subtype.ext
      calc
        (p.2 : G) = (p.1 : G)⁻¹ * ((p.1 : G) * (p.2 : G)) := by group
        _ = (p.1 : G)⁻¹ * ((q.1 : G) * (q.2 : G)) := by rw [hval]
        _ = (q.2 : G) := by rw [hu]; group
    exact Prod.ext hu hr
  · intro x
    rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u, r, hx⟩
    refine ⟨(u, r), ?_⟩
    apply Subtype.ext
    exact hx.symm

set_option backward.isDefEq.respectTransparency false in
private lemma theoremC_orbit_card_eq_index_of_eq_BK
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (hKcent : c.K ≤ Subgroup.centralizer ((c.S0 : Subgroup G) : Set G))
    (hUBK : c.U = c.B ⊔ c.K) (ν : Irr (↥c.H0)) :
    (orbit c.H0 c.U ν.1).card = (c.U.subgroupOf c.H0).index := by
  classical
  let e : ↥c.U × ↥(c.S0 : Subgroup G) ≃* ↥c.H0 :=
    theoremC_H0_mulEquiv_prod_of_eq_BK c h12 hKcent hUBK
  let φ : ClassFunction (↥c.U × ↥(c.S0 : Subgroup G)) := fun p => ν.1 (e p)
  have hφ : IsIrreducibleCharacter φ :=
    isIrreducibleCharacter_congr e ν.2
  rcases irreducibleCharacter_eq_prodChar φ hφ with ⟨α, ψ, hprod⟩
  let : IsCyclic ↥(c.S0 : Subgroup G) := c.S0_cyclic
  let : CommGroup ↥(c.S0 : Subgroup G) := IsCyclic.commGroup
  have hψlin : IsLinearCharacter ψ.1 :=
    isLinearCharacter_of_isIrreducible_of_isCyclic ψ.2
  have hstab_le :
      (Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
        LambdaChar l.1 * ν.1 = ν.1)) ≤ ({1} : Finset (LambdaHom c.H0 c.U)) := by
    intro l hl
    simp only [Finset.mem_singleton]
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u, r, hx⟩
    let uH0 : ↥c.H0 := ⟨(u : G), U_le_H0 c u.2⟩
    let rH0 : ↥c.H0 := ⟨(r : G), S0_le_H0 c r.2⟩
    have her : e (1, r) = rH0 := by
      apply Subtype.ext
      simp [e, theoremC_H0_mulEquiv_prod_of_eq_BK, rH0]
    have hνr : ν.1 rH0 = α.1 1 * ψ.1 r := by
      have h := congrFun hprod (1, r)
      change α.1 1 * ψ.1 r = ν.1 (e (1, r)) at h
      rw [her] at h
      exact h.symm
    have hνrne : ν.1 rH0 ≠ 0 := by
      rw [hνr]
      exact mul_ne_zero (irreducible_char_one_ne_zero α.2)
        (linearChar_ne_zero hψlin r)
    have hstab := (Finset.mem_filter.mp hl).2
    have hlrC : (l.1 rH0 : ℂ) = 1 := by
      have h := congrFun hstab rH0
      apply mul_right_cancel₀ hνrne
      simpa [LambdaChar] using h
    have hlr : l.1 rH0 = 1 := by
      apply Units.ext
      simpa using hlrC
    have hlu : l.1 uH0 = 1 := l.2 uH0 u.2
    have hxr : x = uH0 * rH0 := by
      apply Subtype.ext
      exact hx
    rw [hxr, map_mul, hlu, hlr]
    simp
  have hstab_ge : ({1} : Finset (LambdaHom c.H0 c.U)) ≤
      Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
        LambdaChar l.1 * ν.1 = ν.1) := by
    intro l hl
    rw [Finset.mem_singleton] at hl
    subst l
    exact one_mem_stab c.H0 c.U ν.1
  have hstab :
      Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
        LambdaChar l.1 * ν.1 = ν.1) = {1} :=
    Finset.Subset.antisymm hstab_le hstab_ge
  have hmul := orbit_card_mul_stab c.H0 c.U ν.1
  rw [hstab] at hmul
  simp only [Finset.card_singleton, mul_one] at hmul
  rw [← Nat.card_eq_fintype_card, lambda_card_eq_index c h12] at hmul
  exact hmul

private lemma theoremC_BOf_ne_singleton_imp_U_ne_BK
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {κ : Irr (↥c.H0)} {χ : ClassFunction G}
    (hκB : κ ∈ BOf c h12 χ)
    (horbit_ne : ∀ {ν : Irr (↥c.H0)}, ν ∈ BOf c h12 χ → ν ≠ κ →
      (orbit c.H0 c.U ν.1).card ≠ (c.U.subgroupOf c.H0).index)
    (hKcent : c.K ≤ Subgroup.centralizer ((c.S0 : Subgroup G) : Set G))
    (hBne : BOf c h12 χ ≠ {κ}) :
    c.U ≠ c.B ⊔ c.K := by
  intro hUBK
  apply hBne
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hκB, ?_⟩
  intro ν hνB
  by_contra hνκ
  exact horbit_ne hνB hνκ
    (theoremC_orbit_card_eq_index_of_eq_BK c h12 hKcent hUBK ν)

/-! ## Cardinality-three orbit and delta infrastructure -/

private lemma extract_two_of_card_three {α : Type*} [DecidableEq α]
    (s : Finset α) (κ : α) (hκ : κ ∈ s) (hcard : s.card = 3) :
    ∃ ν₁ ν₂, ν₁ ≠ κ ∧ ν₂ ≠ κ ∧ ν₁ ≠ ν₂ ∧ s = {κ, ν₁, ν₂} := by
  classical
  have herase : (s.erase κ).card = 2 := by
    rw [Finset.card_erase_of_mem hκ, hcard]
  rcases Finset.card_eq_two.mp herase with ⟨ν₁, ν₂, hne, heq⟩
  have hν₁ : ν₁ ≠ κ := by
    have : ν₁ ∈ s.erase κ := by simp [heq]
    exact Finset.ne_of_mem_erase this
  have hν₂ : ν₂ ≠ κ := by
    have : ν₂ ∈ s.erase κ := by simp [heq]
    exact Finset.ne_of_mem_erase this
  refine ⟨ν₁, ν₂, hν₁, hν₂, hne, ?_⟩
  rw [← Finset.insert_erase hκ, heq]

private lemma BOf_extract_two_of_card_three
    {G : Type*} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (χ : ClassFunction G)
    (κ : Irr (↥c.H0)) (hκ : κ ∈ BOf c h12 χ)
    (hcard : (BOf c h12 χ).card = 3) :
    ∃ ν₁ ν₂, ν₁ ≠ κ ∧ ν₂ ≠ κ ∧ ν₁ ≠ ν₂ ∧
      BOf c h12 χ = {κ, ν₁, ν₂} :=
  extract_two_of_card_three (BOf c h12 χ) κ hκ hcard

private lemma conjIrr_involutive_local {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (ν : Irr (↥c.H0)) :
    conjIrr c h12 (conjIrr c h12 ν) = ν := by
  apply Subtype.ext
  rw [conjIrr_coe, conjIrr_coe]
  exact conjChar_conjChar c h12 ν.1

private lemma BOf_card_three_classify {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (χ : ClassFunction G)
    (κ ν₁ ν₂ : Irr (↥c.H0))
    (hB : BOf c h12 χ = {κ, ν₁, ν₂})
    (hκfix : conjIrr c h12 κ = κ)
    (hν₁κ : ν₁ ≠ κ) (hν₂κ : ν₂ ≠ κ) (hν₁ν₂ : ν₁ ≠ ν₂) :
    (conjIrr c h12 ν₁ = ν₁ ∧ conjIrr c h12 ν₂ = ν₂) ∨
      (conjIrr c h12 ν₁ = ν₂ ∧ conjIrr c h12 ν₂ = ν₁) := by
  classical
  have hν₁B : ν₁ ∈ BOf c h12 χ := by rw [hB]; simp
  have hν₂B : ν₂ ∈ BOf c h12 χ := by rw [hB]; simp
  have hconj_mem (ν : Irr (↥c.H0)) (hν : ν ∈ BOf c h12 χ) :
      conjIrr c h12 ν ∈ BOf c h12 χ :=
    (BOf_conj_iff c h12 χ ν).2 hν
  by_cases hν₁fix : conjIrr c h12 ν₁ = ν₁
  · left
    refine ⟨hν₁fix, ?_⟩
    have hm := hconj_mem ν₂ hν₂B
    rw [hB] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm
    · exfalso
      apply hν₂κ
      calc
        ν₂ = conjIrr c h12 (conjIrr c h12 ν₂) :=
          (conjIrr_involutive_local c h12 ν₂).symm
        _ = conjIrr c h12 κ := congrArg (conjIrr c h12) hm
        _ = κ := hκfix
    · exfalso
      apply hν₁ν₂
      calc
        ν₁ = conjIrr c h12 ν₁ := hν₁fix.symm
        _ = conjIrr c h12 (conjIrr c h12 ν₂) :=
          (congrArg (conjIrr c h12) hm).symm
        _ = ν₂ := conjIrr_involutive_local c h12 ν₂
    · exact hm
  · right
    have hm := hconj_mem ν₁ hν₁B
    rw [hB] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    have hpair : conjIrr c h12 ν₁ = ν₂ := by
      rcases hm with hm | hm | hm
      · exfalso
        apply hν₁κ
        calc
          ν₁ = conjIrr c h12 (conjIrr c h12 ν₁) :=
            (conjIrr_involutive_local c h12 ν₁).symm
          _ = conjIrr c h12 κ := congrArg (conjIrr c h12) hm
          _ = κ := hκfix
      · exact False.elim (hν₁fix hm)
      · exact hm
    refine ⟨hpair, ?_⟩
    calc
      conjIrr c h12 ν₂ = conjIrr c h12 (conjIrr c h12 ν₁) :=
        congrArg (conjIrr c h12) hpair.symm
      _ = ν₁ := conjIrr_involutive_local c h12 ν₁

private lemma two_fixed_Irr_of_orbit_invariant {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (ν : Irr (↥c.H0))
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈
      orbit c.H0 c.U ν.1) :
    ∃ μ₁ μ₂ : Irr (↥c.H0),
      μ₁ ≠ μ₂ ∧
      μ₁.1 ∈ orbit c.H0 c.U ν.1 ∧
      μ₂.1 ∈ orbit c.H0 c.U ν.1 ∧
      conjChar c.H0 (s_normalizes_H0 c h12) μ₁.1 = μ₁.1 ∧
      conjChar c.H0 (s_normalizes_H0 c h12) μ₂.1 = μ₂.1 ∧
      (orbit c.H0 c.U ν.1).filter (fun μ =>
        conjChar c.H0 (s_normalizes_H0 c h12) μ = μ) = {μ₁.1, μ₂.1} := by
  classical
  let F : Finset (ClassFunction (↥c.H0)) :=
    (orbit c.H0 c.U ν.1).filter (fun μ =>
      conjChar c.H0 (s_normalizes_H0 c h12) μ = μ)
  have hFcard : F.card = 2 := by
    simpa [F] using lemma_2_1_b c h12 ν.2 hνs
  rcases Finset.card_eq_two.mp hFcard with ⟨a, b, hab, hF⟩
  have haF : a ∈ F := by rw [hF]; simp
  have hbF : b ∈ F := by rw [hF]; simp
  have ha := Finset.mem_filter.mp haF
  have hb := Finset.mem_filter.mp hbF
  let μ₁ : Irr (↥c.H0) :=
    ⟨a, orbit_mem_isIrreducible c.H0 c.U ν.2 ha.1⟩
  let μ₂ : Irr (↥c.H0) :=
    ⟨b, orbit_mem_isIrreducible c.H0 c.U ν.2 hb.1⟩
  have hμne : μ₁ ≠ μ₂ := by
    intro h
    exact hab (congrArg Subtype.val h)
  refine ⟨μ₁, μ₂, hμne, ha.1, hb.1, ?_, ?_, ?_⟩
  · simpa [μ₁] using ha.2
  · simpa [μ₂] using hb.2
  · simpa [F, μ₁, μ₂] using hF

private lemma exists_other_fixed_Irr
    {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (ν : Irr (↥c.H0))
    (hνfix : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1) :
    ∃ μ : Irr (↥c.H0), μ ≠ ν ∧ μ.1 ∈ orbit c.H0 c.U ν.1 ∧
      conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1 := by
  classical
  have hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈
      orbit c.H0 c.U ν.1 := by
    simpa [hνfix] using orbit_self_mem c.H0 c.U ν.1
  rcases two_fixed_Irr_of_orbit_invariant c h12 ν hνs with
    ⟨μ₁, μ₂, hμ₁μ₂, hμ₁L, hμ₂L, hμ₁fix, hμ₂fix, hF⟩
  have hνF : ν.1 ∈ (orbit c.H0 c.U ν.1).filter (fun μ =>
      conjChar c.H0 (s_normalizes_H0 c h12) μ = μ) :=
    Finset.mem_filter.mpr ⟨orbit_self_mem c.H0 c.U ν.1, hνfix⟩
  rw [hF] at hνF
  simp only [Finset.mem_insert, Finset.mem_singleton] at hνF
  rcases hνF with hνμ₁ | hνμ₂
  · have hEq : ν = μ₁ := Subtype.ext hνμ₁
    refine ⟨μ₂, ?_, hμ₂L, hμ₂fix⟩
    intro h
    exact hμ₁μ₂ (hEq.symm.trans h.symm)
  · have hEq : ν = μ₂ := Subtype.ext hνμ₂
    refine ⟨μ₁, ?_, hμ₁L, hμ₁fix⟩
    intro h
    exact hμ₁μ₂ (h.trans hEq)

/-- Pure character algebra: disjoint generalized characters have zero scalar product. -/
private lemma scalarProduct_irr_decomp_local
    {G : Type u} [Group G] [Finite G] {ι : Type u} [Fintype ι]
    {χs : ι → ClassFunction G} {ms : ι → ℤ}
    (hirr : ∀ i, IsIrreducibleCharacter (χs i))
    (hdist : ∀ i j, i ≠ j → χs i ≠ χs j) (i : ι) :
    scalarProduct G (χs i) (∑ j, (ms j : ℂ) • χs j) = (ms i : ℂ) := by
  classical
  rw [scalarProduct_sum_right]
  calc
    ∑ j, scalarProduct G (χs i) ((ms j : ℂ) • χs j) =
        ∑ j, scalarProduct G (χs i) (χs j) * star (ms j : ℂ) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      exact scalarProduct_smul_right (ms j : ℂ) (χs i) (χs j)
    _ = scalarProduct G (χs i) (χs i) * star (ms i : ℂ) := by
      refine Finset.sum_eq_single i ?_ ?_
      · intro j hj hji
        simp [irreducible_scalarProduct_of_ne (hirr i) (hirr j) (hdist i j hji.symm)]
      · intro hnot
        exact (hnot (Finset.mem_univ i)).elim
    _ = (ms i : ℂ) := by simp [irreducible_scalarProduct_self (hirr i)]

private lemma scalarProduct_eq_zero_of_disjoint_local
    {G : Type u} [Group G] [Finite G] {φ ψ : ClassFunction G}
    (hφ : IsGeneralizedCharacter φ) (hψ : IsGeneralizedCharacter ψ)
    (h : Theory.Character.Disjoint φ ψ) : scalarProduct G φ ψ = 0 := by
  classical
  rcases char_decomp_generalized hφ with ⟨ι₁, _, χs, ms, hirr, hdist, hφsum⟩
  rcases char_decomp_generalized hψ with ⟨ι₂, _, ηs, ns, hirr₂, hdist₂, hψsum⟩
  rw [hφsum, hψsum, scalarProduct_sum_left]
  refine Finset.sum_eq_zero ?_
  intro i hi
  rw [scalarProduct_smul_left]
  by_cases hmi : ms i = 0
  · simp [hmi]
  · have hφi : scalarProduct G (χs i) (∑ j, (ms j : ℂ) • χs j) = (ms i : ℂ) :=
      scalarProduct_irr_decomp_local hirr hdist i
    have hφi_ne : scalarProduct G (χs i) φ ≠ 0 := by
      rw [hφsum, hφi]
      exact_mod_cast hmi
    have hzero : scalarProduct G (χs i) ψ = 0 := h (χs i) (hirr i) hφi_ne
    rw [hψsum] at hzero
    simp [hzero]

private lemma tildeNu_sub_one_eq_zero_of_orbit
    {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) {ν μ : Irr (↥c.H0)}
    (hμL : μ.1 ∈ orbit c.H0 c.U ν.1) :
    (tildeNu c h12 ν - tildeNu c h12 μ) 1 = 0 := by
  have hdeg : μ.1 1 = ν.1 1 := orbit_mem_degree_eq c hμL
  have hzero : inducedClassFunction c.H0 (μ.1 - ν.1) 1 = 0 :=
    inducedFromSub_one_eq c h12 hdeg
  have hind := congrFun (tildeNu_ind c h12 hμL) (1 : G)
  rw [hzero] at hind
  change tildeNu c h12 ν 1 - tildeNu c h12 μ 1 = 0
  change 0 = tildeNu c h12 μ 1 - tildeNu c h12 ν 1 at hind
  exact sub_eq_zero.mpr (sub_eq_zero.mp hind.symm).symm

private lemma fixed_fixed_delta_facts
    {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) {ν μ : Irr (↥c.H0)}
    (hνfix : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hμfix : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμL : μ.1 ∈ orbit c.H0 c.U ν.1) (hνμ : ν ≠ μ) :
    normSq G (tildeNu c h12 ν - tildeNu c h12 μ) = 4 ∧
      (tildeNu c h12 ν - tildeNu c h12 μ) 1 = 0 := by
  classical
  have hνμv : ν.1 ≠ μ.1 := fun h => hνμ (Subtype.ext h)
  have hνsμ : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ μ.1 := by
    simpa [hνfix] using hνμv
  have hdis := tildeNu_disjoint c h12 (μ := μ) (ν := ν) hμL hνμv hνsμ
  have hμν0 : scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) = 0 :=
    scalarProduct_eq_zero_of_disjoint_local
      (tildeNu_isGeneralized c h12 μ) (tildeNu_isGeneralized c h12 ν) hdis
  have hνμ0 : scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) = 0 := by
    calc
      scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) =
          star (scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν)) :=
        (scalarProduct_conj _ _).symm
      _ = 0 := by rw [hμν0]; simp
  have hνnorm : normSq G (tildeNu c h12 ν) = 2 := by
    simpa [hνfix] using tildeNu_norm c h12 ν
  have hμnorm : normSq G (tildeNu c h12 μ) = 2 := by
    simpa [hμfix] using tildeNu_norm c h12 μ
  constructor
  · unfold normSq at hνnorm hμnorm ⊢
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right,
      hνnorm, hμnorm, hνμ0, hμν0]
    norm_num
  · exact tildeNu_sub_one_eq_zero_of_orbit c h12 hμL

private lemma nonfixed_fixed_delta_facts
    {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) {ν μ : Irr (↥c.H0)}
    (hνnonfix : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hμfix : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμL : μ.1 ∈ orbit c.H0 c.U ν.1) :
    normSq G (tildeNu c h12 ν - tildeNu c h12 μ) = 3 ∧
      (tildeNu c h12 ν - tildeNu c h12 μ) 1 = 0 := by
  classical
  have hνμ : ν ≠ μ := by
    intro h
    apply hνnonfix
    simpa [h] using hμfix
  have hνμv : ν.1 ≠ μ.1 := fun h => hνμ (Subtype.ext h)
  have hνsμ : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ μ.1 := by
    intro h
    apply hνμv
    calc
      ν.1 = conjChar c.H0 (s_normalizes_H0 c h12)
          (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) :=
        (conjChar_conjChar c h12 ν.1).symm
      _ = conjChar c.H0 (s_normalizes_H0 c h12) μ.1 :=
        congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) h
      _ = μ.1 := hμfix
  have hdis := tildeNu_disjoint c h12 (μ := μ) (ν := ν) hμL hνμv hνsμ
  have hμν0 : scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) = 0 :=
    scalarProduct_eq_zero_of_disjoint_local
      (tildeNu_isGeneralized c h12 μ) (tildeNu_isGeneralized c h12 ν) hdis
  have hνμ0 : scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) = 0 := by
    calc
      scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) =
          star (scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν)) :=
        (scalarProduct_conj _ _).symm
      _ = 0 := by rw [hμν0]; simp
  have hνnorm : normSq G (tildeNu c h12 ν) = 1 := by
    simpa [hνnonfix] using tildeNu_norm c h12 ν
  have hμnorm : normSq G (tildeNu c h12 μ) = 2 := by
    simpa [hμfix] using tildeNu_norm c h12 μ
  constructor
  · unfold normSq at hνnorm hμnorm ⊢
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right,
      hνnorm, hμnorm, hνμ0, hμν0]
    norm_num
  · exact tildeNu_sub_one_eq_zero_of_orbit c h12 hμL

private lemma orbit_delta_orthogonal
    {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {ν₁ ν₂ μ₁ μ₂ : Irr (↥c.H0)}
    (hμ₁L : μ₁.1 ∈ orbit c.H0 c.U ν₁.1)
    (hμ₂L : μ₂.1 ∈ orbit c.H0 c.U ν₂.1)
    (hν₁not : ν₁.1 ∉ orbit c.H0 c.U ν₂.1)
    (hν₁snot : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 ∉
      orbit c.H0 c.U ν₂.1) :
    scalarProduct G (tildeNu c h12 ν₁ - tildeNu c h12 μ₁)
      (tildeNu c h12 ν₂ - tildeNu c h12 μ₂) = 0 := by
  have horth := tildeNu_orthogonal c h12 hμ₁L hμ₂L hν₁not hν₁snot
  have hneg₁ : tildeNu c h12 ν₁ - tildeNu c h12 μ₁ =
      -(tildeNu c h12 μ₁ - tildeNu c h12 ν₁) := by abel
  have hneg₂ : tildeNu c h12 ν₂ - tildeNu c h12 μ₂ =
      -(tildeNu c h12 μ₂ - tildeNu c h12 ν₂) := by abel
  rw [hneg₁, hneg₂, scalarProduct_neg_left, scalarProduct_neg_right]
  simpa using horth

private lemma fixed_BOf_distinct_orbits
    {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    {ν₁ ν₂ : Irr (↥c.H0)}
    (hν₁B : ν₁ ∈ BOf c h12 χ) (hν₂B : ν₂ ∈ BOf c h12 χ)
    (hν₁fix : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 = ν₁.1)
    (hν₁ν₂ : ν₁ ≠ ν₂) :
    ν₁.1 ∉ orbit c.H0 c.U ν₂.1 ∧
      conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 ∉ orbit c.H0 c.U ν₂.1 := by
  have hnot : ν₁.1 ∉ orbit c.H0 c.U ν₂.1 := by
    intro hL
    have hpair := BOf_orbit_pair_conj c h12 hχ hν₁B hν₂B hL hν₁ν₂
    apply hν₁ν₂
    apply Subtype.ext
    exact hν₁fix.symm.trans hpair
  exact ⟨hnot, by simpa [hν₁fix] using hnot⟩

private lemma fixed_two_delta_facts_of_B
    {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    {ν₁ ν₂ μ₁ μ₂ : Irr (↥c.H0)}
    (hν₁B : ν₁ ∈ BOf c h12 χ) (hν₂B : ν₂ ∈ BOf c h12 χ)
    (hν₁fix : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 = ν₁.1)
    (hν₂fix : conjChar c.H0 (s_normalizes_H0 c h12) ν₂.1 = ν₂.1)
    (hμ₁fix : conjChar c.H0 (s_normalizes_H0 c h12) μ₁.1 = μ₁.1)
    (hμ₂fix : conjChar c.H0 (s_normalizes_H0 c h12) μ₂.1 = μ₂.1)
    (hμ₁L : μ₁.1 ∈ orbit c.H0 c.U ν₁.1)
    (hμ₂L : μ₂.1 ∈ orbit c.H0 c.U ν₂.1)
    (hν₁μ₁ : ν₁ ≠ μ₁) (hν₂μ₂ : ν₂ ≠ μ₂) (hν₁ν₂ : ν₁ ≠ ν₂) :
    normSq G (tildeNu c h12 ν₁ - tildeNu c h12 μ₁) = 4 ∧
      normSq G (tildeNu c h12 ν₂ - tildeNu c h12 μ₂) = 4 ∧
      scalarProduct G (tildeNu c h12 ν₁ - tildeNu c h12 μ₁)
        (tildeNu c h12 ν₂ - tildeNu c h12 μ₂) = 0 ∧
      (tildeNu c h12 ν₁ - tildeNu c h12 μ₁) 1 = 0 ∧
      (tildeNu c h12 ν₂ - tildeNu c h12 μ₂) 1 = 0 := by
  have hfacts₁ := fixed_fixed_delta_facts c h12 hν₁fix hμ₁fix hμ₁L hν₁μ₁
  have hfacts₂ := fixed_fixed_delta_facts c h12 hν₂fix hμ₂fix hμ₂L hν₂μ₂
  have hnot := fixed_BOf_distinct_orbits c h12 hχ hν₁B hν₂B hν₁fix hν₁ν₂
  exact ⟨hfacts₁.1, hfacts₂.1,
    orbit_delta_orthogonal c h12 hμ₁L hμ₂L hnot.1 hnot.2,
    hfacts₁.2, hfacts₂.2⟩

private lemma nonfixed_two_fixed_delta_facts
    {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) {ν μ₁ μ₂ : Irr (↥c.H0)}
    (hνnonfix : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hμ₁fix : conjChar c.H0 (s_normalizes_H0 c h12) μ₁.1 = μ₁.1)
    (hμ₂fix : conjChar c.H0 (s_normalizes_H0 c h12) μ₂.1 = μ₂.1)
    (hμ₁L : μ₁.1 ∈ orbit c.H0 c.U ν.1)
    (hμ₂L : μ₂.1 ∈ orbit c.H0 c.U ν.1)
    (hμ₁μ₂ : μ₁ ≠ μ₂) :
    tildeNu c h12 (conjIrr c h12 ν) - tildeNu c h12 μ₂ =
        tildeNu c h12 ν - tildeNu c h12 μ₂ ∧
      normSq G (tildeNu c h12 ν - tildeNu c h12 μ₁) = 3 ∧
      normSq G (tildeNu c h12 ν - tildeNu c h12 μ₂) = 3 ∧
      scalarProduct G (tildeNu c h12 ν - tildeNu c h12 μ₁)
        (tildeNu c h12 ν - tildeNu c h12 μ₂) = 1 ∧
      (tildeNu c h12 ν - tildeNu c h12 μ₁) 1 = 0 ∧
      (tildeNu c h12 ν - tildeNu c h12 μ₂) 1 = 0 := by
  classical
  have hfacts₁ := nonfixed_fixed_delta_facts c h12 hνnonfix hμ₁fix hμ₁L
  have hfacts₂ := nonfixed_fixed_delta_facts c h12 hνnonfix hμ₂fix hμ₂L
  have hνμ (μ : Irr (↥c.H0))
      (hμfix : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1) : ν ≠ μ := by
    intro h
    apply hνnonfix
    simpa [h] using hμfix
  have hνsμ (μ : Irr (↥c.H0))
      (hμfix : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1) :
      conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ μ.1 := by
    intro h
    have hνμv : ν.1 ≠ μ.1 := fun hv => hνμ μ hμfix (Subtype.ext hv)
    apply hνμv
    calc
      ν.1 = conjChar c.H0 (s_normalizes_H0 c h12)
          (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) :=
        (conjChar_conjChar c h12 ν.1).symm
      _ = conjChar c.H0 (s_normalizes_H0 c h12) μ.1 :=
        congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) h
      _ = μ.1 := hμfix
  have hzero_fixed (μ : Irr (↥c.H0))
      (hμfix : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
      (hμL : μ.1 ∈ orbit c.H0 c.U ν.1) :
      scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) = 0 ∧
        scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) = 0 := by
    have hdis := tildeNu_disjoint c h12 (μ := μ) (ν := ν) hμL
      (fun hv => hνμ μ hμfix (Subtype.ext hv)) (hνsμ μ hμfix)
    have hμν0 : scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) = 0 :=
      scalarProduct_eq_zero_of_disjoint_local
        (tildeNu_isGeneralized c h12 μ) (tildeNu_isGeneralized c h12 ν) hdis
    refine ⟨hμν0, ?_⟩
    calc
      scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) =
          star (scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν)) :=
        (scalarProduct_conj _ _).symm
      _ = 0 := by rw [hμν0]; simp
  have hzero₁ := hzero_fixed μ₁ hμ₁fix hμ₁L
  have hzero₂ := hzero_fixed μ₂ hμ₂fix hμ₂L
  have hμ₁L₂ : μ₁.1 ∈ orbit c.H0 c.U μ₂.1 := by
    rw [orbit_eq_of_mem c hμ₂L]
    exact hμ₁L
  have hμ₂μ₁v : μ₂.1 ≠ μ₁.1 := by
    intro h
    exact hμ₁μ₂ (Subtype.ext h.symm)
  have hdis₁₂ := tildeNu_disjoint c h12 (μ := μ₁) (ν := μ₂) hμ₁L₂
    hμ₂μ₁v (by simpa [hμ₂fix] using hμ₂μ₁v)
  have hμ₁μ₂0 : scalarProduct G (tildeNu c h12 μ₁) (tildeNu c h12 μ₂) = 0 :=
    scalarProduct_eq_zero_of_disjoint_local
      (tildeNu_isGeneralized c h12 μ₁) (tildeNu_isGeneralized c h12 μ₂) hdis₁₂
  have hνnorm : scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν) = 1 := by
    have h := tildeNu_norm c h12 ν
    simpa [normSq, hνnonfix] using h
  have hcross : scalarProduct G (tildeNu c h12 ν - tildeNu c h12 μ₁)
      (tildeNu c h12 ν - tildeNu c h12 μ₂) = 1 := by
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right,
      hνnorm, hzero₂.2, hzero₁.1, hμ₁μ₂0]
    norm_num
  refine ⟨?_, hfacts₁.1, hfacts₂.1, hcross, hfacts₁.2, hfacts₂.2⟩
  rw [tildeNu_invariance c h12 ν]

private lemma not_mem_BOf_pair
    {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) {χ : ClassFunction G}
    {κ ν : Irr (↥c.H0)}
    (hB : BOf c h12 χ = {κ, conjIrr c h12 κ})
    (hνκ : ν ≠ κ) (hνκs : ν ≠ conjIrr c h12 κ) :
    ν ∉ BOf c h12 χ := by
  rw [hB]
  simp [hνκ, hνκs]

private lemma orbit_conj_card_eq
    {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (ν : ClassFunction (↥c.H0)) :
    (orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν)).card =
      (orbit c.H0 c.U ν).card := by
  classical
  rw [orbit_conjChar_eq c h12]
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  have h := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hab
  simpa [conjChar_conjChar c h12] using h

private lemma full_orbit_pair_separated_from_nonfull
    {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) {κ ν : Irr (↥c.H0)}
    (hκfull : (orbit c.H0 c.U κ.1).card = (c.U.subgroupOf c.H0).index)
    (hνnonfull : (orbit c.H0 c.U ν.1).card ≠ (c.U.subgroupOf c.H0).index) :
    κ.1 ∉ orbit c.H0 c.U ν.1 ∧
      conjChar c.H0 (s_normalizes_H0 c h12) κ.1 ∉ orbit c.H0 c.U ν.1 := by
  have hκnot : κ.1 ∉ orbit c.H0 c.U ν.1 := by
    intro h
    apply hνnonfull
    rw [← hκfull]
    exact (congrArg Finset.card
      (orbit_eq_of_mem (ν := ν.1) (μ := κ.1) c h)).symm
  have hκsfull :
      (orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) κ.1)).card =
        (c.U.subgroupOf c.H0).index := by
    rw [orbit_conj_card_eq c h12 κ.1, hκfull]
  have hκsnot : conjChar c.H0 (s_normalizes_H0 c h12) κ.1 ∉
      orbit c.H0 c.U ν.1 := by
    intro h
    apply hνnonfull
    rw [← hκsfull]
    exact (congrArg Finset.card
      (orbit_eq_of_mem (ν := ν.1)
        (μ := conjChar c.H0 (s_normalizes_H0 c h12) κ.1) c h)).symm
  exact ⟨hκnot, hκsnot⟩

private lemma nonfull_orbit_members_not_mem_full_B_pair
    {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) {χ : ClassFunction G}
    {κ ν μ : Irr (↥c.H0)}
    (hB : BOf c h12 χ = {κ, conjIrr c h12 κ})
    (hκfull : (orbit c.H0 c.U κ.1).card = (c.U.subgroupOf c.H0).index)
    (hνnonfull : (orbit c.H0 c.U ν.1).card ≠ (c.U.subgroupOf c.H0).index)
    (hμL : μ.1 ∈ orbit c.H0 c.U ν.1) :
    ν ∉ BOf c h12 χ ∧ μ ∉ BOf c h12 χ := by
  have hsep := full_orbit_pair_separated_from_nonfull c h12 hκfull hνnonfull
  have hνκ : ν ≠ κ := by
    intro h
    exact hsep.1 (by simpa [h] using orbit_self_mem c.H0 c.U ν.1)
  have hνκs : ν ≠ conjIrr c h12 κ := by
    intro h
    apply hsep.2
    simpa [h, conjIrr_coe] using orbit_self_mem c.H0 c.U ν.1
  have hμnonfull : (orbit c.H0 c.U μ.1).card ≠
      (c.U.subgroupOf c.H0).index := by
    rw [orbit_eq_of_mem c hμL]
    exact hνnonfull
  have hsepμ := full_orbit_pair_separated_from_nonfull c h12 hκfull hμnonfull
  have hμκ : μ ≠ κ := by
    intro h
    exact hsepμ.1 (by simpa [h] using orbit_self_mem c.H0 c.U μ.1)
  have hμκs : μ ≠ conjIrr c h12 κ := by
    intro h
    apply hsepμ.2
    simpa [h, conjIrr_coe] using orbit_self_mem c.H0 c.U μ.1
  exact ⟨not_mem_BOf_pair c h12 hB hνκ hνκs,
    not_mem_BOf_pair c h12 hB hμκ hμκs⟩

private lemma kappa3_delta_orthogonal_of_not_mem_B
    {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {κ3 ν μ : Irr (↥c.H0)} {χ3 : ClassFunction G}
    (hκ3tilde : tildeNu c h12 κ3 = χ3)
    (hνnot : ν ∉ BOf c h12 χ3) (hμnot : μ ∉ BOf c h12 χ3) :
    scalarProduct G (tildeNu c h12 κ3)
      (tildeNu c h12 ν - tildeNu c h12 μ) = 0 := by
  have hν0 : scalarProduct G χ3 (tildeNu c h12 ν) = 0 := by
    by_contra hne
    exact hνnot ((BOf_mem_iff c h12 χ3 ν).2 hne)
  have hμ0 : scalarProduct G χ3 (tildeNu c h12 μ) = 0 := by
    by_contra hne
    exact hμnot ((BOf_mem_iff c h12 χ3 μ).2 hne)
  rw [hκ3tilde, scalarProduct_sub_right, hν0, hμ0]
  ring

private lemma kappa_difference_delta_orthogonal
    {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {κ1 κ3 ν μ : Irr (↥c.H0)}
    (hκ1L : κ1.1 ∈ orbit c.H0 c.U κ3.1)
    (hμL : μ.1 ∈ orbit c.H0 c.U ν.1)
    (hκ3not : κ3.1 ∉ orbit c.H0 c.U ν.1)
    (hκ3snot : conjChar c.H0 (s_normalizes_H0 c h12) κ3.1 ∉
      orbit c.H0 c.U ν.1) :
    scalarProduct G (tildeNu c h12 κ1 - tildeNu c h12 κ3)
      (tildeNu c h12 ν - tildeNu c h12 μ) = 0 := by
  have horth := tildeNu_orthogonal c h12 hκ1L hμL hκ3not hκ3snot
  have hneg : tildeNu c h12 μ - tildeNu c h12 ν =
      -(tildeNu c h12 ν - tildeNu c h12 μ) := by abel
  rw [hneg, scalarProduct_neg_right] at horth
  simpa using horth

private lemma chi2_delta_pair_eq_neg_chi1
    {G : Type u} [Group G] [Finite G]
    {κ1 κ3 χ1 χ2 δ : ClassFunction G}
    (hκ1tilde : κ1 = χ1 + χ2)
    (hdiff : scalarProduct G (κ1 - κ3) δ = 0)
    (hκ3 : scalarProduct G κ3 δ = 0) :
    scalarProduct G χ2 δ = -scalarProduct G χ1 δ := by
  have hκ1 : scalarProduct G κ1 δ = 0 := by
    rw [scalarProduct_sub_left, hκ3, sub_zero] at hdiff
    exact hdiff
  rw [hκ1tilde, scalarProduct_add_left] at hκ1
  linear_combination hκ1

private lemma chi2_delta_pair_eq_neg_chi1_via_kappa3
    {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {κ1 κ3 ν μ : Irr (↥c.H0)} {χ1 χ2 χ3 : ClassFunction G}
    (hκ1tilde : tildeNu c h12 κ1 = χ1 + χ2)
    (hκ3tilde : tildeNu c h12 κ3 = χ3)
    (hκ1L : κ1.1 ∈ orbit c.H0 c.U κ3.1)
    (hμL : μ.1 ∈ orbit c.H0 c.U ν.1)
    (hκ3not : κ3.1 ∉ orbit c.H0 c.U ν.1)
    (hκ3snot : conjChar c.H0 (s_normalizes_H0 c h12) κ3.1 ∉
      orbit c.H0 c.U ν.1)
    (hνnot : ν ∉ BOf c h12 χ3) (hμnot : μ ∉ BOf c h12 χ3) :
    scalarProduct G χ2 (tildeNu c h12 ν - tildeNu c h12 μ) =
      -scalarProduct G χ1 (tildeNu c h12 ν - tildeNu c h12 μ) := by
  apply chi2_delta_pair_eq_neg_chi1 hκ1tilde
  · exact kappa_difference_delta_orthogonal c h12 hκ1L hμL hκ3not hκ3snot
  · exact kappa3_delta_orthogonal_of_not_mem_B c h12 hκ3tilde hνnot hμnot

/-- A signed irreducible character has norm one. -/
private lemma theoremC_pmIrr_norm_one {chi : ClassFunction G} (hchi : IsPMIrr G chi) :
    normSq G chi = 1 := by
  rcases hchi with hchi | hchi
  · exact irreducible_scalarProduct_self hchi
  · simpa [normSq, scalarProduct_neg_left, scalarProduct_neg_right] using
      irreducible_scalarProduct_self hchi

/-- Residual-character endpoint for the fixed/fixed cardinality-three
configuration.  Removing the common signed `chi1 - chi2` constituent from
two orthogonal norm-four differences leaves two norm-two residuals at
equality in Cauchy--Schwarz, and evaluation at `1` equates the degrees. -/
private lemma theoremC_two_delta_degree_eq
    {chi1 chi2 d1 d2 : ClassFunction G} {a1 a2 : ℂ}
    (hchi1norm : normSq G chi1 = 1) (hchi2norm : normSq G chi2 = 1)
    (hchi12 : scalarProduct G chi1 chi2 = 0)
    (hchi21 : scalarProduct G chi2 chi1 = 0)
    (ha1 : a1 = 1 ∨ a1 = -1) (ha2 : a2 = 1 ∨ a2 = -1)
    (hchi1d1 : scalarProduct G chi1 d1 = a1)
    (hchi2d1 : scalarProduct G chi2 d1 = -a1)
    (hchi1d2 : scalarProduct G chi1 d2 = a2)
    (hchi2d2 : scalarProduct G chi2 d2 = -a2)
    (hd1norm : normSq G d1 = 4) (hd2norm : normSq G d2 = 4)
    (hd12 : scalarProduct G d1 d2 = 0)
    (hd21 : scalarProduct G d2 d1 = 0)
    (hd1one : d1 1 = 0) (hd2one : d2 1 = 0) :
    chi1 1 = chi2 1 := by
  rcases ha1 with ha1 | ha1 <;> rcases ha2 with ha2 | ha2
  all_goals
    subst a1
    subst a2
    have hd1chi1 : scalarProduct G d1 chi1 =
        star (scalarProduct G chi1 d1) := (scalarProduct_star_comm chi1 d1).symm
    have hd1chi2 : scalarProduct G d1 chi2 =
        star (scalarProduct G chi2 d1) := (scalarProduct_star_comm chi2 d1).symm
    have hd2chi1 : scalarProduct G d2 chi1 =
        star (scalarProduct G chi1 d2) := (scalarProduct_star_comm chi1 d2).symm
    have hd2chi2 : scalarProduct G d2 chi2 =
        star (scalarProduct G chi2 d2) := (scalarProduct_star_comm chi2 d2).symm
    have hchi1self : scalarProduct G chi1 chi1 = 1 := by
      simpa [normSq] using hchi1norm
    have hchi2self : scalarProduct G chi2 chi2 = 1 := by
      simpa [normSq] using hchi2norm
    have hd1self : scalarProduct G d1 d1 = 4 := by
      simpa [normSq] using hd1norm
    have hd2self : scalarProduct G d2 d2 = 4 := by
      simpa [normSq] using hd2norm
    let v : ClassFunction G := chi1 - chi2
    let r1 : ClassFunction G := d1 - ((scalarProduct G chi1 d1) • v)
    let r2 : ClassFunction G := d2 - ((scalarProduct G chi1 d2) • v)
    have hr1norm : normSq G r1 = 2 := by
      simp [r1, v, normSq, scalarProduct_sub_left, scalarProduct_sub_right,
        hchi1self, hchi2self, hchi12, hchi21, ha1, hchi2d1,
        hd1chi1, hd1chi2, hd1self]
      norm_num
    have hr2norm : normSq G r2 = 2 := by
      simp [r2, v, normSq, scalarProduct_sub_left, scalarProduct_sub_right,
        hchi1self, hchi2self, hchi12, hchi21, ha2, hchi2d2,
        hd2chi1, hd2chi2, hd2self]
      norm_num
    have hr12 : scalarProduct G r1 r2 =
        -2 * scalarProduct G chi1 d1 * scalarProduct G chi1 d2 := by
      simp [r1, r2, v, scalarProduct_sub_left, scalarProduct_sub_right,
        hchi1self, hchi2self, hchi12, hchi21, ha1, ha2,
        hchi2d1, hchi2d2, hd1chi1, hd1chi2, hd12]
      ring
    have hr21 : scalarProduct G r2 r1 =
        -2 * scalarProduct G chi1 d1 * scalarProduct G chi1 d2 := by
      simp [r1, r2, v, scalarProduct_sub_left, scalarProduct_sub_right,
        hchi1self, hchi2self, hchi12, hchi21, ha1, ha2,
        hchi2d1, hchi2d2, hd2chi1, hd2chi2, hd21]
      ring
    let q : ClassFunction G := r1 +
      ((scalarProduct G chi1 d1 * scalarProduct G chi1 d2) • r2)
    have hr1self : scalarProduct G r1 r1 = 2 := by
      simpa [normSq] using hr1norm
    have hr2self : scalarProduct G r2 r2 = 2 := by
      simpa [normSq] using hr2norm
    have hqnorm : normSq G q = 0 := by
      simp [q, normSq, scalarProduct_add_left, scalarProduct_add_right,
        scalarProduct_neg_left, scalarProduct_neg_right, hr1self, hr2self,
        hr12, hr21, ha1, ha2]
    have hqzero : q = 0 := (normSq_eq_zero_iff q).1 hqnorm
    have hqone := congrFun hqzero 1
    dsimp [q, r1, r2, v] at hqone
    simp [hd1one, hd2one, ha1, ha2] at hqone
    first
    | simpa only [sub_eq_zero] using hqone
    | symm
      simpa only [sub_eq_zero] using hqone

/-- Residual-character endpoint for the exceptional cardinality-three
configuration.  The two norm-three differences have pairing one; after
removing their common signed constituent the residuals are opposite
norm-one generalized characters, but their value at `1` vanishes. -/
private lemma theoremC_exceptional_two_delta_false
    {chi1 chi2 d1 d2 : ClassFunction G} {a : ℂ}
    (hchi1norm : normSq G chi1 = 1) (hchi2norm : normSq G chi2 = 1)
    (hchi12 : scalarProduct G chi1 chi2 = 0)
    (hchi21 : scalarProduct G chi2 chi1 = 0)
    (ha : a = 1 ∨ a = -1)
    (hchi1d1 : scalarProduct G chi1 d1 = a)
    (hchi2d1 : scalarProduct G chi2 d1 = -a)
    (hchi1d2 : scalarProduct G chi1 d2 = a)
    (hchi2d2 : scalarProduct G chi2 d2 = -a)
    (hd1norm : normSq G d1 = 3) (hd2norm : normSq G d2 = 3)
    (hd12 : scalarProduct G d1 d2 = 1)
    (hd21 : scalarProduct G d2 d1 = 1)
    (hd1one : d1 1 = 0) (hd2one : d2 1 = 0)
    (hgenr1 : IsGeneralizedCharacter (d1 - a • (chi1 - chi2))) :
    False := by
  rcases ha with ha | ha
  all_goals
    subst a
    have hd1chi1 : scalarProduct G d1 chi1 =
        star (scalarProduct G chi1 d1) := (scalarProduct_star_comm chi1 d1).symm
    have hd1chi2 : scalarProduct G d1 chi2 =
        star (scalarProduct G chi2 d1) := (scalarProduct_star_comm chi2 d1).symm
    have hd2chi1 : scalarProduct G d2 chi1 =
        star (scalarProduct G chi1 d2) := (scalarProduct_star_comm chi1 d2).symm
    have hd2chi2 : scalarProduct G d2 chi2 =
        star (scalarProduct G chi2 d2) := (scalarProduct_star_comm chi2 d2).symm
    have hchi1self : scalarProduct G chi1 chi1 = 1 := by
      simpa [normSq] using hchi1norm
    have hchi2self : scalarProduct G chi2 chi2 = 1 := by
      simpa [normSq] using hchi2norm
    have hd1self : scalarProduct G d1 d1 = 3 := by
      simpa [normSq] using hd1norm
    have hd2self : scalarProduct G d2 d2 = 3 := by
      simpa [normSq] using hd2norm
    let v : ClassFunction G := chi1 - chi2
    let r1 : ClassFunction G := d1 - ((scalarProduct G chi1 d1) • v)
    let r2 : ClassFunction G := d2 - ((scalarProduct G chi1 d2) • v)
    have hr1norm : normSq G r1 = 1 := by
      simp [r1, v, normSq, scalarProduct_sub_left, scalarProduct_sub_right,
        hchi1self, hchi2self, hchi12, hchi21, ha, hchi2d1,
        hd1chi1, hd1chi2, hd1self]
      norm_num
    have hr2norm : normSq G r2 = 1 := by
      simp [r2, v, normSq, scalarProduct_sub_left, scalarProduct_sub_right,
        hchi1self, hchi2self, hchi12, hchi21, ha, hchi1d2,
        hchi2d2, hd2chi1, hd2chi2, hd2self]
      norm_num
    have hr12 : scalarProduct G r1 r2 = -1 := by
      simp [r1, r2, v, scalarProduct_sub_left, scalarProduct_sub_right,
        hchi1self, hchi2self, hchi12, hchi21, ha, hchi2d1,
        hchi1d2, hchi2d2, hd1chi1, hd1chi2, hd12]
    have hr21 : scalarProduct G r2 r1 = -1 := by
      simp [r1, r2, v, scalarProduct_sub_left, scalarProduct_sub_right,
        hchi1self, hchi2self, hchi12, hchi21, ha, hchi2d1,
        hchi1d2, hchi2d2, hd2chi1, hd2chi2, hd21]
    let q : ClassFunction G := r1 + r2
    have hr1self : scalarProduct G r1 r1 = 1 := by
      simpa [normSq] using hr1norm
    have hr2self : scalarProduct G r2 r2 = 1 := by
      simpa [normSq] using hr2norm
    have hqnorm : normSq G q = 0 := by
      simp [q, normSq, scalarProduct_add_left, scalarProduct_add_right,
        hr1self, hr2self, hr12, hr21]
    have hqzero : q = 0 := (normSq_eq_zero_iff q).1 hqnorm
    have hqone := congrFun hqzero 1
    dsimp [q, r1, r2, v] at hqone
    simp [hd1one, hd2one, ha, hchi1d2] at hqone
    have hdegree : chi1 1 = chi2 1 := by
      first
      | simpa only [sub_eq_zero] using hqone
      | symm
        simpa only [sub_eq_zero] using hqone
    have hr1one : r1 1 = 0 := by
      dsimp [r1, v]
      simp [hd1one, ha, hdegree]
    have hr1gen : IsGeneralizedCharacter r1 := by
      simpa [r1, v, ha] using hgenr1
    have hr1self' : scalarProduct G r1 r1 = 1 := by
      simpa [normSq] using hr1norm
    rcases norm_one_signed_irreducible hr1gen hr1self' with
      ⟨psi, hpsi, hcase⟩
    rcases hcase with hcase | hcase
    · rw [hcase] at hr1one
      exact (irreducible_char_one_ne_zero hpsi) hr1one
    · rw [hcase] at hr1one
      exact (irreducible_char_one_ne_zero hpsi) (by
        simpa using neg_eq_zero.mp hr1one)

private lemma theoremC_BOf_card_three_degree_eq
    {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (hSC : Section3Hyp c)
    {kappa1 : ClassFunction (↥c.H0)} (hkappa1lin : IsLinearCharacter kappa1)
    {kappa3 : Irr (↥c.H0)} {chi1 chi2 chi3 : ClassFunction G}
    (hchi1 : IsPMIrr G chi1) (hchi2 : IsPMIrr G chi2)
    (hkappa1tilde : tildeNu c h12 ⟨kappa1, hkappa1lin.1⟩ = chi1 + chi2)
    (hkappa3tilde : tildeNu c h12 kappa3 = chi3)
    (hpair1 : scalarProduct G chi1 (tildeNu c h12 ⟨kappa1, hkappa1lin.1⟩) = 1)
    (hpair2 : scalarProduct G chi2 (tildeNu c h12 ⟨kappa1, hkappa1lin.1⟩) = 1)
    (hkappa1fix : conjChar c.H0 (s_normalizes_H0 c h12) kappa1 = kappa1)
    (hkappa1full : (orbit c.H0 c.U kappa1).card = (c.U.subgroupOf c.H0).index)
    (hkappa1L : kappa1 ∈ orbit c.H0 c.U kappa3.1)
    (hkappa3full : (orbit c.H0 c.U kappa3.1).card = (c.U.subgroupOf c.H0).index)
    (hB3 : BOf c h12 chi3 = {kappa3, conjIrr c h12 kappa3})
    (hS8 : Nat.card (↥(c.S : Subgroup G)) ≠ 4)
    (hcard : (BOf c h12 chi1).card = 3) :
    chi1 1 = chi2 1 := by
  classical
  let kappa1Irr : Irr (↥c.H0) := ⟨kappa1, hkappa1lin.1⟩
  have hkappa1B : kappa1Irr ∈ BOf c h12 chi1 := by
    rw [BOf_mem_iff]
    rw [show tildeNu c h12 kappa1Irr = tildeNu c h12 ⟨kappa1, hkappa1lin.1⟩ by rfl,
      hpair1]
    norm_num
  have hkappa1fixIrr : conjIrr c h12 kappa1Irr = kappa1Irr := by
    apply Subtype.ext
    simpa [kappa1Irr, conjIrr_coe] using hkappa1fix
  have hchi1norm : normSq G chi1 = 1 := theoremC_pmIrr_norm_one hchi1
  have hchi2norm : normSq G chi2 = 1 := theoremC_pmIrr_norm_one hchi2
  have hchi1self : scalarProduct G chi1 chi1 = 1 := by
    simpa [normSq] using hchi1norm
  have hchi2self : scalarProduct G chi2 chi2 = 1 := by
    simpa [normSq] using hchi2norm
  have hchi12 : scalarProduct G chi1 chi2 = 0 := by
    have h := hpair1
    rw [hkappa1tilde, scalarProduct_add_right, hchi1self] at h
    linear_combination h
  have hchi21 : scalarProduct G chi2 chi1 = 0 := by
    have h := hpair2
    rw [hkappa1tilde, scalarProduct_add_right, hchi2self] at h
    linear_combination h
  have hnot_BOf_chi1_of_fixed_orbit
      {nu mu : Irr (↥c.H0)}
      (hnuB : nu ∈ BOf c h12 chi1)
      (hmuL : mu.1 ∈ orbit c.H0 c.U nu.1)
      (hmufix : conjChar c.H0 (s_normalizes_H0 c h12) mu.1 = mu.1)
      (hmunu : mu ≠ nu) :
      mu ∉ BOf c h12 chi1 := by
    intro hmuB
    have hpair := BOf_orbit_pair_conj c h12 hchi1 hmuB hnuB hmuL hmunu
    apply hmunu
    apply Subtype.ext
    exact hmufix.symm.trans hpair
  have hchi2_delta
      {nu mu : Irr (↥c.H0)}
      (hnuB : nu ∈ BOf c h12 chi1) (hnukappa1 : nu ≠ kappa1Irr)
      (hmuL : mu.1 ∈ orbit c.H0 c.U nu.1) :
      scalarProduct G chi2 (tildeNu c h12 nu - tildeNu c h12 mu) =
        -scalarProduct G chi1 (tildeNu c h12 nu - tildeNu c h12 mu) := by
    have hnunonfull : (orbit c.H0 c.U nu.1).card ≠
        (c.U.subgroupOf c.H0).index :=
      theoremC_chi1_BOf_orbit_ne_m c h12 hSC hkappa1lin hchi1 hkappa1tilde
        hpair1 hkappa1fix hkappa1full hS8 hnuB (by simpa [kappa1Irr] using hnukappa1)
    have hsep := full_orbit_pair_separated_from_nonfull c h12 hkappa3full hnunonfull
    have hnotB3 := nonfull_orbit_members_not_mem_full_B_pair
      c h12 hB3 hkappa3full hnunonfull hmuL
    exact chi2_delta_pair_eq_neg_chi1_via_kappa3 c h12 hkappa1tilde hkappa3tilde
      (by simpa [kappa1Irr] using hkappa1L) hmuL hsep.1 hsep.2 hnotB3.1 hnotB3.2
  rcases BOf_extract_two_of_card_three c h12 chi1 kappa1Irr hkappa1B hcard with
    ⟨nu1, nu2, hnu1kappa1, hnu2kappa1, hnu1nu2, hB⟩
  have hnu1B : nu1 ∈ BOf c h12 chi1 := by rw [hB]; simp
  have hnu2B : nu2 ∈ BOf c h12 chi1 := by rw [hB]; simp
  rcases BOf_card_three_classify c h12 chi1 kappa1Irr nu1 nu2 hB hkappa1fixIrr
      hnu1kappa1 hnu2kappa1 hnu1nu2 with hfixed | hconj
  · have hnu1fix : conjChar c.H0 (s_normalizes_H0 c h12) nu1.1 = nu1.1 := by
      simpa [conjIrr_coe] using congrArg Subtype.val hfixed.1
    have hnu2fix : conjChar c.H0 (s_normalizes_H0 c h12) nu2.1 = nu2.1 := by
      simpa [conjIrr_coe] using congrArg Subtype.val hfixed.2
    rcases exists_other_fixed_Irr c h12 nu1 hnu1fix with
      ⟨mu1, hmu1nu1, hmu1L, hmu1fix⟩
    rcases exists_other_fixed_Irr c h12 nu2 hnu2fix with
      ⟨mu2, hmu2nu2, hmu2L, hmu2fix⟩
    have hmu1not := hnot_BOf_chi1_of_fixed_orbit hnu1B hmu1L hmu1fix hmu1nu1
    have hmu2not := hnot_BOf_chi1_of_fixed_orbit hnu2B hmu2L hmu2fix hmu2nu2
    let d1 : ClassFunction G := tildeNu c h12 nu1 - tildeNu c h12 mu1
    let d2 : ClassFunction G := tildeNu c h12 nu2 - tildeNu c h12 mu2
    rcases fixed_two_delta_facts_of_B c h12 hchi1 hnu1B hnu2B hnu1fix hnu2fix
        hmu1fix hmu2fix hmu1L hmu2L hmu1nu1.symm hmu2nu2.symm hnu1nu2 with
      ⟨hd1norm, hd2norm, hd12, hd1one, hd2one⟩
    let a1 : ℂ := scalarProduct G chi1 (tildeNu c h12 nu1)
    let a2 : ℂ := scalarProduct G chi1 (tildeNu c h12 nu2)
    have ha1 : a1 = 1 ∨ a1 = -1 := by
      simpa [a1] using BOf_scalar_eq_pm_one c h12 hchi1 hnu1B
    have ha2 : a2 = 1 ∨ a2 = -1 := by
      simpa [a2] using BOf_scalar_eq_pm_one c h12 hchi1 hnu2B
    have hmu1zero : scalarProduct G chi1 (tildeNu c h12 mu1) = 0 := by
      by_contra hne
      exact hmu1not ((BOf_mem_iff c h12 chi1 mu1).2 hne)
    have hmu2zero : scalarProduct G chi1 (tildeNu c h12 mu2) = 0 := by
      by_contra hne
      exact hmu2not ((BOf_mem_iff c h12 chi1 mu2).2 hne)
    have hchi1d1 : scalarProduct G chi1 d1 = a1 := by
      simp [d1, a1, scalarProduct_sub_right, hmu1zero]
    have hchi1d2 : scalarProduct G chi1 d2 = a2 := by
      simp [d2, a2, scalarProduct_sub_right, hmu2zero]
    have hchi2d1 : scalarProduct G chi2 d1 = -a1 := by
      calc
        scalarProduct G chi2 d1 =
            -scalarProduct G chi1 (tildeNu c h12 nu1 - tildeNu c h12 mu1) := by
              simpa [d1] using hchi2_delta hnu1B hnu1kappa1 hmu1L
        _ = -a1 := by rw [hchi1d1]
    have hchi2d2 : scalarProduct G chi2 d2 = -a2 := by
      calc
        scalarProduct G chi2 d2 =
            -scalarProduct G chi1 (tildeNu c h12 nu2 - tildeNu c h12 mu2) := by
              simpa [d2] using hchi2_delta hnu2B hnu2kappa1 hmu2L
        _ = -a2 := by rw [hchi1d2]
    have hd21 : scalarProduct G d2 d1 = 0 := by
      calc
        scalarProduct G d2 d1 = star (scalarProduct G d1 d2) :=
          (scalarProduct_conj d1 d2).symm
        _ = 0 := by simpa [d1, d2] using congrArg star hd12
    exact theoremC_two_delta_degree_eq hchi1norm hchi2norm hchi12 hchi21
      ha1 ha2 hchi1d1 hchi2d1 hchi1d2 hchi2d2
      (by simpa [d1] using hd1norm) (by simpa [d2] using hd2norm)
      (by simpa [d1, d2] using hd12) hd21
      (by simpa [d1] using hd1one) (by simpa [d2] using hd2one)
  · have hnu1nonfixIrr : conjIrr c h12 nu1 ≠ nu1 := by
      intro hfix
      exact hnu1nu2 (hfix.symm.trans hconj.1)
    have hnu1nonfix : conjChar c.H0 (s_normalizes_H0 c h12) nu1.1 ≠ nu1.1 := by
      intro hfix
      apply hnu1nonfixIrr
      apply Subtype.ext
      simpa [conjIrr_coe] using hfix
    have hnu1conjL : conjChar c.H0 (s_normalizes_H0 c h12) nu1.1 ∈
        orbit c.H0 c.U nu1.1 :=
      theoremC_chi1_BOf_conj_mem_orbit c h12 hSC hkappa1lin hchi1 hkappa1tilde
        hpair1 hkappa1fix hnu1B (by simpa [kappa1Irr] using hnu1kappa1) hnu1nonfix
    rcases two_fixed_Irr_of_orbit_invariant c h12 nu1 hnu1conjL with
      ⟨mu1, mu2, hmu1mu2, hmu1L, hmu2L, hmu1fix, hmu2fix, _hfixedset⟩
    have hmu1nu1 : mu1 ≠ nu1 := by
      intro h
      apply hnu1nonfix
      simpa [h] using hmu1fix
    have hmu2nu1 : mu2 ≠ nu1 := by
      intro h
      apply hnu1nonfix
      simpa [h] using hmu2fix
    have hmu1not := hnot_BOf_chi1_of_fixed_orbit hnu1B hmu1L hmu1fix hmu1nu1
    have hmu2not := hnot_BOf_chi1_of_fixed_orbit hnu1B hmu2L hmu2fix hmu2nu1
    let d1 : ClassFunction G := tildeNu c h12 nu1 - tildeNu c h12 mu1
    let d2 : ClassFunction G := tildeNu c h12 nu1 - tildeNu c h12 mu2
    rcases nonfixed_two_fixed_delta_facts c h12 hnu1nonfix hmu1fix hmu2fix
        hmu1L hmu2L hmu1mu2 with
      ⟨_hconjdelta, hd1norm, hd2norm, hd12, hd1one, hd2one⟩
    let a : ℂ := scalarProduct G chi1 (tildeNu c h12 nu1)
    have ha : a = 1 ∨ a = -1 := by
      simpa [a] using BOf_scalar_eq_pm_one c h12 hchi1 hnu1B
    have hmu1zero : scalarProduct G chi1 (tildeNu c h12 mu1) = 0 := by
      by_contra hne
      exact hmu1not ((BOf_mem_iff c h12 chi1 mu1).2 hne)
    have hmu2zero : scalarProduct G chi1 (tildeNu c h12 mu2) = 0 := by
      by_contra hne
      exact hmu2not ((BOf_mem_iff c h12 chi1 mu2).2 hne)
    have hchi1d1 : scalarProduct G chi1 d1 = a := by
      simp [d1, a, scalarProduct_sub_right, hmu1zero]
    have hchi1d2 : scalarProduct G chi1 d2 = a := by
      simp [d2, a, scalarProduct_sub_right, hmu2zero]
    have hchi2d1 : scalarProduct G chi2 d1 = -a := by
      calc
        scalarProduct G chi2 d1 =
            -scalarProduct G chi1 (tildeNu c h12 nu1 - tildeNu c h12 mu1) := by
              simpa [d1] using hchi2_delta hnu1B hnu1kappa1 hmu1L
        _ = -a := by rw [hchi1d1]
    have hchi2d2 : scalarProduct G chi2 d2 = -a := by
      calc
        scalarProduct G chi2 d2 =
            -scalarProduct G chi1 (tildeNu c h12 nu1 - tildeNu c h12 mu2) := by
              simpa [d2] using hchi2_delta hnu1B hnu1kappa1 hmu2L
        _ = -a := by rw [hchi1d2]
    have hd21 : scalarProduct G d2 d1 = 1 := by
      calc
        scalarProduct G d2 d1 = star (scalarProduct G d1 d2) :=
          (scalarProduct_conj d1 d2).symm
        _ = 1 := by simpa [d1, d2] using congrArg star hd12
    have hpmgen : ∀ {chi : ClassFunction G}, IsPMIrr G chi →
        IsGeneralizedCharacter chi := by
      intro chi hchi
      rcases hchi with hchi | hchi
      · exact ⟨chi, 0, isCharacter_of_isIrreducibleCharacter hchi,
          isCharacter_zero, by simp⟩
      · exact ⟨0, -chi, isCharacter_zero,
          isCharacter_of_isIrreducibleCharacter hchi, by simp⟩
    have hgenneg : ∀ {phi : ClassFunction G}, IsGeneralizedCharacter phi →
        IsGeneralizedCharacter (-phi) := by
      intro phi hphi
      rcases hphi with ⟨alpha, beta, halpha, hbeta, hphi⟩
      exact ⟨beta, alpha, hbeta, halpha, by rw [hphi]; abel⟩
    have hgensub : ∀ {phi psi : ClassFunction G}, IsGeneralizedCharacter phi →
        IsGeneralizedCharacter psi → IsGeneralizedCharacter (phi - psi) := by
      intro phi psi hphi hpsi
      rcases hphi with ⟨alpha, beta, halpha, hbeta, hphi⟩
      rcases hpsi with ⟨gamma, delta, hgamma, hdelta, hpsi⟩
      exact ⟨alpha + delta, beta + gamma, isCharacter_add halpha hdelta,
        isCharacter_add hbeta hgamma, by rw [hphi, hpsi]; abel⟩
    have hd1gen : IsGeneralizedCharacter d1 := by
      exact hgensub (tildeNu_isGeneralized c h12 nu1) (tildeNu_isGeneralized c h12 mu1)
    have hvgen : IsGeneralizedCharacter (chi1 - chi2) := by
      exact hgensub (hpmgen hchi1) (hpmgen hchi2)
    have hasmulgen : IsGeneralizedCharacter (a • (chi1 - chi2)) := by
      rcases ha with ha | ha
      · simpa [ha] using hvgen
      · simpa [ha] using hgenneg hvgen
    have hgenr1 : IsGeneralizedCharacter (d1 - a • (chi1 - chi2)) :=
      hgensub hd1gen hasmulgen
    exact False.elim (theoremC_exceptional_two_delta_false
      hchi1norm hchi2norm hchi12 hchi21 ha
      hchi1d1 hchi2d1 hchi1d2 hchi2d2
      (by simpa [d1] using hd1norm) (by simpa [d2] using hd2norm)
      (by simpa [d1, d2] using hd12) hd21
      (by simpa [d1] using hd1one) (by simpa [d2] using hd2one) hgenr1)

private lemma theoremC_kappa_one_mem_kappa_orbit
    {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (kappa1 : ClassFunction (↥c.H0))
    (l : LambdaHom c.H0 c.U) :
    kappa1 ∈ orbit c.H0 c.U (kappa c kappa1 l) := by
  classical
  refine Finset.mem_image.mpr ⟨l⁻¹, Finset.mem_univ _, ?_⟩
  ext x
  simp [kappa, LambdaChar]

/-- `B' ≠ B` forces `2 ≤ |B|` (`B` is a nontrivial subgroup). -/
private lemma theoremC_B_card_ge_two (c : Hyp11 G) [Hyp11KData c] (hB' : ⁅c.B, c.B⁆ ≠ c.B) :
    2 ≤ Nat.card c.B := by
  have hBne : c.B ≠ ⊥ := theoremC_B_ne_bot c hB'
  by_contra hle
  have hpos : 0 < Nat.card c.B := Nat.card_pos
  have hle1 : Nat.card c.B ≤ 1 := by omega
  exact hBne (Subgroup.card_eq_one.mp (by omega))

/-- Inequality (7) forces `x ≠ 0` (the numerator is `9` at `x = 0`, and
`8α(1)+1 ≥ 9`). -/
private lemma theoremC_x_ne_zero_of_seven {x : ℝ} {a : ℕ} (ha : 1 ≤ a)
    (hineq : 1 < (3 + (1 + x) ^ 2 + (1 - x) ^ 2 + 4) / (8 * (a : ℝ) + 1)) :
    x ≠ 0 := by
  intro hx0
  have hnum : 3 + (1 + x) ^ 2 + (1 - x) ^ 2 + 4 = 9 := by
    rw [hx0]
    norm_num
  have hdenpos : 0 < 8 * (a : ℝ) + 1 := by nlinarith
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hfrac : (3 + (1 + x) ^ 2 + (1 - x) ^ 2 + 4) / (8 * (a : ℝ) + 1) ≤ 1 := by
    rw [hnum]
    rw [div_le_iff₀ hdenpos]
    nlinarith [haR]
  nlinarith [hfrac, hineq]

/-- Final Frobenius contradiction: inequality (7), `x² ≤ 2|B|` (5),
`α(1) ≥ |B|`, and `|B| ≥ 2` are incompatible. -/
private lemma theoremC_final_contradiction {Bcard : ℕ} {x : ℝ} {a : ℕ}
    (hB2 : 2 ≤ Bcard) (haB : (Bcard : ℝ) ≤ (a : ℝ)) (hx2 : x ^ 2 ≤ 2 * (Bcard : ℝ))
    (hineq : 1 < (3 + (1 + x) ^ 2 + (1 - x) ^ 2 + 4) / (8 * (a : ℝ) + 1)) :
    False := by
  have hdenpos : 0 < 8 * (a : ℝ) + 1 := by nlinarith
  have hlt : 8 * (a : ℝ) + 1 < 3 + (1 + x) ^ 2 + (1 - x) ^ 2 + 4 := by
    have h := (lt_div_iff₀ hdenpos).mp hineq
    simpa using h
  have hnum : 3 + (1 + x) ^ 2 + (1 - x) ^ 2 + 4 = 9 + 2 * x ^ 2 := by
    ring
  have hB2R : (2 : ℝ) ≤ (Bcard : ℝ) := by exact_mod_cast hB2
  nlinarith [hlt, hnum, hx2, haB, hB2R]

/-- Contrapositive of (4): if `|B(χ₁)| = 1` then `x = 0` (hence
`x ≠ 0` forces `2 ≤ |B(χ₁)|`). -/
private lemma theoremC_x_eq_zero_of_card_one {Bcard : ℕ} {x : ℝ}
    (hx : |x| ≤ ((Bcard - 1 : ℕ) : ℝ)) (hcard : Bcard = 1) : x = 0 := by
  have hz : |x| ≤ 0 := by simpa [hcard] using hx
  exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg x))

/-- From (4): `|B(χ₁)| = 2` when `x ≠ 0` and `|B(χ₁)| ≤ 2`. -/
private lemma theoremC_BOf_card_two_of_x_ne_zero {n Bcard : ℕ} {x : ℝ}
    (hn : n ≤ 2) (hx : |x| ≤ ((n - 1 : ℕ) : ℝ) * (Bcard : ℝ))
    (hxne : x ≠ 0) : n = 2 := by
  have hxpos : 0 < |x| := abs_pos.mpr hxne
  by_contra hne
  have hnle1 : n ≤ 1 := by omega
  have hnm : n - 1 = 0 := by omega
  have hz : |x| ≤ 0 := by simpa [hnm] using hx
  nlinarith

/-- One-term Cauchy--Schwarz used for equation (5): if `|x| ≤ |a|` and
`a² ≤ 2|B|`, then `x² ≤ 2|B|`.  (The sum in (4) has at most one term once
`|B(χ₁)| ≤ 2`.) -/
private lemma theoremC_x_sq_le_two_mul_B_of_one_term {x a : ℝ} {B : ℕ}
    (hx : |x| ≤ |a|) (ha2 : a ^ 2 ≤ 2 * (B : ℝ)) : x ^ 2 ≤ 2 * (B : ℝ) := by
  have hx2 : x ^ 2 ≤ a ^ 2 := sq_le_sq.mpr hx
  nlinarith

/-- Sign-independent bound used for (7): from equation (6) and
`|χᵢ(1)| ≥ 8α(1)+1`,
`χ₁(t)²/χ₁(1) + χ₂(t)²/χ₂(1) − χ₃(t)²/χ₃(1) ≤ ((1+x)² + (1−x)² + 4)/D`. -/
private lemma theoremC_L_bound {a1 a2 D c1 c2 c3 : ℝ}
    (hD : 0 < D) (hc1 : D ≤ |c1|) (hc2 : D ≤ |c2|) (hc3 : D ≤ |c3|)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) :
    a1 / c1 + a2 / c2 - 4 / c3 ≤ (a1 + a2 + 4) / D := by
  have h1 : a1 / c1 ≤ a1 / D := by
    by_cases hc : 0 ≤ c1
    · have hcabs : |c1| = c1 := abs_of_nonneg hc
      have hle : D ≤ c1 := by rwa [hcabs] at hc1
      have hpos : 0 < c1 := lt_of_lt_of_le hD hle
      rw [div_le_div_iff₀ hpos hD]
      nlinarith
    · have hneg : c1 < 0 := lt_of_not_ge hc
      have h1' : a1 / c1 ≤ 0 := div_nonpos_of_nonneg_of_nonpos ha1 (le_of_lt hneg)
      have h2' : 0 ≤ a1 / D := div_nonneg ha1 (le_of_lt hD)
      nlinarith
  have h2 : a2 / c2 ≤ a2 / D := by
    by_cases hc : 0 ≤ c2
    · have hcabs : |c2| = c2 := abs_of_nonneg hc
      have hle : D ≤ c2 := by rwa [hcabs] at hc2
      have hpos : 0 < c2 := lt_of_lt_of_le hD hle
      rw [div_le_div_iff₀ hpos hD]
      nlinarith
    · have hneg : c2 < 0 := lt_of_not_ge hc
      have h1' : a2 / c2 ≤ 0 := div_nonpos_of_nonneg_of_nonpos ha2 (le_of_lt hneg)
      have h2' : 0 ≤ a2 / D := div_nonneg ha2 (le_of_lt hD)
      nlinarith
  have h3 : -(4 / c3) ≤ 4 / D := by
    by_cases hc : 0 ≤ c3
    · have hneg : -(4 / c3) ≤ 0 :=
        neg_nonpos.mpr (div_nonneg (by norm_num) hc)
      have hpos' : 0 ≤ 4 / D := div_nonneg (by norm_num) (le_of_lt hD)
      nlinarith
    · have hneg : c3 < 0 := lt_of_not_ge hc
      have hcabs : |c3| = -c3 := abs_of_neg hneg
      have hle : D ≤ -c3 := by rwa [hcabs] at hc3
      have hpos : 0 < -c3 := lt_of_lt_of_le hD hle
      have hEq : -(4 / c3) = 4 / (-c3) := by
        field_simp [hneg.ne']
      rw [hEq]
      rw [div_le_div_iff₀ hpos hD]
      nlinarith
  have hsum : a1 / D + a2 / D + 4 / D = (a1 + a2 + 4) / D := by
    field_simp [hD.ne']
  calc
    a1 / c1 + a2 / c2 - 4 / c3 ≤ a1 / D + a2 / D + 4 / D := by
      nlinarith [h1, h2, h3]
    _ = (a1 + a2 + 4) / D := hsum

/-- Equation (7): Lemma 2.5's lower bound `1 − 3/φ(1) < 2k²|G:H|⁻¹`,
the sign-independent bound above, and `φ(1) ≥ 8α(1)+1` give
`1 < (3 + (1+x)² + (1−x)² + 4)/(8α(1)+1)`. -/
private lemma theoremC_ineq7 {D φ1 L x : ℝ} (hDpos : 0 < D)
    (hφ : D ≤ φ1) (hL1 : 1 - 3 / φ1 < L)
    (hL2 : L ≤ ((1 + x) ^ 2 + (1 - x) ^ 2 + 4) / D) :
    1 < (3 + (1 + x) ^ 2 + (1 - x) ^ 2 + 4) / D := by
  have hφpos : 0 < φ1 := by nlinarith
  have hdiv : 3 / φ1 ≤ 3 / D := by
    rw [div_le_div_iff₀ hφpos hDpos]
    nlinarith
  have h13 : 1 - 3 / D ≤ 1 - 3 / φ1 := by nlinarith
  have hlt : 1 - 3 / D < L := lt_of_le_of_lt h13 hL1
  let A : ℝ := (1 + x) ^ 2 + (1 - x) ^ 2 + 4
  have hEq : 1 - 3 / D = (D - 3) / D := by
    field_simp [hDpos.ne']
  have hlt' : (D - 3) / D < L := by rwa [hEq] at hlt
  have hbound : (D - 3) / D < A / D := lt_of_lt_of_le hlt' hL2
  have hmul : D - 3 < A := by
    have h := (div_lt_iff₀ hDpos).mp hbound
    field_simp [hDpos.ne'] at h
    exact h
  have hgoal : D < A + 3 := by nlinarith
  exact (lt_div_iff₀ hDpos).mpr (by
    dsimp [A] at hgoal ⊢
    nlinarith)

/-- Sign-independent form of equation (7).  When `φ(1)` is negative,
Lemma 2.5's lower bound already gives `1 < L`; otherwise the preceding
positive-denominator argument applies. -/
private lemma theoremC_ineq7_abs {D φ1 L x : ℝ} (hDpos : 0 < D)
    (hφ : D ≤ |φ1|) (hL1 : 1 - 3 / φ1 < L)
    (hL2 : L ≤ ((1 + x) ^ 2 + (1 - x) ^ 2 + 4) / D) :
    1 < (3 + (1 + x) ^ 2 + (1 - x) ^ 2 + 4) / D := by
  by_cases hφnonneg : 0 ≤ φ1
  · apply theoremC_ineq7 hDpos
    · simpa [abs_of_nonneg hφnonneg] using hφ
    · exact hL1
    · exact hL2
  · have hφneg : φ1 < 0 := lt_of_not_ge hφnonneg
    have hdivneg : 3 / φ1 < 0 := div_neg_of_pos_of_neg (by norm_num) hφneg
    have honeL : 1 < L := by nlinarith [hL1, hdivneg]
    have honeA : 1 < ((1 + x) ^ 2 + (1 - x) ^ 2 + 4) / D :=
      lt_of_lt_of_le honeL hL2
    have hthree : 0 < 3 / D := div_pos (by norm_num) hDpos
    have hEq :
        (3 + (1 + x) ^ 2 + (1 - x) ^ 2 + 4) / D =
          ((1 + x) ^ 2 + (1 - x) ^ 2 + 4) / D + 3 / D := by
      field_simp [hDpos.ne']
      ring
    rw [hEq]
    nlinarith

/-- For `ψ ∈ ±Irr(G)` the class-sum identity
`Σ_{χ∈Irr(G)} (χ(t)²/χ(1))·(χ,ψ)_G = ψ(t)²/ψ(1)`: the per-character
terms in the left side of equation (6). -/
private lemma theoremC_signed_irr_t_sum {G : Type u} [Group G] [Fintype G]
    (t : G) {ψ : ClassFunction G} (hψ : IsPMIrr G ψ) :
    (∑ χ : Irr G, (χ.1 t ^ 2 / χ.1 1) * scalarProduct G χ.1 ψ) = ψ t ^ 2 / ψ 1 := by
  classical
  rcases hψ with hψ | hψ
  · let ρ : Irr G := ⟨ψ, hψ⟩
    have hpair : ∀ χ : Irr G, scalarProduct G χ.1 ψ = if χ = ρ then 1 else 0 := by
      intro χ
      by_cases hχρ : χ = ρ
      · subst hχρ
        rw [scalarProduct_irreducible_self hψ]
        simp
      · have hχψ : χ.1 ≠ ψ := by
          intro hEq
          exact hχρ (Subtype.ext hEq)
        rw [scalarProduct_irreducible_orthogonal χ.2 hψ hχψ]
        simp [hχρ]
    calc
      (∑ χ : Irr G, (χ.1 t ^ 2 / χ.1 1) * scalarProduct G χ.1 ψ)
          = ∑ χ : Irr G, (χ.1 t ^ 2 / χ.1 1) * (if χ = ρ then 1 else 0) := by
              refine Finset.sum_congr rfl ?_
              intro χ hχ
              rw [hpair χ]
      _ = ψ t ^ 2 / ψ 1 := by simp [ρ]
  · let ρ : Irr G := ⟨-ψ, hψ⟩
    have hpair : ∀ χ : Irr G, scalarProduct G χ.1 ψ = if χ = ρ then -1 else 0 := by
      intro χ
      by_cases hχρ : χ = ρ
      · subst hχρ
        rw [scalarProduct_neg_left]
        have hself : scalarProduct G ψ ψ = 1 := by
          rw [show ψ = -(-ψ) by simp]
          rw [scalarProduct_neg_left, scalarProduct_neg_right]
          simpa using scalarProduct_irreducible_self hψ
        rw [hself]
        simp
      · have hχψ : χ.1 ≠ -ψ := by
          intro hEq
          exact hχρ (Subtype.ext hEq)
        rw [show ψ = -(-ψ) by simp]
        rw [scalarProduct_neg_right]
        rw [scalarProduct_irreducible_orthogonal χ.2 hψ hχψ]
        simp [hχρ]
    calc
      (∑ χ : Irr G, (χ.1 t ^ 2 / χ.1 1) * scalarProduct G χ.1 ψ)
          = ∑ χ : Irr G, (χ.1 t ^ 2 / χ.1 1) * (if χ = ρ then -1 else 0) := by
              refine Finset.sum_congr rfl ?_
              intro χ hχ
              rw [hpair χ]
      _ = - (ρ.1 t ^ 2 / ρ.1 1) := by simp [ρ]
      _ = ψ t ^ 2 / ψ 1 := by
        have hψρ : ψ = -ρ.1 := by simp [ρ]
        rw [hψρ]
        simp [pow_two, div_neg]

/-- A complex number with zero imaginary part is its own real part. -/
private lemma theoremC_ofReal_re_of_im_zero (z : ℂ) (hz : z.im = 0) : z = (z.re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using hz

/-- The value of a signed irreducible character at an involution is real. -/
private lemma theoremC_pmIrr_involution_im_zero {G : Type u} [Group G] [Fintype G]
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) {t : G} (ht : IsInvolution t) :
    (χ t).im = 0 := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using ht.2)
  rcases hχ with hρ | hρ
  · have hstar : star (χ t) = χ t⁻¹ :=
      star_char_eq_char_inv (isCharacter_of_isIrreducibleCharacter hρ) t
    rw [htinv] at hstar
    have hconj : starRingEnd ℂ (χ t) = χ t := by
      simpa [Complex.star_def] using hstar
    exact (Complex.conj_eq_iff_im.mp hconj)
  · have hstar : star ((-χ) t) = (-χ) t⁻¹ :=
      star_char_eq_char_inv (isCharacter_of_isIrreducibleCharacter hρ) t
    rw [htinv] at hstar
    have hconj : starRingEnd ℂ (χ t) = χ t := by
      have h := congrArg (fun z : ℂ => -z) hstar
      simpa [Complex.star_def] using h
    exact (Complex.conj_eq_iff_im.mp hconj)

/-- For `χ₁ ∈ ±Irr(G)`, `χ₁(t) − 1` is its own real part. -/
private lemma theoremC_x_real_value (c : Hyp11 G) [Hyp11KData c] {χ1 : ClassFunction G}
    (hχ1 : IsPMIrr G χ1) :
    χ1 c.t - 1 = ((χ1 c.t - 1).re : ℂ) := by
  have hz : (χ1 c.t - 1).im = 0 := by
    have h := theoremC_pmIrr_involution_im_zero hχ1 c.t_involution
    rw [Complex.sub_im]
    rw [h, Complex.one_im]
    norm_num
  exact theoremC_ofReal_re_of_im_zero (χ1 c.t - 1) hz

/-- `χ₁(t) = 1 + x` with `x := (χ₁(t) − 1).re`. -/
private lemma theoremC_chi1_t_eq_one_add_x (c : Hyp11 G) [Hyp11KData c] {χ1 : ClassFunction G}
    (hχ1 : IsPMIrr G χ1) :
    χ1 c.t = (1 + ((χ1 c.t - 1).re : ℂ)) := by
  have hx := theoremC_x_real_value c hχ1
  rw [← hx]
  ring

/-- `χ₂(t) = 1 − x` once `χ₁(t) + χ₂(t) = 2`. -/
private lemma theoremC_chi2_t_eq_one_sub_x (c : Hyp11 G) [Hyp11KData c] {χ1 χ2 : ClassFunction G}
    (hχ1 : IsPMIrr G χ1) (hsum : χ1 c.t + χ2 c.t = (2 : ℂ)) :
    χ2 c.t = (1 : ℂ) - ((χ1 c.t - 1).re : ℂ) := by
  have hx := theoremC_x_real_value c hχ1
  have h2 : χ2 c.t = (2 : ℂ) - χ1 c.t := by
    rw [← hsum]
    ring
  rw [h2]
  rw [← hx]
  ring

/-- `κ̃₁(t) = 2`: from the `T`-identity `κ̃₁−κ̃₃ = κ₁^H−κ₃^H` and the
induced values `κᵢ^H(t) = 2κᵢ(t)`. -/
private lemma theoremC_kappaOne_tilde_t_eq_two (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1S0 : ∀ x : ↥c.H0, (x : G) ∈ c.S0 → κ1 x = 1)
    (l3 : LambdaHom c.H0 c.U) (_hl3 : l3 ^ 2 ≠ 1)
    {χ3 : ClassFunction G} (_hχ3 : IsPMIrr G χ3)
    (_hκ3tilde : tildeNu c h12 ⟨kappa c κ1 l3, (kappa_isLinear c h12 hκ1lin l3).1⟩ = χ3)
    (hκ3tilde_t : tildeNu c h12
      ⟨kappa c κ1 l3, (kappa_isLinear c h12 hκ1lin l3).1⟩ c.t =
        2 * (kappa c κ1 l3) (tH0 c)) :
    tildeNu c h12 ⟨κ1, hκ1lin.1⟩ c.t = (2 : ℂ) := by
  classical
  let κ1Irr : Irr (↥c.H0) := ⟨κ1, hκ1lin.1⟩
  let κ3Irr : Irr (↥c.H0) :=
    ⟨kappa c κ1 l3, (kappa_isLinear c h12 hκ1lin l3).1⟩
  have hEq : κ1Irr.1 ∈ orbit c.H0 c.U κ3Irr.1 := by
    dsimp [κ3Irr]
    refine Finset.mem_image.mpr ⟨l3⁻¹, Finset.mem_univ _, ?_⟩
    ext x
    change (LambdaChar (l3⁻¹).1 * (LambdaChar l3.1 * κ1)) x = κ1 x
    simp [LambdaChar]
  have hT : c.t ∈ c.T := by
    rw [Hyp11.T]
    exact ⟨S0_le_H0 c c.t_mem_S0, t_not_mem_U c⟩
  have hH : c.t ∈ c.H := S_le_H c (c.S0_le_S c.t_mem_S0)
  have hOnT := tildeNu_on_T c h12 hEq c.t hT hH
  have hκ1ind : inducedFromSub (h12.H0_normal_in_H).1 κ1 ⟨c.t, hH⟩ = (2 : ℂ) := by
    have hθ := (remark_1_4 (h12.H0_normal_in_H).1 (H0_index c h12)
      (S_le_H c c.s_mem_S) (s_not_mem_H0' c h12) hκ1lin.1).1 c.t
      (S0_le_H0 c c.t_mem_S0) (s_normalizes_H0 c h12 (tH0 c))
    have hval1 : κ1 (tH0 c) = 1 := hκ1S0 (tH0 c) (by simpa [tH0] using c.t_mem_S0)
    have hval1' : κ1 ⟨c.t, S0_le_H0 c c.t_mem_S0⟩ = 1 := by
      simpa [tH0] using hval1
    have hconj : κ1 ⟨c.s * c.t * c.s⁻¹, s_normalizes_H0 c h12 (tH0 c)⟩ = 1 := by
      have hEq1 : c.s * c.t * c.s⁻¹ = c.t := s_conj_t c
      have hmem : (⟨c.s * c.t * c.s⁻¹, s_normalizes_H0 c h12 (tH0 c)⟩ : ↥c.H0) = tH0 c := by
        apply Subtype.ext
        exact hEq1
      rw [hmem]
      exact hval1
    have hθ' : inducedFromSub (h12.H0_normal_in_H).1 κ1
        ⟨c.t, (h12.H0_normal_in_H).1 (tH0 c).2⟩ = (2 : ℂ) := by
      rw [hθ, hval1', hconj]
      norm_num
    simpa [tH0] using hθ'
  have hκ3ind : inducedFromSub (h12.H0_normal_in_H).1 κ3Irr.1 ⟨c.t, hH⟩ =
      (2 : ℂ) * κ3Irr.1 (tH0 c) := by
    have hθ := (remark_1_4 (h12.H0_normal_in_H).1 (H0_index c h12)
      (S_le_H c c.s_mem_S) (s_not_mem_H0' c h12) κ3Irr.2).1 c.t
      (S0_le_H0 c c.t_mem_S0) (s_normalizes_H0 c h12 (tH0 c))
    have hconj : κ3Irr.1 ⟨c.s * c.t * c.s⁻¹, s_normalizes_H0 c h12 (tH0 c)⟩ =
        κ3Irr.1 (tH0 c) := by
      have hEq1 : c.s * c.t * c.s⁻¹ = c.t := s_conj_t c
      have hmem : (⟨c.s * c.t * c.s⁻¹, s_normalizes_H0 c h12 (tH0 c)⟩ : ↥c.H0) = tH0 c := by
        apply Subtype.ext
        exact hEq1
      rw [hmem]
    have hθ' : inducedFromSub (h12.H0_normal_in_H).1 κ3Irr.1
        ⟨c.t, (h12.H0_normal_in_H).1 (tH0 c).2⟩ =
        κ3Irr.1 (tH0 c) + κ3Irr.1 (tH0 c) := by
      rw [hθ, hconj]
      simp [tH0]
    have hθ'' : inducedFromSub (h12.H0_normal_in_H).1 κ3Irr.1
        ⟨c.t, (h12.H0_normal_in_H).1 (tH0 c).2⟩ = (2 : ℂ) * κ3Irr.1 (tH0 c) := by
      rw [hθ']
      ring
    simpa [tH0] using hθ''
  have hDiff : tildeNu c h12 κ1Irr c.t - tildeNu c h12 κ3Irr c.t =
      (2 : ℂ) - 2 * κ3Irr.1 (tH0 c) := by
    rw [hOnT, hκ1ind, hκ3ind]
  calc
    tildeNu c h12 κ1Irr c.t
        = (tildeNu c h12 κ1Irr c.t - tildeNu c h12 κ3Irr c.t) +
            tildeNu c h12 κ3Irr c.t := by ring
    _ = ((2 : ℂ) - 2 * κ3Irr.1 (tH0 c)) + tildeNu c h12 κ3Irr c.t := by rw [hDiff]
    _ = (2 : ℂ) := by
      rw [hκ3tilde_t]
      ring

/-- `χ₁(t) + χ₂(t) = 2` from `κ̃₁ = χ₁ + χ₂` and `κ̃₁(t) = 2`. -/
private lemma theoremC_chi1_add_chi2_t_eq_two (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1S0 : ∀ x : ↥c.H0, (x : G) ∈ c.S0 → κ1 x = 1)
    (l3 : LambdaHom c.H0 c.U) (hl3 : l3 ^ 2 ≠ 1)
    {χ1 χ2 χ3 : ClassFunction G} (_hχ1 : IsPMIrr G χ1) (_hχ2 : IsPMIrr G χ2)
    (hχ3 : IsPMIrr G χ3)
    (hκ1tilde : tildeNu c h12 ⟨κ1, hκ1lin.1⟩ = χ1 + χ2)
    (hκ3tilde : tildeNu c h12 ⟨kappa c κ1 l3, (kappa_isLinear c h12 hκ1lin l3).1⟩ = χ3)
    (hκ3tilde_t : tildeNu c h12
      ⟨kappa c κ1 l3, (kappa_isLinear c h12 hκ1lin l3).1⟩ c.t =
        2 * (kappa c κ1 l3) (tH0 c)) :
    χ1 c.t + χ2 c.t = (2 : ℂ) := by
  have hκ1tilde_t := theoremC_kappaOne_tilde_t_eq_two c h12 hκ1lin hκ1S0 l3 hl3 hχ3 hκ3tilde hκ3tilde_t
  have h := congrFun hκ1tilde c.t
  rw [hκ1tilde_t] at h
  simpa using h.symm

/-- Equation (2) before expanding the constituents of `δκ₁`: Lemma 2.2
case 3 for the pair `κ₁, λ₂κ₁`, under `k₁ = k₂`. -/
private lemma theoremC_delta_equation (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1S0 : ∀ x : ↥c.H0, (x : G) ∈ c.S0 → κ1 x = 1)
    (hκ1comm : ∀ x : ↥c.H0, (x : G) ∈ ⁅(c.S : Subgroup G), c.U⁆ → κ1 x = 1)
    (hk12 : c.k1 = c.k2) :
    (c.H.index : ℂ) * (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
      scalarProduct G χ.1 (deltaNu c h12 ⟨κ1, hκ1lin.1⟩)) =
        (2 * c.k ^ 2 : ℂ) := by
  classical
  let κ1Irr : Irr (↥c.H0) := ⟨κ1, hκ1lin.1⟩
  let κ2Irr : Irr (↥c.H0) :=
    ⟨kappa c κ1 (lambdaTwo c h12),
      (kappa_isLinear c h12 hκ1lin (lambdaTwo c h12)).1⟩
  have hEq : κ1Irr.1 ∈ orbit c.H0 c.U κ2Irr.1 := by
    dsimp [κ2Irr, κ1Irr]
    refine Finset.mem_image.mpr ⟨(lambdaTwo c h12)⁻¹, Finset.mem_univ _, ?_⟩
    ext x
    change (LambdaChar ((lambdaTwo c h12)⁻¹).1 *
      (LambdaChar (lambdaTwo c h12).1 * κ1)) x = κ1 x
    simp [LambdaChar]
  have h2 := lemma_2_2 c h12 (μ := κ1Irr) (ν := κ2Irr) (hEq := hEq)
    (κ1 := κ1) hκ1lin hκ1S0 hκ1comm
  have hV : lemma_2_2_V c κ1Irr.1 κ2Irr.1 = (2 * c.k ^ 2 : ℂ) := by
    exact h2.2.2 rfl rfl hk12
  change (c.H.index : ℂ) * (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
    scalarProduct G χ.1 (inducedClassFunction c.H0
      (κ1 - LambdaChar (lambdaTwo c h12).1 * κ1))) =
        (2 * c.k ^ 2 : ℂ) at hV
  rw [← deltaNu_eq_induced c h12 κ1Irr] at hV
  exact hV

/-- Whichever of the three Theorem-4.3 rows is the distinguished `δκ₁`,
the equation-(2) character sum is `8 / χ₁(1)`. -/
private lemma theoremC_S4_nonsingleton_row_sum (c : Hyp11 G) [Hyp11KData c]
    {χ1 χ2 χ3 χ4 δ : ClassFunction G}
    (hχ1 : IsPMIrr G χ1) (hχ2 : IsPMIrr G χ2)
    (hχ3 : IsPMIrr G χ3) (hχ4 : IsPMIrr G χ4)
    (ht1 : χ1 c.t = 3) (ht2 : χ2 c.t = 1)
    (ht3 : χ3 c.t = 1) (ht4 : χ4 c.t = -1)
    (hdeg2 : χ1 1 = -χ2 1) (hdeg3 : χ1 1 = -χ3 1)
    (hdeg4 : χ1 1 = χ4 1)
    (hrow : δ = χ1 + χ2 + χ3 + χ4 ∨
      δ = χ1 - χ2 + χ3 - χ4 ∨ δ = χ1 + χ2 - χ3 - χ4) :
    (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) * scalarProduct G χ.1 δ) =
      8 / χ1 1 := by
  classical
  have hs1 := theoremC_signed_irr_t_sum c.t hχ1
  have hs2 := theoremC_signed_irr_t_sum c.t hχ2
  have hs3 := theoremC_signed_irr_t_sum c.t hχ3
  have hs4 := theoremC_signed_irr_t_sum c.t hχ4
  have hχ1ne : χ1 1 ≠ 0 := chi_one_ne_zero_of_isPMIrr hχ1
  have hχ2deg : χ2 1 = -χ1 1 := by linear_combination hdeg2
  have hχ3deg : χ3 1 = -χ1 1 := by linear_combination hdeg3
  have hχ4deg : χ4 1 = χ1 1 := hdeg4.symm
  rcases hrow with hrow | hrow | hrow
  · rw [hrow]
    simp only [scalarProduct_add_right, mul_add, Finset.sum_add_distrib]
    rw [hs1, hs2, hs3, hs4, ht1, ht2, ht3, ht4,
      hχ2deg, hχ3deg, hχ4deg]
    field_simp [hχ1ne]
    ring
  · rw [hrow]
    simp only [scalarProduct_add_right, scalarProduct_sub_right, mul_add, mul_sub,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hs1, hs2, hs3, hs4, ht1, ht2, ht3, ht4,
      hχ2deg, hχ3deg, hχ4deg]
    field_simp [hχ1ne]
    ring
  · rw [hrow]
    simp only [scalarProduct_add_right, scalarProduct_sub_right, mul_add, mul_sub,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hs1, hs2, hs3, hs4, ht1, ht2, ht3, ht4,
      hχ2deg, hχ3deg, hχ4deg]
    field_simp [hχ1ne]
    ring

/-- The value of an irreducible character at an involution is an integer:
the representing involution has only the eigenvalues `1` and `-1`. -/
private lemma theoremC_irreducible_involution_int
    {G : Type u} [Group G] [Fintype G]
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    {t : G} (ht : IsInvolution t) :
    ∃ z : ℤ, (z : ℂ) = χ t := by
  classical
  rcases hχ with ⟨n, ρ, _hρ, rfl⟩
  let f : Module.End ℂ (Fin n → ℂ) := ρ t
  have hpow : f ^ 2 = 1 := by
    change (ρ t) ^ 2 = 1
    rw [← map_pow, ht.2, map_one]
  have htrace := Theory.Representation.trace_pow_eq_sum_eigenvalues
    (f := f) (n := 2) (k := 1) (by norm_num) hpow
  simp only [pow_one] at htrace
  let m : f.Eigenvalues → ℤ := fun μ =>
    if (μ : ℂ) = 1 then Module.finrank ℂ (f.eigenspace (μ : ℂ))
    else -Module.finrank ℂ (f.eigenspace (μ : ℂ))
  refine ⟨∑ μ, m μ, ?_⟩
  rw [Representation.character, htrace, Int.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro μ _hμ
  have hμpow : (μ : ℂ) ^ 2 = 1 :=
    Theory.Representation.eigenvalue_pow_eq_one_of_pow_eq_one hpow μ.property
  rcases sq_eq_one_iff.mp hμpow with hμ | hμ
  · simp [m, hμ]
  · have hne : (μ : ℂ) ≠ 1 := by rw [hμ]; norm_num
    simp only [m, if_neg hne, Int.cast_neg]
    rw [hμ]
    norm_num

/-- Signed version of involution-value integrality. -/
private lemma theoremC_pmIrr_involution_int
    {G : Type u} [Group G] [Fintype G]
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    {t : G} (ht : IsInvolution t) :
    ∃ z : ℤ, (z : ℂ) = χ t := by
  rcases hχ with hχ | hχ
  · exact theoremC_irreducible_involution_int hχ ht
  · rcases theoremC_irreducible_involution_int hχ ht with ⟨z, hz⟩
    refine ⟨-z, ?_⟩
    have h := congrArg Neg.neg hz
    simpa using h

/-- Pure divisibility core for the cardinality-three contradiction.  If
`q ∣ k`, `q` is coprime to `H`, and `k²m = z²H` with nonzero `k,m`, then
`q` divides the absolute integer `z`, hence is at most its absolute value. -/
private lemma theoremC_divisor_le_natAbs_of_square_eq
    {q k H : ℕ} {m z : ℤ}
    (hkpos : 0 < k) (hmne : m ≠ 0)
    (hqk : q ∣ k) (hcop : Nat.Coprime q H)
    (heq : (k : ℤ) ^ 2 * m = z ^ 2 * (H : ℤ)) :
    q ≤ z.natAbs := by
  have hz : z ≠ 0 := by
    intro hz
    rw [hz] at heq
    norm_num at heq
    rcases heq with hk | hm
    · exact hkpos.ne' hk
    · exact hmne hm
  have hqpowk : q ^ 2 ∣ k ^ 2 := pow_dvd_pow_of_dvd hqk 2
  have hleft : q ^ 2 ∣ k ^ 2 * m.natAbs :=
    dvd_mul_of_dvd_left hqpowk _
  have habseq : k ^ 2 * m.natAbs = z.natAbs ^ 2 * H := by
    have h := congrArg Int.natAbs heq
    simpa [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] using h
  rw [habseq] at hleft
  have hq2z2 : q ^ 2 ∣ z.natAbs ^ 2 :=
    (hcop.pow_left 2).dvd_of_dvd_mul_right hleft
  have hq2z2Z : ((q : ℤ) ^ 2) ∣ ((z.natAbs : ℤ) ^ 2) := by
    exact_mod_cast hq2z2
  have hqzZ : (q : ℤ) ∣ (z.natAbs : ℤ) :=
    (Int.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hq2z2Z
  have hqz : q ∣ z.natAbs := by exact_mod_cast hqzZ
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hz) hqz

/-- The value at `1` of a signed irreducible character is an integer. -/
private lemma theoremC_pmIrr_one_int {G : Type u} [Group G] [Fintype G]
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) :
    ∃ m : ℤ, (m : ℂ) = χ 1 := by
  rcases hχ with hχpos | hχneg
  · rcases hχpos with ⟨n, ρ, hρ, rfl⟩
    refine ⟨(Module.finrank ℂ (Fin n → ℂ) : ℤ), ?_⟩
    rw [Representation.char_one]
    norm_num
  · rcases hχneg with ⟨n, ρ, hρ, hEq⟩
    have hneg : χ = -ρ.character := by simpa using congrArg Neg.neg hEq
    rw [hneg]
    refine ⟨-(Module.finrank ℂ (Fin n → ℂ) : ℤ), ?_⟩
    rw [Pi.neg_apply, Representation.char_one]
    norm_num

/-- A signed irreducible degree is real: its value at the identity is the
integer degree (possibly with a minus sign). -/
private lemma theoremC_pmIrr_one_eq_real {G : Type u} [Group G] [Fintype G]
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) :
    χ 1 = (((χ 1).re : ℝ) : ℂ) := by
  rcases theoremC_pmIrr_one_int hχ with ⟨m, hm⟩
  rw [← hm]
  norm_num

private lemma theoremC_inv_ge_neg_one_fifth (x : ℝ) (hx : (5 : ℝ) ≤ |x|) :
    (-1 / 5 : ℝ) ≤ x⁻¹ := by
  by_cases h : 0 ≤ x
  · have hx5 : (5 : ℝ) ≤ x := by simpa [abs_of_nonneg h] using hx
    have hi := one_div_le_one_div_of_le (show (0 : ℝ) < 5 by norm_num) hx5
    have hnonneg : 0 ≤ x⁻¹ := inv_nonneg.mpr h
    norm_num [one_div] at hi ⊢
    linarith
  · have hneg : x < 0 := lt_of_not_ge h
    have hx5 : x ≤ (-5 : ℝ) := by
      rw [abs_of_neg hneg] at hx
      linarith
    have hi := one_div_le_one_div_of_neg_of_le
      (show (-5 : ℝ) < 0 by norm_num) hx5
    norm_num [one_div] at hi ⊢
    exact hi

private lemma theoremC_inv_le_one_fifth (x : ℝ) (hx : (5 : ℝ) ≤ |x|) :
    x⁻¹ ≤ (1 / 5 : ℝ) := by
  by_cases h : 0 ≤ x
  · have hx5 : (5 : ℝ) ≤ x := by simpa [abs_of_nonneg h] using hx
    have hi := one_div_le_one_div_of_le (show (0 : ℝ) < 5 by norm_num) hx5
    simpa [one_div] using hi
  · have hneg : x < 0 := lt_of_not_ge h
    have hi : x⁻¹ < 0 := (inv_lt_zero').2 hneg
    have hzero : (0 : ℝ) ≤ 1 / 5 := by norm_num
    exact hi.le.trans hzero

/-- Three signed degrees summing to `-1` give the strict lower reciprocal
bound used for the trivial Section-4 component. -/
private lemma theoremC_three_reciprocal_lower {a b c : ℝ}
    (hsum : a + b + c = -1)
    (ha : (5 : ℝ) ≤ |a|) (hb : (5 : ℝ) ≤ |b|) (hc : (5 : ℝ) ≤ |c|) :
    (3 / 5 : ℝ) < 1 + a⁻¹ + b⁻¹ + c⁻¹ := by
  have hia := theoremC_inv_ge_neg_one_fifth a ha
  have hib := theoremC_inv_ge_neg_one_fifth b hb
  have hic := theoremC_inv_ge_neg_one_fifth c hc
  have hpos : 0 < a ∨ 0 < b ∨ 0 < c := by
    by_contra h
    push Not at h
    have hane : a ≤ 0 := h.1
    have hbne : b ≤ 0 := h.2.1
    have hcne : c ≤ 0 := h.2.2
    have haa : a ≤ -5 := by
      rw [abs_of_nonpos hane] at ha
      linarith
    have hbb : b ≤ -5 := by
      rw [abs_of_nonpos hbne] at hb
      linarith
    have hcc : c ≤ -5 := by
      rw [abs_of_nonpos hcne] at hc
      linarith
    nlinarith
  rcases hpos with hpa | hpb | hpc
  · have hia' : 0 < a⁻¹ := inv_pos.mpr hpa
    nlinarith
  · have hib' : 0 < b⁻¹ := inv_pos.mpr hpb
    nlinarith
  · have hic' : 0 < c⁻¹ := inv_pos.mpr hpc
    nlinarith

/-- Four signed degrees summing to zero have reciprocal total strictly below
`3/5` once every absolute degree is at least five. -/
private lemma theoremC_four_reciprocal_upper {a b c d : ℝ}
    (hsum : a + b + c + d = 0)
    (ha : (5 : ℝ) ≤ |a|) (hb : (5 : ℝ) ≤ |b|)
    (hc : (5 : ℝ) ≤ |c|) (hd : (5 : ℝ) ≤ |d|) :
    a⁻¹ + b⁻¹ + c⁻¹ + d⁻¹ < (3 / 5 : ℝ) := by
  have hia := theoremC_inv_le_one_fifth a ha
  have hib := theoremC_inv_le_one_fifth b hb
  have hic := theoremC_inv_le_one_fifth c hc
  have hid := theoremC_inv_le_one_fifth d hd
  have hneg : a < 0 ∨ b < 0 ∨ c < 0 ∨ d < 0 := by
    by_contra h
    push Not at h
    have hane : 0 ≤ a := h.1
    have hbne : 0 ≤ b := h.2.1
    have hcne : 0 ≤ c := h.2.2.1
    have hdne : 0 ≤ d := h.2.2.2
    have haa : 5 ≤ a := by rw [abs_of_nonneg hane] at ha; exact ha
    have hbb : 5 ≤ b := by rw [abs_of_nonneg hbne] at hb; exact hb
    have hcc : 5 ≤ c := by rw [abs_of_nonneg hcne] at hc; exact hc
    have hdd : 5 ≤ d := by rw [abs_of_nonneg hdne] at hd; exact hd
    nlinarith
  rcases hneg with hna | hnb | hnc | hnd
  · have hia' : a⁻¹ < 0 := (inv_lt_zero').2 hna
    nlinarith
  · have hib' : b⁻¹ < 0 := (inv_lt_zero').2 hnb
    nlinarith
  · have hic' : c⁻¹ < 0 := (inv_lt_zero').2 hnc
    nlinarith
  · have hid' : d⁻¹ < 0 := (inv_lt_zero').2 hnd
    nlinarith

private lemma theoremC_three_reciprocal_lower_fin (f : Fin 4 → ℝ) (i0 : Fin 4)
    (hsum : ∑ i, f i = 0) (h0 : f i0 = 1)
    (habs : ∀ i, i ≠ i0 → (5 : ℝ) ≤ |f i|) :
    (3 / 5 : ℝ) < ∑ i, (f i)⁻¹ := by
  fin_cases i0
  · have hs : f 1 + f 2 + f 3 = -1 := by
      have h0' : f 0 = 1 := by simpa using h0
      have hsum' := hsum
      have hexp : 1 + (f 1 + (f 2 + f 3)) = 0 := by
        simpa [Fin.sum_univ_succ, add_assoc, h0'] using hsum'
      linarith
    have h := theoremC_three_reciprocal_lower hs
      (habs 1 (by decide)) (habs 2 (by decide)) (habs 3 (by decide))
    have h0' : f 0 = 1 := by simpa using h0
    have hexp : (∑ i, (f i)⁻¹) =
        (f 0)⁻¹ + (f 1)⁻¹ + (f 2)⁻¹ + (f 3)⁻¹ := by
      simp [Fin.sum_univ_succ, add_assoc]
    rw [hexp, h0']
    norm_num
    nlinarith [h]
  · have hs : f 0 + f 2 + f 3 = -1 := by
      have h0' : f 1 = 1 := by simpa using h0
      have hsum' := hsum
      have hexp : f 0 + (1 + (f 2 + f 3)) = 0 := by
        simpa [Fin.sum_univ_succ, add_assoc, h0'] using hsum'
      linarith
    have h := theoremC_three_reciprocal_lower hs
      (habs 0 (by decide)) (habs 2 (by decide)) (habs 3 (by decide))
    have h0' : f 1 = 1 := by simpa using h0
    have hexp : (∑ i, (f i)⁻¹) =
        (f 0)⁻¹ + (f 1)⁻¹ + (f 2)⁻¹ + (f 3)⁻¹ := by
      simp [Fin.sum_univ_succ, add_assoc]
    rw [hexp, h0']
    norm_num
    nlinarith [h]
  · have hs : f 0 + f 1 + f 3 = -1 := by
      have h0' : f 2 = 1 := by simpa using h0
      have hsum' := hsum
      have hexp : f 0 + (f 1 + (1 + f 3)) = 0 := by
        simpa [Fin.sum_univ_succ, add_assoc, h0'] using hsum'
      linarith
    have h := theoremC_three_reciprocal_lower hs
      (habs 0 (by decide)) (habs 1 (by decide)) (habs 3 (by decide))
    have h0' : f 2 = 1 := by simpa using h0
    have hexp : (∑ i, (f i)⁻¹) =
        (f 0)⁻¹ + (f 1)⁻¹ + (f 2)⁻¹ + (f 3)⁻¹ := by
      simp [Fin.sum_univ_succ, add_assoc]
    rw [hexp, h0']
    norm_num
    nlinarith [h]
  · have hs : f 0 + f 1 + f 2 = -1 := by
      have h0' : f 3 = 1 := by simpa using h0
      have hsum' := hsum
      have hexp : f 0 + (f 1 + (f 2 + 1)) = 0 := by
        simpa [Fin.sum_univ_succ, add_assoc, h0'] using hsum'
      linarith
    have h := theoremC_three_reciprocal_lower hs
      (habs 0 (by decide)) (habs 1 (by decide)) (habs 2 (by decide))
    have h0' : f 3 = 1 := by simpa using h0
    have hexp : (∑ i, (f i)⁻¹) =
        (f 0)⁻¹ + (f 1)⁻¹ + (f 2)⁻¹ + (f 3)⁻¹ := by
      simp [Fin.sum_univ_succ, add_assoc]
    rw [hexp, h0']
    norm_num
    nlinarith [h]

private lemma theoremC_four_reciprocal_upper_fin (f : Fin 4 → ℝ)
    (hsum : ∑ i, f i = 0)
    (habs : ∀ i, (5 : ℝ) ≤ |f i|) :
    (∑ i, (f i)⁻¹) < (3 / 5 : ℝ) := by
  have hs : f 0 + f 1 + f 2 + f 3 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  have h := theoremC_four_reciprocal_upper hs
    (habs 0) (habs 1) (habs 2) (habs 3)
  have hexp : (∑ i, (f i)⁻¹) =
      (f 0)⁻¹ + (f 1)⁻¹ + (f 2)⁻¹ + (f 3)⁻¹ := by
    simp [Fin.sum_univ_succ, add_assoc]
  rw [hexp]
  exact h

/-- The nonsingleton equation contradicts `(|K|, |G:H|) = 1`: after
`k = 2|K|`, it says `|G:H| = |K|² m` for the integral signed degree `m`. -/
private lemma theoremC_S4_nonsingleton_arithmetic (c : Hyp11 G) [Hyp11KData c]
    (hcop : Nat.Coprime (Nat.card c.K) c.H.index)
    (hK : c.K ≠ ⊥) (hk : c.k = 2 * Nat.card (↥c.K))
    {χ1 : ClassFunction G} (hχ1 : IsPMIrr G χ1)
    (heq : (c.H.index : ℂ) * (8 / χ1 1) = (2 * c.k ^ 2 : ℂ)) :
    False := by
  classical
  rcases theoremC_pmIrr_one_int hχ1 with ⟨m, hm⟩
  have hχ1ne : χ1 1 ≠ 0 := chi_one_ne_zero_of_isPMIrr hχ1
  have hmne : m ≠ 0 := by
    intro hm0
    apply hχ1ne
    rw [← hm, hm0]
    norm_num
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hmne
  have heq' := heq
  rw [← hm, hk] at heq'
  field_simp [hmC] at heq'
  have hcast : (c.H.index : ℂ) =
      ((((Nat.card (↥c.K) : ℤ) ^ 2 * m : ℤ)) : ℂ) := by
    norm_num [Nat.cast_mul, Nat.cast_pow] at heq' ⊢
    linear_combination (1 / 8 : ℂ) * heq'
  have hint : (c.H.index : ℤ) = (Nat.card (↥c.K) : ℤ) ^ 2 * m := by
    exact_mod_cast hcast
  have hdivZ : (Nat.card (↥c.K) : ℤ) ∣ (c.H.index : ℤ) := by
    refine ⟨(Nat.card (↥c.K) : ℤ) * m, ?_⟩
    rw [hint]
    ring
  have hdiv : Nat.card (↥c.K) ∣ c.H.index := by
    exact_mod_cast hdivZ
  have hcardK : Nat.card (↥c.K) = 1 :=
    Nat.Coprime.eq_one_of_dvd hcop hdiv
  exact hK (Subgroup.card_eq_one.mp hcardK)

/-- Under the theorem-C arithmetic hypotheses, every component containing a
linear Section-4 vertex is a singleton.  This factors the nonsingleton
Theorem-4.3 contradiction so it can be used for both the distinguished
`κ₁` vertex and the trivial `H₀` character. -/
private lemma theoremC_S4_component_ncard_eq_one (c : Hyp11 G) [Hyp11KData c]
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    (hUBK : c.U = c.B ⊔ c.K)
    (hcop : Nat.Coprime (Nat.card c.K) c.H.index)
    (hK : c.K ≠ ⊥) (hk : c.k = 2 * Nat.card (↥c.K))
    (hk12 : c.k1 = c.k2)
    {kappa : ClassFunction (↥c.H0)} (hkappalin : IsLinearCharacter kappa)
    (hkappaS0 : ∀ x : ↥c.H0, (x : G) ∈ c.S0 → kappa x = 1)
    (hkappacomm : ∀ x : ↥c.H0,
      (x : G) ∈ ⁅(c.S : Subgroup G), c.U⁆ → kappa x = 1)
    (hkappas : conjChar c.H0 (s_normalizes_H0 c h12) kappa = kappa)
    (hkappat : kappa (tH0 c) = kappa 1)
    {Delta0 : Set (ClassFunction G)}
    (hcomp : IsConnectedComponent c h12 Delta0)
    (hkappaDelta0 : deltaNu c h12 ⟨kappa, hkappalin.1⟩ ∈ Delta0) :
    Delta0.ncard = 1 := by
  classical
  let kappaIrr : Irr (↥c.H0) := ⟨kappa, hkappalin.1⟩
  by_contra hcard
  have hkappaone : kappaIrr.1 1 = 1 := by
    simpa [kappaIrr] using hkappalin.2
  rcases theoremC_S4_nonsingleton_data c h12 hSC hS4 hUBK kappaIrr
      (by simpa [kappaIrr] using hkappas)
      (by simpa [kappaIrr] using hkappat) hkappaone Delta0 hcomp
      (by simpa [kappaIrr] using hkappaDelta0) hcard with
    ⟨nu1, nu2, nu3, hnu1Delta0, hnu2Delta0, hnu3Delta0,
      hnu12, hnu23, hnu13,
      hnu1s, hnu1t, hnu1one, hnu2s, hnu2t, hnu2one,
      hnu3s, hnu3t, hnu3one,
      chi1, chi2, chi3, chi4, hchi1, hchi2, hchi3, hchi4,
      hchi12, hchi13, hchi14, hchi23, hchi24, hchi34,
      hdelta1, hdelta2, hdelta3, hset⟩
  rcases theoremC_S4_nonsingleton_t_values c h12 hSC hS4
      hnu12 hnu23 hnu13 hnu1s hnu1t hnu1one hnu2s hnu2t hnu2one
      hnu3s hnu3t hnu3one hchi1 hchi2 hchi3 hchi4
      hchi12 hchi13 hchi14 hchi23 hchi24 hchi34
      hdelta1 hdelta2 hdelta3 with
    ⟨ht1, ht2, ht3, ht4⟩
  rcases theoremC_S4_nonsingleton_degree_relations c h12
      hdelta1 hdelta2 hdelta3 with
    ⟨hdeg2, hdeg3, hdeg4⟩
  have hkappaRow : deltaNu c h12 kappaIrr = chi1 + chi2 + chi3 + chi4 ∨
      deltaNu c h12 kappaIrr = chi1 - chi2 + chi3 - chi4 ∨
      deltaNu c h12 kappaIrr = chi1 + chi2 - chi3 - chi4 := by
    have hmem : deltaNu c h12 kappaIrr ∈
        ({deltaNu c h12 nu1, deltaNu c h12 nu2,
          deltaNu c h12 nu3} : Set (ClassFunction G)) := by
      rw [← hset]
      simpa [kappaIrr] using hkappaDelta0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with hrow | hrow | hrow
    · exact Or.inl (hrow.trans hdelta1)
    · exact Or.inr (Or.inl (hrow.trans hdelta2))
    · exact Or.inr (Or.inr (hrow.trans hdelta3))
  have hsum := theoremC_S4_nonsingleton_row_sum c hchi1 hchi2 hchi3 hchi4
    ht1 ht2 ht3 ht4 hdeg2 hdeg3 hdeg4 hkappaRow
  have heq := theoremC_delta_equation c h12 hkappalin hkappaS0 hkappacomm hk12
  rw [hsum] at heq
  exact theoremC_S4_nonsingleton_arithmetic c hcop hK hk hchi1 heq

/-- A signed irreducible with nonzero coefficient in two generalized
characters witnesses that they are not disjoint. -/
private lemma theoremC_not_disjoint_of_pmIrr_pairings
    {G : Type u} [Group G] [Fintype G]
    {psi delta epsilon : ClassFunction G} (hpsi : IsPMIrr G psi)
    (hdelta : scalarProduct G psi delta ≠ 0)
    (hepsilon : scalarProduct G psi epsilon ≠ 0) :
    ¬ Theory.Character.Disjoint delta epsilon := by
  intro hdisjoint
  rcases hpsi with hpsi | hpsi
  · exact hepsilon (hdisjoint psi hpsi hdelta)
  · have hdelta' : scalarProduct G (-psi) delta ≠ 0 := by
      rw [scalarProduct_neg_left]
      exact neg_ne_zero.mpr hdelta
    have hepsilon' : scalarProduct G (-psi) epsilon ≠ 0 := by
      rw [scalarProduct_neg_left]
      exact neg_ne_zero.mpr hepsilon
    exact hepsilon' (hdisjoint (-psi) hpsi hdelta')

/-- In a singleton Section-4 component, a signed irreducible occurring with
coefficient one in the distinguished linear `deltaNu` has value one at `t`.
The component argument first shows that its whole `BPrimeOf` is the singleton
containing the distinguished character, then Lemma 4.1(ii) evaluates it. -/
private lemma theoremC_S4_singleton_t_value (c : Hyp11 G) [Hyp11KData c]
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    [Fintype ↥(LambdaHom c.H0 c.U)]
    {kappa : Irr (↥c.H0)}
    (hkappas : conjChar c.H0 (s_normalizes_H0 c h12) kappa.1 = kappa.1)
    (hkappat : kappa.1 (tH0 c) = kappa.1 1) (hkappaone : kappa.1 1 = 1)
    {Delta0 : Set (ClassFunction G)} (hcomp : IsConnectedComponent c h12 Delta0)
    (hkappaDelta0 : deltaNu c h12 kappa ∈ Delta0)
    (hDelta0 : Delta0 = {deltaNu c h12 kappa})
    {psi : ClassFunction G} (hpsi : IsPMIrr G psi)
    (hpair : scalarProduct G psi (deltaNu c h12 kappa) = 1) :
    psi c.t = 1 := by
  classical
  have hkappaB : kappa ∈ BPrimeOf c h12 psi := by
    rw [BPrime_mem_iff_scalar]
    exact ⟨hkappas, hkappat, by rw [hpair]; norm_num⟩
  have hBset : BPrimeOf c h12 psi = {kappa} := by
    ext nu
    constructor
    · intro hnuB
      rcases (BPrime_mem_iff_scalar c h12 psi nu).1 hnuB with
        ⟨hnus, hnut, hnupair⟩
      have hnuDelta : deltaNu c h12 nu ∈ Delta c h12 := by
        rw [Delta]
        exact ⟨nu, hnus, hnut, rfl⟩
      have hnuDelta0 : deltaNu c h12 nu ∈ Delta0 := by
        by_contra hnot
        have hne : deltaNu c h12 nu ≠ deltaNu c h12 kappa := by
          intro heq
          apply hnot
          rw [hDelta0, heq]
          simp
        have hadj : deltaAdjacent c h12 (deltaNu c h12 nu)
            (deltaNu c h12 kappa) := by
          refine ⟨hnuDelta, hcomp.2.1 hkappaDelta0, hne, ?_⟩
          exact theoremC_not_disjoint_of_pmIrr_pairings hpsi hnupair
            (by rw [hpair]; norm_num)
        exact (hcomp.2.2.2 (deltaNu c h12 nu) hnot
          (deltaNu c h12 kappa) hkappaDelta0) hadj
      have hdeltaeq : deltaNu c h12 nu = deltaNu c h12 kappa := by
        have hmem : deltaNu c h12 nu ∈
            ({deltaNu c h12 kappa} : Set (ClassFunction G)) := by
          rwa [← hDelta0]
        simpa using hmem
      have hnueq : nu = kappa :=
        deltaNu_injective c h12 hSC hS4 hnus hnut hkappas hkappat hdeltaeq
      simp [hnueq]
    · intro hnukappa
      have hnueq : nu = kappa := by simpa using hnukappa
      simpa [hnueq] using hkappaB
  have hvalue := (lemma_4_1 c h12 hSC hS4 hpsi ⟨kappa, hkappaB⟩).2.1
  rw [hBset] at hvalue
  simpa [hpair, hkappaone] using hvalue

/-- The signed four-decomposition of the distinguished singleton vertex can
be normalized termwise: its four signed irreducibles are pairwise orthogonal,
each has scalar product one with the vertex, and each takes value one at `t`.
-/
private lemma theoremC_S4_singleton_four_values (c : Hyp11 G) [Hyp11KData c]
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    [Fintype ↥(LambdaHom c.H0 c.U)]
    {kappa : Irr (↥c.H0)}
    (hkappas : conjChar c.H0 (s_normalizes_H0 c h12) kappa.1 = kappa.1)
    (hkappat : kappa.1 (tH0 c) = kappa.1 1) (hkappaone : kappa.1 1 = 1)
    {Delta0 : Set (ClassFunction G)} (hcomp : IsConnectedComponent c h12 Delta0)
    (hkappaDelta0 : deltaNu c h12 kappa ∈ Delta0)
    (hDelta0 : Delta0 = {deltaNu c h12 kappa}) :
    ∃ psi : Fin 4 → ClassFunction G,
      (∀ i, IsPMIrr G (psi i)) ∧
      (∀ {i j}, i ≠ j → scalarProduct G (psi i) (psi j) = 0) ∧
      deltaNu c h12 kappa = ∑ i, psi i ∧
      (∀ i, scalarProduct G (psi i) (deltaNu c h12 kappa) = 1) ∧
      (∀ i, psi i c.t = 1) := by
  classical
  rcases signed_four_decomp_fin c h12 hSC hS4 hkappas with
    ⟨a, sign, ha, hainj, hsign, hdelta⟩
  let psi : Fin 4 → ClassFunction G := fun i => (sign i : ℂ) • a i
  have hpsi : ∀ i, IsPMIrr G (psi i) := by
    intro i
    rcases hsign i with hi | hi
    · left
      simpa [psi, hi] using ha i
    · right
      simpa [psi, hi] using ha i
  have horth : ∀ {i j}, i ≠ j → scalarProduct G (psi i) (psi j) = 0 := by
    intro i j hij
    have haij : a i ≠ a j := by
      intro heq
      exact hij (hainj heq)
    rw [show psi i = (sign i : ℂ) • a i by rfl,
      show psi j = (sign j : ℂ) • a j by rfl,
      scalarProduct_smul_left, scalarProduct_smul_right,
      scalarProduct_irr_ite (ha i) (ha j)]
    simp [haij]
  have hdeltasum : deltaNu c h12 kappa = ∑ i, psi i := by
    simpa [psi] using hdelta
  have hpair : ∀ i, scalarProduct G (psi i) (deltaNu c h12 kappa) = 1 := by
    intro i
    rw [hdeltasum, scalarProduct_sum_right]
    rw [Finset.sum_eq_single i]
    · exact scalarProduct_self_eq_one_of_isPMIrr (hpsi i)
    · intro j _ hji
      exact horth hji.symm
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  refine ⟨psi, hpsi, horth, hdeltasum, hpair, ?_⟩
  intro i
  exact theoremC_S4_singleton_t_value c h12 hSC hS4 hkappas hkappat hkappaone
    hcomp hkappaDelta0 hDelta0 (hpsi i) (hpair i)

/-- The principal character occurs with coefficient one in the Section-4
difference attached to the trivial character of `H₀`.  This is Frobenius
reciprocity for the induced difference `1 - λ₂`. -/
private lemma theoremC_delta_trivial_principal_pairing (c : Hyp11 G) [Hyp11KData c]
    (h12 : Hyp12 c) :
    scalarProduct G (1 : ClassFunction G)
      (deltaNu c h12 ⟨(1 : ClassFunction (↥c.H0)),
        (isLinearCharacter_one (G := ↥c.H0)).1⟩) = 1 := by
  classical
  let oneIrr : Irr (↥c.H0) :=
    ⟨(1 : ClassFunction (↥c.H0)), (isLinearCharacter_one (G := ↥c.H0)).1⟩
  have honeClass : IsClassFunction (1 : ClassFunction G) :=
    irreducibleCharacter_isClassFunction (isIrreducibleCharacter_one G)
  have hres := scalarProduct_restrict_induced c.H0 honeClass
    ((1 : ClassFunction (↥c.H0)) -
      LambdaChar (lambdaTwo c h12).1 * (1 : ClassFunction (↥c.H0)))
  have hlambda :
      LambdaChar (lambdaTwo c h12).1 * (1 : ClassFunction (↥c.H0)) =
        LambdaChar (lambdaTwo c h12).1 := by simp
  have hlambdaIrr : IsIrreducibleCharacter
      (LambdaChar (lambdaTwo c h12).1) :=
    (isLinearCharacter_of_hom (lambdaTwo c h12).1).1
  have hlambdaNe : (1 : ClassFunction (↥c.H0)) ≠
      LambdaChar (lambdaTwo c h12).1 := by
    intro hEq
    apply lambdaTwo_ne_one c h12
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    apply Units.ext
    have hx := congrFun hEq x
    simpa [LambdaChar] using hx.symm
  have hsub : scalarProduct (↥c.H0) (1 : ClassFunction (↥c.H0))
      ((1 : ClassFunction (↥c.H0)) - LambdaChar (lambdaTwo c h12).1) = 1 := by
    rw [scalarProduct_sub_right,
      scalarProduct_irreducible_self (isIrreducibleCharacter_one (↥c.H0)),
      scalarProduct_irr_ite (isIrreducibleCharacter_one (↥c.H0)) hlambdaIrr]
    simp [hlambdaNe]
  change scalarProduct G (1 : ClassFunction G) (deltaNu c h12 oneIrr) = 1
  rw [deltaNu_eq_induced]
  change scalarProduct G (1 : ClassFunction G)
      (inducedClassFunction c.H0
        ((1 : ClassFunction (↥c.H0)) -
          LambdaChar (lambdaTwo c h12).1 * (1 : ClassFunction (↥c.H0)))) = 1
  rw [← hres]
  have honeRes : (fun x : ↥c.H0 => (1 : ClassFunction G) (x : G)) =
      (1 : ClassFunction (↥c.H0)) := by rfl
  rw [honeRes, hlambda]
  exact hsub

/-- If four signed irreducibles sum to a generalized character whose
principal coefficient is one, one of the signed terms is exactly the
principal character (with positive sign). -/
private lemma theoremC_exists_principal_in_four_sum
    (psi : Fin 4 → ClassFunction G) (hpsi : ∀ i, IsPMIrr G (psi i))
    (hsum : scalarProduct G (1 : ClassFunction G) (∑ i, psi i) = 1) :
    ∃ i, psi i = 1 := by
  classical
  by_contra hnone
  push Not at hnone
  have hnonpos : ∀ i,
      (scalarProduct G (1 : ClassFunction G) (psi i)).re ≤ 0 := by
    intro i
    rcases hpsi i with hpos | hneg
    · have hne : (1 : ClassFunction G) ≠ psi i := (hnone i).symm
      rw [scalarProduct_irr_ite (isIrreducibleCharacter_one G) hpos, if_neg hne]
      norm_num
    · rw [show psi i = -(-psi i) by simp, scalarProduct_neg_right]
      rw [scalarProduct_irr_ite (isIrreducibleCharacter_one G) hneg]
      split_ifs <;> norm_num
  have hle :
      (∑ i, (scalarProduct G (1 : ClassFunction G) (psi i)).re) ≤ 0 :=
    Finset.sum_nonpos fun i _ => hnonpos i
  have hre := congrArg Complex.re hsum
  simp only [scalarProduct_sum_right, Complex.re_sum, Complex.one_re] at hre
  rw [hre] at hle
  norm_num at hle

/-- Expand the Lemma-2.2 class sum for a four-term signed decomposition whose
four terms all take value one at `t`. -/
private lemma theoremC_S4_four_reciprocal_sum (c : Hyp11 G) [Hyp11KData c]
    {delta : ClassFunction G} (psi : Fin 4 → ClassFunction G)
    (hpsi : ∀ i, IsPMIrr G (psi i)) (hdelta : delta = ∑ i, psi i)
    (hpsit : ∀ i, psi i c.t = 1) :
    (∑ chi : Irr G, (chi.1 c.t ^ 2 / chi.1 1) *
      scalarProduct G chi.1 delta) = ∑ i, (psi i 1)⁻¹ := by
  classical
  rw [hdelta]
  simp_rw [scalarProduct_sum_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [theoremC_signed_irr_t_sum c.t (hpsi i), hpsit i]
  norm_num

/-- Kernel membership for an irreducible character is equivalent to keeping
its degree.  This theorem-local copy uses the representation chosen by
`charKernel` and the finite-order trace lemma proved above. -/
private lemma theoremC_mem_charKernel_irr_iff
    {K : Type u} [Group K] [Fintype K] {chi : ClassFunction K}
    (hchi : IsIrreducibleCharacter chi) (g : K) :
    g ∈ charKernel (isCharacter_of_isIrreducibleCharacter hchi) ↔
      chi g = chi 1 := by
  classical
  let rho := Classical.choose (Classical.choose_spec
    (isCharacter_of_isIrreducibleCharacter hchi))
  have hdef : charKernel (isCharacter_of_isIrreducibleCharacter hchi) =
      rho.ker := rfl
  have hrho : chi = rho.character :=
    Classical.choose_spec (Classical.choose_spec
      (isCharacter_of_isIrreducibleCharacter hchi))
  rw [hdef, MonoidHom.mem_ker]
  constructor
  · intro hg
    rw [hrho, Representation.character, hg]
    simp
  · intro hg
    apply theoremC_rep_eq_one_of_char_eq_degree rho g
    rw [← hrho]
    exact hg

private lemma theoremC_linearChar_eq_one_of_fixedPointFree_comp
    {K : Type u} [CommGroup K] [Finite K]
    {beta : ClassFunction K} (hbeta : IsLinearCharacter beta) (tau : K ≃* K)
    (htau : ∀ k : K, k ≠ 1 → tau k ≠ k)
    (hfix : ∀ k : K, beta (tau k) = beta k) :
    beta = (1 : ClassFunction K) := by
  classical
  let d : K →* K := {
    toFun := fun k => tau k * k⁻¹
    map_one' := by simp
    map_mul' := by
      intro a b
      simp only [map_mul, mul_inv_rev]
      ac_rfl }
  have hd_inj : Function.Injective d := by
    apply (MonoidHom.ker_eq_bot_iff d).mp
    apply le_bot_iff.mp
    intro k hk
    have hdk : tau k * k⁻¹ = 1 := MonoidHom.mem_ker.mp hk
    have htk : tau k = k := by
      apply mul_right_cancel (b := k⁻¹)
      simpa using hdk
    by_contra hk1
    exact htau k hk1 htk
  have hd_surj : Function.Surjective d :=
    Finite.surjective_of_injective hd_inj
  ext y
  rcases hd_surj y with ⟨k, rfl⟩
  change beta (tau k * k⁻¹) = 1
  rw [linearChar_mul hbeta, hfix, linearChar_inv hbeta]
  exact mul_inv_cancel₀ (linearChar_ne_zero hbeta k)

private lemma theoremC_scalarProduct_comp_smul_eq_of_invariant
    {U K : Type u} [Group U] [Group K] [Fintype K]
    [MulDistribMulAction U K]
    (phi psi : ClassFunction K) (u : U)
    (hphi : ∀ k : K, phi (u • k) = phi k) :
    scalarProduct K phi (fun k => psi (u⁻¹ • k)) = scalarProduct K phi psi := by
  classical
  unfold scalarProduct
  congr 1
  let e : K ≃ K := (MulDistribMulAction.toMulEquiv K u⁻¹).toEquiv
  refine Fintype.sum_equiv e
    (fun k : K => phi k * star (psi (u⁻¹ • k)))
    (fun k : K => phi k * star (psi k)) ?_
  intro k
  change phi k * star (psi (u⁻¹ • k)) =
    phi (u⁻¹ • k) * star (psi (u⁻¹ • k))
  have hk := hphi (u⁻¹ • k)
  simp only [smul_smul, mul_inv_cancel, one_smul] at hk
  rw [hk]

private lemma theoremC_exists_nontrivial_K_constituent
    (c : Hyp11 G) [Hyp11KData c] (alpha : Irr (↥c.U))
    (hK : ¬ c.K ≤ (charKernel
      (isCharacter_of_isIrreducibleCharacter alpha.2)).map
        (Subgroup.subtype c.U)) :
    ∃ beta : IrrBG19 (↥(theoremC_KU c)),
      beta.1 ≠ (1 : ClassFunction (↥(theoremC_KU c))) ∧
      scalarProduct (↥(theoremC_KU c))
        (fun k : ↥(theoremC_KU c) => alpha.1 (k : ↥c.U)) beta.1 ≠ 0 := by
  classical
  let K0 : Subgroup (↥c.U) := theoremC_KU c
  let phi : ClassFunction (↥K0) := fun k => alpha.1 (k : ↥c.U)
  have hphi_char : IsCharacter phi := by
    simpa [phi] using isCharacter_restrict K0
      (isCharacter_of_isIrreducibleCharacter alpha.2)
  have hphi_gen : IsGeneralizedCharacter phi :=
    ⟨phi, 0, hphi_char, isCharacter_zero, by ext x; simp⟩
  by_contra hnone
  push Not at hnone
  have hsum (k : ↥K0) : phi k = ∑ delta : IrrBG19 (↥K0),
      scalarProduct (↥K0) phi delta.1 * delta.1 k := by
    simpa using
      (classFunction_eq_sum_irr_coeffs (G := ↥K0) (φ := phi) hphi_gen k)
  have hconst : ∀ k : ↥K0, phi k = phi 1 := by
    intro k
    rw [hsum k, hsum 1]
    refine Finset.sum_congr rfl ?_
    intro delta _hdelta
    by_cases hdelta_one : delta.1 = (1 : ClassFunction (↥K0))
    · rw [hdelta_one]
      simp
    · have hcoeff : scalarProduct (↥K0) phi delta.1 = 0 :=
        hnone delta hdelta_one
      simp [hcoeff]
  apply hK
  intro k hk
  rw [Subgroup.mem_map]
  refine ⟨⟨k, theoremC_K_le_U c hk⟩, ?_, rfl⟩
  rw [theoremC_mem_charKernel_irr_iff alpha.2
    ⟨k, theoremC_K_le_U c hk⟩]
  have hkK0 : (⟨k, theoremC_K_le_U c hk⟩ : ↥c.U) ∈ K0 := by
    change (⟨k, theoremC_K_le_U c hk⟩ : ↥c.U) ∈
      (c.K : Subgroup G).subgroupOf c.U
    rw [Subgroup.mem_subgroupOf]
    simpa using hk
  have hc := hconst ⟨⟨k, theoremC_K_le_U c hk⟩, hkK0⟩
  simpa [phi] using hc

private lemma theoremC_B_smul_injective_of_frobenius
    (c : Hyp11 G) [Hyp11KData c]
    (hFrob : IsFrobeniusGroupWithKernel (c.B ⊔ c.K) c.K)
    (hBK : c.B ⊓ c.K = ⊥)
    (beta : IrrBG19 (↥(theoremC_KU c)))
    (hbeta_ne : beta.1 ≠ (1 : ClassFunction (↥(theoremC_KU c)))) :
    letI : MulDistribMulAction (↥c.U) (↥(theoremC_KU c)) :=
      theoremC_KU_action c
    letI : MulAction (↥c.U) (IrrBG19 (↥(theoremC_KU c))) :=
      theoremC_KU_irr_action c
    Function.Injective (fun b : ↥c.B =>
      (⟨(b : G), theoremC_B_le_U c b.2⟩ : ↥c.U) • beta) := by
  classical
  let : (theoremC_KU c).Normal := theoremC_KU_normal c
  let : MulDistribMulAction (↥c.U) (↥(theoremC_KU c)) :=
    theoremC_KU_action c
  let : MulAction (↥c.U) (IrrBG19 (↥(theoremC_KU c))) :=
    theoremC_KU_irr_action c
  let : CommGroup (↥(theoremC_KU c)) := {
    (inferInstance : Group (↥(theoremC_KU c))) with
    mul_comm := by
      intro a b
      exact (isMulCommutative_iff.mp (theoremC_KU_comm c)) a b }
  unfold IsFrobeniusGroupWithKernel at hFrob
  rcases hFrob with ⟨_hKN, hfree, _hKne⟩
  intro b1 b2 hb
  let b1U : ↥c.U := ⟨(b1 : G), theoremC_B_le_U c b1.2⟩
  let b2U : ↥c.U := ⟨(b2 : G), theoremC_B_le_U c b2.2⟩
  let xU : ↥c.U := b2U⁻¹ * b1U
  have hb' : b1U • beta = b2U • beta := by
    simpa [b1U, b2U] using hb
  have hxfix : xU • beta = beta := by
    calc
      xU • beta = b2U⁻¹ • (b1U • beta) := by
        simp [xU, mul_smul]
      _ = b2U⁻¹ • (b2U • beta) := by rw [hb']
      _ = beta := by simp
  by_contra hbne
  have hxGne : (xU : G) ≠ 1 := by
    intro hx1
    apply hbne
    apply Subtype.ext
    have hx1' : (b2 : G)⁻¹ * (b1 : G) = 1 := by
      simpa [xU, b1U, b2U] using hx1
    have hmul := congrArg (fun z : G => (b2 : G) * z) hx1'
    simpa [mul_assoc] using hmul
  have hxB : (xU : G) ∈ c.B := by
    change (b2 : G)⁻¹ * (b1 : G) ∈ c.B
    exact c.B.mul_mem (c.B.inv_mem b2.2) b1.2
  have hxX : (xU : G) ∈ c.B ⊔ c.K :=
    (le_sup_left : c.B ≤ c.B ⊔ c.K) hxB
  have hxnotK : (xU : G) ∉ c.K := by
    intro hxK
    have hxinf : (xU : G) ∈ c.B ⊓ c.K :=
      Subgroup.mem_inf.mpr ⟨hxB, hxK⟩
    rw [hBK] at hxinf
    exact hxGne (Subgroup.mem_bot.mp hxinf)
  have hxinvX : (xU⁻¹ : ↥c.U) ∈
      (c.B ⊔ c.K).subgroupOf c.U := by
    rw [Subgroup.mem_subgroupOf]
    exact (c.B ⊔ c.K).inv_mem hxX
  have hxinvnotK : ((xU⁻¹ : ↥c.U) : G) ∉ c.K := by
    intro hxK
    have hxK' : (xU : G) ∈ c.K := by
      have := c.K.inv_mem hxK
      simpa using this
    exact hxnotK hxK'
  let tau : ↥(theoremC_KU c) ≃* ↥(theoremC_KU c) :=
    MulDistribMulAction.toMulEquiv (↥(theoremC_KU c)) xU⁻¹
  have htau : ∀ k : ↥(theoremC_KU c), k ≠ 1 → tau k ≠ k := by
    intro k hk htk
    have hkG : ((k : ↥c.U) : G) ∈ c.K :=
      Subgroup.mem_subgroupOf.mp k.2
    have hkGne : ((k : ↥c.U) : G) ≠ 1 := by
      intro hk1
      apply hk
      apply Subtype.ext
      apply Subtype.ext
      exact hk1
    apply hfree ((xU⁻¹ : ↥c.U) : G)
      (Subgroup.mem_subgroupOf.mp hxinvX) hxinvnotK
      ((k : ↥c.U) : G) hkG hkGne
    have htkU := congrArg (fun z : ↥(theoremC_KU c) => (z : ↥c.U)) htk
    change
      ((MulAut.conjNormal (G := ↥c.U) (H := theoremC_KU c) xU⁻¹) k : ↥c.U) =
        (k : ↥c.U) at htkU
    have htkG := congrArg (fun z : ↥c.U => (z : G)) htkU
    simpa using htkG
  have hfix : ∀ k : ↥(theoremC_KU c), beta.1 (tau k) = beta.1 k := by
    intro k
    have hk := congrFun (congrArg Subtype.val hxfix) k
    change beta.1 (xU⁻¹ • k) = beta.1 k at hk
    exact hk
  exact hbeta_ne
    (theoremC_linearChar_eq_one_of_fixedPointFree_comp
      (theoremC_irr_linear_of_comm (theoremC_KU_comm c) beta)
      tau htau hfix)

private lemma theoremC_frobenius_degree_bound
    (c : Hyp11 G) [Hyp11KData c]
    (hFrob : IsFrobeniusGroupWithKernel (c.B ⊔ c.K) c.K)
    (hBK : c.B ⊓ c.K = ⊥)
    (alpha : Irr (↥c.U))
    (hK : ¬ c.K ≤
      (charKernel (isCharacter_of_isIrreducibleCharacter alpha.2)).map
        (Subgroup.subtype c.U)) :
    (Nat.card (↥c.B) : ℝ) ≤ (alpha.1 1).re := by
  classical
  let : (theoremC_KU c).Normal := theoremC_KU_normal c
  let : MulDistribMulAction (↥c.U) (↥(theoremC_KU c)) :=
    theoremC_KU_action c
  let : MulAction (↥c.U) (IrrBG19 (↥(theoremC_KU c))) :=
    theoremC_KU_irr_action c
  let : CommGroup (↥(theoremC_KU c)) := {
    (inferInstance : Group (↥(theoremC_KU c))) with
    mul_comm := by
      intro a b
      exact (isMulCommutative_iff.mp (theoremC_KU_comm c)) a b }
  let K0 : Subgroup (↥c.U) := theoremC_KU c
  let phi : ClassFunction (↥K0) := fun k => alpha.1 (k : ↥c.U)
  have hphi_char : IsCharacter phi := by
    simpa [phi] using isCharacter_restrict K0
      (isCharacter_of_isIrreducibleCharacter alpha.2)
  rcases theoremC_exists_nontrivial_K_constituent c alpha hK with
    ⟨beta, hbeta_ne, hbeta_coeff⟩
  let f : ↥c.B → IrrBG19 (↥K0) := fun b =>
    (⟨(b : G), theoremC_B_le_U c b.2⟩ : ↥c.U) • beta
  have hf : Function.Injective f := by
    simpa [f, K0] using
      theoremC_B_smul_injective_of_frobenius c hFrob hBK beta hbeta_ne
  have hphi_inv (u : ↥c.U) (k : ↥K0) : phi (u • k) = phi k := by
    change alpha.1 ((u • k : ↥K0) : ↥c.U) = alpha.1 (k : ↥c.U)
    have hclass := irreducibleCharacter_isClassFunction alpha.2 (k : ↥c.U) u
    change alpha.1 (u * (k : ↥c.U) * u⁻¹) = alpha.1 (k : ↥c.U) at hclass
    exact hclass
  have hcoeff_smul (u : ↥c.U) :
      scalarProduct (↥K0) phi (u • beta).1 =
        scalarProduct (↥K0) phi beta.1 := by
    change scalarProduct (↥K0) phi
      (fun k => beta.1 (u⁻¹ • k)) = scalarProduct (↥K0) phi beta.1
    exact theoremC_scalarProduct_comp_smul_eq_of_invariant
      phi beta.1 u (hphi_inv u)
  have hcoeff_nat (delta : IrrBG19 (↥K0)) : ∃ m : ℕ,
      (m : ℂ) = scalarProduct (↥K0) phi delta.1 := by
    rcases scalarProduct_irr_char_nat (χ := delta.1) (ψ := phi)
        delta.2 hphi_char with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    calc
      (m : ℂ) = scalarProduct (↥K0) delta.1 phi := hm
      _ = star (scalarProduct (↥K0) delta.1 phi) := by
        rw [hm.symm]
        simp
      _ = scalarProduct (↥K0) phi delta.1 :=
        scalarProduct_conj delta.1 phi
  let mult : IrrBG19 (↥K0) → ℕ := fun delta =>
    Classical.choose (hcoeff_nat delta)
  have hmult (delta : IrrBG19 (↥K0)) :
      (mult delta : ℂ) = scalarProduct (↥K0) phi delta.1 :=
    Classical.choose_spec (hcoeff_nat delta)
  have hmult_beta_pos : 1 ≤ mult beta := by
    have hne : mult beta ≠ 0 := by
      intro hm0
      apply hbeta_coeff
      rw [← hmult beta, hm0]
      norm_num
    omega
  have hmult_f (b : ↥c.B) : mult (f b) = mult beta := by
    have hcast : (mult (f b) : ℂ) = (mult beta : ℂ) := by
      calc
        (mult (f b) : ℂ) = scalarProduct (↥K0) phi (f b).1 := hmult (f b)
        _ = scalarProduct (↥K0) phi beta.1 := by
          simpa [f] using hcoeff_smul
            (⟨(b : G), theoremC_B_le_U c b.2⟩ : ↥c.U)
        _ = (mult beta : ℂ) := (hmult beta).symm
    exact_mod_cast hcast
  have hmult_f_pos (b : ↥c.B) : 1 ≤ mult (f b) := by
    rw [hmult_f b]
    exact hmult_beta_pos
  have hphi_gen : IsGeneralizedCharacter phi :=
    ⟨phi, 0, hphi_char, isCharacter_zero, by ext x; simp⟩
  have hsum : phi 1 = ∑ delta : IrrBG19 (↥K0), (mult delta : ℂ) := by
    calc
      phi 1 = ∑ delta : IrrBG19 (↥K0),
          scalarProduct (↥K0) phi delta.1 * delta.1 1 := by
        simpa using (classFunction_eq_sum_irr_coeffs
          (G := ↥K0) (φ := phi) hphi_gen (1 : ↥K0))
      _ = ∑ delta : IrrBG19 (↥K0), (mult delta : ℂ) := by
        refine Finset.sum_congr rfl ?_
        intro delta _hdelta
        rw [← hmult delta]
        have hlin := theoremC_irr_linear_of_comm (theoremC_KU_comm c) delta
        rw [hlin.2]
        simp
  rcases alpha.2 with ⟨n, rho, _hrho, halpha⟩
  have hdegree : alpha.1 1 = (n : ℂ) := by
    rw [halpha, Representation.char_one]
    norm_num
  have hn_sum : n = ∑ delta : IrrBG19 (↥K0), mult delta := by
    have hc : (n : ℂ) =
        ((∑ delta : IrrBG19 (↥K0), mult delta : ℕ) : ℂ) := by
      calc
        (n : ℂ) = phi 1 := by simpa [phi] using hdegree.symm
        _ = ∑ delta : IrrBG19 (↥K0), (mult delta : ℂ) := hsum
        _ = ((∑ delta : IrrBG19 (↥K0), mult delta : ℕ) : ℂ) := by
          norm_num
    exact_mod_cast hc
  let S : Finset (IrrBG19 (↥K0)) := Finset.univ.image f
  have hScard : S.card = Nat.card (↥c.B) := by
    calc
      S.card = (Finset.univ : Finset (↥c.B)).card := by
        exact Finset.card_image_of_injective _ hf
      _ = Nat.card (↥c.B) := by simp
  have hS_lower : S.card ≤ ∑ delta ∈ S, mult delta := by
    calc
      S.card = ∑ delta ∈ S, 1 := by simp
      _ ≤ ∑ delta ∈ S, mult delta := by
        apply Finset.sum_le_sum
        intro delta hdelta
        rcases Finset.mem_image.mp hdelta with ⟨b, _hb, rfl⟩
        exact hmult_f_pos b
  have hS_total : (∑ delta ∈ S, mult delta) ≤
      ∑ delta : IrrBG19 (↥K0), mult delta := by
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ S)
  have hnat : Nat.card (↥c.B) ≤ n := by
    rw [← hScard, hn_sum]
    exact hS_lower.trans hS_total
  have hre : (alpha.1 1).re = (n : ℝ) := by
    rw [hdegree]
    norm_num
  rw [hre]
  exact_mod_cast hnat

/-- In a simple group, a nontrivial subgroup `K` cannot lie in the character
kernel of a nonprincipal irreducible character. -/
private lemma theoremC_simple_K_not_le_charKernel (c : Hyp11 G) [Hyp11KData c]
    (hK : c.K ≠ ⊥) (hsimple : IsSimpleGroup G) (chi : Irr G)
    (hchiOne : chi.1 ≠ (1 : ClassFunction G)) :
    ¬ c.K ≤ charKernel (isCharacter_of_isIrreducibleCharacter chi.2) := by
  classical
  let : IsSimpleGroup G := hsimple
  intro hKle
  have hnormal :
      (charKernel (isCharacter_of_isIrreducibleCharacter chi.2)).Normal := by
    change (Classical.choose (Classical.choose_spec
      (isCharacter_of_isIrreducibleCharacter chi.2))).ker.Normal
    exact MonoidHom.normal_ker _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (charKernel (isCharacter_of_isIrreducibleCharacter chi.2)) with
    hbot | htop
  · apply hK
    apply le_bot_iff.mp
    rw [← hbot]
    exact hKle
  · have hconst : ∀ g : G, chi.1 g = chi.1 1 := by
      intro g
      apply (theoremC_mem_charKernel_irr_iff chi.2 g).1
      rw [htop]
      trivial
    have hpairZero : scalarProduct G chi.1 (1 : ClassFunction G) = 0 := by
      rw [scalarProduct_irr_ite chi.2 (isIrreducibleCharacter_one G)]
      simp [hchiOne]
    have hpairDegree : scalarProduct G chi.1 (1 : ClassFunction G) = chi.1 1 := by
      unfold scalarProduct
      simp_rw [hconst]
      simp [Finset.sum_const, nsmul_eq_mul]
    have hdegreeZero : chi.1 1 = 0 := by rw [← hpairDegree, hpairZero]
    exact chi_one_ne_zero_of_isPMIrr (Or.inl chi.2) hdegreeZero

/-- The real degree of an irreducible character is at least one. -/
private lemma theoremC_irr_degree_re_ge_one
    {K : Type u} [Group K] [Fintype K] (chi : Irr K) :
    (1 : ℝ) ≤ (chi.1 1).re := by
  rcases chi.2 with ⟨n, rho, hrho, hchi⟩
  have hdegree : chi.1 1 = (n : ℂ) := by
    rw [hchi, Representation.char_one]
    norm_num
  have hnne : n ≠ 0 := by
    intro hn
    apply chi_one_ne_zero_of_isPMIrr (Or.inl chi.2)
    rw [hdegree, hn]
    norm_num
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hnne
  rw [hdegree]
  norm_num
  exact_mod_cast hn

/-- Negating a class function does not change the set of irreducibles with
nonzero scalar product against it. -/
private lemma theoremC_BOf_neg (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (psi : ClassFunction G) :
    BOf c h12 (-psi) = BOf c h12 psi := by
  ext nu
  rw [BOf_mem_iff, BOf_mem_iff, scalarProduct_neg_left]
  simp

/-- Lemma 3.6 with the witnessing `U`-character degree exposed as a natural
number, for an irreducible character of `G`. -/
private lemma theoremC_irr_lemma36_degree_data
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hm : 4 ≤ (c.U.subgroupOf c.H0).index)
    (hKbot : c.K ≠ ⊥) (hsimple : IsSimpleGroup G)
    {psi : ClassFunction G} (hpsi : IsIrreducibleCharacter psi)
    (hpsiOne : psi ≠ (1 : ClassFunction G))
    (hB : (BOf c h12 psi).Nonempty)
    (horbit : ∀ nu : Irr (↥c.H0), nu ∈ BOf c h12 psi →
      conjChar c.H0 (s_normalizes_H0 c h12) nu.1 ∈ orbit c.H0 c.U nu.1) :
    ∃ alpha : Irr (↥c.U), ∃ a : ℕ,
      ¬ c.K ≤ (charKernel
        (isCharacter_of_isIrreducibleCharacter alpha.2)).map
          (Subgroup.subtype c.U) ∧
      1 ≤ a ∧ (alpha.1 1).re = (a : ℝ) ∧
      (8 * (a : ℝ) + 1) ≤ (psi 1).re := by
  let chi : Irr G := ⟨psi, hpsi⟩
  have hkernel := theoremC_simple_K_not_le_charKernel c hKbot hsimple chi hpsiOne
  rcases theoremC_lemma36 c h12 hSC chi hB hkernel horbit with
    ⟨alpha, hKalpha, hbound⟩
  rcases alpha.2 with ⟨a, sigma, hsigma, halpha⟩
  have halphaC : alpha.1 1 = (a : ℂ) := by
    rw [halpha, Representation.char_one]
    norm_num
  have halphaR : (alpha.1 1).re = (a : ℝ) := by
    rw [halphaC]
    norm_num
  have ha : 1 ≤ a := by
    have := theoremC_irr_degree_re_ge_one alpha
    rw [halphaR] at this
    exact_mod_cast this
  rcases hpsi with ⟨b, rho, hrho, hpsiEq⟩
  have hpsiC : psi 1 = (b : ℂ) := by
    rw [hpsiEq, Representation.char_one]
    norm_num
  have hpsiR : (psi 1).re = (b : ℝ) := by
    rw [hpsiC]
    norm_num
  have hboundNat : 8 * a + 1 ≤ b := by
    apply theoremC_lemma36_degree_bound hm ha
    rw [halphaR, hpsiR] at hbound
    exact hbound
  refine ⟨alpha, a, hKalpha, ha, halphaR, ?_⟩
  rw [hpsiR]
  exact_mod_cast hboundNat

/-- Signed version of `theoremC_irr_lemma36_degree_data`, expressed using
the absolute value of the signed irreducible degree. -/
private lemma theoremC_pmIrr_lemma36_degree_data
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hm : 4 ≤ (c.U.subgroupOf c.H0).index)
    (hKbot : c.K ≠ ⊥) (hsimple : IsSimpleGroup G)
    {psi : ClassFunction G} (hpsi : IsPMIrr G psi)
    (hpsiOne : psi ≠ (1 : ClassFunction G))
    (hpsiNegOne : psi ≠ -(1 : ClassFunction G))
    (hB : (BOf c h12 psi).Nonempty)
    (horbit : ∀ nu : Irr (↥c.H0), nu ∈ BOf c h12 psi →
      conjChar c.H0 (s_normalizes_H0 c h12) nu.1 ∈ orbit c.H0 c.U nu.1) :
    ∃ alpha : Irr (↥c.U), ∃ a : ℕ,
      ¬ c.K ≤ (charKernel
        (isCharacter_of_isIrreducibleCharacter alpha.2)).map
          (Subgroup.subtype c.U) ∧
      1 ≤ a ∧ (alpha.1 1).re = (a : ℝ) ∧
      (8 * (a : ℝ) + 1) ≤ |(psi 1).re| := by
  rcases hpsi with hpos | hneg
  · rcases theoremC_irr_lemma36_degree_data c h12 hSC hm hKbot hsimple
      hpos hpsiOne hB horbit with ⟨alpha, a, hKalpha, ha, halpha, hbound⟩
    refine ⟨alpha, a, hKalpha, ha, halpha, ?_⟩
    have hnonneg : 0 ≤ (psi 1).re :=
      le_trans (by norm_num) (theoremC_irr_degree_re_ge_one ⟨psi, hpos⟩)
    rwa [abs_of_nonneg hnonneg]
  · have hnegOne : -psi ≠ (1 : ClassFunction G) := by
      intro h
      apply hpsiNegOne
      have h' := congrArg Neg.neg h
      simpa using h'
    have hBneg : (BOf c h12 (-psi)).Nonempty := by
      rw [theoremC_BOf_neg]
      exact hB
    have horbitNeg : ∀ nu : Irr (↥c.H0), nu ∈ BOf c h12 (-psi) →
        conjChar c.H0 (s_normalizes_H0 c h12) nu.1 ∈ orbit c.H0 c.U nu.1 := by
      intro nu hnu
      apply horbit nu
      rwa [theoremC_BOf_neg] at hnu
    rcases theoremC_irr_lemma36_degree_data c h12 hSC hm hKbot hsimple
      hneg hnegOne hBneg horbitNeg with
      ⟨alpha, a, hKalpha, ha, halpha, hbound⟩
    refine ⟨alpha, a, hKalpha, ha, halpha, ?_⟩
    have hnonpos : (psi 1).re ≤ 0 := by
      have hge := theoremC_irr_degree_re_ge_one ⟨-psi, hneg⟩
      norm_num at hge
      linarith
    rw [abs_of_nonpos hnonpos]
    norm_num at hbound ⊢
    exact hbound

/-- Equation (3) from the repaired internal-product interface.  A base
constituent fixed by either distinguished reflection restricts irreducibly
to `B`; its doubled degree therefore satisfies both bounds used in
equations (3) and (5). -/
private lemma theoremC_reflection_fixed_degree_bounds
    (c : Hyp11 G) [Hyp11KData c]
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (hUint : (c.B1 ⊓ c.K2) ⊓ (c.B ⊔ c.K) = ⊥)
    (hUcomm : ⁅c.B1 ⊓ c.K2, c.B ⊔ c.K⁆ = ⊥)
    (hB' : ⁅c.B, c.B⁆ ≠ c.B)
    {ν : Irr (↥c.H0)} {α : Irr (↥c.U)}
    (hreflection :
      conjIrrS c c.t1_mem_S α = α ∨ conjIrrS c c.t2_mem_S α = α)
    (hdegree : ν.1 1 = 2 * α.1 1) :
    (ν.1 1).re ≤ (Nat.card c.B : ℝ) ∧
      (ν.1 1).re ^ 2 ≤ 2 * (Nat.card c.B : ℝ) ∧
      |(ν.1 (tH0 c)).re| = (ν.1 1).re := by
  classical
  have hK : ∀ k : G, (hk : k ∈ c.K) →
      α.1 ⟨k, theoremC_K_le_U c hk⟩ = α.1 1 := by
    rcases hreflection with hfix1 | hfix2
    · exact theoremC_reflection_fixed_char_kills_K c c.t1_mem_S
        c.t1_not_mem_S0 α hfix1
    · exact theoremC_reflection_fixed_char_kills_K c c.t2_mem_S
        c.t2_not_mem_S0 α hfix2
  let βfun : ClassFunction (↥c.B) := fun b =>
    α.1 ⟨(b : G), theoremC_B_le_U c b.2⟩
  have hβirr : IsIrreducibleCharacter βfun :=
    theoremC_internalProduct_restrict_B_irr c hU hUint hUcomm α hK
  let β : Irr (↥c.B) := ⟨βfun, hβirr⟩
  have hβone : β.1 1 = α.1 1 := by
    change α.1 ⟨(1 : G), theoremC_B_le_U c c.B.one_mem⟩ = α.1 1
    apply congrArg α.1
    apply Subtype.ext
    rfl
  have hβbound := theoremC_two_beta_sq_le_card hβirr
    (theoremC_B_card_odd c) (theoremC_B_card_ge_two c hB')
  change 2 * (β.1 1).re ^ 2 ≤ (Nat.card (↥c.B) : ℝ) at hβbound
  rw [hβone] at hβbound
  have hαpos : (1 : ℝ) ≤ (α.1 1).re := theoremC_irr_degree_re_ge_one α
  have hdegreeRe : (ν.1 1).re = 2 * (α.1 1).re := by
    rw [hdegree]
    norm_num
  have hlinear : (ν.1 1).re ≤ (Nat.card c.B : ℝ) := by
    rw [hdegreeRe]
    nlinarith
  have hsquare : (ν.1 1).re ^ 2 ≤ 2 * (Nat.card c.B : ℝ) := by
    rw [hdegreeRe]
    nlinarith
  have hsign := char_apply_central_sign (G := ↥c.H0) (t := tH0 c)
    (by simpa [tH0] using t_central_H0' c)
    (by simpa [tH0] using t_H0_sq c) ν.2
  have hνpos : (0 : ℝ) ≤ (ν.1 1).re :=
    le_trans (by norm_num) (theoremC_irr_degree_re_ge_one ν)
  have habs : |(ν.1 (tH0 c)).re| = (ν.1 1).re := by
    rcases hsign with hpos | hneg
    · rw [hpos]
      exact abs_of_nonneg hνpos
    · rw [hneg, Complex.neg_re, abs_neg]
      exact abs_of_nonneg hνpos
  exact ⟨hlinear, hsquare, habs⟩

/-- Uniform equation-(3)/(5) bounds for every `ν ≠ κ₁` in `B(χ₁)`.
This wrapper is valid in both the fixed and exceptional nonfixed orbit
configurations. -/
private lemma theoremC_chi1_other_degree_bounds
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (hUint : (c.B1 ⊓ c.K2) ⊓ (c.B ⊔ c.K) = ⊥)
    (hUcomm : ⁅c.B1 ⊓ c.K2, c.B ⊔ c.K⁆ = ⊥)
    (hB' : ⁅c.B, c.B⁆ ≠ c.B)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    {χ1 χ2 : ClassFunction G} (hχ1 : IsPMIrr G χ1)
    (hκ1tilde : tildeNu c h12 ⟨κ1, hκ1lin.1⟩ = χ1 + χ2)
    (hpairκ1 : scalarProduct G χ1 (tildeNu c h12 ⟨κ1, hκ1lin.1⟩) = 1)
    (hκ1fix : conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1)
    (horbitκ1 : (orbit c.H0 c.U κ1).card = (c.U.subgroupOf c.H0).index)
    (hS8 : Nat.card (↥(c.S : Subgroup G)) ≠ 4)
    {ν : Irr (↥c.H0)} (hνB : ν ∈ BOf c h12 χ1)
    (hνκ : ν ≠ ⟨κ1, hκ1lin.1⟩) :
    (ν.1 1).re ≤ (Nat.card c.B : ℝ) ∧
      (ν.1 1).re ^ 2 ≤ 2 * (Nat.card c.B : ℝ) ∧
      |(ν.1 (tH0 c)).re| = (ν.1 1).re := by
  rcases theoremC_chi1_reflection_fixed_data c h12 hSC hκ1lin hχ1 hκ1tilde
      hpairκ1 hκ1fix horbitκ1 hS8 hνB hνκ with
    ⟨α, hreflection, _hrestrict, hdegree⟩
  exact theoremC_reflection_fixed_degree_bounds c hU hUint hUcomm hB'
    hreflection hdegree

/-- Equation (4), together with the exact erased-sum identity used to
specialize equation (5) when `|B(χ₁)| = 2`. -/
private lemma theoremC_eq4
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (hUint : (c.B1 ⊓ c.K2) ⊓ (c.B ⊔ c.K) = ⊥)
    (hUcomm : ⁅c.B1 ⊓ c.K2, c.B ⊔ c.K⁆ = ⊥)
    (hB' : ⁅c.B, c.B⁆ ≠ c.B)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1S0 : ∀ x : ↥c.H0, (x : G) ∈ c.S0 → κ1 x = 1)
    {χ1 χ2 : ClassFunction G} (hχ1 : IsPMIrr G χ1)
    (hκ1tilde : tildeNu c h12 ⟨κ1, hκ1lin.1⟩ = χ1 + χ2)
    (hpairκ1 : scalarProduct G χ1 (tildeNu c h12 ⟨κ1, hκ1lin.1⟩) = 1)
    (hκ1fix : conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1)
    (horbitκ1 : (orbit c.H0 c.U κ1).card = (c.U.subgroupOf c.H0).index)
    (hS8 : Nat.card (↥(c.S : Subgroup G)) ≠ 4) :
    (χ1 c.t - 1).re =
        ∑ ν ∈ (BOf c h12 χ1).erase ⟨κ1, hκ1lin.1⟩,
          (scalarProduct G χ1 (tildeNu c h12 ν) * ν.1 (tH0 c)).re ∧
      |(χ1 c.t - 1).re| ≤
        (((BOf c h12 χ1).card - 1 : ℕ) : ℝ) * (Nat.card c.B : ℝ) := by
  classical
  let κ1Irr : Irr (↥c.H0) := ⟨κ1, hκ1lin.1⟩
  let others : Finset (Irr (↥c.H0)) := (BOf c h12 χ1).erase κ1Irr
  let term : Irr (↥c.H0) → ℂ := fun ν =>
    scalarProduct G χ1 (tildeNu c h12 ν) * ν.1 (tH0 c)
  have hκ1B : κ1Irr ∈ BOf c h12 χ1 := by
    rw [BOf_mem_iff]
    simpa [κ1Irr] using (show scalarProduct G χ1
      (tildeNu c h12 ⟨κ1, hκ1lin.1⟩) ≠ 0 by rw [hpairκ1]; norm_num)
  have htT : c.t ∈ c.T := by
    rw [Hyp11.T]
    exact ⟨S0_le_H0 c c.t_mem_S0, t_not_mem_U c⟩
  have hχsum := (lemma_2_4 c h12 hχ1).1 c.t htT (S0_le_H0 c c.t_mem_S0)
  change χ1 c.t = ∑ ν ∈ BOf c h12 χ1, term ν at hχsum
  have hκ1t : κ1 (tH0 c) = 1 :=
    hκ1S0 (tH0 c) (by simpa [tH0] using c.t_mem_S0)
  have hκterm : term κ1Irr = 1 := by
    dsimp [term, κ1Irr]
    rw [hpairκ1]
    simpa [tH0] using hκ1t
  have hcomplex : χ1 c.t - 1 = ∑ ν ∈ others, term ν := by
    rw [← Finset.sum_erase_add (s := BOf c h12 χ1)
      (f := term) (a := κ1Irr) hκ1B] at hχsum
    change χ1 c.t =
      (∑ ν ∈ others, term ν) + term κ1Irr at hχsum
    rw [hκterm] at hχsum
    linear_combination hχsum
  have hreal : (χ1 c.t - 1).re = ∑ ν ∈ others, (term ν).re := by
    have h := congrArg Complex.re hcomplex
    have hmap : (∑ ν ∈ others, term ν).re =
        ∑ ν ∈ others, (term ν).re := by
      simp
    rwa [hmap] at h
  have htermAbs : ∀ ν ∈ others, |(term ν).re| = (ν.1 1).re := by
    intro ν hν
    have hνerase := Finset.mem_erase.mp hν
    have hbounds := theoremC_chi1_other_degree_bounds c h12 hSC hU hUint hUcomm
      hB' hκ1lin hχ1 hκ1tilde hpairκ1 hκ1fix horbitκ1 hS8
      hνerase.2 hνerase.1
    rcases BOf_scalar_eq_pm_one c h12 hχ1 hνerase.2 with hplus | hminus
    · dsimp [term]
      rw [hplus]
      norm_num
      exact hbounds.2.2
    · dsimp [term]
      rw [hminus]
      norm_num
      simpa [abs_neg] using hbounds.2.2
  have htriangle : |(χ1 c.t - 1).re| ≤
      ∑ ν ∈ others, (ν.1 1).re := by
    rw [hreal]
    calc
      |∑ ν ∈ others, (term ν).re| ≤
          ∑ ν ∈ others, |(term ν).re| :=
        Finset.abs_sum_le_sum_abs (fun ν => (term ν).re) others
      _ = ∑ ν ∈ others, (ν.1 1).re := by
        refine Finset.sum_congr rfl ?_
        intro ν hν
        exact htermAbs ν hν
  have hsumBound : (∑ ν ∈ others, (ν.1 1).re) ≤
      (others.card : ℝ) * (Nat.card c.B : ℝ) := by
    calc
      (∑ ν ∈ others, (ν.1 1).re) ≤
          ∑ _ν ∈ others, (Nat.card c.B : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro ν hν
        have hνerase := Finset.mem_erase.mp hν
        exact (theoremC_chi1_other_degree_bounds c h12 hSC hU hUint hUcomm
          hB' hκ1lin hχ1 hκ1tilde hpairκ1 hκ1fix horbitκ1 hS8
          hνerase.2 hνerase.1).1
      _ = (others.card : ℝ) * (Nat.card c.B : ℝ) := by
        simp [nsmul_eq_mul]
  have hcardOthers : others.card = (BOf c h12 χ1).card - 1 := by
    dsimp [others]
    exact Finset.card_erase_of_mem hκ1B
  refine ⟨?_, ?_⟩
  · simpa [κ1Irr, others, term] using hreal
  · calc
      |(χ1 c.t - 1).re| ≤ ∑ ν ∈ others, (ν.1 1).re := htriangle
      _ ≤ (others.card : ℝ) * (Nat.card c.B : ℝ) := hsumBound
      _ = (((BOf c h12 χ1).card - 1 : ℕ) : ℝ) *
          (Nat.card c.B : ℝ) := by rw [hcardOthers]

/-- Equation (5): when `B(χ₁)` has exactly two members, equation (4) has a
single remaining term; its squared degree bound gives `x² ≤ 2|B|`. -/
private lemma theoremC_eq5_of_card_two
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (hUint : (c.B1 ⊓ c.K2) ⊓ (c.B ⊔ c.K) = ⊥)
    (hUcomm : ⁅c.B1 ⊓ c.K2, c.B ⊔ c.K⁆ = ⊥)
    (hB' : ⁅c.B, c.B⁆ ≠ c.B)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1S0 : ∀ y : ↥c.H0, (y : G) ∈ c.S0 → κ1 y = 1)
    {χ1 χ2 : ClassFunction G} (hχ1 : IsPMIrr G χ1)
    (hκ1tilde : tildeNu c h12 ⟨κ1, hκ1lin.1⟩ = χ1 + χ2)
    (hpair1 : scalarProduct G χ1
      (tildeNu c h12 ⟨κ1, hκ1lin.1⟩) = 1)
    (hκ1fix : conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1)
    (horbitκ1 : (orbit c.H0 c.U κ1).card =
      (c.U.subgroupOf c.H0).index)
    (hS8 : Nat.card (↥(c.S : Subgroup G)) ≠ 4)
    {x : ℝ} (hχ1t : χ1 c.t = 1 + (x : ℂ))
    (hcard : (BOf c h12 χ1).card = 2) :
    x ^ 2 ≤ 2 * (Nat.card c.B : ℝ) := by
  classical
  let κ1Irr : Irr (↥c.H0) := ⟨κ1, hκ1lin.1⟩
  let others : Finset (Irr (↥c.H0)) := (BOf c h12 χ1).erase κ1Irr
  have hκ1B : κ1Irr ∈ BOf c h12 χ1 := by
    rw [BOf_mem_iff]
    simpa [κ1Irr] using (show scalarProduct G χ1
      (tildeNu c h12 ⟨κ1, hκ1lin.1⟩) ≠ 0 by
        rw [hpair1]
        norm_num)
  have hotherscard : others.card = 1 := by
    dsimp [others]
    rw [Finset.card_erase_of_mem hκ1B, hcard]
  rcases Finset.card_eq_one.mp hotherscard with ⟨nu, hothers⟩
  have hnumem : nu ∈ others := by rw [hothers]; simp
  have hnuerase := Finset.mem_erase.mp hnumem
  have hbounds := theoremC_chi1_other_degree_bounds c h12 hSC hU hUint hUcomm
    hB' hκ1lin hχ1 hκ1tilde hpair1 hκ1fix horbitκ1 hS8
    hnuerase.2 hnuerase.1
  have heq := (theoremC_eq4 c h12 hSC hU hUint hUcomm hB'
    hκ1lin hκ1S0 hχ1 hκ1tilde hpair1 hκ1fix horbitκ1 hS8).1
  have hxre : (χ1 c.t - 1).re = x := by
    rw [hχ1t]
    norm_num
  rw [hxre] at heq
  have hxterm : x =
      (scalarProduct G χ1 (tildeNu c h12 nu) * nu.1 (tH0 c)).re := by
    change x = ∑ eta ∈ others,
      (scalarProduct G χ1 (tildeNu c h12 eta) * eta.1 (tH0 c)).re at heq
    rw [hothers] at heq
    simpa only [Finset.sum_singleton] using heq
  have hxabs : |x| = (nu.1 1).re := by
    rcases BOf_scalar_eq_pm_one c h12 hχ1 hnuerase.2 with hplus | hminus
    · rw [hxterm, hplus]
      norm_num
      exact hbounds.2.2
    · rw [hxterm, hminus]
      norm_num
      simpa [abs_neg] using hbounds.2.2
  apply theoremC_x_sq_le_two_mul_B_of_one_term (a := (nu.1 1).re)
  · rw [hxabs, abs_of_nonneg
      (le_trans (by norm_num) (theoremC_irr_degree_re_ge_one nu))]
  · exact hbounds.2.1

/-- A positive irreducible constituent of a singleton Section-4 vertex that
is nonprincipal has degree at least five, by Lemma 3.6. -/
private lemma theoremC_S4_irr_degree_re_ge_five (c : Hyp11 G) [Hyp11KData c]
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    (hK : c.K ≠ ⊥) (hsimple : IsSimpleGroup G)
    {kappa : Irr (↥c.H0)}
    (hkappas : conjChar c.H0 (s_normalizes_H0 c h12) kappa.1 = kappa.1)
    (hkappat : kappa.1 (tH0 c) = kappa.1 1)
    (chi : Irr G)
    (hpair : scalarProduct G chi.1 (deltaNu c h12 kappa) ≠ 0)
    (hchiOne : chi.1 ≠ (1 : ClassFunction G)) :
    (5 : ℝ) ≤ (chi.1 1).re := by
  classical
  have hkappaBPrime : kappa ∈ BPrimeOf c h12 chi.1 := by
    rw [BPrime_mem_iff_scalar]
    exact ⟨hkappas, hkappat, hpair⟩
  have hBPrime : (BPrimeOf c h12 chi.1).Nonempty :=
    ⟨kappa, hkappaBPrime⟩
  have hB : (BOf c h12 chi.1).Nonempty := by
    simp only [BenderGlauberman.deltaNu] at hpair
    rw [scalarProduct_sub_right] at hpair
    by_cases hfirst : scalarProduct G chi.1 (tildeNu c h12 kappa) = 0
    · refine ⟨lambdaTwoMul c h12 kappa, (BOf_mem_iff c h12 chi.1 _).2 ?_⟩
      intro hsecond
      exact hpair (by rw [hfirst, hsecond]; norm_num)
    · exact ⟨kappa, (BOf_mem_iff c h12 chi.1 kappa).2 hfirst⟩
  have horbit : ∀ nu : Irr (↥c.H0), nu ∈ BOf c h12 chi.1 →
      conjChar c.H0 (s_normalizes_H0 c h12) nu.1 ∈ orbit c.H0 c.U nu.1 := by
    intro nu hnu
    have hfixed := BOf_mem_fixed_of_BPrime_nonempty c h12 hSC hS4
      (Or.inl chi.2) hBPrime hnu
    rw [hfixed]
    refine Finset.mem_image.mpr ⟨1, Finset.mem_univ _, ?_⟩
    ext x
    simp [LambdaChar]
  have hkernel := theoremC_simple_K_not_le_charKernel c hK hsimple chi hchiOne
  rcases theoremC_lemma36 c h12 hSC chi hB hkernel horbit with
    ⟨alpha, _hKalpha, hbound⟩
  have hindex : (c.U.subgroupOf c.H0).index = 2 := by
    have hS0card : Nat.card (↥(c.S0 : Subgroup G)) = 2 := by
      have h := c.S_index_two
      change Nat.card (↥(c.S : Subgroup G)) = 4 at hS4
      rw [hS4] at h
      omega
    rw [U_index_eq_S0_card c h12, hS0card]
  have halpha : (1 : ℝ) ≤ (alpha.1 1).re := theoremC_irr_degree_re_ge_one alpha
  have hfour : (4 : ℝ) < (chi.1 1).re := by
    rw [hindex] at hbound
    norm_num at hbound
    nlinarith
  rcases chi.2 with ⟨n, rho, hrho, hchi⟩
  have hdegree : chi.1 1 = (n : ℂ) := by
    rw [hchi, Representation.char_one]
    norm_num
  have hn : 4 < n := by
    rw [hdegree] at hfour
    norm_num at hfour
    exact_mod_cast hfour
  rw [hdegree]
  norm_num
  exact_mod_cast (by omega : 5 ≤ n)

/-- Signed form of the Section-4 Lemma-3.6 bound.  The value `psi(t)=1`
rules out a negatively signed principal character, while `psi ≠ 1` rules out
the positive principal character. -/
private lemma theoremC_S4_pmIrr_abs_degree_ge_five (c : Hyp11 G) [Hyp11KData c]
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    (hK : c.K ≠ ⊥) (hsimple : IsSimpleGroup G)
    {kappa : Irr (↥c.H0)}
    (hkappas : conjChar c.H0 (s_normalizes_H0 c h12) kappa.1 = kappa.1)
    (hkappat : kappa.1 (tH0 c) = kappa.1 1)
    {psi : ClassFunction G} (hpsi : IsPMIrr G psi)
    (hpair : scalarProduct G psi (deltaNu c h12 kappa) = 1)
    (hpsit : psi c.t = 1) (hpsiOne : psi ≠ (1 : ClassFunction G)) :
    (5 : ℝ) ≤ |(psi 1).re| := by
  classical
  rcases hpsi with hpos | hneg
  · let chi : Irr G := ⟨psi, hpos⟩
    have hbound := theoremC_S4_irr_degree_re_ge_five c h12 hSC hS4 hK hsimple
      hkappas hkappat chi (by rw [hpair]; norm_num) (by simpa [chi] using hpsiOne)
    have hnonneg : 0 ≤ (psi 1).re := le_trans (by norm_num) hbound
    simpa [abs_of_nonneg hnonneg] using hbound
  · let chi : Irr G := ⟨-psi, hneg⟩
    have hchiOne : chi.1 ≠ (1 : ClassFunction G) := by
      intro hEq
      have ht := congrFun hEq c.t
      change (-psi) c.t = (1 : ClassFunction G) c.t at ht
      rw [Pi.neg_apply, hpsit] at ht
      norm_num at ht
    have hpairChi : scalarProduct G chi.1 (deltaNu c h12 kappa) ≠ 0 := by
      change scalarProduct G (-psi) (deltaNu c h12 kappa) ≠ 0
      rw [scalarProduct_neg_left, hpair]
      norm_num
    have hbound := theoremC_S4_irr_degree_re_ge_five c h12 hSC hS4 hK hsimple
      hkappas hkappat chi hpairChi hchiOne
    change (5 : ℝ) ≤ |(psi 1).re|
    change (5 : ℝ) ≤ ((-psi) 1).re at hbound
    rw [Pi.neg_apply, Complex.neg_re] at hbound
    have hnonpos : (psi 1).re ≤ 0 := by nlinarith
    rw [abs_of_nonpos hnonpos]
    exact hbound

/-- The principal character has zero pairing with a nontrivial linear
vertex.  The two terms in `δκ = (κ - λ₂κ)^G` are both nonprincipal; the
second is separated from the principal one by its value `-1` at the chosen
generator of `S₀`. -/
private lemma theoremC_delta_linear_principal_pairing_zero (c : Hyp11 G) [Hyp11KData c]
    (h12 : Hyp12 c)
    {kappa : ClassFunction (↥c.H0)} (hkappalin : IsLinearCharacter kappa)
    (hkappaS0 : ∀ x : ↥c.H0, (x : G) ∈ c.S0 → kappa x = 1)
    (hkappaOne : kappa ≠ (1 : ClassFunction (↥c.H0))) :
    scalarProduct G (1 : ClassFunction G)
      (deltaNu c h12 ⟨kappa, hkappalin.1⟩) = 0 := by
  classical
  let kappaIrr : Irr (↥c.H0) := ⟨kappa, hkappalin.1⟩
  let lambdaIrr : Irr (↥c.H0) := lambdaTwoMul c h12 kappaIrr
  have hkappaIrr : IsIrreducibleCharacter kappaIrr.1 := kappaIrr.2
  have hlambdaIrr : IsIrreducibleCharacter lambdaIrr.1 := lambdaIrr.2
  have hkappaNe : kappaIrr.1 ≠ (1 : ClassFunction (↥c.H0)) := by
    simpa [kappaIrr] using hkappaOne
  let r0H0 : ↥c.H0 :=
    ⟨S0_generator c, S0_le_H0 c (S0_generator_mem_S0 c)⟩
  have hκr0 : kappaIrr.1 r0H0 = 1 := by
    simpa [kappaIrr, r0H0] using hkappaS0 r0H0 (S0_generator_mem_S0 c)
  have hl2r0 : ((lambdaTwo c h12).1 r0H0 : ℂ) = -1 := by
    simpa [r0H0] using lambdaTwo_val_r0_eq_neg_one c h12
  have hlambdaNe : lambdaIrr.1 ≠ (1 : ClassFunction (↥c.H0)) := by
    intro heq
    have hr0 := congrFun heq r0H0
    dsimp [lambdaIrr, lambdaTwoMul] at hr0
    change ((lambdaTwo c h12).1 r0H0 : ℂ) * kappaIrr.1 r0H0 = 1 at hr0
    rw [hl2r0, hκr0] at hr0
    norm_num at hr0
  have hprodIrr : IsIrreducibleCharacter
      (LambdaChar (lambdaTwo c h12).1 * kappaIrr.1) :=
    isIrreducibleCharacter_mul_linear
      (isLinearCharacter_of_hom (lambdaTwo c h12).1) hkappaIrr
  have hprodNe : LambdaChar (lambdaTwo c h12).1 * kappaIrr.1 ≠
      (1 : ClassFunction (↥c.H0)) := by
    simpa [lambdaIrr, lambdaTwoMul] using hlambdaNe
  have hsub : scalarProduct (↥c.H0) (1 : ClassFunction (↥c.H0))
      (kappaIrr.1 - LambdaChar (lambdaTwo c h12).1 * kappaIrr.1) = 0 := by
    rw [scalarProduct_sub_right,
      scalarProduct_irr_ite (isIrreducibleCharacter_one (↥c.H0)) hkappaIrr,
      scalarProduct_irr_ite (isIrreducibleCharacter_one (↥c.H0)) hprodIrr]
    rw [if_neg hkappaNe.symm, if_neg hprodNe.symm]
    norm_num
  have honeClass : IsClassFunction (1 : ClassFunction G) :=
    irreducibleCharacter_isClassFunction (isIrreducibleCharacter_one G)
  have hres := scalarProduct_restrict_induced c.H0 honeClass
    (kappaIrr.1 - LambdaChar (lambdaTwo c h12).1 * kappaIrr.1)
  change scalarProduct G (1 : ClassFunction G)
      (deltaNu c h12 kappaIrr) = 0
  rw [deltaNu_eq_induced]
  rw [← hres]
  have honeRes : (fun x : ↥c.H0 => (1 : ClassFunction G) (x : G)) =
      (1 : ClassFunction (↥c.H0)) := by rfl
  rw [honeRes]
  exact hsub

/-- The nonreal linear orbit representative used in Lemma 2.5 satisfies
the required exact value at `t`.  Lemma 3.4 removes the exceptional
Coherence branch because its `Λ`-orbit is full. -/
private lemma theoremC_lambda3_tilde_t
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (l3 : LambdaHom c.H0 c.U) (hl3 : l3 ^ 2 ≠ 1) :
    tildeNu c h12
      ⟨LambdaChar l3.1, (isLinearCharacter_of_hom l3.1).1⟩ c.t =
        2 * (l3.1 (tH0 c) : ℂ) := by
  classical
  let nu : Irr (↥c.H0) :=
    ⟨LambdaChar l3.1, (isLinearCharacter_of_hom l3.1).1⟩
  have hnus : conjChar c.H0 (s_normalizes_H0 c h12) nu.1 ≠ nu.1 := by
    simpa [nu, lambdaIrr] using lambda_not_fixed_of_sq_ne_one c h12 hl3
  have hchi : IsPMIrr G (tildeNu c h12 nu) :=
    signed_irr_of_nonfixed c h12 hnus
  have hnorm : normSq G (tildeNu c h12 nu) = 1 := by
    rw [tildeNu_norm]
    simp [hnus]
  have hself : scalarProduct G (tildeNu c h12 nu)
      (tildeNu c h12 nu) = 1 := by
    simpa [normSq] using hnorm
  have hnuB : nu ∈ BOf c h12 (tildeNu c h12 nu) := by
    rw [BOf_mem_iff]
    exact ne_of_eq_of_ne hself (by norm_num)
  have hfull : (orbit c.H0 c.U nu.1).card =
      (c.U.subgroupOf c.H0).index := by
    have h := theoremC_kappa_orbit_card c h12
      (isLinearCharacter_of_hom (1 : ↥c.H0 →* ℂˣ)) l3
    have hkappa : kappa c (1 : ClassFunction (↥c.H0)) l3 =
        LambdaChar l3.1 := by
      ext x
      simp [kappa, LambdaChar]
    change (orbit c.H0 c.U
      (kappa c (1 : ClassFunction (↥c.H0)) l3)).card =
        (c.U.subgroupOf c.H0).index at h
    rw [hkappa] at h
    simpa [nu] using h
  exact (lemma_3_4 c h12 hSC hchi hnuB hnus (Or.inr hfull)).2

/-- Equation (6): Lemma 2.2 for `μ = κ₁`, `ν = κ₃` reduces the
`Irr(G)`-sum to the three signed constituents `χ₁, χ₂, χ₃`:
`2k²/|G:H| = χ₁(t)²/χ₁(1) + χ₂(t)²/χ₂(1) − χ₃(t)²/χ₃(1)`. -/
private lemma theoremC_eq6 (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1S0 : ∀ x : ↥c.H0, (x : G) ∈ c.S0 → κ1 x = 1)
    (hκ1comm : ∀ x : ↥c.H0, (x : G) ∈ ⁅(c.S : Subgroup G), c.U⁆ → κ1 x = 1)
    (l3 : LambdaHom c.H0 c.U) (hl3 : l3 ^ 2 ≠ 1)
    {χ1 χ2 χ3 : ClassFunction G} (hχ1 : IsPMIrr G χ1)
    (hχ2 : IsPMIrr G χ2) (hχ3 : IsPMIrr G χ3)
    (hκ1tilde : tildeNu c h12 ⟨κ1, hκ1lin.1⟩ = χ1 + χ2)
    (hκ3tilde : tildeNu c h12 ⟨kappa c κ1 l3, (kappa_isLinear c h12 hκ1lin l3).1⟩ = χ3) :
    (2 * c.k ^ 2 : ℂ) / (c.H.index : ℂ) =
      χ1 c.t ^ 2 / χ1 1 + χ2 c.t ^ 2 / χ2 1 - χ3 c.t ^ 2 / χ3 1 := by
  classical
  let κ1Irr : Irr (↥c.H0) := ⟨κ1, hκ1lin.1⟩
  let κ3Irr : Irr (↥c.H0) :=
    ⟨kappa c κ1 l3, (kappa_isLinear c h12 hκ1lin l3).1⟩
  have hEq : κ1Irr.1 ∈ orbit c.H0 c.U κ3Irr.1 := by
    dsimp [κ3Irr]
    refine Finset.mem_image.mpr ⟨l3⁻¹, Finset.mem_univ _, ?_⟩
    ext x
    change (LambdaChar (l3⁻¹).1 * (LambdaChar l3.1 * κ1)) x = κ1 x
    simp [LambdaChar]
  have h2 := lemma_2_2 c h12 (μ := κ1Irr) (ν := κ3Irr) (hEq := hEq)
    (κ1 := κ1) hκ1lin hκ1S0 hκ1comm
  have hV : lemma_2_2_V c κ1Irr.1 κ3Irr.1 = (2 * c.k ^ 2 : ℂ) := by
    exact h2.2.1 rfl ⟨l3, hl3, rfl⟩
  have hind := tildeNu_ind c h12 hEq
  have hVexp : lemma_2_2_V c κ1Irr.1 κ3Irr.1 =
      (c.H.index : ℂ) * (∑ χ : Irr G,
        (χ.1 c.t ^ 2 / χ.1 1) * scalarProduct G χ.1 (χ1 + χ2 - χ3)) := by
    unfold lemma_2_2_V
    congr 1
    refine Finset.sum_congr rfl ?_
    intro χ hχ
    rw [hind]
    rw [hκ1tilde, hκ3tilde]
  have hmain : (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
      scalarProduct G χ.1 (χ1 + χ2 - χ3)) =
      χ1 c.t ^ 2 / χ1 1 + χ2 c.t ^ 2 / χ2 1 - χ3 c.t ^ 2 / χ3 1 := by
    calc
      (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) * scalarProduct G χ.1 (χ1 + χ2 - χ3))
          = (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
              (scalarProduct G χ.1 χ1 + scalarProduct G χ.1 χ2 -
                scalarProduct G χ.1 χ3)) := by
              refine Finset.sum_congr rfl ?_
              intro χ hχ
              rw [scalarProduct_sub_right, scalarProduct_add_right]
      _ = (∑ χ : Irr G, ((χ.1 c.t ^ 2 / χ.1 1) * scalarProduct G χ.1 χ1 +
          (χ.1 c.t ^ 2 / χ.1 1) * scalarProduct G χ.1 χ2 -
          (χ.1 c.t ^ 2 / χ.1 1) * scalarProduct G χ.1 χ3)) := by
              refine Finset.sum_congr rfl ?_
              intro χ hχ
              rw [mul_sub, mul_add]
      _ = (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) * scalarProduct G χ.1 χ1) +
          (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) * scalarProduct G χ.1 χ2) -
          (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) * scalarProduct G χ.1 χ3) := by
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = χ1 c.t ^ 2 / χ1 1 + χ2 c.t ^ 2 / χ2 1 - χ3 c.t ^ 2 / χ3 1 := by
              rw [theoremC_signed_irr_t_sum (t := c.t) (ψ := χ1) hχ1,
                theoremC_signed_irr_t_sum (t := c.t) (ψ := χ2) hχ2,
                theoremC_signed_irr_t_sum (t := c.t) (ψ := χ3) hχ3]
  have hV2 : (c.H.index : ℂ) *
      (χ1 c.t ^ 2 / χ1 1 + χ2 c.t ^ 2 / χ2 1 - χ3 c.t ^ 2 / χ3 1) =
      (2 * c.k ^ 2 : ℂ) := by
    calc
      (c.H.index : ℂ) *
          (χ1 c.t ^ 2 / χ1 1 + χ2 c.t ^ 2 / χ2 1 - χ3 c.t ^ 2 / χ3 1)
          = (c.H.index : ℂ) * (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
              scalarProduct G χ.1 (χ1 + χ2 - χ3)) := by rw [hmain]
      _ = lemma_2_2_V c κ1Irr.1 κ3Irr.1 := hVexp.symm
      _ = (2 * c.k ^ 2 : ℂ) := hV
  have hindex_ne : (c.H.index : ℂ) ≠ 0 := by
    rw [Subgroup.index_eq_card]
    exact_mod_cast (Nat.card_pos (α := G ⧸ c.H)).ne'
  field_simp [hindex_ne]
  exact hV2.symm

/-- Real form of equation (6), with the signed involution values and signed
degrees normalized for the inequality-(7) estimate. -/
private lemma theoremC_eq6_real
    (c : Hyp11 G) [Hyp11KData c]
    {χ1 χ2 χ3 : ClassFunction G}
    (hχ1 : IsPMIrr G χ1) (hχ2 : IsPMIrr G χ2) (hχ3 : IsPMIrr G χ3)
    {x : ℝ}
    (hχ1t : χ1 c.t = 1 + (x : ℂ))
    (hχ2t : χ2 c.t = 1 - (x : ℂ))
    (hχ3t : χ3 c.t = 2 ∨ χ3 c.t = -2)
    (hEq6 : 2 * (c.k : ℂ) ^ 2 / (c.H.index : ℂ) =
      χ1 c.t ^ 2 / χ1 1 + χ2 c.t ^ 2 / χ2 1 - χ3 c.t ^ 2 / χ3 1) :
    (↑((2 * (c.k : ℚ) ^ 2) / c.H.index : ℚ) : ℝ) =
      (1 + x) ^ 2 / (χ1 1).re + (1 - x) ^ 2 / (χ2 1).re -
        4 / (χ3 1).re := by
  have hχ1real := theoremC_pmIrr_one_eq_real hχ1
  have hχ2real := theoremC_pmIrr_one_eq_real hχ2
  have hχ3real := theoremC_pmIrr_one_eq_real hχ3
  have hEq := hEq6
  rw [hχ1t, hχ2t, hχ1real, hχ2real, hχ3real] at hEq
  rcases hχ3t with hχ3t | hχ3t
  · rw [hχ3t] at hEq
    have hre := congrArg Complex.re hEq
    norm_num [pow_two, Complex.mul_re] at hre ⊢
    exact hre
  · rw [hχ3t] at hEq
    have hre := congrArg Complex.re hEq
    norm_num [pow_two, Complex.mul_re] at hre ⊢
    exact hre

/-- In the cardinality-three branch, equation (6), involution-value
integrality, and `2|K| ∣ k` force `2|K| ≤ |x|`. -/
private lemma theoremC_card_three_lower_bound
    {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c)
    (hcop : Nat.Coprime (Nat.card c.K) c.H.index)
    (hm : 4 ≤ (c.U.subgroupOf c.H0).index)
    {χ1 χ2 χ3 : ClassFunction G} (hχ1 : IsPMIrr G χ1)
    {x : ℝ}
    (hχ1t : χ1 c.t = 1 + (x : ℂ))
    (hχ2t : χ2 c.t = 1 - (x : ℂ))
    (hdeg12 : χ1 1 = χ2 1)
    (hdeg3 : χ3 1 = 2 * χ1 1)
    (hχ3t : χ3 c.t = 2 ∨ χ3 c.t = -2)
    (hEq6 : 2 * (c.k : ℂ) ^ 2 / (c.H.index : ℂ) =
      χ1 c.t ^ 2 / χ1 1 + χ2 c.t ^ 2 / χ2 1 - χ3 c.t ^ 2 / χ3 1) :
    (2 * Nat.card c.K : ℝ) ≤ |x| := by
  classical
  have hχ1ne : χ1 1 ≠ 0 := chi_one_ne_zero_of_isPMIrr hχ1
  have hindex_ne : (c.H.index : ℂ) ≠ 0 := by
    rw [Subgroup.index_eq_card]
    exact_mod_cast (Nat.card_pos (α := G ⧸ c.H)).ne'
  have hmainC :
      (c.k : ℂ) ^ 2 * χ1 1 = (x : ℂ) ^ 2 * (c.H.index : ℂ) := by
    rcases hχ3t with hχ3t | hχ3t
    · rw [hχ1t, hχ2t, ← hdeg12, hdeg3, hχ3t] at hEq6
      field_simp [hχ1ne, hindex_ne] at hEq6
      linear_combination hEq6 / 2
    · rw [hχ1t, hχ2t, ← hdeg12, hdeg3, hχ3t] at hEq6
      field_simp [hχ1ne, hindex_ne] at hEq6
      linear_combination hEq6 / 2
  rcases theoremC_pmIrr_one_int hχ1 with ⟨m, hmχ⟩
  rcases theoremC_pmIrr_involution_int hχ1 c.t_involution with ⟨a, ha⟩
  let z : ℤ := a - 1
  have hzC : (z : ℂ) = (x : ℂ) := by
    dsimp [z]
    rw [Int.cast_sub, ha, hχ1t]
    norm_num
  have hmainZ :
      (c.k : ℤ) ^ 2 * m = z ^ 2 * (c.H.index : ℤ) := by
    have hmainC' := hmainC
    rw [← hmχ, ← hzC] at hmainC'
    exact_mod_cast hmainC'
  have hkpos : 0 < c.k := by
    rw [Hyp11.k]
    have hk1 : 0 < c.k1 := by
      change 0 < ((centralizerIn c.H c.t1).subgroupOf c.H).index
      exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    omega
  have hmne : m ≠ 0 := by
    intro hm0
    apply hχ1ne
    rw [← hmχ, hm0]
    norm_num
  have hDk : 2 * Nat.card c.K ∣ c.k :=
    theoremC_two_mul_K_card_dvd_k c h12 hm
  have hindexOdd : Odd c.H.index := G_H_index_odd c
  have hcop2 : Nat.Coprime (2 * Nat.card c.K) c.H.index := by
    rw [Nat.coprime_mul_iff_left]
    exact ⟨Nat.coprime_two_left.mpr hindexOdd, hcop⟩
  have hlowerNat : 2 * Nat.card c.K ≤ z.natAbs :=
    theoremC_divisor_le_natAbs_of_square_eq hkpos hmne hDk hcop2 hmainZ
  have hlower : (2 * Nat.card c.K : ℝ) ≤ (z.natAbs : ℝ) := by
    exact_mod_cast hlowerNat
  have hzR : (z : ℝ) = x := by
    exact_mod_cast hzC
  calc
    (2 * Nat.card c.K : ℝ) ≤ (z.natAbs : ℝ) := hlower
    _ = |(z : ℝ)| := by simp [← Int.cast_abs]
    _ = |x| := by rw [hzR]

/-- The `|B(χ₁)| = 3` branch is impossible: equation (6) gives
`2|K| ≤ |x|`, equation (4) gives `|x| ≤ 2|B|`, while the
non-singleton `B(χ₁)` condition triggers the Frobenius hypothesis and
therefore `|B| < |K|`. -/
private lemma theoremC_card_three_false
    {G : Type u} [Group G] [Finite G]
    (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (hUint : (c.B1 ⊓ c.K2) ⊓ (c.B ⊔ c.K) = ⊥)
    (hUcomm : ⁅c.B1 ⊓ c.K2, c.B ⊔ c.K⁆ = ⊥)
    (hcop : Nat.Coprime (Nat.card c.K) c.H.index)
    (hB' : ⁅c.B, c.B⁆ ≠ c.B)
    (hFrob : c.U ≠ c.B ⊔ c.K →
      IsFrobeniusGroupWithKernel (c.B ⊔ c.K) c.K)
    (hS8 : Nat.card (↥(c.S : Subgroup G)) ≠ 4)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1S0 : ∀ y : ↥c.H0, (y : G) ∈ c.S0 → κ1 y = 1)
    (l3 : LambdaHom c.H0 c.U)
    {χ1 χ2 χ3 : ClassFunction G}
    (hχ1 : IsPMIrr G χ1) (hχ2 : IsPMIrr G χ2)
    (hκ1tilde : tildeNu c h12 ⟨κ1, hκ1lin.1⟩ = χ1 + χ2)
    (hκ3tilde : tildeNu c h12
      ⟨kappa c κ1 l3, (kappa_isLinear c h12 hκ1lin l3).1⟩ = χ3)
    (hpair1 : scalarProduct G χ1 (tildeNu c h12 ⟨κ1, hκ1lin.1⟩) = 1)
    (hpair2 : scalarProduct G χ2 (tildeNu c h12 ⟨κ1, hκ1lin.1⟩) = 1)
    (hκ1fix : conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1)
    (horbitκ1 : (orbit c.H0 c.U κ1).card =
      (c.U.subgroupOf c.H0).index)
    (hB3 : BOf c h12 χ3 =
      {⟨kappa c κ1 l3, (kappa_isLinear c h12 hκ1lin l3).1⟩,
        conjIrr c h12
          ⟨kappa c κ1 l3, (kappa_isLinear c h12 hκ1lin l3).1⟩})
    (hχ3t : χ3 c.t = 2 ∨ χ3 c.t = -2)
    {x : ℝ}
    (hχ1t : χ1 c.t = 1 + (x : ℂ))
    (hχ2t : χ2 c.t = 1 - (x : ℂ))
    (hEq6 : 2 * (c.k : ℂ) ^ 2 / (c.H.index : ℂ) =
      χ1 c.t ^ 2 / χ1 1 + χ2 c.t ^ 2 / χ2 1 - χ3 c.t ^ 2 / χ3 1)
    (hcard : (BOf c h12 χ1).card = 3) :
    False := by
  classical
  let κ1Irr : Irr (↥c.H0) := ⟨κ1, hκ1lin.1⟩
  let κ3Irr : Irr (↥c.H0) :=
    ⟨kappa c κ1 l3, (kappa_isLinear c h12 hκ1lin l3).1⟩
  have hκ1B : κ1Irr ∈ BOf c h12 χ1 := by
    rw [BOf_mem_iff]
    simpa [κ1Irr] using (show scalarProduct G χ1
      (tildeNu c h12 ⟨κ1, hκ1lin.1⟩) ≠ 0 by
        rw [hpair1]
        norm_num)
  have hκ1L : κ1 ∈ orbit c.H0 c.U κ3Irr.1 := by
    simpa [κ3Irr] using theoremC_kappa_one_mem_kappa_orbit c κ1 l3
  have hκ3orbit : (orbit c.H0 c.U κ3Irr.1).card =
      (c.U.subgroupOf c.H0).index := by
    simpa [κ3Irr] using theoremC_kappa_orbit_card c h12 hκ1lin l3
  have hdeg12 : χ1 1 = χ2 1 :=
    theoremC_BOf_card_three_degree_eq c h12 hSC hκ1lin hχ1 hχ2
      hκ1tilde hκ3tilde hpair1 hpair2 hκ1fix horbitκ1 hκ1L hκ3orbit
      hB3 hS8 hcard
  have hdeg3 : χ3 1 = 2 * χ1 1 := by
    have hzero := tildeNu_sub_one_eq_zero_of_orbit c h12
      (ν := κ3Irr) (μ := κ1Irr) (by simpa [κ1Irr] using hκ1L)
    rw [hκ3tilde, hκ1tilde] at hzero
    change χ3 1 - (χ1 1 + χ2 1) = 0 at hzero
    rw [← hdeg12] at hzero
    linear_combination hzero
  have hm : 4 ≤ (c.U.subgroupOf c.H0).index :=
    theoremC_index_ge4 c h12 hS8
  have hlower : (2 * Nat.card c.K : ℝ) ≤ |x| :=
    theoremC_card_three_lower_bound c h12 hcop hm hχ1 hχ1t hχ2t
      hdeg12 hdeg3 hχ3t hEq6
  have hupper :
      |x| ≤ (2 : ℝ) * (Nat.card c.B : ℝ) := by
    have h := (theoremC_eq4 c h12 hSC hU hUint hUcomm hB'
      hκ1lin hκ1S0 hχ1 hκ1tilde hpair1 hκ1fix horbitκ1 hS8).2
    have hxre : (χ1 c.t - 1).re = x := by
      rw [hχ1t]
      norm_num
    rw [hxre] at h
    rw [hcard] at h
    norm_num at h ⊢
    exact h
  have hBne : BOf c h12 χ1 ≠ {κ1Irr} := by
    intro hsingle
    have hc := congrArg Finset.card hsingle
    rw [hcard] at hc
    simp at hc
  have horbit_ne :
      ∀ {ν : Irr (↥c.H0)}, ν ∈ BOf c h12 χ1 → ν ≠ κ1Irr →
        (orbit c.H0 c.U ν.1).card ≠ (c.U.subgroupOf c.H0).index := by
    intro ν hνB hνκ
    exact theoremC_chi1_BOf_orbit_ne_m c h12 hSC hκ1lin hχ1 hκ1tilde
      hpair1 hκ1fix horbitκ1 hS8 hνB hνκ
  have hKcent :
      c.K ≤ Subgroup.centralizer ((c.S0 : Subgroup G) : Set G) := by
    intro k hk
    exact theoremC_S0_centralizes_K c hk
  have hUne : c.U ≠ c.B ⊔ c.K :=
    theoremC_BOf_ne_singleton_imp_U_ne_BK c h12 hκ1B horbit_ne hKcent hBne
  have hlt : Nat.card c.B < Nat.card c.K :=
    theoremC_card_lt_kernel_of_frobenius (hFrob hUne)
      (show c.B ≤ c.B ⊔ c.K from le_sup_left)
      (theoremC_B_inter_K_bot c hUint)
  have hltR : (Nat.card c.B : ℝ) < (Nat.card c.K : ℝ) := by
    exact_mod_cast hlt
  nlinarith

/-- The `|S| ≥ 8` paper route L851--L977.  The setup chain below is proved:
`κ₁ ≠ 1` (from `B ⊄ U′`), the signed decomposition `κ̃₁ = χ₁+χ₂`,
`κ̃₃ = χ₃`, equation (1), `χ₁(t) = 1+x`, `χ₂(t) = 1−x`, and equation (6).
Equations (2)–(5) eliminate `|B(χ₁)| = 3`; Lemmas 2.5 and 3.6 give
equation (7), and the Frobenius degree bound yields the final contradiction. -/
private theorem theoremC_S_ge_8 (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (hUint : (c.B1 ⊓ c.K2) ⊓ (c.B ⊔ c.K) = ⊥)
    (hUcomm : ⁅c.B1 ⊓ c.K2, c.B ⊔ c.K⁆ = ⊥)
    (hcop : Nat.Coprime (Nat.card c.K) c.H.index)
    (hB' : ⁅c.B, c.B⁆ ≠ c.B)
    (hFrob : c.U ≠ c.B ⊔ c.K → IsFrobeniusGroupWithKernel (c.B ⊔ c.K) c.K)
    (hsimple : IsSimpleGroup G)
    (hS8 : Nat.card (↥(c.S : Subgroup G)) ≠ 4) :
    False := by
  classical
  have hBnotU' : ¬ c.B ≤ ⁅c.U, c.U⁆ := theoremC_B_not_le_Uprime c hU hUint hB'
  rcases exists_kappaOne_ne_one c h12 hBnotU' with ⟨κ1, hκ1lin, hκ1ne, hκ1S0, hκ1comm⟩
  have hm : 4 ≤ (c.U.subgroupOf c.H0).index := theoremC_index_ge4 c h12 hS8
  rcases theoremC_exists_lambda3 c h12 hm with ⟨l3, hl3⟩
  rcases theoremC_kappa_decomp c h12 hκ1lin hκ1S0 hκ1comm l3 hl3 with
    ⟨χ1, χ2, χ3, hχ1, hχ2, hχ3, hκ1tilde, hκ3tilde, hpair1, hpair2⟩
  let κ1Irr : Irr (↥c.H0) := ⟨κ1, hκ1lin.1⟩
  have hκ1fix : conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1 :=
    kappaOne_fixed_by_s c h12 hκ1lin hκ1S0 hκ1comm
  have hκ1B : κ1Irr ∈ BOf c h12 χ1 := by
    rw [BOf_mem_iff]
    rw [hpair1]
    norm_num
  have horbitκ1 : (orbit c.H0 c.U κ1).card = (c.U.subgroupOf c.H0).index := by
    have h := theoremC_kappa_orbit_card c h12 hκ1lin (1 : LambdaHom c.H0 c.U)
    have hk1 : kappa c κ1 (1 : LambdaHom c.H0 c.U) = κ1 := by
      ext x
      simp [kappa, LambdaChar]
    simpa [hk1] using h
  have hκ2not : ⟨kappa c κ1 (lambdaTwo c h12),
      (kappa_isLinear c h12 hκ1lin (lambdaTwo c h12)).1⟩ ∉ BOf c h12 χ1 :=
    theoremC_chi1_kappaTwo_not_mem c h12 hSC hκ1lin hκ1S0 hκ1comm hχ1 hκ1B hκ1fix
      horbitκ1 hS8
  rcases theoremC_chi3_facts c h12 hSC hκ1lin hκ1S0 hκ1comm l3 hl3 hκ3tilde hχ3 with
    ⟨hB3, hχ3t⟩
  let κ3Irr : Irr (↥c.H0) :=
    ⟨kappa c κ1 l3, (kappa_isLinear c h12 hκ1lin l3).1⟩
  have hκ3B : κ3Irr ∈ BOf c h12 χ3 := by
    rw [hB3]
    simp [κ3Irr]
  have hκ3s : conjChar c.H0 (s_normalizes_H0 c h12) (kappa c κ1 l3) ≠ kappa c κ1 l3 := by
    have hiff := kappa_conj_fixed_iff c h12 hκ1lin hκ1S0 hκ1comm l3
    intro hfix
    rcases hiff.mp hfix with h1 | h2
    · have hl3' : l3 ^ 2 = 1 := by
        rw [h1]
        simp
      exact hl3 hl3'
    · have hl3' : l3 ^ 2 = 1 := by
        rw [h2]
        exact lambdaTwo_sq_eq_one c h12
      exact hl3 hl3'
  have hκ3orbit : (orbit c.H0 c.U (kappa c κ1 l3)).card =
      (c.U.subgroupOf c.H0).index := theoremC_kappa_orbit_card c h12 hκ1lin l3
  have hκ3tilde_t : tildeNu c h12 κ3Irr c.t = 2 * κ3Irr.1 (tH0 c) := by
    rcases lemma_3_4 c h12 hSC hχ3 hκ3B hκ3s (Or.inr hκ3orbit) with ⟨_hB, hT⟩
    simpa [κ3Irr] using hT
  have hsum2 : χ1 c.t + χ2 c.t = (2 : ℂ) :=
    theoremC_chi1_add_chi2_t_eq_two c h12 hκ1lin hκ1S0 l3 hl3 hχ1 hχ2 hχ3
      hκ1tilde hκ3tilde hκ3tilde_t
  let x : ℝ := (χ1 c.t - 1).re
  have hχ1t : χ1 c.t = (1 + (x : ℂ)) := by
    simpa [x] using theoremC_chi1_t_eq_one_add_x c hχ1
  have hχ2t : χ2 c.t = (1 : ℂ) - (x : ℂ) := by
    simpa [x] using theoremC_chi2_t_eq_one_sub_x c hχ1 hsum2
  have hEq6 := theoremC_eq6 c h12 hκ1lin hκ1S0 hκ1comm l3 hl3 hχ1 hχ2 hχ3
    hκ1tilde hκ3tilde
  let κ2Irr : Irr (↥c.H0) :=
    ⟨kappa c κ1 (lambdaTwo c h12),
      (kappa_isLinear c h12 hκ1lin (lambdaTwo c h12)).1⟩
  have hcardle3 : (BOf c h12 χ1).card ≤ 3 := theorem_3_2 c h12 hSC hχ1
  have hcardne3 : (BOf c h12 χ1).card ≠ 3 := by
    intro hcard
    exact theoremC_card_three_false c h12 hSC hU hUint hUcomm hcop hB'
      hFrob hS8 hκ1lin hκ1S0 l3 hχ1 hχ2 hκ1tilde hκ3tilde hpair1
      hpair2 hκ1fix horbitκ1 hB3 hχ3t hχ1t hχ2t hEq6 hcard
  have hcardle2 : (BOf c h12 χ1).card ≤ 2 := by omega
  have hK : c.K ≠ ⊥ := by
    by_cases hUBK : c.U = c.B ⊔ c.K
    · exact theoremC_K_ne_one_of_U_eq_BK c h12 hSC hUBK hB' hsimple
    · exact (hFrob hUBK).2.2
  have hκ1B2 : κ1Irr ∈ BOf c h12 χ2 := by
    rw [BOf_mem_iff]
    simpa [κ1Irr] using (show scalarProduct G χ2
      (tildeNu c h12 ⟨κ1, hκ1lin.1⟩) ≠ 0 by
        rw [hpair2]
        norm_num)
  have hκ2not2 : κ2Irr ∉ BOf c h12 χ2 := by
    simpa [κ2Irr] using theoremC_chi1_kappaTwo_not_mem c h12 hSC
      hκ1lin hκ1S0 hκ1comm hχ2 hκ1B2 hκ1fix horbitκ1 hS8
  have hdelta0 : scalarProduct G (1 : ClassFunction G)
      (deltaNu c h12 κ1Irr) = 0 := by
    simpa [κ1Irr] using theoremC_delta_linear_principal_pairing_zero
      c h12 hκ1lin hκ1S0 hκ1ne
  have hpairEq : scalarProduct G (1 : ClassFunction G) (tildeNu c h12 κ1Irr) =
      scalarProduct G (1 : ClassFunction G) (tildeNu c h12 κ2Irr) := by
    change scalarProduct G (1 : ClassFunction G)
      (tildeNu c h12 κ1Irr - tildeNu c h12 κ2Irr) = 0 at hdelta0
    rw [scalarProduct_sub_right] at hdelta0
    linear_combination hdelta0
  have hχ1One : χ1 ≠ (1 : ClassFunction G) := by
    intro h
    apply hκ2not
    rw [BOf_mem_iff, h]
    have hp := hpair1
    rw [h] at hp
    change scalarProduct G (1 : ClassFunction G) (tildeNu c h12 κ2Irr) ≠ 0
    rw [← hpairEq, hp]
    norm_num
  have hχ1NegOne : χ1 ≠ -(1 : ClassFunction G) := by
    intro h
    apply hκ2not
    rw [BOf_mem_iff, h]
    have hp := hpair1
    rw [h, scalarProduct_neg_left] at hp
    change scalarProduct G (-(1 : ClassFunction G)) (tildeNu c h12 κ2Irr) ≠ 0
    rw [scalarProduct_neg_left, ← hpairEq, hp]
    norm_num
  have hχ2One : χ2 ≠ (1 : ClassFunction G) := by
    intro h
    apply hκ2not2
    rw [BOf_mem_iff, h]
    have hp := hpair2
    rw [h] at hp
    change scalarProduct G (1 : ClassFunction G) (tildeNu c h12 κ2Irr) ≠ 0
    rw [← hpairEq, hp]
    norm_num
  have hχ2NegOne : χ2 ≠ -(1 : ClassFunction G) := by
    intro h
    apply hκ2not2
    rw [BOf_mem_iff, h]
    have hp := hpair2
    rw [h, scalarProduct_neg_left] at hp
    change scalarProduct G (-(1 : ClassFunction G)) (tildeNu c h12 κ2Irr) ≠ 0
    rw [scalarProduct_neg_left, ← hpairEq, hp]
    norm_num
  have hχ3One : χ3 ≠ (1 : ClassFunction G) := by
    intro h
    rcases hχ3t with ht | ht
    · rw [h] at ht
      norm_num at ht
    · rw [h] at ht
      norm_num at ht
  have hχ3NegOne : χ3 ≠ -(1 : ClassFunction G) := by
    intro h
    rcases hχ3t with ht | ht
    · rw [h] at ht
      norm_num at ht
    · rw [h] at ht
      norm_num at ht
  have horbit1 : ∀ nu : Irr (↥c.H0), nu ∈ BOf c h12 χ1 →
      conjChar c.H0 (s_normalizes_H0 c h12) nu.1 ∈ orbit c.H0 c.U nu.1 :=
    theoremC_BOf_conj_mem_orbit_of_fixed_member c h12 hSC hχ1 hκ1B hκ1fix
  have horbit2 : ∀ nu : Irr (↥c.H0), nu ∈ BOf c h12 χ2 →
      conjChar c.H0 (s_normalizes_H0 c h12) nu.1 ∈ orbit c.H0 c.U nu.1 :=
    theoremC_BOf_conj_mem_orbit_of_fixed_member c h12 hSC hχ2 hκ1B2 hκ1fix
  have hκ3conjL : conjChar c.H0 (s_normalizes_H0 c h12) κ3Irr.1 ∈
      orbit c.H0 c.U κ3Irr.1 := by
    simpa [κ3Irr] using theoremC_kappa_conj_mem_orbit c h12 hκ1fix l3
  have horbit3 : ∀ nu : Irr (↥c.H0), nu ∈ BOf c h12 χ3 →
      conjChar c.H0 (s_normalizes_H0 c h12) nu.1 ∈ orbit c.H0 c.U nu.1 := by
    exact theoremC_BOf_pair_conj_mem_orbit c h12
      (by simpa [κ3Irr] using hB3) hκ3conjL
  rcases theoremC_pmIrr_lemma36_degree_data c h12 hSC hm hK hsimple
      hχ1 hχ1One hχ1NegOne ⟨κ1Irr, hκ1B⟩ horbit1 with
    ⟨alpha1, a1, hKalpha1, ha1, halpha1, hdegree1⟩
  rcases theoremC_pmIrr_lemma36_degree_data c h12 hSC hm hK hsimple
      hχ2 hχ2One hχ2NegOne ⟨κ1Irr, hκ1B2⟩ horbit2 with
    ⟨alpha2, a2, hKalpha2, ha2, halpha2, hdegree2⟩
  rcases theoremC_pmIrr_lemma36_degree_data c h12 hSC hm hK hsimple
      hχ3 hχ3One hχ3NegOne ⟨κ3Irr, hκ3B⟩ horbit3 with
    ⟨alpha3, a3, hKalpha3, ha3, halpha3, hdegree3⟩
  have hl3t := theoremC_lambda3_tilde_t c h12 hSC l3 hl3
  rcases lemma_2_5 c h12 hm hl3 hl3t with
    ⟨phi, hphiConst, hphiOne, hphit, _hphiLow, hphiL, _hLtwo⟩
  let oneIrr : Irr (↥c.H0) :=
    ⟨(1 : ClassFunction (↥c.H0)),
      (isLinearCharacter_of_hom (1 : ↥c.H0 →* ℂˣ)).1⟩
  have honeB : oneIrr ∈ BOf c h12 phi := by
    rw [BOf_mem_iff]
    simpa [oneIrr] using hphiConst.2
  have honefix : conjChar c.H0 (s_normalizes_H0 c h12) oneIrr.1 = oneIrr.1 := by
    simpa [oneIrr] using one_fixed_by_s c h12
  have hphiNegOne : phi ≠ -(1 : ClassFunction G) := by
    intro h
    have ht := congrFun h c.t
    rw [hphit] at ht
    norm_num at ht
  have horbitphi : ∀ nu : Irr (↥c.H0), nu ∈ BOf c h12 phi →
      conjChar c.H0 (s_normalizes_H0 c h12) nu.1 ∈ orbit c.H0 c.U nu.1 :=
    theoremC_BOf_conj_mem_orbit_of_fixed_member c h12 hSC hphiConst.1
      honeB honefix
  rcases theoremC_pmIrr_lemma36_degree_data c h12 hSC hm hK hsimple
      hphiConst.1 hphiOne hphiNegOne ⟨oneIrr, honeB⟩ horbitphi with
    ⟨alphaphi, aphi, hKalphaphi, haphi, halphaphi, hdegreephi⟩
  let a : ℕ := min a1 (min a2 (min a3 aphi))
  have ha : 1 ≤ a := by
    dsimp [a]
    exact le_min ha1 (le_min ha2 (le_min ha3 haphi))
  have haa1 : a ≤ a1 := by
    dsimp [a]
    exact min_le_left _ _
  have haa2 : a ≤ a2 := by
    dsimp [a]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have haa3 : a ≤ a3 := by
    dsimp [a]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have haaphi : a ≤ aphi := by
    dsimp [a]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let D : ℝ := 8 * (a : ℝ) + 1
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hD1 : D ≤ |(χ1 1).re| := by
    have hcast : (a : ℝ) ≤ (a1 : ℝ) := by exact_mod_cast haa1
    dsimp [D]
    nlinarith [hdegree1]
  have hD2 : D ≤ |(χ2 1).re| := by
    have hcast : (a : ℝ) ≤ (a2 : ℝ) := by exact_mod_cast haa2
    dsimp [D]
    nlinarith [hdegree2]
  have hD3 : D ≤ |(χ3 1).re| := by
    have hcast : (a : ℝ) ≤ (a3 : ℝ) := by exact_mod_cast haa3
    dsimp [D]
    nlinarith [hdegree3]
  have hDphi : D ≤ |(phi 1).re| := by
    have hcast : (a : ℝ) ≤ (aphi : ℝ) := by exact_mod_cast haaphi
    dsimp [D]
    nlinarith [hdegreephi]
  let L : ℝ := ↑((2 * (c.k : ℚ) ^ 2) / c.H.index : ℚ)
  have hEq6real := theoremC_eq6_real c hχ1 hχ2 hχ3 hχ1t hχ2t hχ3t hEq6
  have hL2 : L ≤ ((1 + x) ^ 2 + (1 - x) ^ 2 + 4) / D := by
    dsimp [L]
    rw [hEq6real]
    exact theoremC_L_bound hDpos hD1 hD2 hD3
      (sq_nonneg (1 + x)) (sq_nonneg (1 - x))
  have hineq : 1 < (3 + (1 + x) ^ 2 + (1 - x) ^ 2 + 4) / D :=
    theoremC_ineq7_abs hDpos hDphi (by simpa [L] using hphiL) hL2
  have hxne : x ≠ 0 := by
    apply theoremC_x_ne_zero_of_seven ha
    simpa [D] using hineq
  have heq4 := (theoremC_eq4 c h12 hSC hU hUint hUcomm hB'
    hκ1lin hκ1S0 hχ1 hκ1tilde hpair1 hκ1fix horbitκ1 hS8).2
  have hxre : (χ1 c.t - 1).re = x := by
    rw [hχ1t]
    norm_num
  rw [hxre] at heq4
  have hcard2 : (BOf c h12 χ1).card = 2 :=
    theoremC_BOf_card_two_of_x_ne_zero hcardle2 heq4 hxne
  have hBne : BOf c h12 χ1 ≠ {κ1Irr} := by
    intro hsingle
    have hc := congrArg Finset.card hsingle
    rw [hcard2] at hc
    simp at hc
  have horbit_ne :
      ∀ {nu : Irr (↥c.H0)}, nu ∈ BOf c h12 χ1 → nu ≠ κ1Irr →
        (orbit c.H0 c.U nu.1).card ≠ (c.U.subgroupOf c.H0).index := by
    intro nu hnuB hnuκ
    exact theoremC_chi1_BOf_orbit_ne_m c h12 hSC hκ1lin hχ1 hκ1tilde
      hpair1 hκ1fix horbitκ1 hS8 hnuB hnuκ
  have hKcent : c.K ≤ Subgroup.centralizer ((c.S0 : Subgroup G) : Set G) := by
    intro k hk
    exact theoremC_S0_centralizes_K c hk
  have hUne : c.U ≠ c.B ⊔ c.K :=
    theoremC_BOf_ne_singleton_imp_U_ne_BK c h12 hκ1B horbit_ne hKcent hBne
  have hFrobBK := hFrob hUne
  have haChoice : a = a1 ∨ a = a2 ∨ a = a3 ∨ a = aphi := by
    dsimp [a]
    rcases min_choice a1 (min a2 (min a3 aphi)) with h1 | hrest
    · exact Or.inl h1
    · rcases min_choice a2 (min a3 aphi) with h2 | hrest2
      · exact Or.inr (Or.inl (hrest.trans h2))
      · rcases min_choice a3 aphi with h3 | h4
        · exact Or.inr (Or.inr (Or.inl (hrest.trans (hrest2.trans h3))))
        · exact Or.inr (Or.inr (Or.inr (hrest.trans (hrest2.trans h4))))
  have haB : (Nat.card c.B : ℝ) ≤ (a : ℝ) := by
    rcases haChoice with haeq | haeq | haeq | haeq
    · rw [haeq, ← halpha1]
      exact theoremC_frobenius_degree_bound c hFrobBK
        (theoremC_B_inter_K_bot c hUint) alpha1 hKalpha1
    · rw [haeq, ← halpha2]
      exact theoremC_frobenius_degree_bound c hFrobBK
        (theoremC_B_inter_K_bot c hUint) alpha2 hKalpha2
    · rw [haeq, ← halpha3]
      exact theoremC_frobenius_degree_bound c hFrobBK
        (theoremC_B_inter_K_bot c hUint) alpha3 hKalpha3
    · rw [haeq, ← halphaphi]
      exact theoremC_frobenius_degree_bound c hFrobBK
        (theoremC_B_inter_K_bot c hUint) alphaphi hKalphaphi
  have hx2 : x ^ 2 ≤ 2 * (Nat.card c.B : ℝ) :=
    theoremC_eq5_of_card_two c h12 hSC hU hUint hUcomm hB'
      hκ1lin hκ1S0 hχ1 hκ1tilde hpair1 hκ1fix horbitκ1 hS8 hχ1t hcard2
  exact theoremC_final_contradiction (theoremC_B_card_ge_two c hB') haB hx2
    (by simpa [D] using hineq)

/-- The `|S| = 4` paper route L1200--L1236, using the Section-4 component
classification and reciprocal-degree comparison. -/
private theorem theoremC_case_S4 (c : Hyp11 G) [Hyp11KData c] (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (hUint : (c.B1 ⊓ c.K2) ⊓ (c.B ⊔ c.K) = ⊥)
    (hcop : Nat.Coprime (Nat.card c.K) c.H.index)
    (hB' : ⁅c.B, c.B⁆ ≠ c.B)
    (_hFrob : c.U ≠ c.B ⊔ c.K → IsFrobeniusGroupWithKernel (c.B ⊔ c.K) c.K)
    (hsimple : IsSimpleGroup G)
    (hS4 : Nat.card (↥(c.S : Subgroup G)) = 4) :
    False := by
  classical
  have hUBK : c.U = c.B ⊔ c.K := theoremC_U_eq_BK_of_S4 c hU hS4
  have hk : c.k = 2 * Nat.card (↥c.K) :=
    theoremC_k_eq_two_mul_K_of_S4 c hU hUint hS4
  have hk12 : c.k1 = c.k2 := theoremC_k1_eq_k2_of_S4 c hU hS4
  have hK : c.K ≠ ⊥ :=
    theoremC_K_ne_one_of_S4 c h12 hSC hU hB' hsimple hS4
  have hBnotU' : ¬ c.B ≤ ⁅c.U, c.U⁆ := theoremC_B_not_le_Uprime c hU hUint hB'
  rcases exists_kappaOne_ne_one c h12 hBnotU' with
    ⟨κ1, hκ1lin, hκ1ne, hκ1S0, hκ1comm⟩
  let κ1Irr : Irr (↥c.H0) := ⟨κ1, hκ1lin.1⟩
  have hκ1s : conjChar c.H0 (s_normalizes_H0 c h12) κ1Irr.1 = κ1Irr.1 := by
    simpa [κ1Irr] using kappaOne_fixed_by_s c h12 hκ1lin hκ1S0 hκ1comm
  have hκ1t : κ1Irr.1 (tH0 c) = κ1Irr.1 1 := by
    dsimp [κ1Irr]
    calc
      κ1 (tH0 c) = 1 := hκ1S0 (tH0 c) c.t_mem_S0
      _ = κ1 1 := hκ1lin.2.symm
  have hκ1one : κ1Irr.1 1 = 1 := by simpa [κ1Irr] using hκ1lin.2
  have hκ1Delta : deltaNu c h12 κ1Irr ∈ Delta c h12 := by
    rw [Delta]
    exact ⟨κ1Irr, hκ1s, hκ1t, rfl⟩
  let Δ0 : Set (ClassFunction G) :=
    theoremC_deltaComponent c h12 (deltaNu c h12 κ1Irr)
  have hcomp : IsConnectedComponent c h12 Δ0 := by
    dsimp [Δ0]
    exact theoremC_deltaComponent_isConnected c h12 hκ1Delta
  have hκ1Δ0 : deltaNu c h12 κ1Irr ∈ Δ0 := by
    change deltaNu c h12 κ1Irr ∈ Delta c h12 ∧
      Relation.ReflTransGen (deltaAdjacent c h12)
        (deltaNu c h12 κ1Irr) (deltaNu c h12 κ1Irr)
    exact ⟨hκ1Delta, Relation.ReflTransGen.refl⟩
  have hcard : Δ0.ncard = 1 :=
    theoremC_S4_component_ncard_eq_one c h12 hSC hS4 hUBK hcop hK hk hk12
      hκ1lin hκ1S0 hκ1comm (by simpa [κ1Irr] using hκ1s)
      (by simpa [κ1Irr] using hκ1t) hcomp (by simpa [κ1Irr] using hκ1Δ0)
  rcases Set.ncard_eq_one.mp hcard with ⟨delta, hDelta0'⟩
  have hdeltakappa : delta = deltaNu c h12 κ1Irr := by
    have hmem : deltaNu c h12 κ1Irr ∈
        ({delta} : Set (ClassFunction G)) := by
      rwa [← hDelta0']
    simpa using hmem.symm
  have hDelta0 : Δ0 = {deltaNu c h12 κ1Irr} := by
    simpa [hdeltakappa] using hDelta0'
  rcases theoremC_S4_singleton_four_values c h12 hSC hS4
    hκ1s hκ1t hκ1one hcomp hκ1Δ0 hDelta0 with
    ⟨psi, hpsi, hpsiorth, hdeltasum, hpair, hpsit⟩
  let oneIrr : Irr (↥c.H0) :=
    ⟨(1 : ClassFunction (↥c.H0)), (isLinearCharacter_one (G := ↥c.H0)).1⟩
  have honeLin : IsLinearCharacter oneIrr.1 := by
    simpa [oneIrr] using (isLinearCharacter_one (G := ↥c.H0))
  have honeS0 : ∀ x : ↥c.H0, (x : G) ∈ c.S0 → oneIrr.1 x = 1 := by
    intro x _hx
    rfl
  have honecomm : ∀ x : ↥c.H0,
      (x : G) ∈ ⁅(c.S : Subgroup G), c.U⁆ → oneIrr.1 x = 1 := by
    intro x _hx
    rfl
  have hones : conjChar c.H0 (s_normalizes_H0 c h12) oneIrr.1 = oneIrr.1 := by
    ext x
    simp [oneIrr, conjChar]
  have honet : oneIrr.1 (tH0 c) = oneIrr.1 1 := by simp [oneIrr]
  have honeone : oneIrr.1 1 = 1 := by simp [oneIrr]
  have honeDelta : deltaNu c h12 oneIrr ∈ Delta c h12 := by
    rw [Delta]
    exact ⟨oneIrr, hones, honet, rfl⟩
  let DeltaOne : Set (ClassFunction G) :=
    theoremC_deltaComponent c h12 (deltaNu c h12 oneIrr)
  have hcompOne : IsConnectedComponent c h12 DeltaOne := by
    dsimp [DeltaOne]
    exact theoremC_deltaComponent_isConnected c h12 honeDelta
  have honeDeltaOne : deltaNu c h12 oneIrr ∈ DeltaOne := by
    change deltaNu c h12 oneIrr ∈ Delta c h12 ∧
      Relation.ReflTransGen (deltaAdjacent c h12)
        (deltaNu c h12 oneIrr) (deltaNu c h12 oneIrr)
    exact ⟨honeDelta, Relation.ReflTransGen.refl⟩
  have hcardOne : DeltaOne.ncard = 1 :=
    theoremC_S4_component_ncard_eq_one c h12 hSC hS4 hUBK hcop hK hk hk12
      honeLin honeS0 honecomm hones honet hcompOne honeDeltaOne
  rcases Set.ncard_eq_one.mp hcardOne with ⟨deltaOne, hDeltaOne'⟩
  have hdeltaOne : deltaOne = deltaNu c h12 oneIrr := by
    have hmem : deltaNu c h12 oneIrr ∈
        ({deltaOne} : Set (ClassFunction G)) := by
      rwa [← hDeltaOne']
    simpa using hmem.symm
  have hDeltaOne : DeltaOne = {deltaNu c h12 oneIrr} := by
    simpa [hdeltaOne] using hDeltaOne'
  rcases theoremC_S4_singleton_four_values c h12 hSC hS4
      hones honet honeone hcompOne honeDeltaOne hDeltaOne with
    ⟨phi, hphi, hphiorth, hdeltaOneSum, hphiPair, hphit⟩
  have hprincipalPair : scalarProduct G (1 : ClassFunction G)
      (deltaNu c h12 oneIrr) = 1 := by
    simpa [oneIrr] using theoremC_delta_trivial_principal_pairing c h12
  have hprincipalSum : scalarProduct G (1 : ClassFunction G) (∑ i, phi i) = 1 := by
    rw [← hdeltaOneSum]
    exact hprincipalPair
  rcases theoremC_exists_principal_in_four_sum phi hphi hprincipalSum with
    ⟨iPrincipal, hiPrincipal⟩
  have hpsiExpand := theoremC_S4_four_reciprocal_sum c psi hpsi hdeltasum hpsit
  have hphiExpand := theoremC_S4_four_reciprocal_sum c phi hphi hdeltaOneSum hphit
  have hpsiEquation :=
    theoremC_delta_equation c h12 hκ1lin hκ1S0 hκ1comm hk12
  have hphiEquation :=
    theoremC_delta_equation c h12 honeLin honeS0 honecomm hk12
  rw [hpsiExpand] at hpsiEquation
  rw [hphiExpand] at hphiEquation
  have hindexNe : (c.H.index : ℂ) ≠ 0 := by
    rw [Subgroup.index_eq_card]
    exact_mod_cast (Nat.card_pos (α := G ⧸ c.H)).ne'
  have hreciprocalEq : (∑ i, (phi i 1)⁻¹) = ∑ i, (psi i 1)⁻¹ := by
    apply mul_left_cancel₀ hindexNe
    calc
      (c.H.index : ℂ) * ∑ i, (phi i 1)⁻¹ = (2 * c.k ^ 2 : ℂ) := hphiEquation
      _ = (c.H.index : ℂ) * ∑ i, (psi i 1)⁻¹ := hpsiEquation.symm
  have hdeltaPrincipalZero : scalarProduct G (1 : ClassFunction G)
      (deltaNu c h12 κ1Irr) = 0 := by
    simpa [κ1Irr] using theoremC_delta_linear_principal_pairing_zero
      c h12 hκ1lin hκ1S0 hκ1ne
  have hpsiNeOne : ∀ i, psi i ≠ (1 : ClassFunction G) := by
    intro i hEq
    have hp := hpair i
    rw [hEq, hdeltaPrincipalZero] at hp
    norm_num at hp
  have hphiNeOne : ∀ i, i ≠ iPrincipal → phi i ≠ (1 : ClassFunction G) := by
    intro i hi hEq
    have horth := hphiorth (i := i) (j := iPrincipal) hi
    rw [hEq, hiPrincipal,
      scalarProduct_irreducible_self (isIrreducibleCharacter_one G)] at horth
    norm_num at horth
  have hpsiAbs : ∀ i, (5 : ℝ) ≤ |(psi i 1).re| := by
    intro i
    exact theoremC_S4_pmIrr_abs_degree_ge_five c h12 hSC hS4 hK hsimple
      (kappa := κ1Irr) hκ1s hκ1t (hpsi i) (hpair i) (hpsit i)
      (hpsiNeOne i)
  have hphiAbs : ∀ i, i ≠ iPrincipal → (5 : ℝ) ≤ |(phi i 1).re| := by
    intro i hi
    exact theoremC_S4_pmIrr_abs_degree_ge_five c h12 hSC hS4 hK hsimple
      (kappa := oneIrr) hones honet (hphi i) (hphiPair i) (hphit i)
      (hphiNeOne i hi)
  have hpsiDegreeSumC : (∑ i, psi i 1) = 0 := by
    calc
      (∑ i, psi i 1) = (∑ i, psi i) 1 := by simp
      _ = deltaNu c h12 κ1Irr 1 := (congrFun hdeltasum 1).symm
      _ = 0 := theoremC_deltaNu_one_eq_zero c h12 κ1Irr
  have hphiDegreeSumC : (∑ i, phi i 1) = 0 := by
    calc
      (∑ i, phi i 1) = (∑ i, phi i) 1 := by simp
      _ = deltaNu c h12 oneIrr 1 := (congrFun hdeltaOneSum 1).symm
      _ = 0 := theoremC_deltaNu_one_eq_zero c h12 oneIrr
  have hpsiDegreeSumR : (∑ i, (psi i 1).re) = 0 := by
    have h := congrArg Complex.re hpsiDegreeSumC
    simpa [Complex.re_sum] using h
  have hphiDegreeSumR : (∑ i, (phi i 1).re) = 0 := by
    have h := congrArg Complex.re hphiDegreeSumC
    simpa [Complex.re_sum] using h
  have hphiPrincipalDegree : (phi iPrincipal 1).re = 1 := by
    rw [hiPrincipal]
    norm_num
  have hphiReciprocalCast : (∑ i, (phi i 1)⁻¹) =
      ∑ i, ((↑((phi i 1).re) : ℂ)⁻¹) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun z : ℂ => z⁻¹)
      (theoremC_pmIrr_one_eq_real (hphi i))
  have hpsiReciprocalCast : (∑ i, (psi i 1)⁻¹) =
      ∑ i, ((↑((psi i 1).re) : ℂ)⁻¹) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun z : ℂ => z⁻¹)
      (theoremC_pmIrr_one_eq_real (hpsi i))
  have hreciprocalEqCast := hreciprocalEq
  rw [hphiReciprocalCast, hpsiReciprocalCast] at hreciprocalEqCast
  have hreciprocalEqR : (∑ i, ((phi i 1).re)⁻¹) =
      ∑ i, ((psi i 1).re)⁻¹ := by
    have h := congrArg Complex.re hreciprocalEqCast
    simpa [Complex.re_sum] using h
  have hphiLower := theoremC_three_reciprocal_lower_fin
    (fun i => (phi i 1).re) iPrincipal hphiDegreeSumR
      hphiPrincipalDegree hphiAbs
  have hpsiUpper := theoremC_four_reciprocal_upper_fin
    (fun i => (psi i 1).re) hpsiDegreeSumR hpsiAbs
  nlinarith [hphiLower, hpsiUpper, hreciprocalEqR]

/-- Theorem C: the hypotheses `U = (B1 ∩ K2) × BK`, `(|K|, |G:H|) = 1`,
`B' ≠ B` (and `BK` Frobenius with kernel `K` if `U ≠ BK`) force `G` to be
non-simple. -/
public theorem theorem_C {G : Type u} [Group G] [Finite G] (c : Hyp11 G) [Hyp11KData c]
    (hU : c.U = (c.B1 ⊓ c.K2) ⊔ (c.B ⊔ c.K))
    (hUint : (c.B1 ⊓ c.K2) ⊓ (c.B ⊔ c.K) = ⊥)
    (hUcomm : ⁅c.B1 ⊓ c.K2, c.B ⊔ c.K⁆ = ⊥)
    (hcop : Nat.Coprime (Nat.card c.K) c.H.index)
    (hB' : ⁅c.B, c.B⁆ ≠ c.B)
    (hFrob : c.U ≠ c.B ⊔ c.K → IsFrobeniusGroupWithKernel (c.B ⊔ c.K) c.K) :
    ¬ IsSimpleGroup G := by
  intro hsimple
  have h12 : Hyp12 c := theoremC_hyp12 c
  have hSC : Section3Hyp c := theoremC_section3Hyp c hU hUint
  by_cases hS4 : Nat.card (↥(c.S : Subgroup G)) = 4
  · exact False.elim (theoremC_case_S4 c h12 hSC hU hUint hcop hB' hFrob hsimple hS4)
  · exact False.elim
      (theoremC_S_ge_8 c h12 hSC hU hUint hUcomm hcop hB' hFrob hsimple hS4)

end TheoremC

end CFSG.BenderGlauberman

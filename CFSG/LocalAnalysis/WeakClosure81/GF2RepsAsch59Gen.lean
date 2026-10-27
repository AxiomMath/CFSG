module

public import CFSG.LocalAnalysis.AGLEmbedding.AltBetaGen
public import CFSG.Permutation.AlternatingAutomorphism.ThreeCycle
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch59

open Equiv

variable {Ω : Type*} [DecidableEq Ω]

def pairingSwap (σ : Perm Ω) (x y : Ω) : Perm Ω :=
  swap x y * swap (σ x) (σ y)

theorem pairingSwap_commute {σ : Perm Ω} (hσ : ∀ z, σ (σ z) = z) {x y : Ω}
    (hx : σ x ≠ x) (hy : σ y ≠ y) (hxy : x ≠ y) (hxsy : x ≠ σ y) :
    Commute (pairingSwap σ x y) σ := by
  have hyσx : y ≠ σ x := fun h => hxsy (by rw [h, hσ x])
  have hσxσy : σ x ≠ σ y := fun h => hxy (by rw [← hσ x, ← hσ y, h])
  have hnd : [x, y, σ x, σ y].Nodup := by
    simp [hxy, hx.symm, hxsy, hy.symm, hyσx, hσxσy]
  have hst : swap x y * swap (σ x) (σ y) = swap (σ x) (σ y) * swap x y :=
    (Equiv.Perm.disjoint_swap_swap hnd).commute.eq
  have hσinv : σ⁻¹ = σ := by
    ext z
    exact Equiv.Perm.inv_eq_iff_eq.mpr (hσ z).symm
  have h1 : σ * swap x y * σ = swap (σ x) (σ y) := by
    simpa [hσinv] using (Equiv.swap_apply_apply σ x y).symm
  have h2 : σ * swap (σ x) (σ y) * σ = swap x y := by
    simpa [hσinv, hσ] using (Equiv.swap_apply_apply σ (σ x) (σ y)).symm
  have hσ2 : σ * σ = 1 := by
    ext z
    exact hσ z
  have hconj : σ * pairingSwap σ x y * σ = pairingSwap σ x y := by
    rw [pairingSwap]
    calc σ * (swap x y * swap (σ x) (σ y)) * σ
        = (σ * swap x y * σ) * (σ * swap (σ x) (σ y) * σ) := by
          calc σ * (swap x y * swap (σ x) (σ y)) * σ
              = σ * swap x y * (σ * σ) * swap (σ x) (σ y) * σ := by
                rw [hσ2, mul_one]
                group
            _ = (σ * swap x y * σ) * (σ * swap (σ x) (σ y) * σ) := by group
      _ = swap (σ x) (σ y) * swap x y := by rw [h1, h2]
      _ = swap x y * swap (σ x) (σ y) := hst.symm
  have hmul : σ * pairingSwap σ x y = pairingSwap σ x y * σ := by
    calc σ * pairingSwap σ x y = σ * pairingSwap σ x y * (σ * σ) := by
          rw [hσ2, mul_one]
      _ = (σ * pairingSwap σ x y * σ) * σ := by group
      _ = pairingSwap σ x y * σ := by rw [hconj]
  exact hmul.symm

theorem pairingSwap_mem_alternatingGroup [Fintype Ω] {σ : Perm Ω} {x y : Ω}
    (hxy : x ≠ y) (hσxσy : σ x ≠ σ y) :
    pairingSwap σ x y ∈ alternatingGroup Ω := by
  rw [Perm.mem_alternatingGroup, pairingSwap, Perm.sign_mul, Perm.sign_swap hxy,
    Perm.sign_swap hσxσy]
  norm_num

theorem pairingSwap_apply_left {σ : Perm Ω} {x y : Ω}
    (hx : σ x ≠ x) (hxsy : x ≠ σ y) : pairingSwap σ x y x = y := by
  rw [pairingSwap, Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne (a := σ x) (b := σ y) (x := x) hx.symm hxsy,
    Equiv.swap_apply_left]

theorem pairingSwap_apply_sigma_left {σ : Perm Ω} {x y : Ω}
    (_hx : σ x ≠ x) (hy : σ y ≠ y) (hxsy : x ≠ σ y) :
    pairingSwap σ x y (σ x) = σ y := by
  rw [pairingSwap, Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne (a := x) (b := y) (x := σ y) hxsy.symm hy]

theorem pairingSwap_apply_of_notMem {σ : Perm Ω} {x y z : Ω}
    (hz : z ∉ ({x, σ x, y, σ y} : Finset Ω)) : pairingSwap σ x y z = z := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  obtain ⟨hzx, hzσx, hzy, hzσy⟩ := hz
  rw [pairingSwap, Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne (a := σ x) (b := σ y) (x := z) hzσx hzσy,
    Equiv.swap_apply_of_ne_of_ne (a := x) (b := y) (x := z) hzx hzy]

theorem pairingSwap_image_pair {σ : Perm Ω} (_hσ : ∀ z, σ (σ z) = z) {x y : Ω}
    (hx : σ x ≠ x) (hy : σ y ≠ y) (_hxy : x ≠ y) (hxsy : x ≠ σ y) :
    Finset.image (pairingSwap σ x y) ({x, σ x} : Finset Ω) = {y, σ y} := by
  rw [Finset.image_insert, Finset.image_singleton,
    pairingSwap_apply_left hx hxsy, pairingSwap_apply_sigma_left hx hy hxsy]

theorem exists_fixed_of_odd_card_of_involution [Fintype Ω] {σ : Perm Ω} (hσ : σ ^ 2 = 1)
    {S : Finset Ω}
    (hS : ∀ x ∈ S, σ x ∈ S) (hodd : Odd S.card) : ∃ x ∈ S, σ x = x := by
  have hσ' : ∀ z, σ (σ z) = z := fun z => by
    simpa [pow_two] using congrArg (fun f : Perm Ω => f z) hσ
  have hSinv : ∀ x, σ x ∈ S ↔ x ∈ S := by
    intro x
    constructor
    · intro hx
      have h := hS (σ x) hx
      rwa [hσ' x] at h
    · exact hS x
  by_contra h
  push Not at h
  let σS : Perm {x // x ∈ S} := σ.subtypePerm hSinv
  have hσS2 : σS ^ 2 = 1 := by
    ext x
    change σ (σ (x : Ω)) = (x : Ω)
    exact hσ' x
  have hsupp : σS.support = Finset.univ := by
    ext x
    rw [Perm.mem_support]
    constructor
    · intro _; exact Finset.mem_univ x
    · intro _ hx
      exact h x.1 x.2 (congrArg Subtype.val hx)
  have hdvd : 2 ∣ S.card := by
    have h := Perm.two_dvd_card_support hσS2
    rwa [hsupp, Finset.card_univ, Fintype.card_coe] at h
  exact hodd.not_two_dvd_nat hdvd

theorem pair_eq_of_mem {σ : Perm Ω} (hσ : ∀ z, σ (σ z) = z) {a x : Ω}
    (hx : σ x ≠ x) (h : x ∈ ({a, σ a} : Finset Ω)) :
    ({x, σ x} : Finset Ω) = {a, σ a} := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl
  · rfl
  · rw [hσ a]
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

theorem pair_eq_of_common_mem {σ : Perm Ω} (hσ : ∀ z, σ (σ z) = z) {p q z : Ω}
    (hp : σ p ≠ p) (_hq : σ q ≠ q)
    (hpz : z ∈ ({p, σ p} : Finset Ω)) (hqz : z ∈ ({q, σ q} : Finset Ω)) :
    ({p, σ p} : Finset Ω) = {q, σ q} := by
  have hz : σ z ≠ z := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpz
    rcases hpz with rfl | rfl
    · exact hp
    · rw [hσ p]
      exact hp.symm
  calc ({p, σ p} : Finset Ω) = {z, σ z} := (pair_eq_of_mem hσ hz hpz).symm
    _ = {q, σ q} := pair_eq_of_mem hσ hz hqz

theorem pair_ne_of_notMem {σ : Perm Ω} {p q : Ω}
    (h : q ∉ ({p, σ p} : Finset Ω)) :
    ({p, σ p} : Finset Ω) ≠ {q, σ q} := by
  intro heq
  rw [heq] at h
  exact h (by simp)

theorem not_mem_pair_of_ne {σ : Perm Ω} (hσ : ∀ z, σ (σ z) = z) {p q : Ω}
    (hp : σ p ≠ p) (hq : σ q ≠ q)
    (h : ({p, σ p} : Finset Ω) ≠ {q, σ q}) :
    q ∉ ({p, σ p} : Finset Ω) ∧ σ q ∉ ({p, σ p} : Finset Ω) := by
  constructor
  · intro hq'
    exact h (pair_eq_of_common_mem hσ hp hq hq' (by simp))
  · intro hσq'
    exact h (pair_eq_of_common_mem hσ hp hq hσq' (by simp))

theorem image_pair_of_fixed {σ : Perm Ω} {f : Ω → Ω} {r : Ω}
    (hr : f r = r) (hσr : f (σ r) = σ r) :
    Finset.image f ({r, σ r} : Finset Ω) = {r, σ r} := by
  rw [Finset.image_insert, Finset.image_singleton, hr, hσr]

theorem pairingSwap_image_union_of_fixed_pair {σ : Perm Ω} (hσ : ∀ z, σ (σ z) = z)
    {p q r : Ω} (hp : σ p ≠ p) (hq : σ q ≠ q) (hr : σ r ≠ r)
    (hpq : p ≠ q) (hpsq : p ≠ σ q)
    (hrp : ({r, σ r} : Finset Ω) ≠ {p, σ p})
    (hrq : ({r, σ r} : Finset Ω) ≠ {q, σ q}) :
    Finset.image (pairingSwap σ p q) (({r, σ r} : Finset Ω) ∪ {p, σ p}) =
      ({r, σ r} : Finset Ω) ∪ {q, σ q} := by
  have hnr := not_mem_pair_of_ne hσ hp hr hrp.symm
  have hnrq := not_mem_pair_of_ne hσ hq hr hrq.symm
  have hnotr : r ∉ ({p, σ p, q, σ q} : Finset Ω) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hnr.1 (by rw [h]; exact Finset.mem_insert_self _ _),
      fun h => hnr.1 (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)),
      fun h => hnrq.1 (by rw [h]; exact Finset.mem_insert_self _ _),
      fun h => hnrq.1 (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
  have hnotσr : σ r ∉ ({p, σ p, q, σ q} : Finset Ω) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hnr.2 (by rw [h]; exact Finset.mem_insert_self _ _),
      fun h => hnr.2 (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)),
      fun h => hnrq.2 (by rw [h]; exact Finset.mem_insert_self _ _),
      fun h => hnrq.2 (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
  have hfixr : pairingSwap σ p q r = r := pairingSwap_apply_of_notMem hnotr
  have hfixσr : pairingSwap σ p q (σ r) = σ r := pairingSwap_apply_of_notMem hnotσr
  rw [Finset.image_union, image_pair_of_fixed hfixr hfixσr,
    pairingSwap_image_pair hσ hp hq hpq hpsq]

theorem pairingSwap_mem_centralizer {σ : Perm Ω} (hσ : ∀ z, σ (σ z) = z) {p q : Ω}
    (hp : σ p ≠ p) (hq : σ q ≠ q) (hpq : p ≠ q) (hpsq : p ≠ σ q) :
    pairingSwap σ p q ∈ Subgroup.centralizer ({σ} : Set (Perm Ω)) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (pairingSwap_commute hσ hp hq hpq hpsq).eq

theorem sign_pairingSwap [Fintype Ω] {σ : Perm Ω} {p q : Ω} (hpq : p ≠ q)
    (hσpσq : σ p ≠ σ q) :
    Perm.sign (pairingSwap σ p q) = 1 :=
  Perm.mem_alternatingGroup.mp (pairingSwap_mem_alternatingGroup hpq hσpσq)

theorem swap_sigma_commute {σ : Perm Ω} (hσ : ∀ z, σ (σ z) = z) {x : Ω} :
    Commute (swap x (σ x)) σ := by
  have hσ2 : σ * σ = 1 := by
    ext z
    exact hσ z
  have hσinv : σ⁻¹ = σ := by
    ext z
    exact Equiv.Perm.inv_eq_iff_eq.mpr (hσ z).symm
  have h1 : σ * swap x (σ x) * σ = swap x (σ x) := by
    have h := (Equiv.swap_apply_apply σ x (σ x)).symm
    simpa [hσinv, hσ, Equiv.swap_comm] using h
  have hmul : σ * swap x (σ x) = swap x (σ x) * σ := by
    calc σ * swap x (σ x) = σ * swap x (σ x) * (σ * σ) := by rw [hσ2, mul_one]
      _ = (σ * swap x (σ x) * σ) * σ := by group
      _ = swap x (σ x) * σ := by rw [h1]
  exact hmul.symm

theorem exists_pairingSwap_image_union [Fintype Ω] {σ : Perm Ω} (hσ : ∀ z, σ (σ z) = z)
    {a b x y : Ω} (ha : σ a ≠ a) (hb : σ b ≠ b) (hab : a ≠ b) (hasb : a ≠ σ b)
    (hx : σ x ≠ x) (hy : σ y ≠ y) (hxy : x ≠ y) (hxsy : x ≠ σ y) :
    ∃ τ : Perm Ω, τ ∈ Subgroup.centralizer ({σ} : Set (Perm Ω)) ∧ Perm.sign τ = 1 ∧
      Finset.image τ (({a, σ a} : Finset Ω) ∪ {b, σ b}) =
        ({x, σ x} : Finset Ω) ∪ {y, σ y} := by
  have hyσx : y ≠ σ x := fun h => hxsy (by rw [h, hσ x])
  have hσxσy : σ x ≠ σ y := fun h => hxy (by rw [← hσ x, ← hσ y, h])
  have hPa_ne_Pb : ({a, σ a} : Finset Ω) ≠ {b, σ b} := by
    refine (pair_ne_of_notMem (σ := σ) (p := b) (q := a) ?_).symm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab, hasb⟩
  have hPxy : ({x, σ x} : Finset Ω) ≠ {y, σ y} := by
    intro heq
    have hyPx : y ∈ ({x, σ x} : Finset Ω) := by
      rw [heq]
      exact Finset.mem_insert_self _ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyPx
    exact hyPx.elim (fun h => hxy h.symm) hyσx
  have hyaPx (hxa : x ∈ ({a, σ a} : Finset Ω)) :
      y ∉ ({a, σ a} : Finset Ω) ∧ σ y ∉ ({a, σ a} : Finset Ω) := by
    have hPx : ({x, σ x} : Finset Ω) = {a, σ a} := pair_eq_of_mem hσ hx hxa
    have hPa : ({a, σ a} : Finset Ω) ≠ {y, σ y} := by
      rw [← hPx]
      exact hPxy
    exact not_mem_pair_of_ne hσ ha hy hPa
  have hxaPy (hya : y ∈ ({a, σ a} : Finset Ω)) :
      x ∉ ({a, σ a} : Finset Ω) ∧ σ x ∉ ({a, σ a} : Finset Ω) := by
    have hPy : ({y, σ y} : Finset Ω) = {a, σ a} := pair_eq_of_mem hσ hy hya
    have hPa : ({a, σ a} : Finset Ω) ≠ {x, σ x} := by
      rw [← hPy]
      exact hPxy.symm
    exact not_mem_pair_of_ne hσ ha hx hPa
  have hybPx (hxb : x ∈ ({b, σ b} : Finset Ω)) :
      y ∉ ({b, σ b} : Finset Ω) ∧ σ y ∉ ({b, σ b} : Finset Ω) := by
    have hPx : ({x, σ x} : Finset Ω) = {b, σ b} := pair_eq_of_mem hσ hx hxb
    have hPb : ({b, σ b} : Finset Ω) ≠ {y, σ y} := by
      rw [← hPx]
      exact hPxy
    exact not_mem_pair_of_ne hσ hb hy hPb
  have hxbPy (hyb : y ∈ ({b, σ b} : Finset Ω)) :
      x ∉ ({b, σ b} : Finset Ω) ∧ σ x ∉ ({b, σ b} : Finset Ω) := by
    have hPy : ({y, σ y} : Finset Ω) = {b, σ b} := pair_eq_of_mem hσ hy hyb
    have hPb : ({b, σ b} : Finset Ω) ≠ {x, σ x} := by
      rw [← hPy]
      exact hPxy.symm
    exact not_mem_pair_of_ne hσ hb hx hPb
  have ne_left_of_notMem {p z : Ω} (h : z ∉ ({p, σ p} : Finset Ω)) : z ≠ p :=
    fun hzp => h (by rw [hzp]; exact Finset.mem_insert_self _ _)
  have ne_right_of_notMem {p z : Ω} (h : z ∉ ({p, σ p} : Finset Ω)) : z ≠ σ p :=
    fun hzsp => h (by rw [hzsp]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  by_cases hxa : x ∈ ({a, σ a} : Finset Ω)
  · by_cases hyb : y ∈ ({b, σ b} : Finset Ω)
    · refine ⟨1, by simp, by simp, ?_⟩
      rw [show Finset.image (1 : Perm Ω) (({a, σ a} : Finset Ω) ∪ {b, σ b}) =
          ({a, σ a} : Finset Ω) ∪ {b, σ b} from by simp,
        pair_eq_of_mem hσ hx hxa, pair_eq_of_mem hσ hy hyb]
    · have hby : b ≠ y := fun h => ne_left_of_notMem (p := b) hyb h.symm
      have hbsy : b ≠ σ y := fun h => ne_right_of_notMem (p := b) hyb (by rw [← hσ y, ← h])
      have hσbσy : σ b ≠ σ y := fun h => hby (by rw [← hσ b, ← hσ y, h])
      have hPa_ne_Py : ({a, σ a} : Finset Ω) ≠ {y, σ y} := by
        rw [← pair_eq_of_mem hσ hx hxa]
        exact hPxy
      refine ⟨pairingSwap σ b y, pairingSwap_mem_centralizer hσ hb hy hby hbsy,
        sign_pairingSwap hby hσbσy, ?_⟩
      rw [pairingSwap_image_union_of_fixed_pair hσ hb hy ha hby hbsy hPa_ne_Pb hPa_ne_Py,
        pair_eq_of_mem hσ hx hxa]
  · by_cases hya : y ∈ ({a, σ a} : Finset Ω)
    · by_cases hxb : x ∈ ({b, σ b} : Finset Ω)
      · refine ⟨1, by simp, by simp, ?_⟩
        rw [show Finset.image (1 : Perm Ω) (({a, σ a} : Finset Ω) ∪ {b, σ b}) =
            ({a, σ a} : Finset Ω) ∪ {b, σ b} from by simp,
          pair_eq_of_mem hσ hx hxb, pair_eq_of_mem hσ hy hya, Finset.union_comm]
      · have hbx : b ≠ x := fun h => ne_left_of_notMem (p := b) hxb h.symm
        have hbsx : b ≠ σ x := fun h => ne_right_of_notMem (p := b) hxb (by rw [← hσ x, ← h])
        have hσbσx : σ b ≠ σ x := fun h => hbx (by rw [← hσ b, ← hσ x, h])
        have hPa_ne_Px : ({a, σ a} : Finset Ω) ≠ {x, σ x} := by
          rw [← pair_eq_of_mem hσ hy hya]
          exact hPxy.symm
        refine ⟨pairingSwap σ b x, pairingSwap_mem_centralizer hσ hb hx hbx hbsx,
          sign_pairingSwap hbx hσbσx, ?_⟩
        rw [pairingSwap_image_union_of_fixed_pair hσ hb hx ha hbx hbsx hPa_ne_Pb hPa_ne_Px,
          pair_eq_of_mem hσ hy hya, Finset.union_comm]
    · by_cases hxb : x ∈ ({b, σ b} : Finset Ω)
      · have hay : a ≠ y := fun h => ne_left_of_notMem (p := a) hya h.symm
        have hasy : a ≠ σ y := fun h => ne_right_of_notMem (p := a) hya (by rw [← hσ y, ← h])
        have hσaσy : σ a ≠ σ y := fun h => hay (by rw [← hσ a, ← hσ y, h])
        have hPb_ne_Pa : ({b, σ b} : Finset Ω) ≠ {a, σ a} := hPa_ne_Pb.symm
        have hPb_ne_Py : ({b, σ b} : Finset Ω) ≠ {y, σ y} :=
          pair_ne_of_notMem (σ := σ) (p := b) (q := y) (hybPx hxb).1
        refine ⟨pairingSwap σ a y, pairingSwap_mem_centralizer hσ ha hy hay hasy,
          sign_pairingSwap hay hσaσy, ?_⟩
        rw [show ({a, σ a} : Finset Ω) ∪ {b, σ b} = {b, σ b} ∪ {a, σ a} from
          Finset.union_comm _ _]
        rw [pairingSwap_image_union_of_fixed_pair hσ ha hy hb hay hasy hPb_ne_Pa hPb_ne_Py,
          pair_eq_of_mem hσ hx hxb]
      · by_cases hyb : y ∈ ({b, σ b} : Finset Ω)
        · have hax : a ≠ x := fun h => ne_left_of_notMem (p := a) hxa h.symm
          have hasx : a ≠ σ x :=
            fun h => ne_right_of_notMem (p := a) hxa (by rw [← hσ x, ← h])
          have hσaσx : σ a ≠ σ x := fun h => hax (by rw [← hσ a, ← hσ x, h])
          have hPb_ne_Px : ({b, σ b} : Finset Ω) ≠ {x, σ x} :=
            pair_ne_of_notMem (σ := σ) (p := b) (q := x) hxb
          refine ⟨pairingSwap σ a x, pairingSwap_mem_centralizer hσ ha hx hax hasx,
            sign_pairingSwap hax hσaσx, ?_⟩
          rw [show ({a, σ a} : Finset Ω) ∪ {b, σ b} = {b, σ b} ∪ {a, σ a} from
            Finset.union_comm _ _]
          rw [pairingSwap_image_union_of_fixed_pair hσ ha hx hb hax hasx hPa_ne_Pb.symm
            hPb_ne_Px, pair_eq_of_mem hσ hy hyb, Finset.union_comm]
        · have hby : b ≠ y := fun h => ne_left_of_notMem (p := b) hyb h.symm
          have hbsy : b ≠ σ y :=
            fun h => ne_right_of_notMem (p := b) hyb (by rw [← hσ y, ← h])
          have hσbσy : σ b ≠ σ y := fun h => hby (by rw [← hσ b, ← hσ y, h])
          have hax : a ≠ x := fun h => ne_left_of_notMem (p := a) hxa h.symm
          have hasx : a ≠ σ x :=
            fun h => ne_right_of_notMem (p := a) hxa (by rw [← hσ x, ← h])
          have hσaσx : σ a ≠ σ x := fun h => hax (by rw [← hσ a, ← hσ x, h])
          have hPb_ne_Px : ({b, σ b} : Finset Ω) ≠ {x, σ x} :=
            pair_ne_of_notMem (σ := σ) (p := b) (q := x) hxb
          have hPx_ne_Pb : ({x, σ x} : Finset Ω) ≠ {b, σ b} := hPb_ne_Px.symm
          refine ⟨pairingSwap σ b y * pairingSwap σ a x, ?_, ?_, ?_⟩
          · exact (Subgroup.centralizer ({σ} : Set (Perm Ω))).mul_mem
              (pairingSwap_mem_centralizer hσ hb hy hby hbsy)
              (pairingSwap_mem_centralizer hσ ha hx hax hasx)
          · rw [Perm.sign_mul, sign_pairingSwap hby hσbσy, sign_pairingSwap hax hσaσx,
              one_mul]
          · rw [show ⇑(pairingSwap σ b y * pairingSwap σ a x) =
                ⇑(pairingSwap σ b y) ∘ ⇑(pairingSwap σ a x) from rfl]
            rw [show ({a, σ a} : Finset Ω) ∪ {b, σ b} = {b, σ b} ∪ {a, σ a} from
              Finset.union_comm _ _]
            rw [← Finset.image_image (f := ⇑(pairingSwap σ a x))
              (g := ⇑(pairingSwap σ b y))
              (s := ({b, σ b} : Finset Ω) ∪ {a, σ a})]
            rw [pairingSwap_image_union_of_fixed_pair hσ ha hx hb hax hasx hPa_ne_Pb.symm
              hPb_ne_Px]
            rw [show ({b, σ b} : Finset Ω) ∪ {x, σ x} = {x, σ x} ∪ {b, σ b} from
              Finset.union_comm _ _]
            rw [pairingSwap_image_union_of_fixed_pair hσ hb hy hx hby hbsy hPx_ne_Pb hPxy]

theorem sup_centralizer_eq_of_threeCycles {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (h6 : 6 ≤ Fintype.card Ω) {σ : Perm Ω} (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x y, σ x = x → σ y = y → x = y) {G Y : Subgroup (Perm Ω)}
    (hAG : alternatingGroup Ω ≤ G) (hYG : Y ≤ G) {S : Finset Ω} (hS : S.card = 4)
    (hSσ : ∀ x ∈ S, σ x ∈ S) (hSY : ∀ g : Perm Ω, g.IsThreeCycle → g.support ⊆ S → g ∈ Y)
    (hRY : ∀ ω, σ ω = ω → ∃ R : Finset Ω, ω ∈ R ∧ R.card = 3 ∧
      ∀ g : Perm Ω, g.IsThreeCycle → g.support ⊆ R → g ∈ Y) :
    Y ⊔ (Subgroup.centralizer {σ} ⊓ G) = G := by
  classical
  set C : Subgroup (Perm Ω) := Subgroup.centralizer ({σ} : Set (Perm Ω)) ⊓ G with hC
  set H : Subgroup (Perm Ω) := Y ⊔ C with hH
  have hCG : C ≤ G := fun x hx => (Subgroup.mem_inf.mp hx).2
  have hYH : Y ≤ H := le_sup_left
  have hCH : C ≤ H := le_sup_right
  have hHG : H ≤ G := sup_le hYG hCG
  have hσ2 : σ ^ 2 = 1 := by
    ext z
    exact hσ z
  have hS_nonfixed : ∀ x ∈ S, σ x ≠ x := by
    intro x hxS hxfix
    have hTcard : (S.erase x).card = 3 := by
      rw [Finset.card_erase_of_mem hxS, hS]
    have hTinv : ∀ y ∈ S.erase x, σ y ∈ S.erase x := by
      intro y hy
      rw [Finset.mem_erase] at hy ⊢
      refine ⟨?_, hSσ y hy.2⟩
      intro h
      exact hy.1 (by rw [← hσ y, h, hxfix])
    have hodd : Odd (S.erase x).card := by
      rw [hTcard]
      exact ⟨1, by norm_num⟩
    obtain ⟨y, hyT, hyfix⟩ := exists_fixed_of_odd_card_of_involution hσ2 hTinv hodd
    exact (Finset.mem_erase.mp hyT).1 (hfix y x hyfix hxfix)
  obtain ⟨a, haS⟩ := Finset.card_pos.mp (by rw [hS]; norm_num)
  have ha : σ a ≠ a := hS_nonfixed a haS
  have hσaS : σ a ∈ S := hSσ a haS
  have haσa : a ≠ σ a := ha.symm
  have hσa_erase : σ a ∈ S.erase a := by
    rw [Finset.mem_erase]
    exact ⟨ha, hσaS⟩
  have hcardT : ((S.erase a).erase (σ a)).card = 2 := by
    rw [Finset.card_erase_of_mem hσa_erase, Finset.card_erase_of_mem haS, hS]
  have hex : ∃ b ∈ (S.erase a).erase (σ a), σ b ≠ b := by
    by_contra h
    push Not at h
    obtain ⟨b1, hb1, b2, hb2, hne⟩ :=
      Finset.one_lt_card.mp (by rw [hcardT]; norm_num)
    exact hne (hfix b1 b2 (h b1 hb1) (h b2 hb2))
  obtain ⟨b, hbT, hb_nonfix⟩ := hex
  have hbσa : b ≠ σ a := (Finset.mem_erase.mp hbT).1
  have hb_erase : b ∈ S.erase a := (Finset.mem_erase.mp hbT).2
  have hba : b ≠ a := (Finset.mem_erase.mp hb_erase).1
  have hbS : b ∈ S := (Finset.mem_erase.mp hb_erase).2
  have hb : σ b ≠ b := hb_nonfix
  have hσbS : σ b ∈ S := hSσ b hbS
  have hσb_ne_a : σ b ≠ a := fun h => hbσa (by rw [← hσ b, h])
  have hσb_ne_σa : σ b ≠ σ a := fun h => hba (by rw [← hσ b, ← hσ a, h])
  have hσbT : σ b ∈ (S.erase a).erase (σ a) := by
    rw [Finset.mem_erase, Finset.mem_erase]
    exact ⟨hσb_ne_σa, hσb_ne_a, hσbS⟩
  have hpairT : ({b, σ b} : Finset Ω) = (S.erase a).erase (σ a) := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hbT
      · exact hσbT
    · rw [hcardT, Finset.card_pair hb.symm]
  have hS_eq : S = ({a, σ a} : Finset Ω) ∪ {b, σ b} := by
    have h1 : S = insert a (S.erase a) := (Finset.insert_erase haS).symm
    have h2 : S.erase a = insert (σ a) ((S.erase a).erase (σ a)) :=
      (Finset.insert_erase hσa_erase).symm
    rw [h1, h2, hpairT]
    ext z
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
    tauto
  have hab : a ≠ b := hba.symm
  have hasb : a ≠ σ b := fun h => hbσa (by rw [← hσ b, h])
  have hPa_ne_Pb : ({a, σ a} : Finset Ω) ≠ {b, σ b} := by
    refine (pair_ne_of_notMem (σ := σ) (p := b) (q := a) ?_).symm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab, hasb⟩
  have hunion : ∀ x y : Ω, σ x ≠ x → σ y ≠ y → x ≠ y → x ≠ σ y →
      ∀ g : Perm Ω, g.IsThreeCycle →
        g.support ⊆ ({x, σ x} : Finset Ω) ∪ {y, σ y} → g ∈ H := by
    intro x y hx hy hxy hxsy g hg hgsupp
    obtain ⟨τ, hτcent, hτsign, hτmap⟩ :=
      exists_pairingSwap_image_union hσ ha hb hab hasb hx hy hxy hxsy
    have hτG : τ ∈ G := hAG (Perm.mem_alternatingGroup.mpr hτsign)
    have hτC : τ ∈ C := ⟨hτcent, hτG⟩
    have hτH : τ ∈ H := hCH hτC
    let g' : Perm Ω := τ⁻¹ * g * τ
    have hg' : g'.IsThreeCycle := by
      have hcyc : (τ⁻¹ * g * τ).cycleType = g.cycleType := by
        simpa using Equiv.Perm.cycleType_conj (σ := g) (τ := τ⁻¹)
      rw [Equiv.Perm.IsThreeCycle] at hg ⊢
      dsimp [g']
      rw [hcyc]
      exact hg
    have hsupp' : g'.support ⊆ S := by
      have hmap : g'.support = Finset.image (⇑τ⁻¹) g.support := by
        have h := Equiv.Perm.support_conj (σ := τ⁻¹) (τ := g)
        simpa [g', Finset.map_eq_image] using h
      rw [hmap]
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      have hwU : w ∈ ({x, σ x} : Finset Ω) ∪ {y, σ y} := hgsupp hw
      have hwImg : w ∈ Finset.image τ (({a, σ a} : Finset Ω) ∪ {b, σ b}) := by
        rw [hτmap]
        exact hwU
      rw [Finset.mem_image] at hwImg
      obtain ⟨s, hs, hsw⟩ := hwImg
      rw [← hsw, hS_eq]
      simpa using hs
    have hg'Y : g' ∈ Y := hSY g' hg' hsupp'
    have hgeq : g = τ * g' * τ⁻¹ := by
      dsimp [g']
      group
    rw [hgeq]
    exact H.mul_mem (H.mul_mem hτH (hYH hg'Y)) (H.inv_mem hτH)
  have hthree : ∀ x y z : Ω, σ x ≠ x → σ y ≠ y → σ z ≠ z →
      ({x, σ x} : Finset Ω) ≠ {y, σ y} →
      ({x, σ x} : Finset Ω) ≠ {z, σ z} →
      ({y, σ y} : Finset Ω) ≠ {z, σ z} →
      swap x y * swap y z ∈ H := by
    intro x y z hx hy hz hPxy hPxz hPyz
    have hy_not_Px : y ∉ ({x, σ x} : Finset Ω) ∧ σ y ∉ ({x, σ x} : Finset Ω) :=
      not_mem_pair_of_ne hσ hx hy hPxy
    have hx_not_Py : x ∉ ({y, σ y} : Finset Ω) ∧ σ x ∉ ({y, σ y} : Finset Ω) :=
      not_mem_pair_of_ne hσ hy hx hPxy.symm
    have hz_not_Px : z ∉ ({x, σ x} : Finset Ω) ∧ σ z ∉ ({x, σ x} : Finset Ω) :=
      not_mem_pair_of_ne hσ hx hz hPxz
    have hx_not_Pz : x ∉ ({z, σ z} : Finset Ω) ∧ σ x ∉ ({z, σ z} : Finset Ω) :=
      not_mem_pair_of_ne hσ hz hx hPxz.symm
    have hz_not_Py : z ∉ ({y, σ y} : Finset Ω) ∧ σ z ∉ ({y, σ y} : Finset Ω) :=
      not_mem_pair_of_ne hσ hy hz hPyz
    have hy_not_Pz : y ∉ ({z, σ z} : Finset Ω) ∧ σ y ∉ ({z, σ z} : Finset Ω) :=
      not_mem_pair_of_ne hσ hz hy hPyz.symm
    have hxy : x ≠ y := fun h => hy_not_Px.1 (by rw [← h]; exact Finset.mem_insert_self _ _)
    have hxσy : x ≠ σ y := fun h => hx_not_Py.1 (by rw [h]; simp)
    have hyσx : y ≠ σ x := fun h => hy_not_Px.1 (by rw [h]; simp)
    have hxz : x ≠ z := fun h => hz_not_Px.1 (by rw [← h]; exact Finset.mem_insert_self _ _)
    have hxσz : x ≠ σ z := fun h => hx_not_Pz.1 (by rw [h]; simp)
    have hzx : z ≠ x := hxz.symm
    have hzxσ : z ≠ σ x := fun h => hz_not_Px.1 (by rw [h]; simp)
    have hσxz : σ x ≠ z := fun h => hx_not_Pz.2 (by rw [h]; exact Finset.mem_insert_self _ _)
    have hσxσz : σ x ≠ σ z := fun h => hx_not_Pz.2 (by rw [h]; simp)
    have hyz : y ≠ z := fun h => hz_not_Py.1 (by rw [← h]; exact Finset.mem_insert_self _ _)
    have hyσz : y ≠ σ z := fun h => hy_not_Pz.1 (by rw [h]; simp)
    have hzσz : z ≠ σ z := hz.symm
    have hcc_cyc : (swap x y * swap y (σ x)).IsThreeCycle :=
      CFSG.AGLEmbedding.isThreeCycle_swap_mul_swap hxy hx.symm hyσx
    have hcc_supp : (swap x y * swap y (σ x)).support ⊆
        ({x, σ x} : Finset Ω) ∪ {y, σ y} := by
      rw [CFSG.AGLEmbedding.support_swap_mul_swap_of_ne hxy hx.symm hyσx]
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at ht ⊢
      rcases ht with rfl | rfl | rfl
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (Or.inr rfl)
    have hccH : swap x y * swap y (σ x) ∈ H :=
      hunion x y hx hy hxy hxσy _ hcc_cyc hcc_supp
    have hhh_cyc : (swap (σ x) z * swap z (σ z)).IsThreeCycle :=
      CFSG.AGLEmbedding.isThreeCycle_swap_mul_swap hσxz hσxσz hzσz
    have hhh_supp : (swap (σ x) z * swap z (σ z)).support ⊆
        ({x, σ x} : Finset Ω) ∪ {z, σ z} := by
      rw [CFSG.AGLEmbedding.support_swap_mul_swap_of_ne hσxz hσxσz hzσz]
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at ht ⊢
      rcases ht with rfl | rfl | rfl
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    have hhhH : swap (σ x) z * swap z (σ z) ∈ H :=
      hunion x z hx hz hxz hxσz _ hhh_cyc hhh_supp
    have hhx : (swap (σ x) z * swap z (σ z)) x = x := by
      rw [Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne (a := z) (b := σ z) (x := x) hxz hxσz,
        Equiv.swap_apply_of_ne_of_ne (a := σ x) (b := z) (x := x) hx.symm hxz]
    have hhy : (swap (σ x) z * swap z (σ z)) y = y := by
      rw [Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne (a := z) (b := σ z) (x := y) hyz hyσz,
        Equiv.swap_apply_of_ne_of_ne (a := σ x) (b := z) (x := y) hyσx hyz]
    have hhσx : (swap (σ x) z * swap z (σ z)) (σ x) = z := by
      rw [Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne (a := z) (b := σ z) (x := σ x) hσxz hσxσz,
        Equiv.swap_apply_left]
    have hconj : (swap (σ x) z * swap z (σ z)) * (swap x y * swap y (σ x)) *
        (swap (σ x) z * swap z (σ z))⁻¹ = swap x y * swap y z := by
      rw [show (swap (σ x) z * swap z (σ z)) * (swap x y * swap y (σ x)) *
          (swap (σ x) z * swap z (σ z))⁻¹ =
          ((swap (σ x) z * swap z (σ z)) * swap x y *
            (swap (σ x) z * swap z (σ z))⁻¹) *
          ((swap (σ x) z * swap z (σ z)) * swap y (σ x) *
            (swap (σ x) z * swap z (σ z))⁻¹) by group]
      rw [← Equiv.swap_apply_apply (swap (σ x) z * swap z (σ z)) x y,
        ← Equiv.swap_apply_apply (swap (σ x) z * swap z (σ z)) y (σ x)]
      rw [hhx, hhy, hhσx]
    rw [← hconj]
    exact H.mul_mem (H.mul_mem hhhH hccH) (H.inv_mem hhhH)
  have hswapmem : ∀ x y z : Ω, σ x ≠ x → σ y ≠ y → σ z ≠ z →
      x ≠ y → x ≠ z → y ≠ z → swap x y * swap y z ∈ H := by
    intro x y z hx hy hz hxy hxz hyz
    by_cases hxy_pair : σ x = y ∨ σ y = x
    · have hσxy : σ x = y := by
        rcases hxy_pair with h | h
        · exact h
        · rw [← h, hσ y]
      have hxzσ : x ≠ σ z := fun h => hyz (by rw [← hσxy, h, hσ z])
      have hcyc : (swap x y * swap y z).IsThreeCycle :=
        CFSG.AGLEmbedding.isThreeCycle_swap_mul_swap hxy hxz hyz
      have hsupp : (swap x y * swap y z).support ⊆
          ({x, σ x} : Finset Ω) ∪ {z, σ z} := by
        rw [CFSG.AGLEmbedding.support_swap_mul_swap_of_ne hxy hxz hyz]
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at ht ⊢
        rcases ht with rfl | rfl | rfl
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr hσxy.symm)
        · exact Or.inr (Or.inl rfl)
      exact hunion x z hx hz hxz hxzσ _ hcyc hsupp
    · by_cases hxz_pair : σ x = z ∨ σ z = x
      · have hσxz : σ x = z := by
          rcases hxz_pair with h | h
          · exact h
          · rw [← h, hσ z]
        have hxyσ : x ≠ σ y := fun h => hxy_pair (Or.inl (by rw [h, hσ y]))
        have hcyc : (swap x y * swap y z).IsThreeCycle :=
          CFSG.AGLEmbedding.isThreeCycle_swap_mul_swap hxy hxz hyz
        have hsupp : (swap x y * swap y z).support ⊆
            ({x, σ x} : Finset Ω) ∪ {y, σ y} := by
          rw [CFSG.AGLEmbedding.support_swap_mul_swap_of_ne hxy hxz hyz]
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at ht ⊢
          rcases ht with rfl | rfl | rfl
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl (Or.inr hσxz.symm)
        exact hunion x y hx hy hxy hxyσ _ hcyc hsupp
      · by_cases hyz_pair : σ y = z ∨ σ z = y
        · have hσyz : σ y = z := by
            rcases hyz_pair with h | h
            · exact h
            · rw [← h, hσ z]
          have hxyσ : x ≠ σ y := fun h => hxz (by rw [h, hσyz])
          have hcyc : (swap x y * swap y z).IsThreeCycle :=
            CFSG.AGLEmbedding.isThreeCycle_swap_mul_swap hxy hxz hyz
          have hsupp : (swap x y * swap y z).support ⊆
              ({x, σ x} : Finset Ω) ∪ {y, σ y} := by
            rw [CFSG.AGLEmbedding.support_swap_mul_swap_of_ne hxy hxz hyz]
            intro t ht
            simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at ht ⊢
            rcases ht with rfl | rfl | rfl
            · exact Or.inl (Or.inl rfl)
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr hσyz.symm)
          exact hunion x y hx hy hxy hxyσ _ hcyc hsupp
        · have hPxy : ({x, σ x} : Finset Ω) ≠ {y, σ y} := by
            refine pair_ne_of_notMem (σ := σ) (p := x) (q := y) ?_
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hxy.symm, fun h => hxy_pair (Or.inr (by rw [h, hσ x]))⟩
          have hPxz : ({x, σ x} : Finset Ω) ≠ {z, σ z} := by
            refine pair_ne_of_notMem (σ := σ) (p := x) (q := z) ?_
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hxz.symm, fun h => hxz_pair (Or.inl h.symm)⟩
          have hPyz : ({y, σ y} : Finset Ω) ≠ {z, σ z} := by
            refine pair_ne_of_notMem (σ := σ) (p := y) (q := z) ?_
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hyz.symm, fun h => hyz_pair (Or.inl h.symm)⟩
          exact hthree x y z hx hy hz hPxy hPxz hPyz
  have hnonfixed : ∀ g : Perm Ω, g.IsThreeCycle →
      (∀ z ∈ g.support, σ z ≠ z) → g ∈ H := by
    intro g hg hgnf
    have hgcard : g.support.card = 3 := card_support_eq_three_iff.mpr hg
    obtain ⟨x, y, z, hxy, hxz, hyz, hsupp⟩ := Finset.card_eq_three.mp hgcard
    have hx : σ x ≠ x := hgnf x (by rw [hsupp]; simp)
    have hy : σ y ≠ y := hgnf y (by rw [hsupp]; simp)
    have hz : σ z ≠ z := hgnf z (by rw [hsupp]; simp)
    rcases CFSG.AlternatingAutomorphism.eq_or_eq_inv_of_support_eq
      (CFSG.AGLEmbedding.isThreeCycle_swap_mul_swap hxy hxz hyz) hg
      (by rw [CFSG.AGLEmbedding.support_swap_mul_swap_of_ne hxy hxz hyz, hsupp])
      with h | h
    · rw [h]
      exact hswapmem x y z hx hy hz hxy hxz hyz
    · rw [h]
      exact H.inv_mem (hswapmem x y z hx hy hz hxy hxz hyz)
  let P : Type _ := {z : Ω // σ z ≠ z}
  have hPcard : 5 ≤ Nat.card P := by
    have hfix_card : (Finset.univ.filter (fun z => σ z = z)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact hfix x y hx hy
    have hsplit : (Finset.univ.filter (fun z => σ z ≠ z)).card +
        (Finset.univ.filter (fun z => σ z = z)).card = Fintype.card Ω := by
      simpa using
        Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun z => σ z ≠ z)
    have hPnat : Nat.card P = (Finset.univ.filter (fun z => σ z ≠ z)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    omega
  have hAltP : ∀ g : Perm P, g ∈ alternatingGroup P → Perm.ofSubtype g ∈ H := by
    intro g hg
    have hmem : g ∈ Subgroup.closure {c : Perm P | c.IsThreeCycle} := by
      rw [Perm.closure_three_cycles_eq_alternating]
      exact hg
    have hmap := Subgroup.mem_map_of_mem
      (Perm.ofSubtype (p := fun z => σ z ≠ z) : Perm P →* Perm Ω) hmem
    rw [MonoidHom.map_closure] at hmap
    have hsub : ∀ c : Perm P, c.IsThreeCycle → Perm.ofSubtype c ∈ H := by
      intro c hc
      refine hnonfixed (Perm.ofSubtype c) ?_ ?_
      · rw [Perm.IsThreeCycle, Perm.cycleType_ofSubtype, ← Perm.IsThreeCycle]
        exact hc
      · intro z hz
        by_contra hzf
        exact (Perm.mem_support.mp hz) (Perm.ofSubtype_apply_of_not_mem c (by simpa using hzf))
    exact (Subgroup.closure_le H).mpr (by rintro _ ⟨c, hc, rfl⟩; exact hsub c hc) hmap
  have hfixed : ∀ ω : Ω, σ ω = ω → ∀ u v : Ω, u ≠ v → σ u ≠ u → σ v ≠ v →
      swap ω u * swap u v ∈ H := by
    intro ω hω u v huv hu hv
    obtain ⟨R, hωR, hRcard, hRYall⟩ := hRY ω hω
    have hRerase : (R.erase ω).card = 2 := by
      rw [Finset.card_erase_of_mem hωR, hRcard]
    obtain ⟨r, s, hrs, hRs⟩ := Finset.card_eq_two.mp hRerase
    have hr_erase : r ∈ R.erase ω := by
      rw [hRs]
      exact Finset.mem_insert_self _ _
    have hs_erase : s ∈ R.erase ω := by
      rw [hRs]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hrR : r ∈ R := (Finset.mem_erase.mp hr_erase).2
    have hsR : s ∈ R := (Finset.mem_erase.mp hs_erase).2
    have hrω : r ≠ ω := (Finset.mem_erase.mp hr_erase).1
    have hsω : s ≠ ω := (Finset.mem_erase.mp hs_erase).1
    have hr_nf : σ r ≠ r := fun h => hrω (hfix r ω h hω)
    have hs_nf : σ s ≠ s := fun h => hsω (hfix s ω h hω)
    have hωr : ω ≠ r := hrω.symm
    have hωs : ω ≠ s := hsω.symm
    have hc0_cyc : (swap ω r * swap r s).IsThreeCycle :=
      CFSG.AGLEmbedding.isThreeCycle_swap_mul_swap hωr hωs hrs
    have hc0_supp : (swap ω r * swap r s).support ⊆ R := by
      rw [CFSG.AGLEmbedding.support_swap_mul_swap_of_ne hωr hωs hrs]
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact hωR
      · exact hrR
      · exact hsR
    have hc0Y : swap ω r * swap r s ∈ Y := hRYall _ hc0_cyc hc0_supp
    have hc0H : swap ω r * swap r s ∈ H := hYH hc0Y
    let rP : P := ⟨r, hr_nf⟩
    let sP : P := ⟨s, hs_nf⟩
    let uP : P := ⟨u, hu⟩
    let vP : P := ⟨v, hv⟩
    have hrsP : rP ≠ sP := by
      intro h
      exact hrs (congrArg Subtype.val h)
    let xfun : Fin 2 → P := fun i => if (i : ℕ) = 0 then rP else sP
    have hxinj : Function.Injective xfun := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · have h : rP = sP := by simpa [xfun] using hij
        exact absurd h hrsP
      · have h : sP = rP := by simpa [xfun] using hij
        exact absurd h.symm hrsP
      · rfl
    let x : Fin 2 ↪ P := ⟨xfun, hxinj⟩
    let yfun : Fin 2 → P := fun i => if (i : ℕ) = 0 then uP else vP
    have hyinj : Function.Injective yfun := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · have h : uP = vP := by simpa [yfun] using hij
        exact absurd (congrArg Subtype.val h) huv
      · have h : vP = uP := by simpa [yfun] using hij
        exact absurd (congrArg Subtype.val h.symm) huv
      · rfl
    let y : Fin 2 ↪ P := ⟨yfun, hyinj⟩
    have hmt : MulAction.IsMultiplyPretransitive (↥(alternatingGroup P)) P
        (Nat.card P - 2) := alternatingGroup.isMultiplyPretransitive P
    have hmt2 : MulAction.IsMultiplyPretransitive (↥(alternatingGroup P)) P 2 :=
      @MulAction.isMultiplyPretransitive_of_le (↥(alternatingGroup P)) P _ _ 2
        (Nat.card P - 2) hmt (by omega) (by omega) (by infer_instance)
    obtain ⟨g, hgxy⟩ := (MulAction.isMultiplyPretransitive_iff.mp hmt2) x y
    have hgr : (g : Perm P) rP = uP := by
      have h0 := congrArg (fun e : Fin 2 ↪ P => e 0) hgxy
      have h0' : (g : Perm P) (x 0) = y 0 := by
        change (g • x) 0 = y 0
        exact h0
      have hx0 : x 0 = rP := by
        change xfun 0 = rP
        simp [xfun]
      have hy0 : y 0 = uP := by
        change yfun 0 = uP
        simp [yfun]
      rwa [hx0, hy0] at h0'
    have hgs : (g : Perm P) sP = vP := by
      have h1 := congrArg (fun e : Fin 2 ↪ P => e 1) hgxy
      have h1' : (g : Perm P) (x 1) = y 1 := by
        change (g • x) 1 = y 1
        exact h1
      have hx1 : x 1 = sP := by
        change xfun 1 = sP
        simp [xfun]
      have hy1 : y 1 = vP := by
        change yfun 1 = vP
        simp [yfun]
      rwa [hx1, hy1] at h1'
    let hperm : Perm Ω := Perm.ofSubtype (g : Perm P)
    have hhH : hperm ∈ H := hAltP (g : Perm P) g.property
    have hω' : hperm ω = ω := by
      apply Perm.ofSubtype_apply_of_not_mem
      simpa using hω
    have hr' : hperm r = u := by
      rw [Perm.ofSubtype_apply_of_mem (g : Perm P) hr_nf, hgr]
    have hs' : hperm s = v := by
      rw [Perm.ofSubtype_apply_of_mem (g : Perm P) hs_nf, hgs]
    have hconj : hperm * (swap ω r * swap r s) * hperm⁻¹ = swap ω u * swap u v := by
      rw [show hperm * (swap ω r * swap r s) * hperm⁻¹ =
          (hperm * swap ω r * hperm⁻¹) * (hperm * swap r s * hperm⁻¹) by group]
      rw [← Equiv.swap_apply_apply hperm ω r, ← Equiv.swap_apply_apply hperm r s]
      rw [hω', hr', hs']
    have hconjH : hperm * (swap ω r * swap r s) * hperm⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem hhH hc0H) (H.inv_mem hhH)
    rwa [hconj] at hconjH
  have hcycles : ∀ x y z : Ω, x ≠ y → x ≠ z → y ≠ z → swap x y * swap y z ∈ H := by
    intro x y z hxy hxz hyz
    by_cases hx : σ x = x
    · have hy : σ y ≠ y := fun h => hxy (hfix y x h hx).symm
      have hz : σ z ≠ z := fun h => hxz (hfix z x h hx).symm
      exact hfixed x hx y z hyz hy hz
    · by_cases hy : σ y = y
      · have hz : σ z ≠ z := fun h => hyz (hfix z y h hy).symm
        rw [CFSG.AGLEmbedding.swap_mul_swap_rotate hxy hxz]
        exact hfixed y hy z x hxz.symm hz hx
      · by_cases hz : σ z = z
        · rw [CFSG.AGLEmbedding.swap_mul_swap_rotate hxy hxz,
            CFSG.AGLEmbedding.swap_mul_swap_rotate hyz hxy.symm]
          exact hfixed z hz x y hxy hx hy
        · exact hswapmem x y z hx hy hz hxy hxz hyz
  have hAlt : alternatingGroup Ω ≤ H :=
    CFSG.AGLEmbedding.alternatingGroup_le_of_swap_mul_swap_mem hcycles
  refine le_antisymm (sup_le hYG hCG) ?_
  intro g hg
  by_cases hgAlt : g ∈ alternatingGroup Ω
  · exact hAlt hgAlt
  · have hsign : Perm.sign g = -1 := by
      rcases Int.units_eq_one_or (Perm.sign g) with h | h
      · exact absurd (Perm.mem_alternatingGroup.mpr h) hgAlt
      · exact h
    have hswap_cent : swap a (σ a) ∈ Subgroup.centralizer ({σ} : Set (Perm Ω)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (swap_sigma_commute hσ).eq
    have hswap_sign : Perm.sign (swap a (σ a)) = -1 := Perm.sign_swap ha.symm
    have hga_even : g * swap a (σ a) ∈ alternatingGroup Ω := by
      rw [Perm.mem_alternatingGroup, Perm.sign_mul, hsign, hswap_sign]
      norm_num
    have hgaG : g * swap a (σ a) ∈ G := hAG hga_even
    have hswapG : swap a (σ a) ∈ G := by
      have h := G.mul_mem (G.inv_mem hg) hgaG
      rwa [show g⁻¹ * (g * swap a (σ a)) = swap a (σ a) by group] at h
    have hswapH : swap a (σ a) ∈ H := hCH ⟨hswap_cent, hswapG⟩
    have hgs_even : g * (swap a (σ a))⁻¹ ∈ alternatingGroup Ω := by
      rw [Perm.mem_alternatingGroup, Perm.sign_mul, hsign, Perm.sign_inv, hswap_sign]
      norm_num
    have hgsH : g * (swap a (σ a))⁻¹ ∈ H := hAlt hgs_even
    have heq : g = (g * (swap a (σ a))⁻¹) * swap a (σ a) := by group
    rw [heq]
    exact H.mul_mem hgsH hswapH

end CFSG.LocalAnalysis.WeakClosure81.Asch59

module

public import CFSG.Timmesfeld.RankTwo.Levi
public import CFSG.Timmesfeld.Transvection.PresSpRoots
public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Open.StatedDefs
public import CFSG.LieType.Universal.Unitary.Extras
import CFSG.LieType.Universal.Unitary.Extras.Basic
import CFSG.LieType.Universal.Unitary.Extras.Commutator
import all CFSG.LieType.Universal.Unitary.Roots
import Mathlib.Tactic
public import CFSG.LieType.Steinberg.Isogeny.Lift
public import CFSG.LieType.TitsSimplicity
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.RankOne
public import Certificates.Certificate43

public section

namespace CFSG.Timmesfeld.Transvection.Pres

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.Steinberg
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)
open scoped commutatorElement

@[expose] def bcLastIdx (r : ℕ) (hr : 1 ≤ r) : Fin ((2 * r + 1) / 2) := ⟨r - 1, by omega⟩

@[expose] def bcPrevIdx (r : ℕ) (hr : 2 ≤ r) : Fin ((2 * r + 1) / 2) := ⟨r - 2, by omega⟩

@[expose] def bc2Coeffs : Finset (ℤ × ℤ) :=
  {(1, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2),
    (-1, 0), (0, -1), (0, -2), (-1, -1), (-1, -2), (-2, -2)}

private def bc2PosCoeffs : Finset (ℤ × ℤ) :=
  {(1, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)}

private def a1bc1Coeffs : Finset (ℤ × ℤ) :=
  {(1, 0), (-1, 0), (0, 1), (0, -1), (0, 2), (0, -2)}

private lemma toStd_bc2_formula {r : ℕ} (hr : 2 ≤ r) (x y : ℤ) :
    toStd (2 * r + 1)
        (x • Pi.single (bcPrevIdx r hr) 1 + y • Pi.single (bcLastIdx r (by omega)) 1) =
      x • Pi.single (bcPrevIdx r hr) 1 + (y - x) • Pi.single (bcLastIdx r (by omega)) 1 := by
  rw [toStd_add']
  simp only [toStd_zsmul]
  have hodd : ¬ Even (2 * r + 1) := by
    rw [Nat.not_even_iff_odd]
    exact ⟨r, by omega⟩
  have hP : (bcPrevIdx r hr).val + 1 < (2 * r + 1) / 2 := by
    change r - 2 + 1 < (2 * r + 1) / 2
    omega
  have hL : ¬ (bcLastIdx r (by omega)).val + 1 < (2 * r + 1) / 2 := by
    change ¬ r - 1 + 1 < (2 * r + 1) / 2
    have h1 : r - 1 + 1 = r := Nat.sub_add_cancel (by omega)
    rw [h1]
    omega
  rw [toStd_single_of_odd hodd hL]
  rw [toStd_single_of_lt (2 * r + 1) hP]
  have hPL : (⟨(bcPrevIdx r hr).val + 1, by
      have := (bcPrevIdx r hr).isLt
      omega⟩ : Fin ((2 * r + 1) / 2)) = bcLastIdx r (by omega) := by
    apply Fin.ext
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
    simp [bcPrevIdx, bcLastIdx]
  rw [hPL]
  module

theorem toStd_bc2 {r : ℕ} (hr : 2 ≤ r) :
    let P := bcPrevIdx r hr
    let L := bcLastIdx r (Nat.one_le_of_lt hr)
    toStd (2 * r + 1) (Pi.single P 1) = rt (Sum.inl P) (Sum.inr L) ∧
    toStd (2 * r + 1) (Pi.single L 1) = wt (Sum.inl L) ∧
    toStd (2 * r + 1) (2 • Pi.single L 1) = rt (Sum.inl L) (Sum.inl L) ∧
    toStd (2 * r + 1) (Pi.single P 1 + Pi.single L 1) = wt (Sum.inl P) ∧
    toStd (2 * r + 1) (Pi.single P 1 + 2 • Pi.single L 1) = rt (Sum.inl P) (Sum.inl L) ∧
    toStd (2 * r + 1) (2 • Pi.single P 1 + 2 • Pi.single L 1) = rt (Sum.inl P) (Sum.inl P) := by
  dsimp only
  constructor
  · have h := toStd_bc2_formula hr 1 0
    simpa [rt, wt] using h
  constructor
  · have h := toStd_bc2_formula hr 0 1
    simpa [rt, wt] using h
  constructor
  · have h := toStd_bc2_formula hr 0 2
    simpa [rt, wt, two_mul] using h
  constructor
  · have h := toStd_bc2_formula hr 1 1
    simpa [rt, wt] using h
  constructor
  · have h := toStd_bc2_formula hr 1 2
    simpa [rt, wt] using h
  · have h := toStd_bc2_formula hr 2 2
    simpa [rt, wt, two_mul] using h

theorem unitaryLongRoot_odd {r : ℕ} (h : 2 ≤ 2 * r + 1) :
    unitaryLongRoot (2 * r + 1) h =
      2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt
        (Nat.pos_of_mul_pos_left (Nat.le_of_lt_succ h)))) 1 := by
  unfold unitaryLongRoot
  have hmod : (2 * r + 1) % 2 ≠ 0 := by omega
  have hidx : (⟨(2 * r + 1) / 2 - 1, by omega⟩ : Fin ((2 * r + 1) / 2)) =
      bcLastIdx r (by omega) := by
    apply Fin.ext
    simp [bcLastIdx]
    omega
  rw [if_neg hmod, hidx]

theorem statedLieAdmissible_psu_odd {r : ℕ} (hr : 2 ≤ r) {f : ℕ} (hf : 1 ≤ f) :
    CFSG.Open.StatedLieAdmissible .PSU (2 * r + 1) 2 f := by
  refine ⟨Nat.prime_two, hf, by omega, ?_⟩
  rintro h
  have := (Prod.mk.inj h).1
  omega

theorem eq_zero_last_of_mem_pairRoots {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) {r : ℕ} (hr : 2 ≤ r)
    {i j : Fin ((2 * r + 1) / 2)}
    (hi : i ≠ bcLastIdx r (Nat.one_le_of_lt hr))
    (hj : j ≠ bcLastIdx r (Nat.one_le_of_lt hr)) {γ : Fin ((2 * r + 1) / 2) → ℤ}
    (hγ : γ ∈ pairRoots (rootDatum hF (2 * r + 1)) i j) :
    γ (bcLastIdx r (Nat.one_le_of_lt hr)) = 0 :=
  hγ.2 _ (Ne.symm hi) (Ne.symm hj)

private lemma eq_bc2_of_support {r : ℕ} (hr : 2 ≤ r) {γ : Fin ((2 * r + 1) / 2) → ℤ}
    (hγ : ∀ k, k ≠ bcPrevIdx r hr → k ≠ bcLastIdx r (by omega) → γ k = 0) :
    γ = γ (bcPrevIdx r hr) • Pi.single (bcPrevIdx r hr) 1 +
      γ (bcLastIdx r (by omega)) • Pi.single (bcLastIdx r (by omega)) 1 := by
  funext k
  have hPL : (bcPrevIdx r hr) ≠ bcLastIdx r (by omega) := by
    apply Fin.ne_of_val_ne
    simp [bcPrevIdx, bcLastIdx]
    omega
  by_cases hkP : k = bcPrevIdx r hr
  · subst hkP
    have h1 : (Pi.single (bcPrevIdx r hr) (1 : ℤ) : Fin ((2 * r + 1) / 2) → ℤ)
        (bcPrevIdx r hr) = 1 := by
      rw [Pi.single_eq_same]
    have h2 : (Pi.single (bcLastIdx r (by omega)) (1 : ℤ) : Fin ((2 * r + 1) / 2) → ℤ)
        (bcPrevIdx r hr) = 0 := by
      rw [Pi.single_eq_of_ne hPL]
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, h1, h2]
    simp
  · by_cases hkL : k = bcLastIdx r (by omega)
    · subst hkL
      have h1 : (Pi.single (bcPrevIdx r hr) (1 : ℤ) : Fin ((2 * r + 1) / 2) → ℤ)
          (bcLastIdx r (by omega)) = 0 := by
        rw [Pi.single_eq_of_ne (Ne.symm hPL)]
      have h2 : (Pi.single (bcLastIdx r (by omega)) (1 : ℤ) : Fin ((2 * r + 1) / 2) → ℤ)
          (bcLastIdx r (by omega)) = 1 := by
        rw [Pi.single_eq_same]
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, h1, h2]
      simp
    · have hk0 := hγ k hkP hkL
      simp [hk0, hkP, hkL]

private lemma weight_sub_bounds {n : ℕ} {i j : Fin n} {a : Fin (n / 2)}
    (hji : j ≠ Fin.rev i) :
    -1 ≤ weight n i a - weight n j a ∧ weight n i a - weight n j a ≤ 1 := by
  have h1 := weight_apply_bounds i a
  have h2 := weight_apply_bounds j a
  have hne : ¬ (weight n i a = 1 ∧ weight n j a = -1) := by
    rintro ⟨hi1, hj1⟩
    apply hji
    apply Fin.ext
    rw [weight_apply'] at hi1 hj1
    simp only [Fin.val_rev]
    have := a.isLt
    have := i.isLt
    have := j.isLt
    split_ifs at hi1 hj1 <;> omega
  have hne2 : ¬ (weight n i a = -1 ∧ weight n j a = 1) := by
    rintro ⟨hi1, hj1⟩
    apply hji
    apply Fin.ext
    rw [weight_apply'] at hi1 hj1
    simp only [Fin.val_rev]
    have := a.isLt
    have := i.isLt
    have := j.isLt
    split_ifs at hi1 hj1 <;> omega
  constructor <;> omega

private lemma weight_prevI_eq_zero_or_lastI_eq_zero {r : ℕ} (hr : 2 ≤ r) (i : Fin (2 * r + 1)) :
    weight (2 * r + 1) i (bcPrevIdx r hr) = 0 ∨
      weight (2 * r + 1) i (bcLastIdx r (by omega)) = 0 := by
  by_contra h
  push Not at h
  have hP := h.1
  have hL := h.2
  rw [weight_apply'] at hP hL
  simp only [bcPrevIdx, bcLastIdx] at hP hL
  split_ifs at hP hL <;> omega

private lemma two_mul_eq_or {w : ℤ} (h1 : -1 ≤ w) (h2 : w ≤ 1) :
    (2 * w = -2 ∨ 2 * w = 0 ∨ 2 * w = 2) := by omega

private lemma bc2Coeffs_of_unit {x d : ℤ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1)
    (hd1 : -1 ≤ d) (hd2 : d ≤ 1) (h0 : x ≠ 0 ∨ d ≠ 0) :
    (x, x + d) ∈ bc2Coeffs := by
  have hx : x = -1 ∨ x = 0 ∨ x = 1 := by omega
  have hd : d = -1 ∨ d = 0 ∨ d = 1 := by omega
  rcases hx with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;>
    simp_all [bc2Coeffs]

private lemma bc2Coeffs_of_two {x d : ℤ} (hx : x = -2 ∨ x = 0 ∨ x = 2)
    (hd : d = -2 ∨ d = 0 ∨ d = 2) (h0 : x ≠ 0 ∨ d ≠ 0) (hone : x = 0 ∨ d = 0) :
    (x, x + d) ∈ bc2Coeffs := by
  rcases hx with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;>
    simp_all [bc2Coeffs]

private lemma roots_of_bc2_coeffs_pos {r : ℕ} (hr : 2 ≤ r) {x y : ℤ}
    (hxy : (x, y) ∈ bc2PosCoeffs) :
    (x • Pi.single (bcPrevIdx r hr) 1 + y • Pi.single (bcLastIdx r (by omega)) 1) ∈
      CFSG.LieType.RootSystem.roots (isFiniteType_cartan (2 * r + 1))
        (divisible (2 * r + 1)) := by
  have hodd : ¬ Even (2 * r + 1) := by
    rw [Nat.not_even_iff_odd]
    exact ⟨r, by omega⟩
  have hmid : Fin.rev (midIdx (2 * r + 1) hodd) = midIdx (2 * r + 1) hodd :=
    rev_midIdx hodd
  have hwmid : weight (2 * r + 1) (midIdx (2 * r + 1) hodd) = 0 :=
    weight_eq_zero_of_rev_eq hmid
  simp only [bc2PosCoeffs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hxy
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  · refine mem_roots_of_weight_sub (n := 2 * r + 1)
      (a := lowIdx (bcPrevIdx r hr)) (b := lowIdx (bcLastIdx r (by omega))) ?_ ?_
    · apply Fin.ne_of_val_ne
      simp [lowIdx, bcPrevIdx, bcLastIdx]
      omega
    · rw [toStd_bc2_formula hr 1 0, weight_lowIdx, weight_lowIdx]
      module
  · refine mem_roots_of_weight_sub (n := 2 * r + 1)
      (a := lowIdx (bcLastIdx r (by omega))) (b := midIdx (2 * r + 1) hodd) ?_ ?_
    · apply Fin.ne_of_val_ne
      simp [lowIdx, bcPrevIdx, bcLastIdx, midIdx]
      omega
    · rw [toStd_bc2_formula hr 0 1, weight_lowIdx, hwmid]
      module
  · refine mem_roots_of_weight_sub (n := 2 * r + 1)
      (a := lowIdx (bcLastIdx r (by omega))) (b := Fin.rev (lowIdx (bcLastIdx r (by omega)))) ?_ ?_
    · apply Fin.ne_of_val_ne
      simp [lowIdx, Fin.val_rev, bcLastIdx]
      omega
    · rw [toStd_bc2_formula hr 0 2, weight_lowIdx, weight_rev_lowIdx]
      module
  · refine mem_roots_of_weight_sub (n := 2 * r + 1)
      (a := lowIdx (bcPrevIdx r hr)) (b := midIdx (2 * r + 1) hodd) ?_ ?_
    · apply Fin.ne_of_val_ne
      simp [lowIdx, bcPrevIdx, bcLastIdx, midIdx]
      omega
    · rw [toStd_bc2_formula hr 1 1, weight_lowIdx, hwmid]
      module
  · refine mem_roots_of_weight_sub (n := 2 * r + 1)
      (a := lowIdx (bcPrevIdx r hr)) (b := Fin.rev (lowIdx (bcLastIdx r (by omega)))) ?_ ?_
    · apply Fin.ne_of_val_ne
      simp [lowIdx, Fin.val_rev, bcPrevIdx, bcLastIdx]
      omega
    · rw [toStd_bc2_formula hr 1 2, weight_lowIdx, weight_rev_lowIdx]
      module
  · refine mem_roots_of_weight_sub (n := 2 * r + 1)
      (a := lowIdx (bcPrevIdx r hr)) (b := Fin.rev (lowIdx (bcPrevIdx r hr))) ?_ ?_
    · apply Fin.ne_of_val_ne
      simp [lowIdx, Fin.val_rev, bcPrevIdx]
      omega
    · rw [toStd_bc2_formula hr 2 2, weight_lowIdx, weight_rev_lowIdx]
      module

private lemma roots_of_bc2_coeffs_neg {r : ℕ} (hr : 2 ≤ r) {x y : ℤ}
    (hxy : (-x, -y) ∈ bc2PosCoeffs) :
    (x • Pi.single (bcPrevIdx r hr) 1 + y • Pi.single (bcLastIdx r (by omega)) 1) ∈
      CFSG.LieType.RootSystem.roots (isFiniteType_cartan (2 * r + 1))
        (divisible (2 * r + 1)) := by
  have hpos := roots_of_bc2_coeffs_pos hr (x := -x) (y := -y) hxy
  have hneg := CFSG.LieType.Steinberg.OfCartan.neg_mem_roots
    (isFiniteType_cartan (2 * r + 1)) hpos
  convert hneg using 2
  module

private lemma roots_of_bc2_coeffs {r : ℕ} (hr : 2 ≤ r) {x y : ℤ}
    (hxy : (x, y) ∈ bc2Coeffs) :
    (x • Pi.single (bcPrevIdx r hr) 1 + y • Pi.single (bcLastIdx r (by omega)) 1) ∈
      CFSG.LieType.RootSystem.roots (isFiniteType_cartan (2 * r + 1))
        (divisible (2 * r + 1)) := by
  simp only [bc2Coeffs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hxy
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  · exact roots_of_bc2_coeffs_pos hr (by simp [bc2PosCoeffs])
  · exact roots_of_bc2_coeffs_pos hr (by simp [bc2PosCoeffs])
  · exact roots_of_bc2_coeffs_pos hr (by simp [bc2PosCoeffs])
  · exact roots_of_bc2_coeffs_pos hr (by simp [bc2PosCoeffs])
  · exact roots_of_bc2_coeffs_pos hr (by simp [bc2PosCoeffs])
  · exact roots_of_bc2_coeffs_pos hr (by simp [bc2PosCoeffs])
  · exact roots_of_bc2_coeffs_neg hr (by simp [bc2PosCoeffs])
  · exact roots_of_bc2_coeffs_neg hr (by simp [bc2PosCoeffs])
  · exact roots_of_bc2_coeffs_neg hr (by simp [bc2PosCoeffs])
  · exact roots_of_bc2_coeffs_neg hr (by simp [bc2PosCoeffs])
  · exact roots_of_bc2_coeffs_neg hr (by simp [bc2PosCoeffs])
  · exact roots_of_bc2_coeffs_neg hr (by simp [bc2PosCoeffs])


private lemma bc2_coeffs_of_weight_sub {r : ℕ} (hr : 2 ≤ r)
    {γ : Fin ((2 * r + 1) / 2) → ℤ} {i j : Fin (2 * r + 1)}
    (hji : j ≠ Fin.rev i)
    (hγeq : γ = γ (bcPrevIdx r hr) • Pi.single (bcPrevIdx r hr) 1 +
      γ (bcLastIdx r (by omega)) • Pi.single (bcLastIdx r (by omega)) 1)
    (hPL : (bcPrevIdx r hr) ≠ bcLastIdx r (by omega))
    (hto : toStd (2 * r + 1) γ =
      γ (bcPrevIdx r hr) • Pi.single (bcPrevIdx r hr) 1 +
        (γ (bcLastIdx r (by omega)) - γ (bcPrevIdx r hr)) •
          Pi.single (bcLastIdx r (by omega)) 1)
    (h0 : γ (bcPrevIdx r hr) ≠ 0 ∨
      γ (bcLastIdx r (by omega)) - γ (bcPrevIdx r hr) ≠ 0)
    (hstd : toStd (2 * r + 1) γ =
      weight (2 * r + 1) i - weight (2 * r + 1) j) :
    ∃ x y : ℤ, (x, y) ∈ bc2Coeffs ∧
      γ = x • Pi.single (bcPrevIdx r hr) 1 + y • Pi.single (bcLastIdx r (by omega)) 1 := by
  have hxP : γ (bcPrevIdx r hr) =
      (weight (2 * r + 1) i - weight (2 * r + 1) j) (bcPrevIdx r hr) := by
    have hcomp := congrFun (hto.symm.trans hstd) (bcPrevIdx r hr)
    simpa [Pi.add_apply, Pi.smul_apply, Pi.single_apply, hPL] using hcomp
  have hdL : γ (bcLastIdx r (by omega)) - γ (bcPrevIdx r hr) =
      (weight (2 * r + 1) i - weight (2 * r + 1) j) (bcLastIdx r (by omega)) := by
    have hcomp := congrFun (hto.symm.trans hstd) (bcLastIdx r (by omega))
    simpa [Pi.add_apply, Pi.smul_apply, Pi.single_apply, Ne.symm hPL] using hcomp
  have hbP := weight_sub_bounds (n := 2 * r + 1) (i := i) (j := j)
    (a := bcPrevIdx r hr) hji
  have hbL := weight_sub_bounds (n := 2 * r + 1) (i := i) (j := j)
    (a := bcLastIdx r (by omega)) hji
  have hmem' := bc2Coeffs_of_unit
    (x := γ (bcPrevIdx r hr)) (d := γ (bcLastIdx r (by omega)) - γ (bcPrevIdx r hr))
    (by rw [hxP]; exact hbP.1) (by rw [hxP]; exact hbP.2)
    (by rw [hdL]; exact hbL.1) (by rw [hdL]; exact hbL.2) h0
  refine ⟨γ (bcPrevIdx r hr), γ (bcLastIdx r (by omega)), ?_, hγeq⟩
  simpa [add_sub_cancel_left] using hmem'

private lemma bc2_coeffs_of_two_smul {r : ℕ} (hr : 2 ≤ r)
    {γ : Fin ((2 * r + 1) / 2) → ℤ} {i : Fin (2 * r + 1)}
    (hγeq : γ = γ (bcPrevIdx r hr) • Pi.single (bcPrevIdx r hr) 1 +
      γ (bcLastIdx r (by omega)) • Pi.single (bcLastIdx r (by omega)) 1)
    (hPL : (bcPrevIdx r hr) ≠ bcLastIdx r (by omega))
    (hto : toStd (2 * r + 1) γ =
      γ (bcPrevIdx r hr) • Pi.single (bcPrevIdx r hr) 1 +
        (γ (bcLastIdx r (by omega)) - γ (bcPrevIdx r hr)) •
          Pi.single (bcLastIdx r (by omega)) 1)
    (h0 : γ (bcPrevIdx r hr) ≠ 0 ∨
      γ (bcLastIdx r (by omega)) - γ (bcPrevIdx r hr) ≠ 0)
    (hstd : toStd (2 * r + 1) γ = 2 • weight (2 * r + 1) i) :
    ∃ x y : ℤ, (x, y) ∈ bc2Coeffs ∧
      γ = x • Pi.single (bcPrevIdx r hr) 1 + y • Pi.single (bcLastIdx r (by omega)) 1 := by
  have hxP : γ (bcPrevIdx r hr) = (2 • weight (2 * r + 1) i) (bcPrevIdx r hr) := by
    have hcomp := congrFun (hto.symm.trans hstd) (bcPrevIdx r hr)
    simpa [Pi.add_apply, Pi.smul_apply, Pi.single_apply, hPL] using hcomp
  have hdL : γ (bcLastIdx r (by omega)) - γ (bcPrevIdx r hr) =
      (2 • weight (2 * r + 1) i) (bcLastIdx r (by omega)) := by
    have hcomp := congrFun (hto.symm.trans hstd) (bcLastIdx r (by omega))
    simpa [Pi.add_apply, Pi.smul_apply, Pi.single_apply, Ne.symm hPL] using hcomp
  have hwP := weight_apply_bounds i (bcPrevIdx r hr)
  have hwL := weight_apply_bounds i (bcLastIdx r (by omega))
  have hx : γ (bcPrevIdx r hr) = -2 ∨ γ (bcPrevIdx r hr) = 0 ∨ γ (bcPrevIdx r hr) = 2 := by
    rw [hxP]
    simpa [Pi.smul_apply, smul_eq_mul] using two_mul_eq_or hwP.1 hwP.2
  have hd : γ (bcLastIdx r (by omega)) - γ (bcPrevIdx r hr) = -2 ∨
      γ (bcLastIdx r (by omega)) - γ (bcPrevIdx r hr) = 0 ∨
      γ (bcLastIdx r (by omega)) - γ (bcPrevIdx r hr) = 2 := by
    rw [hdL]
    simpa [Pi.smul_apply, smul_eq_mul] using two_mul_eq_or hwL.1 hwL.2
  have hone : γ (bcPrevIdx r hr) = 0 ∨ γ (bcLastIdx r (by omega)) - γ (bcPrevIdx r hr) = 0 := by
    rcases weight_prevI_eq_zero_or_lastI_eq_zero hr i with h | h
    · left
      rw [hxP]
      simp [h]
    · right
      rw [hdL]
      simp [h]
  have hmem' := bc2Coeffs_of_two hx hd h0 hone
  refine ⟨γ (bcPrevIdx r hr), γ (bcLastIdx r (by omega)), ?_, hγeq⟩
  simpa [add_sub_cancel_left] using hmem'

private lemma bc2_coeffs_of_weight {r : ℕ} (hr : 2 ≤ r)
    {γ : Fin ((2 * r + 1) / 2) → ℤ} {i : Fin (2 * r + 1)}
    (hγeq : γ = γ (bcPrevIdx r hr) • Pi.single (bcPrevIdx r hr) 1 +
      γ (bcLastIdx r (by omega)) • Pi.single (bcLastIdx r (by omega)) 1)
    (hPL : (bcPrevIdx r hr) ≠ bcLastIdx r (by omega))
    (hto : toStd (2 * r + 1) γ =
      γ (bcPrevIdx r hr) • Pi.single (bcPrevIdx r hr) 1 +
        (γ (bcLastIdx r (by omega)) - γ (bcPrevIdx r hr)) •
          Pi.single (bcLastIdx r (by omega)) 1)
    (h0 : γ (bcPrevIdx r hr) ≠ 0 ∨
      γ (bcLastIdx r (by omega)) - γ (bcPrevIdx r hr) ≠ 0)
    (hstd : toStd (2 * r + 1) γ = weight (2 * r + 1) i) :
    ∃ x y : ℤ, (x, y) ∈ bc2Coeffs ∧
      γ = x • Pi.single (bcPrevIdx r hr) 1 + y • Pi.single (bcLastIdx r (by omega)) 1 := by
  have hxP : γ (bcPrevIdx r hr) = weight (2 * r + 1) i (bcPrevIdx r hr) := by
    have hcomp := congrFun (hto.symm.trans hstd) (bcPrevIdx r hr)
    simpa [Pi.add_apply, Pi.smul_apply, Pi.single_apply, hPL] using hcomp
  have hdL : γ (bcLastIdx r (by omega)) - γ (bcPrevIdx r hr) =
      weight (2 * r + 1) i (bcLastIdx r (by omega)) := by
    have hcomp := congrFun (hto.symm.trans hstd) (bcLastIdx r (by omega))
    simpa [Pi.add_apply, Pi.smul_apply, Pi.single_apply, Ne.symm hPL] using hcomp
  have hbP := weight_apply_bounds i (bcPrevIdx r hr)
  have hbL := weight_apply_bounds i (bcLastIdx r (by omega))
  have hmem' := bc2Coeffs_of_unit
    (x := γ (bcPrevIdx r hr)) (d := γ (bcLastIdx r (by omega)) - γ (bcPrevIdx r hr))
    (by rw [hxP]; exact hbP.1) (by rw [hxP]; exact hbP.2)
    (by rw [hdL]; exact hbL.1) (by rw [hdL]; exact hbL.2) h0
  refine ⟨γ (bcPrevIdx r hr), γ (bcLastIdx r (by omega)), ?_, hγeq⟩
  simpa [add_sub_cancel_left] using hmem'

theorem mem_pairRoots_bc2 {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) {r : ℕ} (hr : 2 ≤ r)
    {γ : Fin ((2 * r + 1) / 2) → ℤ} :
    γ ∈ pairRoots (rootDatum hF (2 * r + 1)) (bcPrevIdx r hr)
        (bcLastIdx r (Nat.one_le_of_lt hr)) ↔
      ∃ x y : ℤ, (x, y) ∈ bc2Coeffs ∧
        γ = x • Pi.single (bcPrevIdx r hr) 1 +
          y • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1 := by
  constructor
  · rintro ⟨hroots, hsupp⟩
    have hγeq := eq_bc2_of_support hr hsupp
    have hPL : (bcPrevIdx r hr) ≠ bcLastIdx r (by omega) := by
      apply Fin.ne_of_val_ne
      simp [bcPrevIdx, bcLastIdx]
      omega
    have hto : toStd (2 * r + 1) γ =
        γ (bcPrevIdx r hr) • Pi.single (bcPrevIdx r hr) 1 +
          (γ (bcLastIdx r (by omega)) - γ (bcPrevIdx r hr)) •
            Pi.single (bcLastIdx r (by omega)) 1 := by
      rw [hγeq, toStd_bc2_formula hr (γ (bcPrevIdx r hr)) (γ (bcLastIdx r (by omega)))]
      simp [Pi.add_apply, Pi.smul_apply, Pi.single_apply, hPL, Ne.symm hPL]
    have hne0 : γ ≠ 0 :=
      CFSG.LieType.RootSystem.ne_zero_of_mem_roots (isFiniteType_cartan (2 * r + 1))
        (divisible (2 * r + 1)) hroots
    have h0 : γ (bcPrevIdx r hr) ≠ 0 ∨
        γ (bcLastIdx r (by omega)) - γ (bcPrevIdx r hr) ≠ 0 := by
      by_contra h
      push Not at h
      apply hne0
      have hL0 : γ (bcLastIdx r (by omega)) = 0 := by omega
      rw [hγeq]
      simp [h.1, hL0]
    have hroots' : γ ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartan (2 * r + 1))
        (divisible (2 * r + 1)) := hroots
    rw [roots_eq] at hroots'
    rcases hroots' with ⟨i, j, hij, hi, hj, hji, hstd⟩ |
      ⟨i, hi, hstd⟩ | ⟨he, i, hi, hstd⟩
    · exact bc2_coeffs_of_weight_sub hr hji hγeq hPL hto h0 hstd
    · exact bc2_coeffs_of_two_smul hr hγeq hPL hto h0 hstd
    · exact bc2_coeffs_of_weight hr hγeq hPL hto h0 hstd

  · rintro ⟨x, y, hxy, rfl⟩
    refine ⟨roots_of_bc2_coeffs hr hxy, ?_⟩
    change ∀ k : Fin ((2 * r + 1) / 2), k ≠ bcPrevIdx r hr →
      k ≠ bcLastIdx r (by omega) →
        ((x • Pi.single (bcPrevIdx r hr) 1 + y • Pi.single (bcLastIdx r (by omega)) 1 :
          Fin ((2 * r + 1) / 2) → ℤ)) k = 0
    intro k hkP hkL
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
      Pi.single_eq_of_ne hkP, Pi.single_eq_of_ne hkL]
    simp



private lemma two_mul_ht_bc2 {r : ℕ} (hr : 2 ≤ r) (x y : ℤ) :
    2 * ht (x • Pi.single (bcPrevIdx r hr) 1 + y • Pi.single (bcLastIdx r (by omega)) 1) =
      2 * (x + y) := by
  have hP : lv (2 * r + 1) (Pi.single (bcPrevIdx r hr) 1) = 4 := by
    rw [lv_single]
    simp only [bcPrevIdx, Fin.val_mk]
    rw [Nat.cast_sub (by omega : 2 ≤ r)]
    push_cast
    ring
  have hL : lv (2 * r + 1) (Pi.single (bcLastIdx r (by omega)) 1) = 2 := by
    rw [lv_single]
    simp only [bcLastIdx, Fin.val_mk]
    rw [Nat.cast_sub (by omega : 1 ≤ r)]
    push_cast
    ring
  rw [two_mul_ht, toStd_bc2_formula hr x y, map_add, map_zsmul, map_zsmul, hP, hL]
  ring

private lemma ht_bc2_formula {r : ℕ} (hr : 2 ≤ r) (x y : ℤ) :
    ht (x • Pi.single (bcPrevIdx r hr) 1 + y • Pi.single (bcLastIdx r (by omega)) 1) = x + y := by
  have h := two_mul_ht_bc2 hr x y
  omega

private lemma bc2PosCoeffs_of_mem {x y : ℤ} (hxy : (x, y) ∈ bc2Coeffs) (h : 0 < x + y) :
    (x, y) ∈ bc2PosCoeffs := by
  simp only [bc2Coeffs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hxy
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;> simp_all [bc2PosCoeffs]

private lemma bc2PosCoeffs_subset {x y : ℤ} (h : (x, y) ∈ bc2PosCoeffs) :
    (x, y) ∈ bc2Coeffs := by
  simp only [bc2PosCoeffs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;> simp [bc2Coeffs]

private lemma bc2PosCoeffs_pos {x y : ℤ} (h : (x, y) ∈ bc2PosCoeffs) : 0 < x + y := by
  simp only [bc2PosCoeffs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;> omega

theorem mem_pairRoots_bc2_pos {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) {r : ℕ} (hr : 2 ≤ r)
    {γ : Fin ((2 * r + 1) / 2) → ℤ} :
    γ ∈ pairRoots (rootDatum hF (2 * r + 1)) (bcPrevIdx r hr)
        (bcLastIdx r (Nat.one_le_of_lt hr)) ∩
      (CFSG.LieType.Steinberg.RootSystem.ofCartan (isFiniteType_cartan (2 * r + 1))
        (divisible (2 * r + 1))).pos ↔
      ∃ x y : ℤ,
        (x, y) ∈ ({(1, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)} : Finset (ℤ × ℤ)) ∧
          γ = x • Pi.single (bcPrevIdx r hr) 1 +
            y • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1 := by
  constructor
  · rintro ⟨hpair, hpos⟩
    obtain ⟨x, y, hxy, hγeq⟩ := (mem_pairRoots_bc2 hF hr).mp hpair
    have hsum : 0 < x + y := by
      have h := hpos.2
      rw [hγeq, ht_bc2_formula hr x y] at h
      exact h
    exact ⟨x, y, by simpa [bc2PosCoeffs] using bc2PosCoeffs_of_mem hxy hsum, hγeq⟩
  · rintro ⟨x, y, hxy, hγeq⟩
    have hxy' : (x, y) ∈ bc2PosCoeffs := by simpa [bc2PosCoeffs] using hxy
    have hsum := bc2PosCoeffs_pos hxy'
    have hpair : γ ∈ pairRoots (rootDatum hF (2 * r + 1)) (bcPrevIdx r hr)
        (bcLastIdx r (by omega)) :=
      (mem_pairRoots_bc2 hF hr).mpr ⟨x, y, bc2PosCoeffs_subset hxy', hγeq⟩
    refine ⟨hpair, ?_⟩
    change γ ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartan (2 * r + 1))
      (divisible (2 * r + 1)) ∧ 0 < ht γ
    exact ⟨hpair.1, by rw [hγeq, ht_bc2_formula hr x y]; exact hsum⟩

private def nextI {r : ℕ} (i : Fin ((2 * r + 1) / 2)) (hi : i.val + 3 ≤ r) :
    Fin ((2 * r + 1) / 2) := ⟨i.val + 1, by omega⟩

private lemma weight_sub_support_le_two {n : ℕ} {p q : Fin n} {a b c : Fin (n / 2)}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : weight n p a - weight n q a ≠ 0)
    (hb : weight n p b - weight n q b ≠ 0)
    (hc : weight n p c - weight n q c ≠ 0) : False := by
  have ha' : weight n p a ≠ 0 ∨ weight n q a ≠ 0 := by
    by_contra h
    push Not at h
    apply ha
    rw [h.1, h.2, sub_zero]
  have hb' : weight n p b ≠ 0 ∨ weight n q b ≠ 0 := by
    by_contra h
    push Not at h
    apply hb
    rw [h.1, h.2, sub_zero]
  have hc' : weight n p c ≠ 0 ∨ weight n q c ≠ 0 := by
    by_contra h
    push Not at h
    apply hc
    rw [h.1, h.2, sub_zero]
  rcases ha' with haP | haQ <;> rcases hb' with hbP | hbQ <;>
    rcases hc' with hcP | hcQ
  · exact hab (eq_of_weight_ne_zero haP hbP)
  · exact hab (eq_of_weight_ne_zero haP hbP)
  · exact hac (eq_of_weight_ne_zero haP hcP)
  · exact hbc (eq_of_weight_ne_zero hbQ hcQ)
  · exact hbc (eq_of_weight_ne_zero hbP hcP)
  · exact hac (eq_of_weight_ne_zero haQ hcQ)
  · exact hab (eq_of_weight_ne_zero haQ hbQ)
  · exact hab (eq_of_weight_ne_zero haQ hbQ)

private lemma toStd_a1bc1_formula {r : ℕ} {i : Fin ((2 * r + 1) / 2)}
    (hi : i.val + 3 ≤ r) (x y : ℤ) :
    toStd (2 * r + 1) (x • Pi.single i 1 + y • Pi.single (bcLastIdx r (by omega)) 1) =
      x • Pi.single i 1 - x • Pi.single (nextI i hi) 1 +
        y • Pi.single (bcLastIdx r (by omega)) 1 := by
  rw [toStd_add']
  simp only [toStd_zsmul]
  have hodd : ¬ Even (2 * r + 1) := by
    rw [Nat.not_even_iff_odd]
    exact ⟨r, by omega⟩
  have hni : i.val + 1 < (2 * r + 1) / 2 := by
    have := i.isLt
    omega
  have hL : ¬ (bcLastIdx r (by omega)).val + 1 < (2 * r + 1) / 2 := by
    change ¬ r - 1 + 1 < (2 * r + 1) / 2
    have h1 : r - 1 + 1 = r := Nat.sub_add_cancel (by omega)
    rw [h1]
    omega
  rw [toStd_single_of_odd hodd hL]
  rw [toStd_single_of_lt (2 * r + 1) hni]
  rw [show (⟨i.val + 1, hni⟩ : Fin ((2 * r + 1) / 2)) = nextI i hi from Fin.ext rfl]
  module

private lemma eq_a1bc1_of_support {r : ℕ} {i : Fin ((2 * r + 1) / 2)}
    (hi : i.val + 3 ≤ r) {γ : Fin ((2 * r + 1) / 2) → ℤ}
    (hγ : ∀ k, k ≠ i → k ≠ bcLastIdx r (by omega) → γ k = 0) :
    γ = γ i • Pi.single i 1 +
      γ (bcLastIdx r (by omega)) • Pi.single (bcLastIdx r (by omega)) 1 := by
  funext k
  have hiL : i ≠ bcLastIdx r (by omega) := by
    apply Fin.ne_of_val_ne
    simp only [bcLastIdx, Fin.val_mk]
    omega
  by_cases hkI : k = i
  · subst hkI
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hiL]
    simp
  · by_cases hkL : k = bcLastIdx r (by omega)
    · subst hkL
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [Pi.single_eq_of_ne (Ne.symm hiL), Pi.single_eq_same]
      simp
    · have hk0 := hγ k hkI hkL
      simp [hk0, hkI, hkL]

private lemma a1bc1Coeffs_of_unit {x y : ℤ} (hx : x = -1 ∨ x = 0 ∨ x = 1)
    (hy : y = -1 ∨ y = 0 ∨ y = 1) (h0 : x ≠ 0 ∨ y ≠ 0) (hone : x = 0 ∨ y = 0) :
    (x, y) ∈ a1bc1Coeffs := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    simp_all [a1bc1Coeffs]

private lemma a1bc1Coeffs_of_two {x y : ℤ} (hx : x = 0)
    (hy : y = -2 ∨ y = 0 ∨ y = 2) (h0 : y ≠ 0) : (x, y) ∈ a1bc1Coeffs := by
  rcases hy with rfl | rfl | rfl
  · simp [a1bc1Coeffs, hx]
  · exact absurd rfl h0
  · simp [a1bc1Coeffs, hx]

private lemma a1bc1_coeffs_of_weight_sub {r : ℕ}
    {i : Fin ((2 * r + 1) / 2)} (hi : i.val + 3 ≤ r)
    {γ : Fin ((2 * r + 1) / 2) → ℤ} {p q : Fin (2 * r + 1)}
    (hqp : q ≠ Fin.rev p)
    (hiL : i ≠ bcLastIdx r (by omega)) (hiNext : i ≠ nextI i hi)
    (hnextL : nextI i hi ≠ bcLastIdx r (by omega))
    (hγeq : γ = γ i • Pi.single i 1 +
      γ (bcLastIdx r (by omega)) • Pi.single (bcLastIdx r (by omega)) 1)
    (hto : toStd (2 * r + 1) γ =
      γ i • Pi.single i 1 - γ i • Pi.single (nextI i hi) 1 +
        γ (bcLastIdx r (by omega)) • Pi.single (bcLastIdx r (by omega)) 1)
    (h0 : γ i ≠ 0 ∨ γ (bcLastIdx r (by omega)) ≠ 0)
    (hstd : toStd (2 * r + 1) γ = weight (2 * r + 1) p - weight (2 * r + 1) q) :
    ∃ x y : ℤ, (x, y) ∈ a1bc1Coeffs ∧
      γ = x • Pi.single i 1 + y • Pi.single (bcLastIdx r (by omega)) 1 := by
  have hxi : γ i = (weight (2 * r + 1) p - weight (2 * r + 1) q) i := by
    have hcomp := congrFun (hto.symm.trans hstd) i
    simpa [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hiL, hiNext,
      hnextL] using hcomp
  have hxi1 : -γ i = (weight (2 * r + 1) p - weight (2 * r + 1) q) (nextI i hi) := by
    have hcomp := congrFun (hto.symm.trans hstd) (nextI i hi)
    simpa [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hiL, hiNext,
      hnextL] using hcomp
  have hyL : γ (bcLastIdx r (by omega)) =
      (weight (2 * r + 1) p - weight (2 * r + 1) q) (bcLastIdx r (by omega)) := by
    have hcomp := congrFun (hto.symm.trans hstd) (bcLastIdx r (by omega))
    simpa [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hiL, hiNext,
      hnextL] using hcomp
  rw [Pi.sub_apply] at hxi hxi1 hyL
  have hnotboth : ¬ (γ i ≠ 0 ∧ γ (bcLastIdx r (by omega)) ≠ 0) := by
    rintro ⟨hx, hy⟩
    exact weight_sub_support_le_two hiNext hiL hnextL
      (by rw [← hxi]; exact hx)
      (by rw [← hxi1]; exact neg_ne_zero.mpr hx)
      (by rw [← hyL]; exact hy)
  have hsep : γ i = 0 ∨ γ (bcLastIdx r (by omega)) = 0 := by
    by_contra h
    push Not at h
    exact hnotboth h
  have hbL := weight_sub_bounds (n := 2 * r + 1) (i := p) (j := q)
    (a := bcLastIdx r (by omega)) hqp
  have hbI := weight_sub_bounds (n := 2 * r + 1) (i := p) (j := q) (a := i) hqp
  rcases hsep with hx0 | hy0
  · have hyne : γ (bcLastIdx r (by omega)) ≠ 0 := by
      rcases h0 with h | h
      · exact absurd hx0 h
      · exact h
    have hxb : -1 ≤ γ (bcLastIdx r (by omega)) ∧
        γ (bcLastIdx r (by omega)) ≤ 1 := by
      rw [hyL]
      exact hbL
    have hx : γ i = -1 ∨ γ i = 0 ∨ γ i = 1 := by
      right; left; exact hx0
    have hy : γ (bcLastIdx r (by omega)) = -1 ∨
        γ (bcLastIdx r (by omega)) = 0 ∨ γ (bcLastIdx r (by omega)) = 1 := by
      omega
    exact ⟨γ i, γ (bcLastIdx r (by omega)),
      a1bc1Coeffs_of_unit hx hy h0 (Or.inl hx0), hγeq⟩
  · have hxne : γ i ≠ 0 := by
      rcases h0 with h | h
      · exact h
      · exact absurd hy0 h
    have hxb : -1 ≤ γ i ∧ γ i ≤ 1 := by
      rw [hxi]
      exact hbI
    have hx : γ i = -1 ∨ γ i = 0 ∨ γ i = 1 := by omega
    have hy : γ (bcLastIdx r (by omega)) = -1 ∨
        γ (bcLastIdx r (by omega)) = 0 ∨ γ (bcLastIdx r (by omega)) = 1 := by
      right; left; exact hy0
    exact ⟨γ i, γ (bcLastIdx r (by omega)),
      a1bc1Coeffs_of_unit hx hy h0 (Or.inr hy0), hγeq⟩

private lemma a1bc1_coeffs_of_two_smul {r : ℕ}
    {i : Fin ((2 * r + 1) / 2)} (hi : i.val + 3 ≤ r)
    {γ : Fin ((2 * r + 1) / 2) → ℤ} {p : Fin (2 * r + 1)}
    (hiL : i ≠ bcLastIdx r (by omega)) (hiNext : i ≠ nextI i hi)
    (hnextL : nextI i hi ≠ bcLastIdx r (by omega))
    (hγeq : γ = γ i • Pi.single i 1 +
      γ (bcLastIdx r (by omega)) • Pi.single (bcLastIdx r (by omega)) 1)
    (hto : toStd (2 * r + 1) γ =
      γ i • Pi.single i 1 - γ i • Pi.single (nextI i hi) 1 +
        γ (bcLastIdx r (by omega)) • Pi.single (bcLastIdx r (by omega)) 1)
    (h0 : γ i ≠ 0 ∨ γ (bcLastIdx r (by omega)) ≠ 0)
    (hstd : toStd (2 * r + 1) γ = 2 • weight (2 * r + 1) p) :
    ∃ x y : ℤ, (x, y) ∈ a1bc1Coeffs ∧
      γ = x • Pi.single i 1 + y • Pi.single (bcLastIdx r (by omega)) 1 := by
  have hxi : γ i = (2 • weight (2 * r + 1) p) i := by
    have hcomp := congrFun (hto.symm.trans hstd) i
    simpa [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hiL, hiNext,
      hnextL] using hcomp
  have hxi1 : -γ i = (2 • weight (2 * r + 1) p) (nextI i hi) := by
    have hcomp := congrFun (hto.symm.trans hstd) (nextI i hi)
    simpa [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hiL, hiNext,
      hnextL] using hcomp
  have hyL : γ (bcLastIdx r (by omega)) =
      (2 • weight (2 * r + 1) p) (bcLastIdx r (by omega)) := by
    have hcomp := congrFun (hto.symm.trans hstd) (bcLastIdx r (by omega))
    simpa [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hiL, hiNext,
      hnextL] using hcomp
  have hx0 : γ i = 0 := by
    by_contra hx
    have hwi : weight (2 * r + 1) p i ≠ 0 := by
      intro hw
      apply hx
      rw [hxi]
      simp [Pi.smul_apply, hw]
    have hwi1 : weight (2 * r + 1) p (nextI i hi) ≠ 0 := by
      intro hw
      have h := hxi1
      simp [Pi.smul_apply, hw] at h
      omega
    exact hiNext (eq_of_weight_ne_zero hwi hwi1)
  have hyne : γ (bcLastIdx r (by omega)) ≠ 0 := by
    rcases h0 with h | h
    · exact absurd hx0 h
    · exact h
  have hwL := weight_apply_bounds p (bcLastIdx r (by omega))
  have hy : γ (bcLastIdx r (by omega)) = -2 ∨ γ (bcLastIdx r (by omega)) = 0 ∨
      γ (bcLastIdx r (by omega)) = 2 := by
    rw [hyL]
    simpa [Pi.smul_apply, smul_eq_mul] using two_mul_eq_or hwL.1 hwL.2
  exact ⟨γ i, γ (bcLastIdx r (by omega)), a1bc1Coeffs_of_two hx0 hy hyne, hγeq⟩

private lemma a1bc1_coeffs_of_weight {r : ℕ}
    {i : Fin ((2 * r + 1) / 2)} (hi : i.val + 3 ≤ r)
    {γ : Fin ((2 * r + 1) / 2) → ℤ} {p : Fin (2 * r + 1)}
    (hiL : i ≠ bcLastIdx r (by omega)) (hiNext : i ≠ nextI i hi)
    (hnextL : nextI i hi ≠ bcLastIdx r (by omega))
    (hγeq : γ = γ i • Pi.single i 1 +
      γ (bcLastIdx r (by omega)) • Pi.single (bcLastIdx r (by omega)) 1)
    (hto : toStd (2 * r + 1) γ =
      γ i • Pi.single i 1 - γ i • Pi.single (nextI i hi) 1 +
        γ (bcLastIdx r (by omega)) • Pi.single (bcLastIdx r (by omega)) 1)
    (h0 : γ i ≠ 0 ∨ γ (bcLastIdx r (by omega)) ≠ 0)
    (hstd : toStd (2 * r + 1) γ = weight (2 * r + 1) p) :
    ∃ x y : ℤ, (x, y) ∈ a1bc1Coeffs ∧
      γ = x • Pi.single i 1 + y • Pi.single (bcLastIdx r (by omega)) 1 := by
  have hxi : γ i = weight (2 * r + 1) p i := by
    have hcomp := congrFun (hto.symm.trans hstd) i
    simpa [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hiL, hiNext,
      hnextL] using hcomp
  have hxi1 : -γ i = weight (2 * r + 1) p (nextI i hi) := by
    have hcomp := congrFun (hto.symm.trans hstd) (nextI i hi)
    simpa [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hiL, hiNext,
      hnextL] using hcomp
  have hyL : γ (bcLastIdx r (by omega)) = weight (2 * r + 1) p (bcLastIdx r (by omega)) := by
    have hcomp := congrFun (hto.symm.trans hstd) (bcLastIdx r (by omega))
    simpa [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hiL, hiNext,
      hnextL] using hcomp
  have hx0 : γ i = 0 := by
    by_contra hx
    have hwi : weight (2 * r + 1) p i ≠ 0 := by
      rw [← hxi]
      exact hx
    have hwi1 : weight (2 * r + 1) p (nextI i hi) ≠ 0 := by
      rw [← hxi1]
      exact neg_ne_zero.mpr hx
    exact hiNext (eq_of_weight_ne_zero hwi hwi1)
  have hyne : γ (bcLastIdx r (by omega)) ≠ 0 := by
    rcases h0 with h | h
    · exact absurd hx0 h
    · exact h
  have hwL := weight_apply_bounds p (bcLastIdx r (by omega))
  have hy : γ (bcLastIdx r (by omega)) = -1 ∨
      γ (bcLastIdx r (by omega)) = 0 ∨ γ (bcLastIdx r (by omega)) = 1 := by
    rw [hyL]
    omega
  exact ⟨γ i, γ (bcLastIdx r (by omega)),
    a1bc1Coeffs_of_unit (Or.inr (Or.inl hx0)) hy h0 (Or.inl hx0), hγeq⟩

private lemma a1bc1_roots {r : ℕ} {i : Fin ((2 * r + 1) / 2)}
    (hi : i.val + 3 ≤ r) {x y : ℤ} (hxy : (x, y) ∈ a1bc1Coeffs) :
    (x • Pi.single i 1 + y • Pi.single (bcLastIdx r (by omega)) 1) ∈
      CFSG.LieType.RootSystem.roots (isFiniteType_cartan (2 * r + 1))
        (divisible (2 * r + 1)) := by
  have hodd : ¬ Even (2 * r + 1) := by
    rw [Nat.not_even_iff_odd]
    exact ⟨r, by omega⟩
  have hmid : Fin.rev (midIdx (2 * r + 1) hodd) = midIdx (2 * r + 1) hodd :=
    rev_midIdx hodd
  have hwmid : weight (2 * r + 1) (midIdx (2 * r + 1) hodd) = 0 :=
    weight_eq_zero_of_rev_eq hmid
  simp only [a1bc1Coeffs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hxy
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  · refine mem_roots_of_weight_sub (n := 2 * r + 1)
      (a := lowIdx i) (b := lowIdx (nextI i hi)) ?_ ?_
    · apply Fin.ne_of_val_ne
      simp only [lowIdx, nextI, Fin.val_mk]
      omega
    · rw [toStd_a1bc1_formula hi 1 0, weight_lowIdx, weight_lowIdx]
      module
  · refine mem_roots_of_weight_sub (n := 2 * r + 1)
      (a := Fin.rev (lowIdx i)) (b := Fin.rev (lowIdx (nextI i hi))) ?_ ?_
    · apply Fin.ne_of_val_ne
      simp only [lowIdx, Fin.val_rev, nextI, Fin.val_mk]
      omega
    · rw [toStd_a1bc1_formula hi (-1) 0, weight_rev_lowIdx, weight_rev_lowIdx]
      module
  · refine mem_roots_of_weight_sub (n := 2 * r + 1)
      (a := lowIdx (bcLastIdx r (by omega))) (b := midIdx (2 * r + 1) hodd) ?_ ?_
    · apply Fin.ne_of_val_ne
      simp only [lowIdx, bcLastIdx, midIdx, Fin.val_mk]
      omega
    · rw [toStd_a1bc1_formula hi 0 1, weight_lowIdx, hwmid]
      module
  · refine mem_roots_of_weight_sub (n := 2 * r + 1)
      (a := Fin.rev (lowIdx (bcLastIdx r (by omega)))) (b := midIdx (2 * r + 1) hodd) ?_ ?_
    · apply Fin.ne_of_val_ne
      simp only [lowIdx, Fin.val_rev, bcLastIdx, midIdx, Fin.val_mk]
      omega
    · rw [toStd_a1bc1_formula hi 0 (-1), weight_rev_lowIdx, hwmid]
      module
  · refine mem_roots_of_weight_sub (n := 2 * r + 1)
      (a := lowIdx (bcLastIdx r (by omega)))
      (b := Fin.rev (lowIdx (bcLastIdx r (by omega)))) ?_ ?_
    · apply Fin.ne_of_val_ne
      simp only [lowIdx, Fin.val_rev, bcLastIdx, Fin.val_mk]
      omega
    · rw [toStd_a1bc1_formula hi 0 2, weight_lowIdx, weight_rev_lowIdx]
      module
  · refine mem_roots_of_weight_sub (n := 2 * r + 1)
      (a := Fin.rev (lowIdx (bcLastIdx r (by omega))))
      (b := lowIdx (bcLastIdx r (by omega))) ?_ ?_
    · apply Fin.ne_of_val_ne
      simp only [lowIdx, Fin.val_rev, bcLastIdx, Fin.val_mk]
      omega
    · rw [toStd_a1bc1_formula hi 0 (-2), weight_rev_lowIdx, weight_lowIdx]
      module

theorem mem_pairRoots_a1bc1 {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) {r : ℕ} (hr : 2 ≤ r)
    {i : Fin ((2 * r + 1) / 2)} (hi : i.val + 3 ≤ r)
    {γ : Fin ((2 * r + 1) / 2) → ℤ} :
    γ ∈ pairRoots (rootDatum hF (2 * r + 1)) i
        (bcLastIdx r (Nat.one_le_of_lt hr)) ↔ ∃ x y : ℤ,
      (x, y) ∈ ({(1, 0), (-1, 0), (0, 1), (0, -1), (0, 2), (0, -2)} : Finset (ℤ × ℤ)) ∧
        γ = x • Pi.single i 1 + y • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1 := by
  constructor
  · rintro ⟨hroots, hsupp⟩
    have hiL : i ≠ bcLastIdx r (by omega) := by
      apply Fin.ne_of_val_ne
      simp only [bcLastIdx, Fin.val_mk]
      omega
    have hiNext : i ≠ nextI i hi := by
      apply Fin.ne_of_val_ne
      simp only [nextI, Fin.val_mk]
      omega
    have hnextL : nextI i hi ≠ bcLastIdx r (by omega) := by
      apply Fin.ne_of_val_ne
      simp only [nextI, bcLastIdx, Fin.val_mk]
      omega
    have hγeq := eq_a1bc1_of_support hi hsupp
    have hto : toStd (2 * r + 1) γ =
        γ i • Pi.single i 1 - γ i • Pi.single (nextI i hi) 1 +
          γ (bcLastIdx r (by omega)) • Pi.single (bcLastIdx r (by omega)) 1 := by
      rw [hγeq, toStd_a1bc1_formula hi (γ i) (γ (bcLastIdx r (by omega)))]
      simp [Pi.add_apply, Pi.smul_apply, Pi.single_apply, hiL, hiNext, hnextL]
    have hne0 : γ ≠ 0 :=
      CFSG.LieType.RootSystem.ne_zero_of_mem_roots (isFiniteType_cartan (2 * r + 1))
        (divisible (2 * r + 1)) hroots
    have h0 : γ i ≠ 0 ∨ γ (bcLastIdx r (by omega)) ≠ 0 := by
      by_contra h
      push Not at h
      apply hne0
      have hL0 : γ (bcLastIdx r (by omega)) = 0 := h.2
      rw [hγeq]
      simp [h.1, hL0]
    have hroots' : γ ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartan (2 * r + 1))
        (divisible (2 * r + 1)) := hroots
    rw [roots_eq] at hroots'
    rcases hroots' with ⟨p, q, hpq, hp, hq, hqp, hstd⟩ |
      ⟨p, hp, hstd⟩ | ⟨he, p, hp, hstd⟩
    · obtain ⟨x, y, hmem, heq⟩ :=
        a1bc1_coeffs_of_weight_sub hi hqp hiL hiNext hnextL hγeq hto h0 hstd
      exact ⟨x, y, by simpa [a1bc1Coeffs] using hmem, heq⟩
    · obtain ⟨x, y, hmem, heq⟩ :=
        a1bc1_coeffs_of_two_smul hi hiL hiNext hnextL hγeq hto h0 hstd
      exact ⟨x, y, by simpa [a1bc1Coeffs] using hmem, heq⟩
    · obtain ⟨x, y, hmem, heq⟩ :=
        a1bc1_coeffs_of_weight hi hiL hiNext hnextL hγeq hto h0 hstd
      exact ⟨x, y, by simpa [a1bc1Coeffs] using hmem, heq⟩
  · rintro ⟨x, y, hxy, rfl⟩
    have hxy' : (x, y) ∈ a1bc1Coeffs := by simpa [a1bc1Coeffs] using hxy
    refine ⟨a1bc1_roots hi hxy', ?_⟩
    change ∀ k : Fin ((2 * r + 1) / 2), k ≠ i → k ≠ bcLastIdx r (by omega) →
      ((x • Pi.single i 1 + y • Pi.single (bcLastIdx r (by omega)) 1 :
        Fin ((2 * r + 1) / 2) → ℤ)) k = 0
    intro k hkI hkL
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
      Pi.single_eq_of_ne hkI, Pi.single_eq_of_ne hkL]
    simp

end CFSG.Timmesfeld.Transvection.Pres

module

public import CFSG.Monster.B.Co2.PermArr
public import Certificates.Data.CFSGNative.Co3Schreier.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
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

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3.Native

variable {n : ℕ}

section Restrict

variable (I : List (Fin n)) (H : Subgroup (Equiv.Perm (Fin n)))
  (hH : ∀ h ∈ H, ∀ p ∈ I, h p ∈ I)

@[expose] def listSub : SubMulAction H (Fin n) where
  carrier := {p | p ∈ I}
  smul_mem' h p hp := hH h h.2 p hp

@[expose] def listEquiv (hI : I.Nodup) : Fin I.length ≃ listSub I H hH :=
  (hI.getEquiv I).trans (Equiv.subtypeEquivRight fun _ => Iff.rfl)

theorem listEquiv_apply (hI : I.Nodup) (i : Fin I.length) :
    ((listEquiv I H hH hI i : listSub I H hH) : Fin n) = I.get i := rfl

@[expose] def restrictHom (hI : I.Nodup) : H →* Equiv.Perm (Fin I.length) :=
  (listEquiv I H hH hI).symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom H (listSub I H hH))

theorem restrictHom_apply (hI : I.Nodup) (h : H) (i : Fin I.length) :
    restrictHom I H hH hI h i = (listEquiv I H hH hI).symm (h • listEquiv I H hH hI i) := rfl

theorem get_restrictHom (hI : I.Nodup) (h : H) (i : Fin I.length) :
    I.get (restrictHom I H hH hI h i) = (h : Equiv.Perm (Fin n)) (I.get i) := by
  have e : listEquiv I H hH hI (restrictHom I H hH hI h i) = h • listEquiv I H hH hI i := by
    rw [restrictHom_apply, Equiv.apply_symm_apply]
  have e' := congrArg Subtype.val e
  rw [listEquiv_apply] at e'
  exact e'

theorem restrictHom_eq_iff (hI : I.Nodup) (h : H) (i j : Fin I.length) :
    restrictHom I H hH hI h i = j ↔ (h : Equiv.Perm (Fin n)) (I.get i) = I.get j := by
  rw [← get_restrictHom I H hH hI h i]
  constructor
  · rintro rfl
    rfl
  · intro e
    exact (hI.get_inj_iff).1 e

theorem restrictHom_eq_one (hI : I.Nodup) (h : H)
    (hfix : ∀ p ∈ I, (h : Equiv.Perm (Fin n)) p = p) : restrictHom I H hH hI h = 1 := by
  refine Equiv.ext fun i => ?_
  rw [Equiv.Perm.one_apply, restrictHom_eq_iff]
  exact hfix _ (List.get_mem I i)

end Restrict

theorem posIn_eq {I : Array ℕ} (hI : I.toList.Nodup) {j : ℕ} (hj : j < I.size) :
    posIn I I[j] = j := by
  unfold posIn
  have : Array.findIdx? (· == I[j]) I = some j := by
    rw [Array.findIdx?_eq_some_iff_getElem]
    refine ⟨hj, by simp, fun k hkj => ?_⟩
    intro hk
    simp only [beq_iff_eq] at hk
    have hk' : k < I.size := by omega
    have := (List.Nodup.getElem_inj_iff hI).1 (by
      rw [Array.getElem_toList, Array.getElem_toList]
      exact hk : I.toList[k]'(by simpa using hk') = I.toList[j]'(by simpa using hj))
    omega
  rw [this, Option.getD_some]

theorem rep_restrictA {I : List (Fin n)} {Iarr : Array ℕ} (hsize : Iarr.size = I.length)
    (hval : ∀ i : Fin I.length, Iarr[(i : ℕ)]! = (I.get i : ℕ)) (hnd : Iarr.toList.Nodup)
    {H : Subgroup (Equiv.Perm (Fin n))} (hH : ∀ h ∈ H, ∀ p ∈ I, h p ∈ I) (hI : I.Nodup)
    {m : Array ℕ} {h : H} (hm : Rep n m (h : Equiv.Perm (Fin n))) :
    Rep I.length (restrictA Iarr m) (restrictHom I H hH hI h) := by
  intro i
  have hi : (i : ℕ) < Iarr.size := by rw [hsize]; exact i.2
  set j := restrictHom I H hH hI h i
  have hj : (j : ℕ) < Iarr.size := by rw [hsize]; exact j.2
  have e1 : m[Iarr[(i : ℕ)]!]! = Iarr[(j : ℕ)]! := by
    rw [hval i, hm (I.get i), hval j, ← get_restrictHom I H hH hI h i]
  rw [restrictA, getElem!_ofFn_nat _ hi]
  change posIn Iarr m[Iarr[(i : ℕ)]!]! = (j : ℕ)
  rw [e1, getElem!_pos Iarr (j : ℕ) hj, posIn_eq hnd hj]

theorem rep_renameA {k : ℕ} {c π : Array ℕ} {C P : Equiv.Perm (Fin k)} (hc : Rep k c C)
    (hinv : isInvA k c (invCand k c) = true) (hπ : Rep k π P) :
    Rep k (renameA k c π) (C * P * C⁻¹) :=
  rep_compA (rep_compA hc hπ) (rep_inv_of_isInvA hc hinv)

theorem nat_any_iff' {n : ℕ} {p : ℕ → Bool} :
    (Nat.any n fun i _ => p i) = true ↔ ∃ i < n, p i = true := by
  rw [Nat.any_eq_finRange_any, List.any_eq_true]
  constructor
  · rintro ⟨⟨i, hi⟩, -, h⟩
    exact ⟨i, hi, h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, hi⟩, List.mem_finRange _, h⟩

theorem anyLt_iff {n : ℕ} {p : ℕ → Bool} : anyLt n p = true ↔ ∃ i < n, p i = true :=
  nat_any_iff'

theorem closure_eq_of_coversOK {gs hs : Array (Array ℕ)} {G H : ℕ → Equiv.Perm (Fin n)}
    (hG : ∀ i < gs.size, Rep n gs[i]! (G i)) (hH : ∀ j < hs.size, Rep n hs[j]! (H j))
    (h : coversOK n gs hs = true) :
    Subgroup.closure {g | ∃ i < gs.size, G i = g} =
      Subgroup.closure {g | ∃ j < hs.size, H j = g} := by
  simp only [coversOK, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    have hk := allLt_spec h1 hi
    simp only [Bool.or_eq_true] at hk
    rcases hk with hk | hk
    · rw [eq_of_eqA (hG i hi) rep_idA hk]
      exact Subgroup.one_mem _
    · obtain ⟨j, hj, he⟩ := anyLt_iff.1 hk
      rw [eq_of_eqA (hG i hi) (hH j hj) he]
      exact Subgroup.subset_closure ⟨j, hj, rfl⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨i, hi, he⟩ := anyLt_iff.1 (allLt_spec h2 hj)
    rw [eq_of_eqA (hH j hj) (hG i hi) he]
    exact Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem dual_eq_sum_proj {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (ψ : Module.Dual K (ι → K)) :
    ψ = ∑ c, ψ (Pi.single c 1) • (LinearMap.proj c : Module.Dual K (ι → K)) := by
  refine LinearMap.pi_ext fun c x => ?_
  rw [LinearMap.sum_apply, Finset.sum_eq_single c]
  · have e : (Pi.single c x : ι → K) = x • Pi.single c 1 := by
      ext d; by_cases h : d = c <;> simp [h]
    rw [LinearMap.smul_apply, LinearMap.coe_proj, Function.eval, Pi.single_eq_same, smul_eq_mul,
      e, map_smul, smul_eq_mul, mul_comm]
  · intro d _ hd
    rw [LinearMap.smul_apply, LinearMap.coe_proj, Function.eval, Pi.single_eq_of_ne hd, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ c) h

end CFSG.Sporadic.Schreier.Co3

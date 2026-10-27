module

public import CFSG.RankThree.Lattice.SteinbergBIQuotient
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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.Lattice

open Polynomial Matrix Module

variable {n : ℕ}

@[expose] def castLin (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℚ) where
  toFun v i := (v i : ℚ)
  map_add' u v := by
    ext i
    simp
  map_smul' c v := by
    ext i
    simp

theorem castLin_apply (v : Fin n → ℤ) (i : Fin n) : castLin n v i = (v i : ℚ) :=
  rfl

theorem castLin_injective : Function.Injective (castLin n) := by
  intro u v h
  funext i
  have hi := congrFun h i
  rw [castLin_apply, castLin_apply] at hi
  exact_mod_cast hi

@[expose] def ratSpan (Λ : Submodule ℤ (Fin n → ℤ)) : Submodule ℚ (Fin n → ℚ) :=
  Submodule.span ℚ (castLin n '' Λ)

@[expose] def saturation (Λ : Submodule ℤ (Fin n → ℤ)) : Submodule ℤ (Fin n → ℤ) :=
  ((ratSpan Λ).restrictScalars ℤ).comap (castLin n)

@[expose] noncomputable def satIndex (Λ : Submodule ℤ (Fin n → ℤ)) : ℕ :=
  Λ.toAddSubgroup.relIndex (saturation Λ).toAddSubgroup

theorem mem_saturation {Λ : Submodule ℤ (Fin n → ℤ)} {v : Fin n → ℤ} :
    v ∈ saturation Λ ↔ castLin n v ∈ ratSpan Λ :=
  Iff.rfl

theorem le_saturation (Λ : Submodule ℤ (Fin n → ℤ)) : Λ ≤ saturation Λ :=
  fun v hv => Submodule.subset_span ⟨v, hv, rfl⟩

theorem ratSpan_span (S : Set (Fin n → ℤ)) :
    ratSpan (Submodule.span ℤ S) = Submodule.span ℚ (castLin n '' S) := by
  rw [ratSpan, ← Submodule.map_coe, Submodule.map_span, Submodule.span_span_of_tower]

theorem castLin_mulVec (A : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) :
    castLin n (A *ᵥ v) = A.map (Int.castRingHom ℚ) *ᵥ castLin n v := by
  funext i
  exact RingHom.map_mulVec (Int.castRingHom ℚ) A v i

@[expose] def padLin {k : ℕ} (n : ℕ) : (Fin k → ℤ) →ₗ[ℤ] (Fin n → ℤ) where
  toFun y i := if h : (i : ℕ) < k then y ⟨i, h⟩ else 0
  map_add' y z := by
    ext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c y := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem padLin_castLE {k : ℕ} (hk : k ≤ n) (y : Fin k → ℤ) (a : Fin k) :
    padLin n y (Fin.castLE hk a) = y a := by
  simp [padLin]

theorem padLin_top {k : ℕ} (hk : k ≤ n) {v : Fin n → ℤ} (hv : ∀ i : Fin n, k ≤ (i : ℕ) → v i = 0) :
    padLin n (fun a : Fin k => v (Fin.castLE hk a)) = v := by
  funext i
  simp only [padLin, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs with h
  · rfl
  · exact (hv i (by omega)).symm

section Cert

variable {k : ℕ} (hk : k ≤ n) (m : Fin k → Fin n → ℤ) (P P' : Matrix (Fin n) (Fin n) ℤ)

@[expose] def certMat : Matrix (Fin k) (Fin k) ℤ :=
  Matrix.of fun a j => (P' *ᵥ m j) (Fin.castLE hk a)

variable {hk m P P'}

theorem mulVec_mulVec_of_mul_eq_one (hPP : P * P' = 1) (v : Fin n → ℤ) : P *ᵥ (P' *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]

theorem certMat_mulVec (hzero : ∀ i : Fin n, k ≤ (i : ℕ) → ∀ j, (P' *ᵥ m j) i = 0)
    (z : Fin k → ℤ) : P' *ᵥ (∑ j, z j • m j) = padLin n (certMat hk m P' *ᵥ z) := by
  funext i
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, padLin, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs with h
  · simp only [certMat, Matrix.mulVec, dotProduct, Matrix.of_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    rfl
  · exact Finset.sum_eq_zero fun j _ => by rw [hzero i (by omega) j, mul_zero]

theorem linearIndependent_of_cert (hzero : ∀ i : Fin n, k ≤ (i : ℕ) → ∀ j, (P' *ᵥ m j) i = 0)
    (hdet : (certMat hk m P').det ≠ 0) : LinearIndependent ℤ m := by
  rw [Fintype.linearIndependent_iff]
  intro z hz
  have h := certMat_mulVec (hk := hk) hzero z
  rw [hz, Matrix.mulVec_zero] at h
  have h0 : certMat hk m P' *ᵥ z = 0 := by
    funext a
    have := congrFun h (Fin.castLE hk a)
    rw [padLin_castLE] at this
    exact this.symm
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet h0)

theorem linearIndependent_castLin_of_cert (hdet : (certMat hk m P').det ≠ 0) :
    LinearIndependent ℚ fun j => castLin n (m j) := by
  rw [Fintype.linearIndependent_iff]
  intro z hz
  have hdetQ : ((certMat hk m P').map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast]
    exact_mod_cast hdet
  set CQ := (certMat hk m P').map (Int.castRingHom ℚ)
  have h0 : CQ *ᵥ z = 0 := by
    funext a
    have := congrFun (congrArg (fun v => P'.map (Int.castRingHom ℚ) *ᵥ v) hz) (Fin.castLE hk a)
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec_zero, Pi.zero_apply, ← castLin_mulVec, castLin_apply] at this
    simp only [CQ, certMat, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply,
      Pi.zero_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    rfl
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdetQ h0)

theorem mem_saturation_span_iff (hPP : P * P' = 1)
    (hzero : ∀ i : Fin n, k ≤ (i : ℕ) → ∀ j, (P' *ᵥ m j) i = 0)
    (hdet : (certMat hk m P').det ≠ 0) (v : Fin n → ℤ) :
    v ∈ saturation (Submodule.span ℤ (Set.range m)) ↔
      ∀ i : Fin n, k ≤ (i : ℕ) → (P' *ᵥ v) i = 0 := by
  rw [mem_saturation, ratSpan_span]
  constructor
  · intro hv i hi
    let φ : (Fin n → ℚ) →ₗ[ℚ] ℚ :=
      (LinearMap.proj i).comp (Matrix.toLin' (P'.map (Int.castRingHom ℚ)))
    have hle : Submodule.span ℚ (castLin n '' Set.range m) ≤ LinearMap.ker φ := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, φ, LinearMap.coe_comp, Function.comp_apply,
        Matrix.toLin'_apply, LinearMap.coe_proj, Function.eval, ← castLin_mulVec, castLin_apply,
        hzero i hi j, Int.cast_zero]
    have h := hle hv
    simp only [LinearMap.mem_ker, φ, LinearMap.coe_comp, Function.comp_apply, Matrix.toLin'_apply,
      LinearMap.coe_proj, Function.eval, ← castLin_mulVec, castLin_apply] at h
    exact_mod_cast h
  · intro hv
    set C := certMat hk m P'
    set y : Fin k → ℤ := fun a => (P' *ᵥ v) (Fin.castLE hk a)
    set z := C.adjugate *ᵥ y
    have hu : P' *ᵥ (∑ j, z j • m j) = C.det • (P' *ᵥ v) := by
      rw [certMat_mulVec hzero, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
        Matrix.one_mulVec, map_smul, padLin_top hk hv]
    have hu' : ∑ j, z j • m j = C.det • v := by
      rw [← mulVec_mulVec_of_mul_eq_one hPP (∑ j, z j • m j), hu, Matrix.mulVec_smul,
        mulVec_mulVec_of_mul_eq_one hPP]
    have hmem : castLin n (C.det • v) ∈ Submodule.span ℚ (castLin n '' Set.range m) := by
      rw [← hu', map_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [map_zsmul]
      exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨m j, ⟨j, rfl⟩, rfl⟩)
    have hC : (C.det : ℚ) ≠ 0 := by exact_mod_cast hdet
    have hv' : castLin n v = (C.det : ℚ)⁻¹ • castLin n (C.det • v) := by
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ hC, one_smul]
    rw [hv']
    exact Submodule.smul_mem _ _ hmem

theorem relIndex_saturation_of_cert (hPP : P * P' = 1)
    (hzero : ∀ i : Fin n, k ≤ (i : ℕ) → ∀ j, (P' *ᵥ m j) i = 0)
    (hdet : (certMat hk m P').det ≠ 0) :
    satIndex (Submodule.span ℤ (Set.range m)) = (certMat hk m P').det.natAbs := by
  set Λ := Submodule.span ℤ (Set.range m)
  have hP'P : P' * P = 1 := mul_eq_one_comm.1 hPP
  have hmemS := mem_saturation_span_iff hPP hzero hdet
  let φ : (Fin k → ℤ) ≃ₗ[ℤ] saturation Λ :=
    { toFun := fun y => ⟨P *ᵥ padLin n y, (hmemS _).2 fun i hi => by
        rw [Matrix.mulVec_mulVec, hP'P, Matrix.one_mulVec]
        have hik : ¬ ((i : ℕ) < k) := by omega
        simp [padLin, hik]⟩
      invFun := fun v a => (P' *ᵥ (v : Fin n → ℤ)) (Fin.castLE hk a)
      map_add' := fun y z => by
        ext1
        simp only [map_add, Matrix.mulVec_add, Submodule.coe_add]
      map_smul' := fun c y => by
        ext1
        simp only [map_smul, Matrix.mulVec_smul, Submodule.coe_smul, RingHom.id_apply]
      left_inv := fun y => by
        funext a
        simp only
        rw [Matrix.mulVec_mulVec, hP'P, Matrix.one_mulVec, padLin_castLE]
      right_inv := fun v => by
        ext1
        simp only
        rw [padLin_top hk ((hmemS _).1 v.2), mulVec_mulVec_of_mul_eq_one hPP] }
  let b₂ : Basis (Fin k) ℤ (saturation Λ) := (Pi.basisFun ℤ (Fin k)).map φ
  have hli : LinearIndependent ℤ m := linearIndependent_of_cert hzero hdet
  let bΛ : Basis (Fin k) ℤ Λ := Basis.span hli
  let N : Submodule ℤ (saturation Λ) := Λ.comap (saturation Λ).subtype
  let bN : Basis (Fin k) ℤ N := bΛ.map (Submodule.comapSubtypeEquivOfLe (le_saturation Λ)).symm
  have h := Submodule.natAbs_det_basis_change b₂ N bN
  have hcomp : ((↑) ∘ bN : Fin k → saturation Λ) =
      fun j => ⟨m j, le_saturation Λ (Submodule.subset_span ⟨j, rfl⟩)⟩ := by
    funext j
    ext1
    change ((Basis.span hli j : Λ) : Fin n → ℤ) = m j
    rw [Basis.span_apply]
  have hdetb : b₂.det ((↑) ∘ bN) = (certMat hk m P').det := by
    rw [hcomp, Basis.det_apply]
    congr 1
  rw [hdetb] at h
  rw [h]
  rfl

end Cert

end CFSG.RankThree.Lattice

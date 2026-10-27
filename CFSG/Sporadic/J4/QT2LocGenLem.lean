module

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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Sporadic.J4.QT2

open Matrix

section Images

variable {G M : Type*} [Group G] [Monoid M]

@[expose] def msSubgroup (φ : G →* M) (hφ : Function.Injective φ) (S : Set M) (h1 : (1 : M) ∈ S)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hsq : ∀ a ∈ S, a * a = 1) : Subgroup G where
  carrier := φ ⁻¹' S
  one_mem' := by simpa using h1
  mul_mem' := fun {x y} hx hy => by simpa using hmul _ hx _ hy
  inv_mem' := fun {x} hx => by
    have hxx : x * x = 1 := hφ (by simpa using hsq _ hx)
    have hinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    simpa [hinv] using hx

theorem mem_msSubgroup (φ : G →* M) (hφ : Function.Injective φ) (S : Set M) (h1 : (1 : M) ∈ S)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hsq : ∀ a ∈ S, a * a = 1) {x : G} :
    x ∈ msSubgroup φ hφ S h1 hmul hsq ↔ φ x ∈ S := Iff.rfl

theorem preimage_ncard_le (φ : G →* M) (hφ : Function.Injective φ) (S : Set M) (hS : S.Finite) :
    (φ ⁻¹' S).ncard ≤ S.ncard :=
  Set.ncard_le_ncard_of_injOn φ (fun _ hx => hx) hφ.injOn hS

theorem subgroup_eq_of_images (φ : G →* M) (hφ : Function.Injective φ) (S : Set M)
    (hS : S.Finite) {n : ℕ} (hcard : S.ncard ≤ n) {W U : Subgroup G} (hW : ∀ w ∈ W, φ w ∈ S)
    (hU : ∀ u ∈ U, φ u ∈ S) (hWc : Nat.card W = n) (hUc : Nat.card U = n) : W = U := by
  have hfin : (φ ⁻¹' S).Finite := hS.preimage hφ.injOn
  have hle : (φ ⁻¹' S).ncard ≤ n := (preimage_ncard_le φ hφ S hS).trans hcard
  have hWs : (W : Set G) ⊆ φ ⁻¹' S := fun w hw => hW w hw
  have hUs : (U : Set G) ⊆ φ ⁻¹' S := fun u hu => hU u hu
  have hWn : (W : Set G).ncard = n := by rw [← hWc]; exact (Nat.card_coe_set_eq _).symm
  have hUn : (U : Set G).ncard = n := by rw [← hUc]; exact (Nat.card_coe_set_eq _).symm
  have e1 : (W : Set G) = φ ⁻¹' S :=
    Set.eq_of_subset_of_ncard_le hWs (by rw [hWn]; exact hle) hfin
  have e2 : (U : Set G) = φ ⁻¹' S :=
    Set.eq_of_subset_of_ncard_le hUs (by rw [hUn]; exact hle) hfin
  exact SetLike.coe_injective (e1.trans e2.symm)

theorem card_eq_of_cover [Finite G] (φ : G →* M) (hφ : Function.Injective φ) (S : Set M)
    (hS : S.Finite) {n : ℕ} (hcard : S.ncard ≤ n) {U : Subgroup G} (hU : ∀ u ∈ U, φ u ∈ S)
    (f : Fin n → G) (hf : ∀ i, f i ∈ U) (hinj : Function.Injective f) : Nat.card U = n := by
  have hfin : (φ ⁻¹' S).Finite := hS.preimage hφ.injOn
  have hle : (φ ⁻¹' S).ncard ≤ n :=
    (Set.ncard_le_ncard_of_injOn φ (fun _ hx => hx) hφ.injOn hS).trans hcard
  have hUs : (U : Set G) ⊆ φ ⁻¹' S := fun u hu => hU u hu
  have h1 : Nat.card U ≤ n := by
    have e : Nat.card U = (U : Set G).ncard := Nat.card_coe_set_eq (U : Set G)
    rw [e]
    exact (Set.ncard_le_ncard hUs hfin).trans hle
  have h2 : n ≤ Nat.card U := by
    have hi : Function.Injective (fun i : Fin n => (⟨f i, hf i⟩ : U)) := fun a b hab =>
      hinj (congrArg Subtype.val hab)
    have := Nat.card_le_card_of_injective _ hi
    simpa using this
  omega

theorem conj_images (φ : G →* M) (S : Set M) (g : G) (U : Subgroup G)
    (hU : ∀ u ∈ U, φ g * φ u * φ g⁻¹ ∈ S) :
    ∀ x ∈ U.map (MulAut.conj g).toMonoidHom, φ x ∈ S := by
  rintro _ ⟨u, hu, rfl⟩
  have := hU u hu
  simpa [MulAut.conj_apply, map_mul] using this

theorem card_map_conj (g : G) (U : Subgroup G) :
    Nat.card (U.map (MulAut.conj g).toMonoidHom) = Nat.card U :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

end Images

section Fixed

variable {K : Type*} [Field K] {n : ℕ}

@[expose] noncomputable def fixPhi (A : Matrix (Fin n) (Fin n) K) :
    (Fin n → K) →ₗ[K] (Fin n → K) := Matrix.vecMulLinear (A - 1)

@[expose] noncomputable def fixDim (A : Matrix (Fin n) (Fin n) K) : ℕ :=
  Module.finrank K (LinearMap.ker (fixPhi A))

theorem linIndep_of_biorth {m : ℕ} (f d : Fin m → Fin n → K)
    (h : ∀ i j, f i ⬝ᵥ d j = if i = j then 1 else 0) : LinearIndependent K f := by
  let D : Matrix (Fin m) (Fin n) K := Matrix.of d
  have hcomp : LinearIndependent K ((Matrix.mulVecLin D) ∘ f) := by
    have e : (Matrix.mulVecLin D) ∘ f = fun i => Pi.basisFun K (Fin m) i := by
      funext i j
      simp only [Function.comp_apply, Matrix.mulVecLin_apply, Pi.basisFun_apply]
      show (d j ⬝ᵥ f i) = (Pi.single i (1 : K) : Fin m → K) j
      rw [dotProduct_comm, h i j]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    rw [e]
    exact (Pi.basisFun K (Fin m)).linearIndependent
  exact LinearIndependent.of_comp _ hcomp

theorem le_fixDim {A : Matrix (Fin n) (Fin n) K} {m : ℕ} (f d : Fin m → Fin n → K)
    (hbi : ∀ i j, f i ⬝ᵥ d j = if i = j then 1 else 0) (hfix : ∀ i, f i ᵥ* A = f i) :
    m ≤ fixDim A := by
  have hmem : ∀ i, f i ∈ LinearMap.ker (fixPhi A) := by
    intro i
    rw [LinearMap.mem_ker]
    show f i ᵥ* (A - 1) = 0
    rw [Matrix.vecMul_sub, Matrix.vecMul_one, hfix i, sub_self]
  have hli : LinearIndependent K (fun i => (⟨f i, hmem i⟩ : LinearMap.ker (fixPhi A))) := by
    refine LinearIndependent.of_comp (LinearMap.ker (fixPhi A)).subtype ?_
    exact linIndep_of_biorth f d hbi
  have := hli.fintype_card_le_finrank
  simpa [fixDim] using this

theorem fixDim_le_of_range {A : Matrix (Fin n) (Fin n) K} {m : ℕ} (f d : Fin m → Fin n → K)
    (hbi : ∀ i j, f i ⬝ᵥ d j = if i = j then 1 else 0)
    (hrange : ∀ i, ∃ x, x ᵥ* (A - 1) = f i) : fixDim A ≤ n - m := by
  have hmem : ∀ i, f i ∈ LinearMap.range (fixPhi A) := by
    intro i
    obtain ⟨x, hx⟩ := hrange i
    exact ⟨x, hx⟩
  have hli : LinearIndependent K (fun i => (⟨f i, hmem i⟩ : LinearMap.range (fixPhi A))) := by
    refine LinearIndependent.of_comp (LinearMap.range (fixPhi A)).subtype ?_
    exact linIndep_of_biorth f d hbi
  have h1 := hli.fintype_card_le_finrank
  have h2 := LinearMap.finrank_range_add_finrank_ker (fixPhi A)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2
  rw [Fintype.card_fin] at h1
  unfold fixDim
  omega

theorem fixDim_conj_le (P Q : Matrix (Fin n) (Fin n) K) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (A : Matrix (Fin n) (Fin n) K) : fixDim (P * A * Q) ≤ fixDim A := by
  have key : ∀ x : Fin n → K, (x ᵥ* P) ᵥ* (A - 1) = (x ᵥ* (P * A * Q - 1)) ᵥ* P := by
    intro x
    rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul]
    congr 1
    calc P * (A - 1) = P * A * (Q * P) - P := by
          rw [hQP, mul_one, mul_sub, mul_one]
      _ = (P * A * Q - 1) * P := by rw [sub_mul, one_mul, mul_assoc (P * A) Q P]
  have hmem : ∀ x : LinearMap.ker (fixPhi (P * A * Q)),
      (Matrix.vecMulLinear P) (x : Fin n → K) ∈ LinearMap.ker (fixPhi A) := by
    intro x
    have hx : (x : Fin n → K) ᵥ* (P * A * Q - 1) = 0 := LinearMap.mem_ker.1 x.2
    rw [LinearMap.mem_ker]
    show ((x : Fin n → K) ᵥ* P) ᵥ* (A - 1) = 0
    rw [key, hx, Matrix.zero_vecMul]
  let ψ : LinearMap.ker (fixPhi (P * A * Q)) →ₗ[K] LinearMap.ker (fixPhi A) :=
    ((Matrix.vecMulLinear P).comp (LinearMap.ker (fixPhi (P * A * Q))).subtype).codRestrict _ hmem
  have hinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : (x : Fin n → K) ᵥ* P = (y : Fin n → K) ᵥ* P := congrArg Subtype.val hxy
    have h2 : ∀ z : Fin n → K, z = (z ᵥ* P) ᵥ* Q := by
      intro z
      rw [Matrix.vecMul_vecMul, hPQ, Matrix.vecMul_one]
    apply Subtype.ext
    rw [h2 (x : Fin n → K), h2 (y : Fin n → K), h1]
  exact LinearMap.finrank_le_finrank_of_injective hinj

theorem fixDim_conj (P Q : Matrix (Fin n) (Fin n) K) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (A : Matrix (Fin n) (Fin n) K) : fixDim (P * A * Q) = fixDim A := by
  refine le_antisymm (fixDim_conj_le P Q hPQ hQP A) ?_
  have := fixDim_conj_le Q P hQP hPQ (P * A * Q)
  have e : Q * (P * A * Q) * P = A := by
    calc Q * (P * A * Q) * P = (Q * P) * A * (Q * P) := by simp only [mul_assoc]
      _ = A := by rw [hQP, one_mul, mul_one]
  rwa [e] at this

end Fixed

end CFSG.Sporadic.J4.QT2

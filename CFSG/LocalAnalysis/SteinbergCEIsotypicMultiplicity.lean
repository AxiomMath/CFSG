module

import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall
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
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.LittleWedderburn
public import Mathlib.RingTheory.Radical.NatInt
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

public noncomputable section

namespace CFSG.LocalAnalysis.CommutingFactor

open Module TensorProduct

variable {k : Type*} [Field k] {S : Type*} [AddCommGroup S] [Module k S]

section Defs

variable {D : Subgroup (Module.End k S)ˣ} {I : Submodule k S}

@[expose] def resD (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End k S) v ∈ I) (d : D) :
    Module.End k I :=
  (d.1 : Module.End k S).restrict (hDI d d.2)

theorem coe_resD (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End k S) v ∈ I) (d : D) (v : I) :
    ((resD hDI d v : I) : S) = (d.1 : Module.End k S) v :=
  rfl

@[expose] def commutantD (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End k S) v ∈ I) :
    Subalgebra k (Module.End k I) :=
  Subalgebra.centralizer k (Set.range (resD hDI))

theorem mem_commutantD (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End k S) v ∈ I)
    {φ : Module.End k I} : φ ∈ commutantD hDI ↔ ∀ d : D, resD hDI d * φ = φ * resD hDI d := by
  rw [commutantD, Subalgebra.mem_centralizer_iff]
  constructor
  · intro h d
    exact h _ ⟨d, rfl⟩
  · rintro h _ ⟨d, rfl⟩
    exact h d

@[expose] def fixedSub (A : Subgroup (Module.End k S)ˣ) : Submodule k S where
  carrier := {v | ∀ a ∈ A, (a : Module.End k S) v = v}
  add_mem' {v w} hv hw a ha := by rw [map_add, hv a ha, hw a ha]
  zero_mem' a _ := map_zero _
  smul_mem' c v hv a ha := by rw [map_smul, hv a ha]

theorem mem_fixedSub {A : Subgroup (Module.End k S)ˣ} {v : S} :
    v ∈ fixedSub A ↔ ∀ a ∈ A, (a : Module.End k S) v = v :=
  Iff.rfl

@[expose] def homD (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End k S) v ∈ I) :
    Submodule k (I →ₗ[k] S) where
  carrier := {f | ∀ d : D, ∀ v : I, f (resD hDI d v) = (d.1 : Module.End k S) (f v)}
  add_mem' {f g} hf hg d v := by
    rw [LinearMap.add_apply, LinearMap.add_apply, hf d v, hg d v, map_add]
  zero_mem' d v := by rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
  smul_mem' c f hf d v := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hf d v, map_smul]

theorem mem_homD (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End k S) v ∈ I) {f : I →ₗ[k] S} :
    f ∈ homD hDI ↔ ∀ d : D, ∀ v : I, f (resD hDI d v) = (d.1 : Module.End k S) (f v) :=
  Iff.rfl

@[expose] def evalHom (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End k S) v ∈ I) :
    I ⊗[k] homD hDI →ₗ[k] S :=
  TensorProduct.lift (homD hDI).subtype.flip

theorem evalHom_tmul (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End k S) v ∈ I) (v : I)
    (f : homD hDI) : evalHom hDI (v ⊗ₜ f) = (f : I →ₗ[k] S) v :=
  rfl

variable {X : Subgroup (Module.End k S)ˣ}

@[expose] def homAct (hXD : ∀ x ∈ X, ∀ d ∈ D, x * d = d * x)
    (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End k S) v ∈ I) : Representation k X (homD hDI) where
  toFun x :=
    { toFun := fun f => ⟨(x.1 : Module.End k S) ∘ₗ (f : I →ₗ[k] S), fun d v => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, f.2 d v]
        have h := congrArg (fun u : (Module.End k S)ˣ => (u : Module.End k S) ((f : I →ₗ[k] S) v))
          (hXD x x.2 d d.2)
        exact h⟩
      map_add' := fun f g => Subtype.ext (LinearMap.comp_add _ _ _)
      map_smul' := fun c f => Subtype.ext (LinearMap.comp_smul _ _ _) }
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    rfl
  map_mul' x y := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    rfl

theorem homAct_apply (hXD : ∀ x ∈ X, ∀ d ∈ D, x * d = d * x)
    (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End k S) v ∈ I) (x : X) (f : homD hDI) (v : I) :
    ((homAct hXD hDI x f : homD hDI) : I →ₗ[k] S) v =
      (x.1 : Module.End k S) ((f : I →ₗ[k] S) v) :=
  rfl

end Defs

section Invariance

variable {X D : Subgroup (Module.End k S)ˣ}

theorem invariant_sup {W : Submodule k S}
    (hX : ∀ x ∈ X, ∀ v ∈ W, (x : Module.End k S) v ∈ W)
    (hD : ∀ d ∈ D, ∀ v ∈ W, (d : Module.End k S) v ∈ W) :
    ∀ g ∈ X ⊔ D, ∀ v ∈ W, (g : Module.End k S) v ∈ W := by
  intro g hg
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction'' with
  | mem g hg =>
    rcases hg with hg | hg
    · exact hX g hg
    · exact hD g hg
  | inv_mem g hg =>
    rcases hg with hg | hg
    · exact hX g⁻¹ (X.inv_mem hg)
    · exact hD g⁻¹ (D.inv_mem hg)
  | one => intro v hv; exact hv
  | mul g h _ _ ihg ihh => intro v hv; exact ihg _ (ihh v hv)

theorem disjoint_or_le {J W : Submodule k S}
    (hJD : ∀ d ∈ D, ∀ v ∈ J, (d : Module.End k S) v ∈ J)
    (hJ : ∀ U ≤ J, (∀ d ∈ D, ∀ v ∈ U, (d : Module.End k S) v ∈ U) → U = ⊥ ∨ U = J)
    (hWD : ∀ d ∈ D, ∀ v ∈ W, (d : Module.End k S) v ∈ W) : Disjoint J W ∨ J ≤ W := by
  rcases hJ (J ⊓ W) inf_le_left (fun d hd v hv => ⟨hJD d hd v hv.1, hWD d hd v hv.2⟩) with
    h | h
  · exact Or.inl (disjoint_iff.mpr h)
  · exact Or.inr (h ▸ inf_le_right)

theorem map_map_inv (u : (Module.End k S)ˣ) (W : Submodule k S) :
    (W.map (u⁻¹ : (Module.End k S)ˣ).val).map (u : Module.End k S) = W := by
  rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Module.End.one_eq_id, Submodule.map_id]

theorem map_irreducible {x : (Module.End k S)ˣ} (hx : ∀ d ∈ D, x * d = d * x)
    {I : Submodule k S} (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End k S) v ∈ I)
    (hIirr : ∀ U ≤ I, (∀ d ∈ D, ∀ v ∈ U, (d : Module.End k S) v ∈ U) → U = ⊥ ∨ U = I) :
    (∀ d ∈ D, ∀ v ∈ I.map (x : Module.End k S),
      (d : Module.End k S) v ∈ I.map (x : Module.End k S)) ∧
    ∀ U ≤ I.map (x : Module.End k S), (∀ d ∈ D, ∀ v ∈ U, (d : Module.End k S) v ∈ U) →
      U = ⊥ ∨ U = I.map (x : Module.End k S) := by
  have hcomm : ∀ d ∈ D, ∀ v, (x : Module.End k S) ((d : Module.End k S) v) =
      (d : Module.End k S) ((x : Module.End k S) v) := fun d hd v => by
    have h := congrArg (fun u : (Module.End k S)ˣ => (u : Module.End k S) v) (hx d hd)
    simpa only [Units.val_mul, Module.End.mul_apply] using h
  have hcomm' : ∀ d ∈ D, ∀ v, ((x⁻¹ : (Module.End k S)ˣ) : Module.End k S)
      ((d : Module.End k S) v) = (d : Module.End k S) ((x⁻¹ : (Module.End k S)ˣ).val v) := by
    intro d hd v
    have h := hcomm d hd ((x⁻¹ : (Module.End k S)ˣ).val v)
    have e : (x : Module.End k S) ((x⁻¹ : (Module.End k S)ˣ).val v) = v := by
      rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_apply]
    rw [e] at h
    rw [← h, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  refine ⟨?_, fun U hU hUD => ?_⟩
  · rintro d hd _ ⟨v, hv, rfl⟩
    exact ⟨(d : Module.End k S) v, hDI d hd v hv, hcomm d hd v⟩
  · have hU' : U.map (x⁻¹ : (Module.End k S)ˣ).val ≤ I := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨v, hv, rfl⟩ := hU hw
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
      exact hv
    have hUD' : ∀ d ∈ D, ∀ v ∈ U.map (x⁻¹ : (Module.End k S)ˣ).val,
        (d : Module.End k S) v ∈ U.map (x⁻¹ : (Module.End k S)ˣ).val := by
      rintro d hd _ ⟨w, hw, rfl⟩
      exact ⟨(d : Module.End k S) w, hUD d hd w hw, hcomm' d hd w⟩
    rcases hIirr _ hU' hUD' with h | h
    · left
      rw [← map_map_inv x U, h, Submodule.map_bot]
    · right
      rw [← map_map_inv x U, h]

end Invariance

section Decomposition

variable [Finite k] [FiniteDimensional k S] {X D : Subgroup (Module.End k S)ˣ}

omit [FiniteDimensional k S] in
theorem finite_endUnits [FiniteDimensional k S] : Finite (Module.End k S)ˣ := by
  have : Finite S := Module.finite_of_finite k
  have : Finite (Module.End k S) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := Module.End k S))
  exact Finite.of_injective _ Units.val_injective

theorem exists_isotypic_equiv (hXD : ∀ x ∈ X, ∀ d ∈ D, x * d = d * x)
    (hirr : ∀ W : Submodule k S,
      (∀ g ∈ X ⊔ D, ∀ v ∈ W, (g : Module.End k S) v ∈ W) → W = ⊥ ∨ W = ⊤)
    {I : Submodule k S} (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End k S) v ∈ I) (hI0 : I ≠ ⊥)
    (hIirr : ∀ U ≤ I, (∀ d ∈ D, ∀ v ∈ U, (d : Module.End k S) v ∈ U) → U = ⊥ ∨ U = I) :
    ∃ (r : ℕ) (Φ : (Fin r → I) ≃ₗ[k] S),
      ∀ d : D, ∀ v, Φ (fun i => resD hDI d (v i)) = (d.1 : Module.End k S) (Φ v) := by
  classical
  have := finite_endUnits (k := k) (S := S)
  let := Fintype.ofFinite (Module.End k S)ˣ
  set f : (Module.End k S)ˣ → Submodule k S := fun x => I.map (x : Module.End k S) with hf
  have hfX : ∀ x ∈ X, (∀ d ∈ D, ∀ v ∈ f x, (d : Module.End k S) v ∈ f x) ∧
      ∀ U ≤ f x, (∀ d ∈ D, ∀ v ∈ U, (d : Module.End k S) v ∈ U) → U = ⊥ ∨ U = f x :=
    fun x hx => map_irreducible (fun d hd => hXD x hx d hd) hDI hIirr
  set 𝒞 := ((Finset.univ.filter (· ∈ X)).powerset.filter fun s => s.SupIndep f) with h𝒞
  have h𝒞ne : 𝒞.Nonempty := ⟨∅, by simp [𝒞, Finset.supIndep_empty]⟩
  obtain ⟨s, hs𝒞, hsmax⟩ := Finset.exists_max_image 𝒞 Finset.card h𝒞ne
  simp only [𝒞, Finset.mem_filter, Finset.mem_powerset] at hs𝒞
  obtain ⟨hsX', hsind⟩ := hs𝒞
  have hsX : ∀ x ∈ s, x ∈ X := fun x hx => by simpa using hsX' hx
  have hsupD : ∀ d ∈ D, ∀ v ∈ s.sup f, (d : Module.End k S) v ∈ s.sup f := by
    intro d hd
    refine Finset.sup_induction (p := fun W => ∀ v ∈ W, (d : Module.End k S) v ∈ W) ?_ ?_ ?_
    · intro v hv
      rw [Submodule.mem_bot] at hv
      rw [hv, map_zero]
      exact Submodule.zero_mem _
    · intro W₁ h₁ W₂ h₂ v hv
      obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add]
      exact Submodule.add_mem_sup (h₁ w₁ hw₁) (h₂ w₂ hw₂)
    · intro x hx
      exact (hfX x (hsX x hx)).1 d hd
  have hle : ∀ x ∈ X, f x ≤ s.sup f := by
    intro x hx
    by_cases hxs : x ∈ s
    · exact Finset.le_sup (f := f) hxs
    rcases disjoint_or_le (hfX x hx).1 (hfX x hx).2 hsupD with h | h
    · exfalso
      have hmem : insert x s ∈ 𝒞 := by
        simp only [𝒞, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.insert_subset (by simpa using hx) hsX', hsind.insert h⟩
      have := hsmax _ hmem
      rw [Finset.card_insert_of_notMem hxs] at this
      omega
    · exact h
  have hsupX : ∀ x ∈ X, ∀ v ∈ s.sup f, (x : Module.End k S) v ∈ s.sup f := by
    intro x hx
    refine Finset.sup_induction
      (p := fun W => ∀ v ∈ W, (x : Module.End k S) v ∈ s.sup f) ?_ ?_ ?_
    · intro v hv
      rw [Submodule.mem_bot] at hv
      rw [hv, map_zero]
      exact Submodule.zero_mem _
    · intro W₁ h₁ W₂ h₂ v hv
      obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add]
      exact Submodule.add_mem _ (h₁ w₁ hw₁) (h₂ w₂ hw₂)
    · intro y hy v hv
      apply hle (x * y) (X.mul_mem hx (hsX y hy))
      obtain ⟨w, hw, rfl⟩ := hv
      exact ⟨w, hw, by rw [Units.val_mul, Module.End.mul_apply]⟩
  have htop : s.sup f = ⊤ := by
    rcases hirr _ (invariant_sup hsupX hsupD) with h | h
    · exfalso
      apply hI0
      have h1 := hle 1 X.one_mem
      rw [h, le_bot_iff] at h1
      change I.map ((1 : (Module.End k S)ˣ) : Module.End k S) = ⊥ at h1
      rwa [Units.val_one, Module.End.one_eq_id, Submodule.map_id] at h1
    · exact h
  set r := s.card
  set e := s.equivFin
  set xs : Fin r → (Module.End k S)ˣ := fun i => (e.symm i : (Module.End k S)ˣ) with hxs
  have hxsX : ∀ i, xs i ∈ X := fun i => hsX _ (e.symm i).2
  have hind : iSupIndep (f ∘ xs) := hsind.independent.comp e.symm.injective
  set Φ₀ : (Fin r → I) →ₗ[k] S :=
    ∑ i, (xs i : Module.End k S) ∘ₗ I.subtype ∘ₗ LinearMap.proj i with hΦ₀def
  have hΦ₀ : ∀ v, Φ₀ v = ∑ i, (xs i : Module.End k S) (v i) := by
    intro v
    simp [Φ₀]
  have hinj : Function.Injective Φ₀ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    rw [hΦ₀] at hv
    have h0 := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp hind Finset.univ
      (fun i => (xs i : Module.End k S) (v i)) (fun i _ => ⟨v i, (v i).2, rfl⟩) hv
    funext i
    apply Subtype.ext
    have h1 := h0 i (Finset.mem_univ i)
    have e2 : ((v i : I) : S) =
        ((xs i)⁻¹ : (Module.End k S)ˣ).val ((xs i : Module.End k S) (v i)) := by
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
    rw [e2]
    change (xs i : Module.End k S) (v i) = 0 at h1
    rw [h1, map_zero]
    rfl
  have hsurj : Function.Surjective Φ₀ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← htop]
    refine Finset.sup_le fun x hx => ?_
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨Pi.single (e ⟨x, hx⟩) ⟨w, hw⟩, ?_⟩
    rw [hΦ₀, Finset.sum_eq_single (e ⟨x, hx⟩)]
    · simp [xs]
    · intro j _ hj
      simp [hj]
    · simp
  refine ⟨r, LinearEquiv.ofBijective Φ₀ (show Function.Bijective Φ₀ from ⟨hinj, hsurj⟩),
    fun d v => ?_⟩
  rw [LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply, hΦ₀, hΦ₀, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_resD]
  have h := congrArg (fun u : (Module.End k S)ˣ => (u : Module.End k S) (v i))
    (hXD (xs i) (hxsX i) d d.2)
  simpa only [Units.val_mul, Module.End.mul_apply] using h

end Decomposition

section Schur

variable {D : Subgroup (Module.End k S)ˣ} {I : Submodule k S}
  (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End k S) v ∈ I)

include hDI in
theorem injective_of_mem_commutantD
    (hIirr : ∀ U ≤ I, (∀ d ∈ D, ∀ v ∈ U, (d : Module.End k S) v ∈ U) → U = ⊥ ∨ U = I)
    {φ : Module.End k I} (hφ : φ ∈ commutantD hDI) (hφ0 : φ ≠ 0) : Function.Injective φ := by
  rw [mem_commutantD] at hφ
  rw [← LinearMap.ker_eq_bot]
  have hK : (LinearMap.ker φ).map I.subtype ≤ I := Submodule.map_subtype_le _ _
  have hKD : ∀ d ∈ D, ∀ v ∈ (LinearMap.ker φ).map I.subtype,
      (d : Module.End k S) v ∈ (LinearMap.ker φ).map I.subtype := by
    rintro d hd _ ⟨v, hv, rfl⟩
    refine ⟨resD hDI ⟨d, hd⟩ v, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hv ⊢
    have h := LinearMap.congr_fun (hφ ⟨d, hd⟩) v
    rw [Module.End.mul_apply, Module.End.mul_apply, hv, map_zero] at h
    exact h.symm
  rcases hIirr _ hK hKD with h | h
  · exact Submodule.map_injective_of_injective I.injective_subtype
      (h.trans (Submodule.map_bot _).symm)
  · exfalso
    apply hφ0
    apply LinearMap.ext
    intro v
    have hv : (v : S) ∈ (LinearMap.ker φ).map I.subtype := by rw [h]; exact v.2
    obtain ⟨w, hw, hwv⟩ := hv
    rw [LinearMap.zero_apply, ← Subtype.ext hwv]
    exact hw

include hDI in
theorem commutantD_isField [Finite k] [FiniteDimensional k S] (hI0 : I ≠ ⊥)
    (hIirr : ∀ U ≤ I, (∀ d ∈ D, ∀ v ∈ U, (d : Module.End k S) v ∈ U) → U = ⊥ ∨ U = I) :
    IsField (commutantD hDI) ∧ Finite (commutantD hDI) := by
  have : Finite S := Module.finite_of_finite k
  have : Finite (Module.End k I) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := Module.End k I))
  have hfin : Finite (commutantD hDI) := Subtype.finite
  have hnt : Nontrivial (commutantD hDI) := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
    refine ⟨⟨1, 0, fun h => hv0 ?_⟩⟩
    have h1 := congrArg (fun φ : commutantD hDI => ((φ : Module.End k I) ⟨v, hv⟩ : S)) h
    simpa using h1
  have hnzd : NoZeroDivisors (commutantD hDI) := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra h
    push Not at h
    have ha := injective_of_mem_commutantD hDI hIirr a.2
      (fun h0 => h.1 (Subtype.ext h0))
    apply h.2
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    apply ha
    have h1 := congrArg (fun φ : commutantD hDI => (φ : Module.End k I) v) hab
    simpa using h1
  have := NoZeroDivisors.to_isDomain (commutantD hDI)
  have hF := Finite.isDomain_to_isField (commutantD hDI)
  exact ⟨⟨hF.exists_pair_ne, hF.mul_comm, hF.mul_inv_cancel⟩, hfin⟩

end Schur

section Consequences

variable {D : Subgroup (Module.End k S)ˣ} {I : Submodule k S}
  (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End k S) v ∈ I) {r : ℕ} (Φ : (Fin r → I) ≃ₗ[k] S)

include hDI in
theorem symm_equivariant
    (hΦ : ∀ d : D, ∀ v, Φ (fun i => resD hDI d (v i)) = (d.1 : Module.End k S) (Φ v))
    (d : D) (w : S) :
    Φ.symm ((d.1 : Module.End k S) w) = fun i => resD hDI d (Φ.symm w i) := by
  apply Φ.injective
  rw [LinearEquiv.apply_symm_apply, hΦ, LinearEquiv.apply_symm_apply]

include hDI in
theorem faithful_on_I
    (hΦ : ∀ d : D, ∀ v, Φ (fun i => resD hDI d (v i)) = (d.1 : Module.End k S) (Φ v))
    {d : (Module.End k S)ˣ} (hd : d ∈ D) (h : ∀ v ∈ I, (d : Module.End k S) v = v) : d = 1 := by
  apply Units.ext
  apply LinearMap.ext
  intro w
  have hres : ∀ u : I, resD hDI ⟨d, hd⟩ u = u := fun u => Subtype.ext (h u u.2)
  have e := hΦ ⟨d, hd⟩ (Φ.symm w)
  simp only [hres, LinearEquiv.apply_symm_apply] at e
  rw [Units.val_one, Module.End.one_apply]
  exact e.symm

@[expose] def matOf : Module.End k S ≃+* Matrix (Fin r) (Fin r) (Module.End k I) :=
  Φ.symm.conjRingEquiv.trans (endVecRingEquivMatrixEnd (Fin r) k I)

theorem matOf_apply (g : Module.End k S) (i j : Fin r) (v : I) :
    matOf Φ g i j v = Φ.symm (g (Φ (Pi.single j v))) i :=
  rfl

include hDI in
theorem matOf_resD
    (hΦ : ∀ d : D, ∀ v, Φ (fun i => resD hDI d (v i)) = (d.1 : Module.End k S) (Φ v))
    (d : D) : matOf Φ (d.1 : Module.End k S) = Matrix.diagonal fun _ => resD hDI d := by
  ext i j v
  rw [matOf_apply, symm_equivariant hDI Φ hΦ, LinearEquiv.symm_apply_apply,
    Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

include hDI in
theorem commute_iff_mem
    (hΦ : ∀ d : D, ∀ v, Φ (fun i => resD hDI d (v i)) = (d.1 : Module.End k S) (Φ v))
    (g : Module.End k S) :
    (∀ d : D, (d.1 : Module.End k S) * g = g * d.1) ↔
      ∀ i j, matOf Φ g i j ∈ commutantD hDI := by
  constructor
  · intro h i j
    rw [mem_commutantD]
    intro d
    have e := congrArg (matOf Φ) (h d)
    rw [map_mul, map_mul, matOf_resD hDI Φ hΦ] at e
    have e' := congrFun (congrFun e i) j
    rwa [Matrix.diagonal_mul, Matrix.mul_diagonal] at e'
  · intro h d
    apply (matOf Φ).injective
    rw [map_mul, map_mul, matOf_resD hDI Φ hΦ]
    refine Matrix.ext fun i j => ?_
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    exact (mem_commutantD hDI).mp (h i j) d

include hDI in
theorem exists_centralizer_equiv
    (hΦ : ∀ d : D, ∀ v, Φ (fun i => resD hDI d (v i)) = (d.1 : Module.End k S) (Φ v)) :
    ∃ ψ : Subgroup.centralizer (D : Set (Module.End k S)ˣ) ≃*
        (Matrix (Fin r) (Fin r) (commutantD hDI))ˣ,
      ∀ g i j (v : I), (((ψ g : Matrix (Fin r) (Fin r) (commutantD hDI)) i j :
        Module.End k I) v) = Φ.symm ((g.1 : Module.End k S) (Φ (Pi.single j v))) i := by
  classical
  set F := commutantD hDI
  set T := matOf (k := k) Φ
  set ι : Matrix (Fin r) (Fin r) F →+* Matrix (Fin r) (Fin r) (Module.End k I) :=
    F.val.toRingHom.mapMatrix with hιdef
  have hι : Function.Injective ι := fun a b h => Matrix.ext fun i j =>
    Subtype.ext (congrFun (congrFun h i) j)
  have hC : ∀ g : (Module.End k S)ˣ, g ∈ Subgroup.centralizer (D : Set (Module.End k S)ˣ) ↔
      ∀ i j, T g i j ∈ F := by
    intro g
    rw [Subgroup.mem_centralizer_iff, ← commute_iff_mem hDI Φ hΦ]
    constructor
    · intro h d
      have e := congrArg Units.val (h d.1 d.2)
      rwa [Units.val_mul, Units.val_mul] at e
    · intro h d hd
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      exact h ⟨d, hd⟩
  let AF : ∀ a : Module.End k S, (∀ i j, T a i j ∈ F) → Matrix (Fin r) (Fin r) F :=
    fun a ha => Matrix.of fun i j => ⟨T a i j, ha i j⟩
  have hAF : ∀ a ha, ι (AF a ha) = T a := fun a ha => Matrix.ext fun i j => rfl
  let ψ₀ : Subgroup.centralizer (D : Set (Module.End k S)ˣ) →* (Matrix (Fin r) (Fin r) F)ˣ :=
    { toFun := fun g =>
        { val := AF g.1.val ((hC g.1).mp g.2)
          inv := AF (g.1⁻¹).val ((hC g.1⁻¹).mp (Subgroup.inv_mem _ g.2))
          val_inv := hι (by
            rw [map_mul, hAF, hAF, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
              map_one, map_one])
          inv_val := hι (by
            rw [map_mul, hAF, hAF, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
              map_one, map_one]) }
      map_one' := Units.ext (hι (by
        change ι (AF _ _) = ι 1
        rw [hAF, map_one]
        exact map_one T))
      map_mul' := fun g h => Units.ext (hι (by
        change ι (AF _ _) = ι (AF _ _ * AF _ _)
        rw [map_mul, hAF, hAF, hAF]
        exact map_mul T _ _)) }
  have hinj : Function.Injective ψ₀ := by
    intro g h e
    have e1 := congrArg (fun u : (Matrix (Fin r) (Fin r) F)ˣ => ι u.val) e
    change ι (AF _ _) = ι (AF _ _) at e1
    rw [hAF, hAF] at e1
    exact Subtype.ext (Units.ext (T.injective e1))
  have hsurj : Function.Surjective ψ₀ := by
    intro u
    set a := T.symm (ι u.val)
    set b := T.symm (ι (u⁻¹ : (Matrix (Fin r) (Fin r) F)ˣ).val)
    have hab : a * b = 1 := T.injective (by
      rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, ← map_mul,
        Units.mul_inv, map_one, map_one])
    have hba : b * a = 1 := T.injective (by
      rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, ← map_mul,
        Units.inv_mul, map_one, map_one])
    set g : (Module.End k S)ˣ := ⟨a, b, hab, hba⟩
    have hg : g ∈ Subgroup.centralizer (D : Set (Module.End k S)ˣ) := by
      rw [hC]
      intro i j
      change T (T.symm (ι u.val)) i j ∈ F
      rw [RingEquiv.apply_symm_apply]
      exact (u.val i j).2
    refine ⟨⟨g, hg⟩, Units.ext (hι ?_)⟩
    change ι (AF _ _) = ι u.val
    rw [hAF]
    exact RingEquiv.apply_symm_apply _ _
  exact ⟨MulEquiv.ofBijective ψ₀ ⟨hinj, hsurj⟩, fun g i j v => rfl⟩

omit [Module k S] in
theorem finrank_fin_fun_eq (W : Type*) [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (n : ℕ) : finrank k (Fin n → W) = n * finrank k W := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]

include hDI in
theorem finrank_fixedSub [FiniteDimensional k S]
    (hΦ : ∀ d : D, ∀ v, Φ (fun i => resD hDI d (v i)) = (d.1 : Module.End k S) (Φ v))
    {A : Subgroup (Module.End k S)ˣ} (hA : A ≤ D) :
    finrank k (fixedSub A) = r * finrank k ↥(I ⊓ fixedSub A) := by
  have hsym : ∀ a (ha : a ∈ A) (w : S), Φ.symm ((a : Module.End k S) w) =
      fun i => resD hDI ⟨a, hA ha⟩ (Φ.symm w i) :=
    fun a ha w => symm_equivariant hDI Φ hΦ ⟨a, hA ha⟩ w
  let e : fixedSub A ≃ₗ[k] (Fin r → ↥(I ⊓ fixedSub A)) :=
    { toFun := fun w i => ⟨(Φ.symm w i : S), Submodule.mem_inf.mpr ⟨(Φ.symm w i).2,
        mem_fixedSub.mpr fun a ha => by
          have h := congrFun (hsym a ha w) i
          rw [mem_fixedSub.mp w.2 a ha] at h
          exact (congrArg Subtype.val h).symm⟩⟩
      invFun := fun u => ⟨Φ (fun i => ⟨(u i : S), (Submodule.mem_inf.mp (u i).2).1⟩),
        mem_fixedSub.mpr fun a ha => by
          rw [← hΦ ⟨a, hA ha⟩]
          congr 1
          funext i
          exact Subtype.ext (mem_fixedSub.mp (Submodule.mem_inf.mp (u i).2).2 a ha)⟩
      left_inv := fun w => Subtype.ext (by
        change Φ (fun i => ⟨((Φ.symm w i : I) : S), _⟩) = w
        exact Φ.apply_symm_apply w)
      right_inv := fun u => funext fun i => Subtype.ext (by
        change ((Φ.symm (Φ (fun i => ⟨(u i : S), _⟩)) i : I) : S) = u i
        rw [LinearEquiv.symm_apply_apply])
      map_add' := fun w w' => funext fun i => Subtype.ext (by
        change ((Φ.symm (w + w' : S) i : I) : S) = (Φ.symm w i : S) + (Φ.symm w' i : S)
        rw [map_add]
        rfl)
      map_smul' := fun c w => funext fun i => Subtype.ext (by
        change ((Φ.symm (c • (w : S)) i : I) : S) = c • (Φ.symm w i : S)
        rw [map_smul]
        rfl) }
  rw [e.finrank_eq, finrank_fin_fun_eq]

theorem not_injective_of_perfect {G H : Type*} [Group G] [Group H] [Nontrivial G]
    [Group.IsPerfect G] (hH : ∀ a b : H, a * b = b * a) (f : G →* H) :
    ¬ Function.Injective f := by
  intro hf
  have : IsMulCommutative G := ⟨⟨fun a b => hf (by rw [map_mul, map_mul, hH])⟩⟩
  exact Group.IsPerfect.not_isMulCommutative G this

theorem units_matrix_one_comm {R : Type*} [Semiring R] (hR : ∀ a b : R, a * b = b * a)
    (a b : (Matrix (Fin 1) (Fin 1) R)ˣ) : a * b = b * a := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, hR]

end Consequences

section Tensor

variable {X D : Subgroup (Module.End k S)ˣ} {I : Submodule k S}
  (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End k S) v ∈ I) {r : ℕ} (Φ : (Fin r → I) ≃ₗ[k] S)

include hDI in
theorem homD_equiv_pi
    (hΦ : ∀ d : D, ∀ v, Φ (fun i => resD hDI d (v i)) = (d.1 : Module.End k S) (Φ v)) :
    Nonempty (homD hDI ≃ₗ[k] (Fin r → commutantD hDI)) := by
  refine ⟨{
    toFun := fun f i => ⟨LinearMap.proj i ∘ₗ Φ.symm.toLinearMap ∘ₗ (f : I →ₗ[k] S),
      (mem_commutantD hDI).mpr fun d => LinearMap.ext fun v => by
        change resD hDI d (Φ.symm ((f : I →ₗ[k] S) v) i) =
          Φ.symm ((f : I →ₗ[k] S) (resD hDI d v)) i
        rw [f.2 d v, symm_equivariant hDI Φ hΦ]⟩
    invFun := fun φ => ⟨Φ.toLinearMap ∘ₗ LinearMap.pi fun i => (φ i : Module.End k I),
      fun d v => by
        change Φ (fun i => (φ i : Module.End k I) (resD hDI d v)) =
          (d.1 : Module.End k S) (Φ (fun i => (φ i : Module.End k I) v))
        rw [← hΦ d]
        congr 1
        funext i
        have h := LinearMap.congr_fun ((mem_commutantD hDI).mp (φ i).2 d) v
        exact h.symm⟩
    left_inv := fun f => Subtype.ext (LinearMap.ext fun v => by
      change Φ (fun i => Φ.symm ((f : I →ₗ[k] S) v) i) = (f : I →ₗ[k] S) v
      exact Φ.apply_symm_apply _)
    right_inv := fun φ => funext fun i => Subtype.ext (LinearMap.ext fun v => by
      change Φ.symm (Φ (fun i => (φ i : Module.End k I) v)) i = (φ i : Module.End k I) v
      rw [LinearEquiv.symm_apply_apply])
    map_add' := fun f g => funext fun i => Subtype.ext (LinearMap.ext fun v => by
      change Φ.symm ((f : I →ₗ[k] S) v + (g : I →ₗ[k] S) v) i =
        Φ.symm ((f : I →ₗ[k] S) v) i + Φ.symm ((g : I →ₗ[k] S) v) i
      rw [map_add]
      rfl)
    map_smul' := fun c f => funext fun i => Subtype.ext (LinearMap.ext fun v => by
      change Φ.symm (c • (f : I →ₗ[k] S) v) i = c • Φ.symm ((f : I →ₗ[k] S) v) i
      rw [map_smul]
      rfl) }⟩

include hDI in
theorem evalHom_surjective
    (hΦ : ∀ d : D, ∀ v, Φ (fun i => resD hDI d (v i)) = (d.1 : Module.End k S) (Φ v)) :
    Function.Surjective (evalHom hDI) := by
  classical
  have hmem : ∀ i, Φ.toLinearMap ∘ₗ LinearMap.single k (fun _ : Fin r => I) i ∈ homD hDI := by
    intro i d v
    change Φ (Pi.single i (resD hDI d v)) = (d.1 : Module.End k S) (Φ (Pi.single i v))
    rw [← hΦ d]
    congr 1
    funext l
    by_cases hl : l = i
    · subst hl
      simp
    · simp [hl]
  intro w
  refine ⟨∑ i, (Φ.symm w i) ⊗ₜ ⟨_, hmem i⟩, ?_⟩
  rw [map_sum]
  have h : ∀ i, evalHom hDI ((Φ.symm w i) ⊗ₜ ⟨_, hmem i⟩) = Φ (Pi.single i (Φ.symm w i)) :=
    fun i => rfl
  simp only [h]
  rw [← map_sum, Finset.univ_sum_single, LinearEquiv.apply_symm_apply]

include hDI in
theorem tensor_case [Finite k] [FiniteDimensional k S] (hXD : ∀ x ∈ X, ∀ d ∈ D, x * d = d * x)
    (hirr : ∀ W : Submodule k S,
      (∀ g ∈ X ⊔ D, ∀ v ∈ W, (g : Module.End k S) v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hI0 : I ≠ ⊥)
    (hΦ : ∀ d : D, ∀ v, Φ (fun i => resD hDI d (v i)) = (d.1 : Module.End k S) (Φ v))
    (hr : 1 ≤ r) (hbot : commutantD hDI = ⊥) :
    Function.Bijective (evalHom hDI) ∧
      (∀ (d : D) (v : I) (f : homD hDI),
        evalHom hDI (resD hDI d v ⊗ₜ f) = (d.1 : Module.End k S) (evalHom hDI (v ⊗ₜ f))) ∧
      (∀ (x : X) (v : I) (f : homD hDI),
        evalHom hDI (v ⊗ₜ homAct hXD hDI x f) = (x.1 : Module.End k S) (evalHom hDI (v ⊗ₜ f))) ∧
      Function.Injective (homAct hXD hDI) ∧ Nontrivial (homD hDI) ∧
      ∀ N : Submodule k (homD hDI), (∀ (x : X), ∀ f ∈ N, homAct hXD hDI x f ∈ N) →
        N = ⊥ ∨ N = ⊤ := by
  classical
  have hInt : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr hI0
  have hIpos : 0 < finrank k I := Module.finrank_pos
  have hEnd : Nontrivial (Module.End k I) := inferInstance
  have hM : finrank k (homD hDI) = r := by
    obtain ⟨e⟩ := homD_equiv_pi hDI Φ hΦ
    have h1 : Nat.card (homD hDI) = Nat.card (commutantD hDI) ^ r := by
      rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin r),
        Fintype.card_fin]
    have h2 : Nat.card (commutantD hDI) = Nat.card k := by
      rw [hbot]
      exact Nat.card_congr (Algebra.botEquiv k (Module.End k I)).toEquiv
    have h3 : Nat.card (homD hDI) = Nat.card k ^ finrank k (homD hDI) :=
      Module.natCard_eq_pow_finrank
    rw [h1, h2] at h3
    exact (Nat.pow_right_injective Finite.one_lt_card h3).symm
  have hS : finrank k S = r * finrank k I := by
    rw [← Φ.finrank_eq, finrank_fin_fun_eq]
  have hIM : finrank k (I ⊗[k] homD hDI) = finrank k S := by
    rw [Module.finrank_tensorProduct, hM, hS, mul_comm]
  have hsurj := evalHom_surjective hDI Φ hΦ
  have hbij : Function.Bijective (evalHom hDI) :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hIM).mpr hsurj, hsurj⟩
  have hxev : ∀ (x : X) (t : I ⊗[k] homD hDI), (x.1 : Module.End k S) (evalHom hDI t) =
      evalHom hDI (LinearMap.lTensor I (homAct hXD hDI x) t) := by
    intro x t
    induction t using TensorProduct.inductionOn with
    | tmul v f => rfl
    | add t t' ht ht' => simp only [map_add, ht, ht']
  refine ⟨hbij, fun d v f => f.2 d v, fun x v f => rfl, ?_, ?_, fun N hN => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro w
    obtain ⟨t, rfl⟩ := hsurj w
    rw [hxev, hx, Module.End.one_eq_id, LinearMap.lTensor_id, LinearMap.id_apply]
    rfl
  · exact Module.nontrivial_of_finrank_pos (by rw [hM]; omega)
  ·
    set E := evalHom hDI ∘ₗ LinearMap.lTensor I N.subtype with hE
    have hWX : ∀ x ∈ X, ∀ w ∈ LinearMap.range E, (x : Module.End k S) w ∈ LinearMap.range E := by
      rintro x hx _ ⟨t, rfl⟩
      set ρN : N →ₗ[k] N := (homAct hXD hDI ⟨x, hx⟩).restrict (fun f hf => hN ⟨x, hx⟩ f hf)
      refine ⟨LinearMap.lTensor I ρN t, ?_⟩
      induction t using TensorProduct.inductionOn with
      | tmul v n => rfl
      | add t t' ht ht' => simp only [map_add, ht, ht']
    have hWD : ∀ d ∈ D, ∀ w ∈ LinearMap.range E, (d : Module.End k S) w ∈ LinearMap.range E := by
      rintro d hd _ ⟨t, rfl⟩
      refine ⟨LinearMap.rTensor N (resD hDI ⟨d, hd⟩) t, ?_⟩
      induction t using TensorProduct.inductionOn with
      | tmul v n => exact (n : homD hDI).2 ⟨d, hd⟩ v
      | add t t' ht ht' => simp only [map_add, ht, ht']
    rcases hirr _ (invariant_sup hWX hWD) with hW | hW
    · left
      rw [eq_bot_iff]
      intro n hn
      rw [Submodule.mem_bot]
      apply Subtype.ext
      apply LinearMap.ext
      intro v
      have h : E (v ⊗ₜ ⟨n, hn⟩) ∈ LinearMap.range E := ⟨_, rfl⟩
      rw [hW, Submodule.mem_bot] at h
      exact h
    · right
      have : Module.Free k N := Module.Free.of_divisionRing k N
      have hEinj : Function.Injective E :=
        hbij.1.comp (Module.Flat.lTensor_preserves_injective_linearMap _ N.injective_subtype)
      have h1 := LinearMap.finrank_range_of_inj hEinj
      rw [hW, finrank_top, Module.finrank_tensorProduct, ← hIM,
        Module.finrank_tensorProduct] at h1
      apply Submodule.eq_top_of_finrank_eq
      exact (Nat.eq_of_mul_eq_mul_left hIpos h1).symm

end Tensor

theorem commuting_factor_irreducible_modules_have_isotypic_multiplicity [Finite k]
    [FiniteDimensional k S] [Nontrivial S] {X D : Subgroup (Module.End k S)ˣ}
    (hXD : ∀ x ∈ X, ∀ d ∈ D, x * d = d * x)
    (hirr : ∀ W : Submodule k S,
      (∀ g ∈ X ⊔ D, ∀ v ∈ W, (g : Module.End k S) v ∈ W) → W = ⊥ ∨ W = ⊤)
    {I : Submodule k S} (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End k S) v ∈ I) (hI0 : I ≠ ⊥)
    (hIirr : ∀ U ≤ I, (∀ d ∈ D, ∀ v ∈ U, (d : Module.End k S) v ∈ U) → U = ⊥ ∨ U = I) :
    ∃ (r : ℕ) (Φ : (Fin r → I) ≃ₗ[k] S), 1 ≤ r ∧
      (∀ d : D, ∀ v, Φ (fun i => resD hDI d (v i)) = (d.1 : Module.End k S) (Φ v)) ∧
      (∀ d ∈ D, (∀ v ∈ I, (d : Module.End k S) v = v) → d = 1) ∧
      IsField (commutantD hDI) ∧ Finite (commutantD hDI) ∧
      X ≤ Subgroup.centralizer (D : Set (Module.End k S)ˣ) ∧
      (∃ ψ : Subgroup.centralizer (D : Set (Module.End k S)ˣ) ≃*
          (Matrix (Fin r) (Fin r) (commutantD hDI))ˣ,
        ∀ g i j (v : I), (((ψ g : Matrix (Fin r) (Fin r) (commutantD hDI)) i j :
          Module.End k I) v) = Φ.symm ((g.1 : Module.End k S) (Φ (Pi.single j v))) i) ∧
      (∀ A : Subgroup (Module.End k S)ˣ, A ≤ D →
        finrank k S - finrank k (fixedSub A) =
          r * (finrank k I - finrank k ↥(I ⊓ fixedSub A))) ∧
      (X ≠ ⊥ → Group.IsPerfect X → 2 ≤ r) ∧
      (Nat.card k = 2 → Nat.card (commutantD hDI) = 2 → X ≠ ⊥ → Group.IsPerfect X → 3 ≤ r) ∧
      (commutantD hDI = ⊥ →
        Function.Bijective (evalHom hDI) ∧
        (∀ (d : D) (v : I) (f : homD hDI),
          evalHom hDI (resD hDI d v ⊗ₜ f) = (d.1 : Module.End k S) (evalHom hDI (v ⊗ₜ f))) ∧
        (∀ (x : X) (v : I) (f : homD hDI), evalHom hDI (v ⊗ₜ homAct hXD hDI x f) =
          (x.1 : Module.End k S) (evalHom hDI (v ⊗ₜ f))) ∧
        Function.Injective (homAct hXD hDI) ∧ Nontrivial (homD hDI) ∧
        ∀ N : Submodule k (homD hDI), (∀ (x : X), ∀ f ∈ N, homAct hXD hDI x f ∈ N) →
          N = ⊥ ∨ N = ⊤) := by
  obtain ⟨r, Φ, hΦ⟩ := exists_isotypic_equiv hXD hirr hDI hI0 hIirr
  have hr : 1 ≤ r := by
    by_contra h
    obtain rfl : r = 0 := by omega
    have : Subsingleton S := Φ.symm.injective.subsingleton
    exact not_subsingleton S this
  obtain ⟨hF, hFfin⟩ := commutantD_isField hDI hI0 hIirr
  have hXC : X ≤ Subgroup.centralizer (D : Set (Module.End k S)ˣ) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun d hd => (hXD x hx d hd).symm
  obtain ⟨ψ, hψ⟩ := exists_centralizer_equiv hDI Φ hΦ
  set ρX : X →* (Matrix (Fin r) (Fin r) (commutantD hDI))ˣ :=
    ψ.toMonoidHom.comp (Subgroup.inclusion hXC)
  have hρX : Function.Injective ρX := ψ.injective.comp (Subgroup.inclusion_injective hXC)
  have hone : r = 1 → X ≠ ⊥ → ¬ Group.IsPerfect X := by
    rintro rfl hX1 hXp
    have : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX1
    exact not_injective_of_perfect (units_matrix_one_comm hF.mul_comm) ρX hρX
  refine ⟨r, Φ, hr, hΦ, fun d hd h => faithful_on_I hDI Φ hΦ hd h, hF, hFfin, hXC, ⟨ψ, hψ⟩,
    fun A hA => ?_, fun hX1 hXp => ?_, fun _ hF2 hX1 hXp => ?_,
    fun hbot => tensor_case hDI Φ hXD hirr hI0 hΦ hr hbot⟩
  · rw [finrank_fixedSub hDI Φ hΦ hA, ← Φ.finrank_eq, finrank_fin_fun_eq, ← Nat.mul_sub]
  · by_contra h
    exact hone (by omega) hX1 hXp
  · by_contra h
    rcases (show r = 1 ∨ r = 2 by omega) with h1 | rfl
    · exact hone h1 hX1 hXp
    · have : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX1
      have : Group.IsSolvable (Matrix (Fin 2) (Fin 2) (commutantD hDI))ˣ := by
        let := IsField.toField (R := commutantD hDI)
          ⟨hF.exists_pair_ne, hF.mul_comm, hF.mul_inv_cancel⟩
        exact CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable
          _ (Or.inl hF2)
      exact Group.IsPerfect.not_isSolvable X (Group.isSolvable_of_isSolvable_injective hρX)

end CFSG.LocalAnalysis.CommutingFactor

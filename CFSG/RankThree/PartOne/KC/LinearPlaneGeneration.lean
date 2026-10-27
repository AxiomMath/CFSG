module

public import CFSG.RankThree.Classical.SteinbergBJBlockMixingGeneration
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
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

public section

namespace CFSG.RankThree.PartOne.KCLinPlane

open Module CFSG.RankThree.Classical

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]


theorem det_one_add_of_range_le_ker [FiniteDimensional K V] (δ : Module.End K V)
    (W : Submodule K V) (h1 : ∀ v, δ v ∈ W) (h2 : ∀ w ∈ W, δ w = 0) :
    LinearMap.det (1 + δ) = 1 := by
  have hW : W ≤ W.comap (1 + δ) := by
    intro w hw
    simp only [Submodule.mem_comap, LinearMap.add_apply, Module.End.one_apply, h2 w hw, add_zero]
    exact hw
  rw [LinearMap.det_eq_det_mul_det W (1 + δ) hW]
  have e1 : (1 + δ).restrict hW = LinearMap.id := by
    ext ⟨w, hw⟩
    simp [LinearMap.restrict_apply, h2 w hw]
  have e2 : W.mapQ W (1 + δ) hW = LinearMap.id := by
    refine Submodule.linearMap_qext _ ?_
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.add_apply, Module.End.one_apply, LinearMap.id_comp]
    rw [Submodule.Quotient.eq]
    simpa using W.neg_mem (h1 v)
  rw [e1, e2, LinearMap.det_id, LinearMap.det_id, one_mul]

@[expose] def suppGroup (e : Module.End K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | LinearEquiv.det g = 1 ∧ (∀ v, g (e v) = e (g v)) ∧ ∀ v, g (v - e v) = v - e v}
  mul_mem' := by
    rintro g₁ g₂ ⟨hd₁, hc₁, hf₁⟩ ⟨hd₂, hc₂, hf₂⟩
    refine ⟨by rw [map_mul, hd₁, hd₂, one_mul], fun v => ?_, fun v => ?_⟩
    · change g₁ (g₂ (e v)) = e (g₁ (g₂ v))
      rw [hc₂, hc₁]
    · change g₁ (g₂ (v - e v)) = v - e v
      rw [hf₂, hf₁]
  one_mem' := ⟨map_one _, fun v => rfl, fun v => rfl⟩
  inv_mem' := by
    rintro g ⟨hd, hc, hf⟩
    refine ⟨by rw [map_inv, hd, inv_one], fun v => ?_, fun v => ?_⟩
    · change g.symm (e v) = e (g.symm v)
      apply g.injective
      rw [LinearEquiv.apply_symm_apply, hc, LinearEquiv.apply_symm_apply]
    · change g.symm (v - e v) = v - e v
      rw [LinearEquiv.symm_apply_eq, hf]


theorem suppGroup_mono {e ε : Module.End K V} (he : e * e = e) (h1 : e * ε = e)
    (h2 : ε * e = e) : suppGroup e ≤ suppGroup ε := by
  rintro g ⟨hd, hc, hf⟩
  have ee : ∀ v, e (e v) = e v := fun v => by
    simpa using congrArg (fun f : Module.End K V => f v) he
  have e1 : ∀ v, e (ε v) = e v := fun v => by
    simpa using congrArg (fun f : Module.End K V => f v) h1
  have e2 : ∀ v, ε (e v) = e v := fun v => by
    simpa using congrArg (fun f : Module.End K V => f v) h2
  refine ⟨hd, fun v => ?_, fun v => ?_⟩
  · have ht : g (ε v - e v) = ε v - e v := by
      have h0 : e (ε v - e v) = 0 := by rw [map_sub, e1, ee, sub_self]
      have := hf (ε v - e v)
      rwa [h0, sub_zero] at this
    have hsplit : ε v = e v + (ε v - e v) := by abel
    have h3 : g v = e (g v) + (v - e v) :=
      calc g v = g (e v) + g (v - e v) := by rw [← map_add]; congr 1; abel
        _ = e (g v) + (v - e v) := by rw [hc v, hf v]
    calc g (ε v) = g (e v + (ε v - e v)) := by rw [← hsplit]
      _ = e (g v) + (ε v - e v) := by rw [map_add, hc, ht]
      _ = ε (g v) := by
        conv_rhs => rw [h3]
        rw [map_add, e2, map_sub, e2]
  · have h0 : e (v - ε v) = 0 := by rw [map_sub, e1, sub_self]
    have := hf (v - ε v)
    rwa [h0, sub_zero] at this

section Idem

variable {e f : Module.End K V}

theorem idem_apply (he : e * e = e) (v : V) : e (e v) = e v := by
  simpa using congrArg (fun g : Module.End K V => g v) he

theorem orth_apply (hef : e * f = 0) (v : V) : e (f v) = 0 := by
  simpa using congrArg (fun g : Module.End K V => g v) hef

theorem r_idem (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (hfe : f * e = 0) :
    (1 - e - f) * (1 - e - f) = 1 - e - f := by
  simp only [sub_mul, mul_sub, one_mul, mul_one, he, hf, hef, hfe]
  abel

theorem mem_range_e (he : e * e = e) (hfe : f * e = 0) {x : V}
    (hx : x ∈ LinearMap.range e) : e x = x ∧ f x = 0 ∧ (1 - e - f) x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨idem_apply he y, orth_apply hfe y, ?_⟩
  simp [idem_apply he y, orth_apply hfe y]

theorem mem_range_f (hf : f * f = f) (hef : e * f = 0) {x : V}
    (hx : x ∈ LinearMap.range f) : e x = 0 ∧ f x = x ∧ (1 - e - f) x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨orth_apply hef y, idem_apply hf y, ?_⟩
  simp [idem_apply hf y, orth_apply hef y]

theorem mem_range_r (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (hfe : f * e = 0) {x : V}
    (hx : x ∈ LinearMap.range (1 - e - f)) : e x = 0 ∧ f x = 0 ∧ (1 - e - f) x = x := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨?_, ?_, idem_apply (r_idem he hf hef hfe) y⟩
  · simp [idem_apply he y, orth_apply hef y]
  · simp [idem_apply hf y, orth_apply hfe y]

variable (e f)

@[expose] def dec3 (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (hfe : f * e = 0) :
    V ≃ₗ[K] (LinearMap.range e × LinearMap.range f) × LinearMap.range (1 - e - f) where
  toFun v := ((⟨e v, LinearMap.mem_range_self _ v⟩, ⟨f v, LinearMap.mem_range_self _ v⟩),
    ⟨(1 - e - f) v, LinearMap.mem_range_self _ v⟩)
  map_add' u v := by
    ext
    · simp
    · simp
    · simp; abel
  map_smul' c v := by ext <;> simp
  invFun p := (p.1.1 : V) + (p.1.2 : V) + (p.2 : V)
  left_inv v := by simp
  right_inv p := by
    obtain ⟨⟨u, w⟩, c⟩ := p
    obtain ⟨hu1, hu2, hu3⟩ := mem_range_e he hfe u.2
    obtain ⟨hw1, hw2, hw3⟩ := mem_range_f hf hef w.2
    obtain ⟨hc1, hc2, hc3⟩ := mem_range_r he hf hef hfe c.2
    ext
    · simp [hu1, hw1, hc1]
    · simp [hu2, hw2, hc2]
    · show ((1 - e - f) ((u : V) + (w : V) + (c : V)) : V) = (c : V)
      rw [map_add, map_add, hu3, hw3, hc3]
      simp

@[expose] def liftPair (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (hfe : f * e = 0) :
    ((LinearMap.range e × LinearMap.range f) ≃ₗ[K] (LinearMap.range e × LinearMap.range f)) →*
      (V ≃ₗ[K] V) where
  toFun h := (dec3 e f he hf hef hfe).trans
    ((h.prodCongr (LinearEquiv.refl K (LinearMap.range (1 - e - f)))).trans
      (dec3 e f he hf hef hfe).symm)
  map_one' := by
    ext v
    simp
  map_mul' h₁ h₂ := by
    ext v
    simp

theorem liftPair_apply (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (hfe : f * e = 0)
    (h : (LinearMap.range e × LinearMap.range f) ≃ₗ[K] (LinearMap.range e × LinearMap.range f))
    (v : V) :
    liftPair e f he hf hef hfe h v =
      ((h (⟨e v, LinearMap.mem_range_self _ v⟩, ⟨f v, LinearMap.mem_range_self _ v⟩)).1 : V) +
      ((h (⟨e v, LinearMap.mem_range_self _ v⟩, ⟨f v, LinearMap.mem_range_self _ v⟩)).2 : V) +
      (1 - e - f) v := rfl

theorem det_liftPair [FiniteDimensional K V] (he : e * e = e) (hf : f * f = f) (hef : e * f = 0)
    (hfe : f * e = 0)
    (h : (LinearMap.range e × LinearMap.range f) ≃ₗ[K] (LinearMap.range e × LinearMap.range f)) :
    LinearEquiv.det (liftPair e f he hf hef hfe h) = LinearEquiv.det h := by
  have h1 := LinearEquiv.det_conj (h.prodCongr (LinearEquiv.refl K (LinearMap.range (1 - e - f))))
    (dec3 e f he hf hef hfe).symm
  have h2 : LinearEquiv.det (h.prodCongr (LinearEquiv.refl K (LinearMap.range (1 - e - f)))) =
      LinearEquiv.det h := by
    apply Units.ext
    rw [LinearEquiv.coe_det, LinearEquiv.coe_det]
    have : ((h.prodCongr (LinearEquiv.refl K (LinearMap.range (1 - e - f)))) :
        ((LinearMap.range e × LinearMap.range f) × LinearMap.range (1 - e - f)) →ₗ[K]
          ((LinearMap.range e × LinearMap.range f) × LinearMap.range (1 - e - f))) =
        (h : (LinearMap.range e × LinearMap.range f) →ₗ[K]
          (LinearMap.range e × LinearMap.range f)).prodMap (LinearMap.id) := by
      ext p <;> rfl
    rw [this, LinearMap.det_prodMap, LinearMap.det_id, mul_one]
  rw [← h2, ← h1]
  rfl

theorem liftPair_prodCongr_left_apply (he : e * e = e) (hf : f * f = f) (hef : e * f = 0)
    (hfe : f * e = 0) (g : LinearMap.range e ≃ₗ[K] LinearMap.range e) (v : V) :
    liftPair e f he hf hef hfe (g.prodCongr (LinearEquiv.refl K (LinearMap.range f))) v =
      v - e v + (g ⟨e v, LinearMap.mem_range_self _ v⟩ : V) := by
  rw [liftPair_apply]
  simp only [LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  simp only [LinearMap.sub_apply, Module.End.one_apply]
  abel

theorem liftPair_prodCongr_right_apply (he : e * e = e) (hf : f * f = f) (hef : e * f = 0)
    (hfe : f * e = 0) (g : LinearMap.range f ≃ₗ[K] LinearMap.range f) (v : V) :
    liftPair e f he hf hef hfe ((LinearEquiv.refl K (LinearMap.range e)).prodCongr g) v =
      v - f v + (g ⟨f v, LinearMap.mem_range_self _ v⟩ : V) := by
  rw [liftPair_apply]
  simp only [LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  simp only [LinearMap.sub_apply, Module.End.one_apply]
  abel

end Idem

section Pair

variable {e f : Module.End K V}

theorem det_eq_one_iff (g : V ≃ₗ[K] V) :
    LinearEquiv.det g = 1 ↔ LinearMap.det (g : V →ₗ[K] V) = 1 := by
  rw [← LinearEquiv.coe_det, Units.val_eq_one]

variable (f) in
@[expose] def toU (x : Module.End K V) (hx : e * x = x) :
    LinearMap.range f →ₗ[K] LinearMap.range e :=
  (x.comp (LinearMap.range f).subtype).codRestrict (LinearMap.range e) (fun w =>
    LinearMap.mem_range.mpr ⟨x w, by simpa using LinearMap.congr_fun hx w⟩)

variable (e) in
@[expose] def toW (y : Module.End K V) (hy : f * y = y) :
    LinearMap.range e →ₗ[K] LinearMap.range f :=
  (y.comp (LinearMap.range e).subtype).codRestrict (LinearMap.range f) (fun w =>
    LinearMap.mem_range.mpr ⟨y w, by simpa using LinearMap.congr_fun hy w⟩)

theorem toU_apply (x : Module.End K V) (hx : e * x = x) (w : LinearMap.range f) :
    ((toU f x hx w : LinearMap.range e) : V) = x w := rfl

theorem toW_apply (y : Module.End K V) (hy : f * y = y) (w : LinearMap.range e) :
    ((toW e y hy w : LinearMap.range f) : V) = y w := rfl

theorem toU_ne_zero {x : Module.End K V} (hx : e * x = x) (hxf : x * f = x) (hx0 : x ≠ 0) :
    toU f x hx ≠ 0 := by
  intro h
  apply hx0
  ext v
  have h1 := congrArg (fun T : LinearMap.range f →ₗ[K] LinearMap.range e =>
    ((T ⟨f v, LinearMap.mem_range_self _ v⟩ : LinearMap.range e) : V)) h
  simp only [toU_apply, LinearMap.zero_apply, Submodule.coe_zero] at h1
  have h2 : x (f v) = x v := by simpa using LinearMap.congr_fun hxf v
  rw [h2] at h1
  simpa using h1

theorem toW_ne_zero {y : Module.End K V} (hy : f * y = y) (hye : y * e = y) (hy0 : y ≠ 0) :
    toW e y hy ≠ 0 := by
  intro h
  apply hy0
  ext v
  have h1 := congrArg (fun T : LinearMap.range e →ₗ[K] LinearMap.range f =>
    ((T ⟨e v, LinearMap.mem_range_self _ v⟩ : LinearMap.range f) : V)) h
  simp only [toW_apply, LinearMap.zero_apply, Submodule.coe_zero] at h1
  have h2 : y (e v) = y v := by simpa using LinearMap.congr_fun hye v
  rw [h2] at h1
  simpa using h1

theorem liftPair_blockUpper_apply (he : e * e = e) (hf : f * f = f) (hef : e * f = 0)
    (hfe : f * e = 0) (D : LinearMap.range f →ₗ[K] LinearMap.range e) (v : V) :
    liftPair e f he hf hef hfe (blockUpper D) v =
      v + (D ⟨f v, LinearMap.mem_range_self _ v⟩ : V) := by
  rw [liftPair_apply, blockUpper_apply]
  simp only [LinearMap.sub_apply, Module.End.one_apply, Submodule.coe_add]
  abel

theorem liftPair_blockLower_apply (he : e * e = e) (hf : f * f = f) (hef : e * f = 0)
    (hfe : f * e = 0) (C : LinearMap.range e →ₗ[K] LinearMap.range f) (v : V) :
    liftPair e f he hf hef hfe (blockLower C) v =
      v + (C ⟨e v, LinearMap.mem_range_self _ v⟩ : V) := by
  rw [liftPair_apply, blockLower_apply]
  simp only [LinearMap.sub_apply, Module.End.one_apply, Submodule.coe_add]
  abel

end Pair

section PairMain

variable {e f : Module.End K V} [FiniteDimensional K V]

theorem det_prodCongr_left (g : LinearMap.range e ≃ₗ[K] LinearMap.range e) :
    LinearEquiv.det (g.prodCongr (LinearEquiv.refl K (LinearMap.range f))) =
      LinearEquiv.det g := by
  apply Units.ext
  rw [LinearEquiv.coe_det, LinearEquiv.coe_det]
  have : ((g.prodCongr (LinearEquiv.refl K (LinearMap.range f))) :
      (LinearMap.range e × LinearMap.range f) →ₗ[K] (LinearMap.range e × LinearMap.range f)) =
      (g : LinearMap.range e →ₗ[K] LinearMap.range e).prodMap (LinearMap.id) := by
    ext p <;> rfl
  rw [this, LinearMap.det_prodMap, LinearMap.det_id, mul_one]

theorem det_prodCongr_right (g : LinearMap.range f ≃ₗ[K] LinearMap.range f) :
    LinearEquiv.det ((LinearEquiv.refl K (LinearMap.range e)).prodCongr g) =
      LinearEquiv.det g := by
  apply Units.ext
  rw [LinearEquiv.coe_det, LinearEquiv.coe_det]
  have : (((LinearEquiv.refl K (LinearMap.range e)).prodCongr g) :
      (LinearMap.range e × LinearMap.range f) →ₗ[K] (LinearMap.range e × LinearMap.range f)) =
      (LinearMap.id : LinearMap.range e →ₗ[K] LinearMap.range e).prodMap
        (g : LinearMap.range f →ₗ[K] LinearMap.range f) := by
    ext p <;> rfl
  rw [this, LinearMap.det_prodMap, LinearMap.det_id, one_mul]

theorem liftPair_prodCongr_left_mem (he : e * e = e) (hf : f * f = f) (hef : e * f = 0)
    (hfe : f * e = 0) (g : LinearMap.range e ≃ₗ[K] LinearMap.range e)
    (hg : LinearEquiv.det g = 1) :
    liftPair e f he hf hef hfe (g.prodCongr (LinearEquiv.refl K (LinearMap.range f))) ∈
      suppGroup e := by
  refine ⟨?_, fun v => ?_, fun v => ?_⟩
  · rw [det_liftPair, det_prodCongr_left, hg]
  · have hu : e (g ⟨e v, LinearMap.mem_range_self _ v⟩ : V) =
        (g ⟨e v, LinearMap.mem_range_self _ v⟩ : V) :=
      (mem_range_e he hfe (g ⟨e v, LinearMap.mem_range_self _ v⟩).2).1
    have hee : (⟨e (e v), LinearMap.mem_range_self _ (e v)⟩ : LinearMap.range e) =
        ⟨e v, LinearMap.mem_range_self _ v⟩ := Subtype.ext (idem_apply he v)
    rw [liftPair_prodCongr_left_apply, liftPair_prodCongr_left_apply, hee, map_add, map_sub,
      idem_apply he v, hu]
  · have h0 : e (v - e v) = 0 := by rw [map_sub, idem_apply he, sub_self]
    have h1 : (⟨e (v - e v), LinearMap.mem_range_self _ (v - e v)⟩ : LinearMap.range e) = 0 :=
      Subtype.ext h0
    rw [liftPair_prodCongr_left_apply, h1, map_zero]
    simp [h0]

theorem liftPair_prodCongr_right_mem (he : e * e = e) (hf : f * f = f) (hef : e * f = 0)
    (hfe : f * e = 0) (g : LinearMap.range f ≃ₗ[K] LinearMap.range f)
    (hg : LinearEquiv.det g = 1) :
    liftPair e f he hf hef hfe ((LinearEquiv.refl K (LinearMap.range e)).prodCongr g) ∈
      suppGroup f := by
  refine ⟨?_, fun v => ?_, fun v => ?_⟩
  · rw [det_liftPair, det_prodCongr_right, hg]
  · have hu : f (g ⟨f v, LinearMap.mem_range_self _ v⟩ : V) =
        (g ⟨f v, LinearMap.mem_range_self _ v⟩ : V) :=
      (mem_range_f hf hef (g ⟨f v, LinearMap.mem_range_self _ v⟩).2).2.1
    have hee : (⟨f (f v), LinearMap.mem_range_self _ (f v)⟩ : LinearMap.range f) =
        ⟨f v, LinearMap.mem_range_self _ v⟩ := Subtype.ext (idem_apply hf v)
    rw [liftPair_prodCongr_right_apply, liftPair_prodCongr_right_apply, hee, map_add, map_sub,
      idem_apply hf v, hu]
  · have h0 : f (v - f v) = 0 := by rw [map_sub, idem_apply hf, sub_self]
    have h1 : (⟨f (v - f v), LinearMap.mem_range_self _ (v - f v)⟩ : LinearMap.range f) = 0 :=
      Subtype.ext h0
    rw [liftPair_prodCongr_right_apply, h1, map_zero]
    simp [h0]

end PairMain

section PairLemma

variable {e f : Module.End K V} [FiniteDimensional K V]

theorem exists_mem_one_add_of_mixing (he : e * e = e) (hf : f * f = f) (hef : e * f = 0)
    (hfe : f * e = 0) (hU : 2 ≤ finrank K (LinearMap.range e))
    (hW : 2 ≤ finrank K (LinearMap.range f))
    (G : Subgroup (V ≃ₗ[K] V)) (hG : ∀ g ∈ G, LinearEquiv.det g = 1)
    (hSe : suppGroup e ≤ G) (hSf : suppGroup f ≤ G)
    {β : Module.End K V} (hβe : e * β = β) (hβf : β * f = β) (hβ0 : β ≠ 0)
    (hβG : ∃ u ∈ G, ∀ v, u v = v + β v)
    {γ : Module.End K V} (hγf : f * γ = γ) (hγe : γ * e = γ) (hγ0 : γ ≠ 0)
    (hγG : ∃ u ∈ G, ∀ v, u v = v + γ v)
    {δ : Module.End K V} (hδe : e * δ = δ) (hδf : δ * f = δ) :
    ∃ u ∈ G, ∀ v, u v = v + δ v := by
  classical
  set H : Subgroup ((LinearMap.range e × LinearMap.range f) ≃ₗ[K]
      (LinearMap.range e × LinearMap.range f)) := G.comap (liftPair e f he hf hef hfe) with hH
  have hmemH : ∀ h, h ∈ H ↔ liftPair e f he hf hef hfe h ∈ G := fun h => Iff.rfl
  have hSL : ∀ h ∈ H, LinearMap.det (h : (LinearMap.range e × LinearMap.range f) →ₗ[K]
      (LinearMap.range e × LinearMap.range f)) = 1 := by
    intro h hh
    have h1 := hG _ ((hmemH h).mp hh)
    rw [det_liftPair] at h1
    exact (det_eq_one_iff h).mp h1
  have hSLU : ∀ g : LinearMap.range e ≃ₗ[K] LinearMap.range e,
      LinearMap.det (g : LinearMap.range e →ₗ[K] LinearMap.range e) = 1 →
      g.prodCongr (LinearEquiv.refl K (LinearMap.range f)) ∈ H := fun g hg =>
    (hmemH _).mpr (hSe (liftPair_prodCongr_left_mem he hf hef hfe g ((det_eq_one_iff g).mpr hg)))
  have hSLV : ∀ g : LinearMap.range f ≃ₗ[K] LinearMap.range f,
      LinearMap.det (g : LinearMap.range f →ₗ[K] LinearMap.range f) = 1 →
      (LinearEquiv.refl K (LinearMap.range e)).prodCongr g ∈ H := fun g hg =>
    (hmemH _).mpr (hSf (liftPair_prodCongr_right_mem he hf hef hfe g ((det_eq_one_iff g).mpr hg)))
  obtain ⟨uβ, huβG, huβ⟩ := hβG
  obtain ⟨uγ, huγG, huγ⟩ := hγG
  have hB : blockUpper (toU f β hβe) ∈ H := by
    rw [hmemH]
    have : liftPair e f he hf hef hfe (blockUpper (toU f β hβe)) = uβ := by
      ext v
      rw [liftPair_blockUpper_apply, huβ, toU_apply]
      congr 1
      simpa using LinearMap.congr_fun hβf v
    rw [this]
    exact huβG
  have hC : blockLower (toW e γ hγf) ∈ H := by
    rw [hmemH]
    have : liftPair e f he hf hef hfe (blockLower (toW e γ hγf)) = uγ := by
      ext v
      rw [liftPair_blockLower_apply, huγ, toW_apply]
      congr 1
      simpa using LinearMap.congr_fun hγe v
    rw [this]
    exact huγG
  have hBJ := special_linear_two_block_mixing_unipotents_generate hU hW H hSL hSLU hSLV
    (toU_ne_zero hβe hβf hβ0) hB (toW_ne_zero hγf hγe hγ0) hC
  have hδrange : ∀ v, δ v ∈ LinearMap.range e := fun v =>
    LinearMap.mem_range.mpr ⟨δ v, by simpa using LinearMap.congr_fun hδe v⟩
  have hδker : ∀ w ∈ LinearMap.range e, δ w = 0 := by
    rintro _ ⟨y, rfl⟩
    have h1 : δ (e y) = δ (f (e y)) := by simpa using (LinearMap.congr_fun hδf (e y)).symm
    rw [h1]
    have : f (e y) = 0 := orth_apply hfe y
    rw [this, map_zero]
  set u := liftPair e f he hf hef hfe (blockUpper (toU f δ hδe)) with hu
  have huv : ∀ v, u v = v + δ v := by
    intro v
    rw [hu, liftPair_blockUpper_apply, toU_apply]
    congr 1
    simpa using LinearMap.congr_fun hδf v
  have hulin : (u : V →ₗ[K] V) = 1 + δ := by
    ext v
    simp [huv]
  have hdet : LinearMap.det (blockUpper (toU f δ hδe) :
      (LinearMap.range e × LinearMap.range f) →ₗ[K] (LinearMap.range e × LinearMap.range f)) =
      1 := by
    rw [← det_eq_one_iff, ← det_liftPair e f he hf hef hfe, det_eq_one_iff, hulin]
    exact det_one_add_of_range_le_ker δ (LinearMap.range e) hδrange hδker
  exact ⟨u, (hmemH _).mp ((hBJ _).mpr hdet), huv⟩

end PairLemma

section Blocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → Module.End K V)

omit [Fintype ι] [DecidableEq ι] in
theorem e_apply_of_mem_range (hidem : ∀ i, e i * e i = e i) {i : ι} {x : V}
    (hx : x ∈ LinearMap.range (e i)) : e i x = x := by
  obtain ⟨y, rfl⟩ := hx
  simpa using congrArg (fun f : Module.End K V => f y) (hidem i)

omit [Fintype ι] [DecidableEq ι] in
theorem e_apply_of_mem_range_ne (horth : ∀ i j, i ≠ j → e i * e j = 0) {i j : ι} (hij : j ≠ i)
    {x : V} (hx : x ∈ LinearMap.range (e i)) : e j x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  simpa using congrArg (fun f : Module.End K V => f y) (horth j i hij)

@[expose] def blockDecomp (hidem : ∀ i, e i * e i = e i) (horth : ∀ i j, i ≠ j → e i * e j = 0)
    (hsum : ∑ i, e i = 1) : V ≃ₗ[K] (∀ i, LinearMap.range (e i)) where
  toFun v i := ⟨e i v, LinearMap.mem_range_self _ v⟩
  map_add' u v := by
    funext i
    exact Subtype.ext (map_add (e i) u v)
  map_smul' c v := by
    funext i
    exact Subtype.ext (map_smul (e i) c v)
  invFun w := ∑ i, (w i : V)
  left_inv v := by
    have := LinearMap.congr_fun hsum v
    simpa [LinearMap.sum_apply] using this
  right_inv w := by
    funext j
    apply Subtype.ext
    change e j (∑ i, (w i : V)) = (w j : V)
    rw [map_sum, Finset.sum_eq_single j]
    · exact e_apply_of_mem_range e hidem (w j).2
    · intro i _ hij
      exact e_apply_of_mem_range_ne e horth (Ne.symm hij) (w i).2
    · intro h
      exact absurd (Finset.mem_univ j) h

omit [DecidableEq ι] in
theorem blockDecomp_symm_apply (hidem : ∀ i, e i * e i = e i)
    (horth : ∀ i j, i ≠ j → e i * e j = 0) (hsum : ∑ i, e i = 1)
    (w : ∀ i, LinearMap.range (e i)) :
    (blockDecomp e hidem horth hsum).symm w = ∑ i, (w i : V) := rfl

variable [FiniteDimensional K V]

@[expose] noncomputable def blockBasis (hidem : ∀ i, e i * e i = e i)
    (horth : ∀ i j, i ≠ j → e i * e j = 0) (hsum : ∑ i, e i = 1) :
    Basis (Σ i, Fin (finrank K (LinearMap.range (e i)))) K V :=
  (Pi.basis (fun i => Module.finBasis K (LinearMap.range (e i)))).map
    (blockDecomp e hidem horth hsum).symm

theorem blockBasis_apply (hidem : ∀ i, e i * e i = e i) (horth : ∀ i j, i ≠ j → e i * e j = 0)
    (hsum : ∑ i, e i = 1) (i : ι) (k : Fin (finrank K (LinearMap.range (e i)))) :
    blockBasis e hidem horth hsum ⟨i, k⟩ =
      ((Module.finBasis K (LinearMap.range (e i)) k : LinearMap.range (e i)) : V) := by
  rw [blockBasis, Basis.map_apply, Pi.basis_apply, blockDecomp_symm_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · intro h
    exact absurd (Finset.mem_univ i) h

omit [DecidableEq ι] in
theorem blockBasis_coord (hidem : ∀ i, e i * e i = e i)
    (horth : ∀ i j, i ≠ j → e i * e j = 0) (hsum : ∑ i, e i = 1) (i : ι)
    (k : Fin (finrank K (LinearMap.range (e i)))) (v : V) :
    (blockBasis e hidem horth hsum).coord ⟨i, k⟩ v =
      (Module.finBasis K (LinearMap.range (e i))).coord k
        ⟨e i v, LinearMap.mem_range_self _ v⟩ := by
  rw [Basis.coord_apply, blockBasis, Basis.map_repr]
  simp [Pi.basis_repr, Basis.coord_apply]
  rfl

theorem e_blockBasis (hidem : ∀ i, e i * e i = e i) (horth : ∀ i j, i ≠ j → e i * e j = 0)
    (hsum : ∑ i, e i = 1) (m i : ι) (k : Fin (finrank K (LinearMap.range (e i)))) :
    e m (blockBasis e hidem horth hsum ⟨i, k⟩) =
      if m = i then blockBasis e hidem horth hsum ⟨i, k⟩ else 0 := by
  rw [blockBasis_apply]
  have hmem := (Module.finBasis K (LinearMap.range (e i)) k).2
  by_cases hmi : m = i
  · subst hmi
    simpa using e_apply_of_mem_range e hidem hmem
  · simpa [hmi] using e_apply_of_mem_range_ne e horth hmi hmem

theorem coord_blockBasis_e (hidem : ∀ i, e i * e i = e i) (horth : ∀ i j, i ≠ j → e i * e j = 0)
    (hsum : ∑ i, e i = 1) (m i : ι) (k : Fin (finrank K (LinearMap.range (e i)))) (v : V) :
    (blockBasis e hidem horth hsum).coord ⟨i, k⟩ (e m v) =
      if m = i then (blockBasis e hidem horth hsum).coord ⟨i, k⟩ v else 0 := by
  rw [blockBasis_coord, blockBasis_coord]
  by_cases hmi : m = i
  · subst hmi
    have : (⟨e m (e m v), LinearMap.mem_range_self _ (e m v)⟩ : LinearMap.range (e m)) =
        ⟨e m v, LinearMap.mem_range_self _ v⟩ := Subtype.ext (by
      simpa using congrArg (fun f : Module.End K V => f v) (hidem m))
    simp [this]
  · have : (⟨e i (e m v), LinearMap.mem_range_self _ (e m v)⟩ : LinearMap.range (e i)) = 0 :=
      Subtype.ext (by
        simpa using congrArg (fun f : Module.End K V => f v) (horth i m (Ne.symm hmi)))
    simp [hmi, this]

end Blocks

section Main

theorem det_slAction {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (A : Matrix.SpecialLinearGroup ι K) : LinearEquiv.det (slAction b A) = 1 := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  have : ((slAction b A : V ≃ₗ[K] V) : V →ₗ[K] V) = Matrix.toLin b b (A : Matrix ι ι K) := rfl
  rw [this, LinearMap.det_toLin, A.2]
  rfl

theorem transvection_mem_suppGroup {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : Module.End K V)
    (b : Basis ι K V) {i j : ι} (hij : i ≠ j) (c : K) (hi : ε (b i) = b i)
    (hj : ∀ v, b.coord j (ε v) = b.coord j v) :
    slAction b (Matrix.SpecialLinearGroup.transvection hij c) ∈ suppGroup ε := by
  refine ⟨det_slAction b _, fun v => ?_, fun v => ?_⟩
  · rw [slAction_transvection_apply, slAction_transvection_apply, map_add, hj, map_smul, hi]
  · rw [slAction_transvection_apply, map_sub, hj, sub_self, mul_zero, zero_smul, add_zero]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → Module.End K V) [FiniteDimensional K V]

theorem generation_of_blocks (hidem : ∀ i, e i * e i = e i)
    (horth : ∀ i j, i ≠ j → e i * e j = 0) (hsum : ∑ i, e i = 1) (z : ι) (A : Finset ι)
    (hzA : z ∉ A) (hA : A.Nonempty) (hinact : ∀ i, i ≠ z → i ∉ A → e i = 0)
    (hdim : ∀ i ∈ A, 2 ≤ finrank K (LinearMap.range (e i)))
    (G : Subgroup (V ≃ₗ[K] V)) (hG : ∀ g ∈ G, LinearEquiv.det g = 1)
    (hsupp : ∀ i ∈ A, suppGroup (e z + e i) ≤ G)
    (hmix : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∃ β : Module.End K V, e i * β = β ∧ β * e j = β ∧
      β ≠ 0 ∧ ∃ u ∈ G, ∀ v, u v = v + β v) :
    ∀ g : V ≃ₗ[K] V, LinearEquiv.det g = 1 → g ∈ G := by
  classical
  set b := blockBasis e hidem horth hsum with hb
  intro g hg
  refine mem_of_det_eq_one_of_transvection_mem b G (fun i j hij c => ?_) hg
  obtain ⟨a, k⟩ := i
  obtain ⟨a', k'⟩ := j
  have hact : ∀ (m : ι) (kk : Fin (finrank K (LinearMap.range (e m)))), m = z ∨ m ∈ A := by
    intro m kk
    by_contra hcon
    push Not at hcon
    have h0 := hinact m hcon.1 hcon.2
    have : finrank K (LinearMap.range (e m)) = 0 := by rw [h0]; simp
    exact absurd kk.2 (by omega)
  have hTv : ∀ v, slAction b (Matrix.SpecialLinearGroup.transvection hij c) v =
      v + (c * b.coord ⟨a', k'⟩ v) • b ⟨a, k⟩ := fun v => slAction_transvection_apply b hij c v
  by_cases hcross : a ∈ A ∧ a' ∈ A ∧ a ≠ a'
  · obtain ⟨haA, ha'A, haa'⟩ := hcross
    obtain ⟨β, hβe, hβf, hβ0, hβG⟩ := hmix a haA a' ha'A haa'
    obtain ⟨γ, hγf, hγe, hγ0, hγG⟩ := hmix a' ha'A a haA (Ne.symm haa')
    have haz : a ≠ z := fun h => hzA (h ▸ haA)
    have ha'z : a' ≠ z := fun h => hzA (h ▸ ha'A)
    let δ : Module.End K V := (c • b.coord ⟨a', k'⟩).smulRight (b ⟨a, k⟩)
    have hδv : ∀ v, δ v = (c * b.coord ⟨a', k'⟩ v) • b ⟨a, k⟩ := fun v => by
      simp [δ]
    have hδe : e a * δ = δ := by
      ext v
      rw [Module.End.mul_apply, hδv, map_smul, e_blockBasis e hidem horth hsum a a k]
      simp
      rfl
    have hδf : δ * e a' = δ := by
      ext v
      rw [Module.End.mul_apply, hδv, hδv, coord_blockBasis_e e hidem horth hsum a' a' k' v]
      simp
      rfl
    have hSe : suppGroup (e a) ≤ G := by
      refine le_trans (suppGroup_mono (hidem a) ?_ ?_) (hsupp a haA)
      · rw [mul_add, horth a z haz, hidem a, zero_add]
      · rw [add_mul, horth z a (Ne.symm haz), hidem a, zero_add]
    have hSf : suppGroup (e a') ≤ G := by
      refine le_trans (suppGroup_mono (hidem a') ?_ ?_) (hsupp a' ha'A)
      · rw [mul_add, horth a' z ha'z, hidem a', zero_add]
      · rw [add_mul, horth z a' (Ne.symm ha'z), hidem a', zero_add]
    obtain ⟨u, huG, huv⟩ := exists_mem_one_add_of_mixing (e := e a) (f := e a') (hidem a)
      (hidem a') (horth a a' haa') (horth a' a (Ne.symm haa')) (hdim a haA) (hdim a' ha'A) G hG
      hSe hSf hβe hβf hβ0 hβG hγf hγe hγ0 hγG hδe hδf
    have : slAction b (Matrix.SpecialLinearGroup.transvection hij c) = u := by
      ext v
      rw [hTv, huv, hδv]
    rw [this]
    exact huG
  · obtain ⟨i₀, hi₀A, hai₀, ha'i₀⟩ : ∃ i₀ ∈ A, (a = z ∨ a = i₀) ∧ (a' = z ∨ a' = i₀) := by
      by_cases haA : a ∈ A
      · refine ⟨a, haA, Or.inr rfl, ?_⟩
        by_cases ha'A : a' ∈ A
        · right
          by_contra hne
          exact hcross ⟨haA, ha'A, fun h => hne h.symm⟩
        · rcases hact a' k' with h | h
          · exact Or.inl h
          · exact absurd h ha'A
      · rcases hact a k with h | h
        · by_cases ha'A : a' ∈ A
          · exact ⟨a', ha'A, Or.inl h, Or.inr rfl⟩
          · rcases hact a' k' with h' | h'
            · exact ⟨hA.choose, hA.choose_spec, Or.inl h, Or.inl h'⟩
            · exact absurd h' ha'A
        · exact absurd h haA
    have hi₀z : i₀ ≠ z := fun h => hzA (h ▸ hi₀A)
    have hmem : slAction b (Matrix.SpecialLinearGroup.transvection hij c) ∈
        suppGroup (e z + e i₀) := by
      refine transvection_mem_suppGroup _ b hij c ?_ ?_
      · rw [LinearMap.add_apply, e_blockBasis e hidem horth hsum z a k,
          e_blockBasis e hidem horth hsum i₀ a k]
        rcases hai₀ with h | h
        · subst h
          simp [hi₀z]
          rfl
        · subst h
          simp [Ne.symm hi₀z]
          rfl
      · intro v
        rw [LinearMap.add_apply, map_add, coord_blockBasis_e e hidem horth hsum z a' k' v,
          coord_blockBasis_e e hidem horth hsum i₀ a' k' v]
        rcases ha'i₀ with h | h
        · subst h
          simp [hi₀z]
          rfl
        · subst h
          simp [Ne.symm hi₀z]
          rfl
    exact hsupp i₀ hi₀A hmem

end Main


end CFSG.RankThree.PartOne.KCLinPlane

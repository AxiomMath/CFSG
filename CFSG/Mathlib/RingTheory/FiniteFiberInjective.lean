module

public import CFSG.Mathlib.RingTheory.KrullDimensionComparison

public noncomputable section

namespace CFSG

universe u v

variable {k : Type u} [Field k]

theorem algHom_injective_of_finite_fiber [IsAlgClosed k] {A : Type v} [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (f : A →ₐ[k] A) (s : A →ₐ[k] k)
    (hfin : {s' : A →ₐ[k] k | s'.comp f = s.comp f}.Finite) :
    Function.Injective f := by
  classical
  let I : Ideal A := RingHom.ker f.toRingHom
  have hI : I = ⊥ := by
    by_contra hIbot
    let q : A →ₐ[k] A ⧸ I := Ideal.Quotient.mkₐ k I
    have hker : ∀ a ∈ I, f a = 0 := by
      intro a ha
      exact ha
    let fbar : A ⧸ I →ₐ[k] A := Ideal.Quotient.liftₐ I f hker
    have hfbar : fbar.comp q = f := Ideal.Quotient.liftₐ_comp I f hker
    have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective k I
    have hset : {s' : A →ₐ[k] k | s'.comp fbar = s.comp fbar} =
        {s' : A →ₐ[k] k | s'.comp f = s.comp f} := by
      ext s'
      constructor
      · intro h
        change s'.comp fbar = s.comp fbar at h
        change s'.comp f = s.comp f
        rw [← hfbar, ← AlgHom.comp_assoc, h, AlgHom.comp_assoc]
      · intro h
        apply AlgHom.ext
        intro z
        obtain ⟨a, rfl⟩ := hq z
        have h' := AlgHom.congr_fun h a
        rw [← hfbar] at h'
        simpa only [AlgHom.comp_apply] using h'
    have hfinbar : {s' : A →ₐ[k] k | s'.comp fbar = s.comp fbar}.Finite := by
      rw [hset]
      exact hfin
    let : Algebra.FiniteType k (A ⧸ I) := Algebra.FiniteType.quotient k I
    have hle := ringKrullDim_le_of_finite_fiber (k := k) (R := A ⧸ I) (S := A) fbar s hfinbar
    have hlt := ringKrullDim_quotient_lt_of_ne_bot (k := k) (A := A) (I := I) hIbot
    exact not_lt_of_ge hle hlt
  intro x y hxy
  have hmem : x - y ∈ I := by
    change f.toRingHom (x - y) = 0
    rw [map_sub]
    change f x - f y = 0
    rw [hxy, sub_self]
  rw [hI] at hmem
  exact sub_eq_zero.mp (by simpa using hmem)


end CFSG

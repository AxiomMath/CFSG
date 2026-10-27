module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Module.ZMod

public noncomputable section

open scoped BigOperators

namespace CFSG.ShultStronglyClosedTI

theorem binary_functionals_separate {A : Type*} [AddCommGroup A]
    [Module (ZMod 2) A] (a : A)
    (h : ∀ f : A →+ ZMod 2, f a = 0) : a = 0 := by
  by_contra ha
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) ha
  have hz := h f.toAddMonoidHom
  exact one_ne_zero (hf.symm.trans hz)

theorem binary_additive_retraction {A C : Type*} [AddCommGroup A] [AddCommGroup C]
    [Module (ZMod 2) A] [Module (ZMod 2) C]
    (i : C →+ A) (hi : Function.Injective i) :
    ∃ r : A →+ C, ∀ c, r (i c) = c := by
  let il := i.toZModLinearMap 2
  obtain ⟨r, hr⟩ := il.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (by simpa [il] using hi))
  exact ⟨r.toAddMonoidHom, fun c => congrArg (fun f : C →ₗ[ZMod 2] C => f c) hr⟩

def oddActionAverage {T A C : Type*} [Monoid T] [Fintype T]
    [AddCommGroup A] [AddCommGroup C]
    (α : T →* AddMonoid.End A) (r : A →+ C) : A →+ C :=
  ∑ t : T, r.comp (α t)

@[simp]
theorem oddActionAverage_apply {T A C : Type*} [Monoid T] [Fintype T]
    [AddCommGroup A] [AddCommGroup C]
    (α : T →* AddMonoid.End A) (r : A →+ C) (a : A) :
    oddActionAverage α r a = ∑ t : T, r (α t a) := by
  simp only [oddActionAverage, AddMonoidHom.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro t _
  rfl

theorem oddActionAverage_invariant {T A C : Type*} [Group T] [Fintype T]
    [AddCommGroup A] [AddCommGroup C]
    (α : T →* AddMonoid.End A) (r : A →+ C) (t : T) (a : A) :
    oddActionAverage α r (α t a) = oddActionAverage α r a := by
  simp only [oddActionAverage_apply]
  exact Fintype.sum_equiv (Equiv.mulRight t) _ _ (fun s => by
    change r (α s (α t a)) = r (α (s * t) a)
    rw [map_mul]
    rfl)

theorem oddActionAverage_retracts {T A C : Type*} [Group T] [Fintype T]
    [AddCommGroup A] [AddCommGroup C] [Module (ZMod 2) C]
    (hodd : Odd (Fintype.card T)) (α : T →* AddMonoid.End A)
    (i : C →+ A) (hfixed : ∀ t c, α t (i c) = i c)
    (r : A →+ C) (hr : ∀ c, r (i c) = c) (c : C) :
    oddActionAverage α r (i c) = c := by
  simp only [oddActionAverage_apply, hfixed, hr, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul (R := ZMod 2), hodd.natCast_zmod_two, one_smul]

theorem exists_oddInvariant_retraction {T A C : Type*} [Group T] [Finite T]
    [AddCommGroup A] [AddCommGroup C]
    [Module (ZMod 2) A] [Module (ZMod 2) C]
    (hodd : Odd (Nat.card T)) (α : T →* AddMonoid.End A)
    (i : C →+ A) (hi : Function.Injective i)
    (hfixed : ∀ t c, α t (i c) = i c) :
    ∃ r : A →+ C, (∀ c, r (i c) = c) ∧ (∀ t a, r (α t a) = r a) := by
  classical
  let := Fintype.ofFinite T
  obtain ⟨r, hr⟩ := binary_additive_retraction i hi
  refine ⟨oddActionAverage α r, ?_, oddActionAverage_invariant α r⟩
  exact oddActionAverage_retracts (by simpa [Nat.card_eq_fintype_card] using hodd)
    α i hfixed r hr

end CFSG.ShultStronglyClosedTI

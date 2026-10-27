module

public import CFSG.SignalizerFunctorTheorem.Coprime.CommutatorGeneration
public import CFSG.LocalAnalysis.SignalizerFunctor.MinimalIncompleteSolvable
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeSetCore

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Glauberman

variable {G : Type*} [Group G]

@[expose] def primeCoreIn (π : Set ℕ) (H : Subgroup G) : Subgroup G :=
  (primeSetCore (GroupType := H) π).map H.subtype

@[expose] def IsSylowOf (q : ℕ) (T U : Subgroup G) : Prop :=
  ∃ P : Sylow q U, (P : Subgroup U).map U.subtype = T

@[expose] def omegaCenter (q : ℕ) (T : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ T ∧ (∀ t ∈ T, z * t = t * z) ∧ z ^ q = 1}
  one_mem' := ⟨T.one_mem, fun t _ => by rw [one_mul, mul_one], one_pow q⟩
  mul_mem' := by
    rintro x y ⟨hxT, hxc, hxq⟩ ⟨hyT, hyc, hyq⟩
    refine ⟨T.mul_mem hxT hyT, fun t ht => ?_, ?_⟩
    · rw [mul_assoc, hyc t ht, ← mul_assoc, hxc t ht, mul_assoc]
    · rw [(show Commute x y from hxc y hyT).mul_pow q, hxq, hyq, one_mul]
  inv_mem' := by
    rintro x ⟨hxT, hxc, hxq⟩
    refine ⟨T.inv_mem hxT, fun t ht => ?_, by rw [inv_pow, hxq, inv_one]⟩
    have h := hxc t ht
    calc x⁻¹ * t = x⁻¹ * (t * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * t) * x⁻¹ := by rw [h]
      _ = t * x⁻¹ := by group

@[expose] def thompsonJ (q : ℕ) (T : Subgroup G) : Subgroup G :=
  sSup {E | E ≤ T ∧ IsElemAbelian q E ∧
    ∀ E' : Subgroup G, E' ≤ T → IsElemAbelian q E' → Nat.card E' ≤ Nat.card E}

@[expose] def ThompsonFactorizable (q : ℕ) (U T : Subgroup G) : Prop :=
  primeCoreIn ({q}ᶜ : Set ℕ) U ⊔ (U ⊓ Subgroup.normalizer (thompsonJ q T : Set G)) ⊔
    (U ⊓ Subgroup.centralizer (omegaCenter q T : Set G)) = U

structure Setting (p : ℕ) (A : Subgroup G) (θ : Subgroup G → Subgroup G) : Prop where
  prime : p.Prime
  elementary : IsElemAbelian p A
  large : p ^ 3 ≤ Nat.card A
  conditions : SolvableSignalizerConditions p 1 A θ
  locallyComplete : solvableSignalizerLocallyComplete p 1 A θ
  spectrum : signalizerSpectrum p 1 A θ = {2, 3}
  incomplete : ¬ solvableSignalizerCompatible p 1 A θ
    (⨆ S ∈ signalizerFunctorEk p 1 A, θ S)

@[expose] def hyperplaneMeet (p q : ℕ) (A B : Subgroup G) (θ : Subgroup G → Subgroup G) :
    Subgroup G :=
  ⨅ S ∈ signalizerFunctorEk p 1 A, ⨅ (_ : S ≤ B), primeCoreIn ({q}ᶜ : Set ℕ) (θ S)

@[expose] def hyperplaneMeetJoin (p q : ℕ) (A : Subgroup G) (θ : Subgroup G → Subgroup G) :
    Subgroup G :=
  ⨆ B ∈ Coprime.hyperplanes p A, hyperplaneMeet p q A B θ

end CFSG.SignalizerFunctorTheorem.Glauberman

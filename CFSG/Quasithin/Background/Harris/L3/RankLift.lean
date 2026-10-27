module

public import CFSG.Quasithin.Background.SmithB42SL3Aut
public import CFSG.Quasithin.Background.Harris.L3.RankElem
public import CFSG.Quasithin.Background.SmithB42SL3Base

public section

namespace CFSG.Quasithin.G11.Harris.L3

open scoped MatrixGroups
open Matrix CFSG.QuasithinUnique.Setup.X7a CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Quasithin.B42SL3 CFSG.ComponentClassification.CatalogueBHigherLinearAction

section Lift

variable {F : Type} [Field F] [CharP F 2] {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) SL(3, F) U) (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F)
  (A : Subgroup (U ≃ₗ[ZMod 2] U))

include hker in
theorem commute_of_mem_lift [CFSG.IsElementaryAbelian 2 A] {s t : SL(3, F)} (hs2 : s * s = 1)
    (ht2 : t * t = 1) {a b : U ≃ₗ[ZMod 2] U} (haA : a ∈ A) (hbA : b ∈ A)
    (ha : ∀ u, a u = ρ s u) (hb : ∀ u, b u = ρ t u) : s * t = t * s := by
  have hab : a * b = b * a :=
    CFSG.QuasithinUnique.Setup.Layer.Actor.comm_of_isElementaryAbelian_two inferInstance a haA b hbA
  have hρ : ρ (s * t) = ρ (t * s) := by
    refine LinearMap.ext fun u => ?_
    have h1 : ρ s (ρ t u) = ρ t (ρ s u) := by
      rw [← hb u, ← ha u, ← ha (b u), ← hb (a u)]
      exact congrArg (fun e : U ≃ₗ[ZMod 2] U => e u) hab
    simpa using h1
  have hρ1 : ρ (s * t * s⁻¹ * t⁻¹) = 1 := by
    have : s * t * s⁻¹ * t⁻¹ = (s * t) * (t * s)⁻¹ := by group
    rw [this, map_mul, hρ, ← map_mul, mul_inv_cancel, map_one]
  exact commute_of_commutator_mem_scalars hs2 ht2 (hker _ hρ1)

@[expose] def liftGroup [CFSG.IsElementaryAbelian 2 A] : Subgroup SL(3, F) where
  carrier := {t | t * t = 1 ∧ ∃ a ∈ A, ∀ u, (a : U ≃ₗ[ZMod 2] U) u = ρ t u}
  one_mem' := ⟨by simp, 1, A.one_mem, fun u => by simp⟩
  mul_mem' := by
    rintro s t ⟨hs2, a, haA, ha⟩ ⟨ht2, b, hbA, hb⟩
    have hc := commute_of_mem_lift ρ hker A hs2 ht2 haA hbA ha hb
    refine ⟨?_, a * b, A.mul_mem haA hbA, fun u => ?_⟩
    · calc s * t * (s * t) = s * (t * s) * t := by group
        _ = s * (s * t) * t := by rw [hc]
        _ = (s * s) * (t * t) := by group
        _ = 1 := by rw [hs2, ht2, one_mul]
    · show a (b u) = ρ (s * t) u
      rw [map_mul, Module.End.mul_apply, hb u, ha]
  inv_mem' := by
    rintro t ⟨ht2, a, haA, ha⟩
    rw [inv_eq_of_mul_eq_one_right ht2]
    exact ⟨ht2, a, haA, ha⟩

end Lift

section Inner

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {U : Type} [AddCommGroup U]
  [Module (ZMod 2) U] (ρ : Representation (ZMod 2) SL(3, F) U)
  (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F) (A : Subgroup (U ≃ₗ[ZMod 2] U))
  (hA : ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y) [CFSG.IsElementaryAbelian 2 A]

include hker hA in
theorem card_innerPart_le_card_liftGroup {f : ℕ} (hf : 1 ≤ f) (hNat : Nat.card F = 2 ^ f)
    (hirr : ρ.IsIrreducible) :
    Nat.card (innerPart ρ hker A hA) ≤ Nat.card (liftGroup ρ hker A) := by
  classical
  have key : ∀ a : ↥(innerPart ρ hker A hA), ∃ t : SL(3, F), t ∈ liftGroup ρ hker A ∧
      ∀ u, ((a : ↥A) : U ≃ₗ[ZMod 2] U) u = ρ t u := fun a => by
    obtain ⟨t, ht, hat⟩ := exists_lift_of_inner ρ hker A hA hf hNat hirr a.1 a.2
    exact ⟨t, ⟨ht, a.1.1, a.1.2, hat⟩, hat⟩
  choose g hg hga using key
  refine Nat.card_le_card_of_injective (fun a => (⟨g a, hg a⟩ : ↥(liftGroup ρ hker A))) ?_
  intro a b hab
  have h1 : g a = g b := congrArg Subtype.val hab
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro u
  rw [hga a u, hga b u, h1]

include hA in
omit [Fintype F] in
theorem twist_fixed_of_mem_lift {a₀ : ↥A} {M : GL (Fin 3) F} {σ : F ≃+* F}
    (hMσ : normalizerHom ρ hker A hA a₀ = LinearFlag.conjAut 3 F M * LinearFlag.fieldAut 3 F σ) {s : SL(3, F)}
    (hs : s ∈ liftGroup ρ hker A) :
    slConjugation 3 F M (SpecialLinearGroup.map σ.toRingHom s) = s := by
  obtain ⟨hs2, a, haA, ha⟩ := hs
  obtain ⟨y, hy, hproj⟩ := exists_induced ρ hker A hA a₀ s
  set w := slConjugation 3 F M (SpecialLinearGroup.map σ.toRingHom s) with hw
  have hyw : proj 3 F y = proj 3 F w := by
    rw [hproj, hMσ, MulAut.mul_apply, fieldAut_proj, conjAut_proj]
  have hcomm : a * (a₀ : U ≃ₗ[ZMod 2] U) = (a₀ : U ≃ₗ[ZMod 2] U) * a :=
    CFSG.QuasithinUnique.Setup.Layer.Actor.comm_of_isElementaryAbelian_two inferInstance a haA
      a₀ a₀.2
  have hρ : ρ y = ρ s := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨u, rfl⟩ := (a₀ : U ≃ₗ[ZMod 2] U).surjective v
    calc ρ y ((a₀ : U ≃ₗ[ZMod 2] U) u) = (a₀ : U ≃ₗ[ZMod 2] U) (ρ s u) := (hy u).symm
      _ = (a₀ : U ≃ₗ[ZMod 2] U) (a u) := by rw [ha u]
      _ = a ((a₀ : U ≃ₗ[ZMod 2] U) u) := (congrArg (fun e : U ≃ₗ[ZMod 2] U => e u) hcomm).symm
      _ = ρ s ((a₀ : U ≃ₗ[ZMod 2] U) u) := ha _
  have hsy : s⁻¹ * y ∈ scalars 3 F := by
    apply hker
    rw [map_mul, hρ, ← map_mul, inv_mul_cancel, map_one]
  have hsw : s⁻¹ * w ∈ scalars 3 F := by
    have h1 : proj 3 F s = proj 3 F y := proj_eq_proj_iff.mpr hsy
    exact proj_eq_proj_iff.mp (h1.trans hyw)
  have hww : w * w = 1 := by
    rw [hw, ← map_mul, ← map_mul, hs2, map_one, map_one]
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hzz : (s⁻¹ * w) * (s⁻¹ * w) = 1 := by
    have hzc := Subgroup.mem_center_iff.mp (scalars_le_center 3 F hsw) s⁻¹
    calc (s⁻¹ * w) * (s⁻¹ * w) = ((s⁻¹ * w) * s⁻¹) * w := by group
      _ = (s⁻¹ * (s⁻¹ * w)) * w := by rw [hzc]
      _ = (s⁻¹ * s⁻¹) * (w * w) := by group
      _ = 1 := by rw [hs', hs2, hww, one_mul]
  exact (inv_mul_eq_one.mp (eq_one_of_mem_scalars_of_mul_self hsw hzz)).symm

end Inner

end CFSG.Quasithin.G11.Harris.L3

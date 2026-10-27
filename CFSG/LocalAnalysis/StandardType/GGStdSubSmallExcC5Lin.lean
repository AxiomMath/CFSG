module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

public section

namespace CFSG.StandardType.SmallExc

open Module Matrix

variable {r : ℕ} {G : Type*} [Group G]

@[expose] def subgroupModule (f : Multiplicative (Fin r → ZMod 3) →* G) (S : Subgroup G) :
    Submodule (ZMod 3) (Fin r → ZMod 3) where
  carrier := {v | f (Multiplicative.ofAdd v) ∈ S}
  add_mem' := fun {a b} ha hb => by
    have := S.mul_mem ha hb
    rwa [← map_mul, ← ofAdd_add] at this
  zero_mem' := by simp
  smul_mem' := fun c v hv => by
    have h : c • v = c.val • v := by rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
    show f (Multiplicative.ofAdd (c • v)) ∈ S
    rw [h, ofAdd_nsmul, map_pow]
    exact S.pow_mem hv _

theorem mem_subgroupModule {f : Multiplicative (Fin r → ZMod 3) →* G} {S : Subgroup G}
    {v : Fin r → ZMod 3} : v ∈ subgroupModule f S ↔ f (Multiplicative.ofAdd v) ∈ S :=
  Iff.rfl

theorem natCard_eq_pow_finrank {f : Multiplicative (Fin r → ZMod 3) →* G}
    (hf : Function.Injective f) {S : Subgroup G} (hS : S ≤ f.range) :
    Nat.card S = 3 ^ finrank (ZMod 3) (subgroupModule f S) := by
  have e : subgroupModule f S ≃ S := Equiv.ofBijective
    (fun v => ⟨f (Multiplicative.ofAdd v.1), v.2⟩)
    ⟨fun a b h => Subtype.ext (Multiplicative.ofAdd.injective (hf (congrArg Subtype.val h))),
      fun s => by
        obtain ⟨u, hu⟩ := hS s.2
        refine ⟨⟨Multiplicative.toAdd u, ?_⟩, Subtype.ext hu⟩
        show f (Multiplicative.ofAdd (Multiplicative.toAdd u)) ∈ S
        rw [ofAdd_toAdd, hu]
        exact s.2⟩
  rw [← Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod]

theorem three_cube_le_card_inf (hr : 6 ≤ r) {f : Multiplicative (Fin r → ZMod 3) →* G}
    (hf : Function.Injective f) {A Kl : Subgroup G} (hA : A ≤ f.range)
    (hcard : 3 ^ (r - 1) ≤ Nat.card A) (Gs : Submodule (ZMod 3) (Fin r → ZMod 3))
    (hGs : ∀ g ∈ Gs, f (Multiplicative.ofAdd g) ∈ Kl) {x : G} (hx : x ^ 3 = 1)
    (hperp : ∀ v : Fin r → ZMod 3, (∀ g ∈ Gs, g ⬝ᵥ v = 0) → f (Multiplicative.ofAdd v) ∈ A →
      f (Multiplicative.ofAdd v) ∈ Subgroup.zpowers x) :
    3 ^ 3 ≤ Nat.card ↥(A ⊓ Kl) := by
  let B : LinearMap.BilinForm (ZMod 3) (Fin r → ZMod 3) := Matrix.toBilin' 1
  have hBnd : B.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' _ (by simp)
  have hBv : ∀ u v, B u v = u ⬝ᵥ v := fun u v => by simp [B, Matrix.toBilin'_apply']
  let O := B.orthogonal Gs
  have hmemO : ∀ v, v ∈ O ↔ ∀ g ∈ Gs, g ⬝ᵥ v = 0 := fun v => by
    simp only [O, LinearMap.BilinForm.mem_orthogonal_iff, hBv]
  let A' := subgroupModule f A
  have hdimA : r - 1 ≤ finrank (ZMod 3) A' := by
    have h := natCard_eq_pow_finrank hf hA
    rw [h] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard
  have hAO : finrank (ZMod 3) ↥(A' ⊓ O) ≤ 1 := by
    have hord : orderOf x ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) hx
    haveI : Finite (Subgroup.zpowers x) := Nat.finite_of_card_ne_zero (by
      rw [Nat.card_zpowers]
      exact (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hx⟩)).ne')
    have hinj : Function.Injective (fun v : ↥(A' ⊓ O) => (⟨f (Multiplicative.ofAdd v.1),
        hperp v.1 ((hmemO v.1).1 v.2.2) v.2.1⟩ : Subgroup.zpowers x)) := fun a b hab =>
      Subtype.ext (Multiplicative.ofAdd.injective (hf (congrArg Subtype.val hab)))
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod, Nat.card_zpowers] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (h1.trans (hord.trans (by norm_num)))
  have hV : finrank (ZMod 3) (Fin r → ZMod 3) = r := by simp
  have hsup1 : finrank (ZMod 3) ↥(A' ⊔ O) ≤ r := (Submodule.finrank_le _).trans hV.le
  have hmod1 := Submodule.finrank_sup_add_finrank_inf_eq A' O
  have hdimO : finrank (ZMod 3) O ≤ 2 := by omega
  have hdimOrth : finrank (ZMod 3) O = r - finrank (ZMod 3) Gs := by
    rw [LinearMap.BilinForm.finrank_orthogonal hBnd Gs, hV]
  have hGsle : finrank (ZMod 3) Gs ≤ r := (Submodule.finrank_le _).trans hV.le
  have hsup2 : finrank (ZMod 3) ↥(A' ⊔ Gs) ≤ r := (Submodule.finrank_le _).trans hV.le
  have hmod2 := Submodule.finrank_sup_add_finrank_inf_eq A' Gs
  have hdim3 : 3 ≤ finrank (ZMod 3) ↥(A' ⊓ Gs) := by omega
  haveI : Finite (Multiplicative (Fin r → ZMod 3)) :=
    Finite.of_equiv (Fin r → ZMod 3) Multiplicative.ofAdd
  haveI : Finite ↥f.range := Finite.of_surjective
    (fun u : Multiplicative (Fin r → ZMod 3) => (⟨f u, u, rfl⟩ : ↥f.range)) fun s => by
      obtain ⟨u, hu⟩ := s.2
      exact ⟨u, Subtype.ext hu⟩
  haveI : Finite ↥(A ⊓ Kl) := Finite.of_injective
    (fun s : ↥(A ⊓ Kl) => (⟨s.1, hA s.2.1⟩ : ↥f.range)) fun a b h =>
      Subtype.ext (congrArg (fun y : ↥f.range => y.1) h)
  have hinj2 : Function.Injective (fun v : ↥(A' ⊓ Gs) =>
      (⟨f (Multiplicative.ofAdd v.1), v.2.1, hGs v.1 v.2.2⟩ : ↥(A ⊓ Kl))) := fun a b hab =>
    Subtype.ext (Multiplicative.ofAdd.injective (hf (congrArg Subtype.val hab)))
  have h3 := Nat.card_le_card_of_injective _ hinj2
  rw [Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod] at h3
  exact (Nat.pow_le_pow_right (by norm_num) hdim3).trans h3

end CFSG.StandardType.SmallExc

end

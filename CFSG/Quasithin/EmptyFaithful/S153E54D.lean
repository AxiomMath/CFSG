module

public import CFSG.Quasithin.EmptyFaithful.S153E54C

public section

namespace CFSG.Quasithin

namespace S153E54

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152O4 CFSG.Quasithin.Om4Model
open CFSG.Quasithin.S153E

section ActionModel

variable {G : Type} [Group G] [Finite G] {V A : Subgroup G}

theorem exists_action_model (hV : IsElemAbelian 2 V) (hcard : Nat.card V = 16)
    (hA : A ≤ Subgroup.normalizer (V : Set G)) {q : IntMod V hV → ZMod 2}
    (hq1 : IsQuadraticFormOn q) (hq2 : IsNondegQuadratic q) (hq3 : IsPlusType q)
    (hAΩ : ∀ g : MulAut (IntMod V hV), g ∈ autI hV A ↔
      g ∈ orthogonalGroupOf q ∧ Even (rk (commV (Subgroup.zpowers g)))) :
    ∃ (ψ : IntMod V hV ≃* Multiplicative Mt) (α : ↥A →* OmG),
      Function.Surjective α ∧
      (∀ x : ↥A, α x = 1 ↔ (x : G) ∈ Subgroup.centralizer (V : Set G)) ∧
      (∀ (a : ↥A) (v : IntMod V hV), Multiplicative.toAdd (ψ (convI hV ⟨a, hA a.2⟩ v)) =
        omSmul (α a) (Multiplicative.toAdd (ψ v))) ∧
      (∀ x y : IntMod V hV, quadPolar q x y =
        polarDet (Multiplicative.toAdd (ψ x)) (Multiplicative.toAdd (ψ y))) ∧
      (∀ x : IntMod V hV, q x = (Multiplicative.toAdd (ψ x)).det) := by
  have hcard' : Nat.card (IntMod V hV) = 16 := hcard
  obtain ⟨c, hqc⟩ := exists_vec_iso hcard' hq1 hq2 hq3
  let f : ↥A →* MulAut (IntMod V hV) := (convI hV).comp (Subgroup.inclusion hA)
  have hf : ∀ a : ↥A, f a = convI hV ⟨a, hA a.2⟩ := fun a => rfl
  have hfr : ∀ a : ↥A, f a ∈ (rhoV c).range := fun a =>
    (range_iff hcard' hq1 hq2 hq3 c hqc _).2
      ((hAΩ _).1 (hf a ▸ convI_mem_autI hV a.2 (hA a.2)))
  let α' : ↥A →* Gam :=
    ((MonoidHom.ofInjective (rhoV_injective c)).symm : (rhoV c).range ≃* Gam).toMonoidHom.comp
      (f.codRestrict (rhoV c).range hfr)
  have hα' : ∀ a : ↥A, rhoV c (α' a) = f a := fun a => by
    have := (MonoidHom.ofInjective (rhoV_injective c)).apply_symm_apply
      (⟨f a, hfr a⟩ : (rhoV c).range)
    exact congrArg Subtype.val this
  refine ⟨c.trans thetaV, (Psi : Gam ≃* OmG).toMonoidHom.comp α', ?_, ?_, ?_, ?_, ?_⟩
  · intro l
    have hl : rhoV c (Psi.symm l) ∈ (rhoV c).range := ⟨_, rfl⟩
    obtain ⟨hlO, hlE⟩ := (range_iff hcard' hq1 hq2 hq3 c hqc _).1 hl
    obtain ⟨g, hgA, hg⟩ := (mem_autI hV).1 ((hAΩ _).2 ⟨hlO, hlE⟩)
    refine ⟨⟨g, hgA⟩, ?_⟩
    have h1 : α' ⟨g, hgA⟩ = Psi.symm l := by
      apply rhoV_injective c
      rw [hα']
      exact hg
    show Psi (α' ⟨g, hgA⟩) = l
    rw [h1, MulEquiv.apply_symm_apply]
  · intro x
    show Psi (α' x) = 1 ↔ _
    rw [map_eq_one_iff _ Psi.injective]
    have h1 : α' x = 1 ↔ f x = 1 := by
      rw [← hα' x, ← map_one (rhoV c)]
      exact (rhoV_injective c).eq_iff.symm
    rw [h1, hf, convI_eq_one_iff hV]
  · intro a v
    show Multiplicative.toAdd (thetaV (c _)) = omSmul (Psi (α' a)) (Multiplicative.toAdd (thetaV (c v)))
    rw [toAdd_thetaV, toAdd_thetaV, ← hf, ← hα', rhoV_apply, toMt_act]
    rfl
  · intro x y
    show quadPolar q x y = polarDet (Multiplicative.toAdd (thetaV (c x)))
      (Multiplicative.toAdd (thetaV (c y)))
    rw [toAdd_thetaV, toAdd_thetaV]
    exact quadPolar_eq_polarDet c hqc x y
  · intro x
    show q x = (Multiplicative.toAdd (thetaV (c x))).det
    rw [toAdd_thetaV, ← toMt_det]
    exact hqc x

end ActionModel

end S153E54

end CFSG.Quasithin

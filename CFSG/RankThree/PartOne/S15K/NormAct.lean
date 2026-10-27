module

public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.RankThree.PartOne.S15K

variable {G : Type*} [Group G]

@[expose] noncomputable def actP {I : Subgroup G} {P : Type*} [Group P] (φ : ↥I ≃* P) :
    ↥(Subgroup.normalizer (I : Set G)) →* MulAut P :=
  (MulAut.congr φ).toMonoidHom.comp I.normalizerMonoidHom

theorem actP_apply {I : Subgroup G} {P : Type*} [Group P] (φ : ↥I ≃* P)
    (g : ↥(Subgroup.normalizer (I : Set G))) (x : ↥I) :
    actP φ g (φ x) = φ (I.normalizerMonoidHom g x) := by
  simp [actP, MulAut.congr_apply]

theorem coe_normalizerMonoidHom_apply {I : Subgroup G} (g : ↥(Subgroup.normalizer (I : Set G)))
    (x : ↥I) : ((I.normalizerMonoidHom g x : ↥I) : G) = (g : G) * x * (g : G)⁻¹ := rfl

theorem mulAut_conj_apply' {C : Type*} [Group C] (β : MulAut C) (d : C) :
    MulAut.conj (β d) = β * MulAut.conj d * β⁻¹ := by
  ext x
  simp [MulAut.conj_apply]

theorem compat_of_actP {I : Subgroup G} {P : Type*} [Group P] (φ : ↥I ≃* P)
    {g : ↥(Subgroup.normalizer (I : Set G))} {t : MulAut P} (ht : actP φ g = t) (x : ↥I) :
    ((MulAut.conj : P →* MulAut P).comp φ.toMonoidHom) (I.normalizerMonoidHom g x) =
      t * ((MulAut.conj : P →* MulAut P).comp φ.toMonoidHom) x * t⁻¹ := by
  have h1 : φ (I.normalizerMonoidHom g x) = t (φ x) := by rw [← ht, actP_apply]
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  show MulAut.conj (φ (I.normalizerMonoidHom g x)) = t * MulAut.conj (φ x) * t⁻¹
  rw [h1, mulAut_conj_apply']

end CFSG.RankThree.PartOne.S15K

module

public import CFSG.LocalAnalysis.StandardType.GGWAutCommon
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112WeylE7
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112WeylE8

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggWAutE_engine {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (A R : Subgroup (V ≃ₗ[ZMod 3] V)) (hR : R = reflGp A)
    (habs : ZS.AbsIrred 3 R) {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ}
    (hInner : GGQ2WeylInner n C) (hW : GGWeylModel3 C R) :
    ∀ a ∈ A, ∃ r ∈ R, (∀ v, a v = r v) ∨ (∀ v, a v = -(r v)) := by
  intro a ha
  obtain ⟨z, α, hz, hspan, hα, hWeyl⟩ := hW
  have hnorm : a ∈ Subgroup.normalizer (ggQ2WeylOf z α : Set (V ≃ₗ[ZMod 3] V)) :=
    Subgroup.mem_set_normalizer_iff.mpr (fun x => by
      constructor
      · intro hx
        have hxR : x ∈ R := by rw [hWeyl]; exact hx
        have h1 : a * x * a⁻¹ ∈ reflGp A := ggWAut_reflGp_conj A ha (hR ▸ hxR)
        rw [← hR, hWeyl] at h1
        exact h1
      · intro hx
        have hxR : a * x * a⁻¹ ∈ R := by rw [hWeyl]; exact hx
        have h1 : a⁻¹ * (a * x * a⁻¹) * a ∈ reflGp A :=
          ggWAut_reflGp_conj A (A.inv_mem ha) (hR ▸ hxR)
        have h2 : a⁻¹ * (a * x * a⁻¹) * a = x := by group
        rw [h2, ← hR, hWeyl] at h1
        exact h1)
  obtain ⟨w, hw, hconj⟩ := hInner z hz hspan α hα a hnorm
  have hwR : w ∈ R := by rw [hWeyl]; exact hw
  refine ⟨w, hwR, ?_⟩
  exact ggWAut_pm_of_conj A R hR habs ha hwR (fun r hr _ => by
    have hr' : r ∈ ggQ2WeylOf z α := by rw [hWeyl] at hr; exact hr
    exact hconj r hr')

theorem ggWAut_E7 {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V]
    (A R : Subgroup (V ≃ₗ[ZMod 3] V)) (hRA : R ≤ A) (hR : R = reflGp A)
    (habs : ZS.AbsIrred 3 R) (hW : GGWeylModel3 (CartanMatrix.E 7) R) :
    ∀ a ∈ A, ∃ r ∈ R, (∀ v, a v = r v) ∨ (∀ v, a v = -(r v)) := by
  have _hRA := hRA
  exact ggWAutE_engine A R hR habs ggQ2WeylInner_E7 hW

theorem ggWAut_E8 {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V]
    (A R : Subgroup (V ≃ₗ[ZMod 3] V)) (hRA : R ≤ A) (hR : R = reflGp A)
    (habs : ZS.AbsIrred 3 R) (hW : GGWeylModel3 (CartanMatrix.E 8) R) :
    ∀ a ∈ A, ∃ r ∈ R, (∀ v, a v = r v) ∨ (∀ v, a v = -(r v)) := by
  have _hRA := hRA
  exact ggWAutE_engine A R hR habs ggQ2WeylInner_E8 hW

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionTop

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

theorem ggSporK_generalizedFitting_eq_top {W K : Type} [Group W] [Finite W] [Group K]
    (hsimple : IsSimpleGroup ↥(CFSG.generalizedFitting W))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting W), a * b ≠ b * a)
    (hInn : ∀ φ : MulAut K, ∃ g : K, φ = MulAut.conj g)
    (he : Nonempty (↥(CFSG.generalizedFitting W) ≃* K)) :
    CFSG.generalizedFitting W = ⊤ := by
  obtain ⟨e⟩ := he
  have hKn : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  rw [eq_top_iff]
  intro w _
  set F := CFSG.generalizedFitting W
  let φ : MulAut ↥F := MulAut.conjNormal (H := F) w
  obtain ⟨g, hg⟩ := hInn ((e.symm.trans φ).trans e)
  set k : ↥F := e.symm g with hk
  have hcomm : ∀ x ∈ F, (k : W)⁻¹ * w * x = x * ((k : W)⁻¹ * w) := by
    intro x hx
    have h1 := congrArg (fun m => e.symm (m (e ⟨x, hx⟩))) hg
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply,
      map_mul, map_inv, MulEquiv.symm_apply_apply] at h1
    have h2 := congrArg Subtype.val h1
    rw [MulAut.conjNormal_apply] at h2
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    calc (k : W)⁻¹ * w * x = (k : W)⁻¹ * (w * x * w⁻¹) * w := by group
      _ = (k : W)⁻¹ * ((k : W) * x * (k : W)⁻¹) * w := by rw [h2]
      _ = x * ((k : W)⁻¹ * w) := by group
  have hwk : (k : W)⁻¹ * w = 1 := ggEq_one_of_commute_generalizedFitting hsimple hnab
    fun x hx => hcomm x hx
  have hw' : w = k := by
    calc w = (k : W) * ((k : W)⁻¹ * w) := by group
      _ = k := by rw [hwk, mul_one]
  rw [hw']
  exact k.2

theorem ggSporK_nonempty_mulEquiv {W K : Type} [Group W] [Finite W] [Group K]
    (hsimple : IsSimpleGroup ↥(CFSG.generalizedFitting W))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting W), a * b ≠ b * a)
    (hInn : ∀ φ : MulAut K, ∃ g : K, φ = MulAut.conj g)
    (he : Nonempty (↥(CFSG.generalizedFitting W) ≃* K)) : Nonempty (W ≃* K) := by
  obtain ⟨e⟩ := he
  have htop := ggSporK_generalizedFitting_eq_top hsimple hnab hInn ⟨e⟩
  exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans e⟩

end CFSG.StandardType.SporadicShape

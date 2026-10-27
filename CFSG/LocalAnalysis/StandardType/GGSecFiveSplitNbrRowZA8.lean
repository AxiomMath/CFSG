module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZReduce
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZTransfer
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZA8Shift
public import CFSG.LocalAnalysis.StandardType.GGSL9TwoProj
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggTorusDetEltElt_ggSL9 :
    NbrFrameDet.GGTorusDetEltElt 7 3 (GGSL9V ≃ₗ[ZMod 2] GGSL9V) := by
  intro E hE hr _
  obtain ⟨g, rfl⟩ := exists_conj_eq_ggSL9Torus hE hr
  refine ⟨3, (MulAut.conj g).toMonoidHom.comp ggSL9TorusCoord,
    (MulAut.conj g).injective.comp ggSL9TorusCoord_injective, ?_, g * ggSL9Shift * g⁻¹,
    ggSL9ShiftCoord, fun f => ?_, by norm_num, ?_⟩
  · rw [MonoidHom.range_comp, range_ggSL9TorusCoord]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← ggSL9Shift_conj_torusCoord f]
    group
  · intro h
    have h2 := congrArg (fun u : (ZMod 7)ˣ => (u : ZMod 7)) h
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at h2
    rw [ggDetAut_ggSL9ShiftCoord] at h2
    revert h2
    decide

theorem ggDetAt_A8 : GGDetAt 7 ⟨.A, 8, 1⟩ := by
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ', 3,
    TypeA.ggTorusLift_of_mulEquiv (ggSL9RecipeEquiv hK) ggTorusLift_ggSL9, ?_⟩
  intro L' _ _ ψ A hA
  exact NbrFrameDet.ggTorusDetElt_of_elt (by norm_num) subset_rfl center_ggSL9_eq_bot
    (ggCenterPrime_ggSL9 (by norm_num)) ggTorusDetEltElt_ggSL9 L'
    ((ggSL9RecipeEquiv hK).toMonoidHom.comp ψ) A
    (hA.mulEquiv (ggSL9RecipeEquiv hK) fun _ hφ => congr_ggSL9RecipeEquiv_mem hK hφ)

theorem ggRowP_ZA8_eq_label : ∀ lab : LargeEvenLabel, ggRowP_ZA8 7 lab → lab = ⟨.A, 8, 1⟩ := by
  rintro ⟨t, r, n⟩ ⟨h1, h2, h3, -⟩
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem ggRowZA8_absurd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {K : Subgroup G}
    (hK : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K) (hrow : GGInnerDiagOnLabel ggRowP_ZA8 p Bs K) : False := by
  refine ggRowZ_absurd_of_detElt ggLabelRigidInput_holds (S := ggRowP_ZA8) ?_ hcfg hK hrow
  intro p' _ _ lab _ h
  have hp7 : p' = 7 := h.2.2.2
  subst hp7
  rw [ggRowP_ZA8_eq_label lab h]
  exact ggDetAt_A8

end CFSG.StandardType

end

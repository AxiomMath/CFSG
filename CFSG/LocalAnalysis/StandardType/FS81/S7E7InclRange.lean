module

public import CFSG.LocalAnalysis.StandardType.FS81.S7E7Incl

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction CFSG.QuasithinUnique

local notation "Dθ" => EPilot.perpLevi Tag.E8 (GaloisField 2 1)

section E7Model


private theorem adjointGroupE7RingEquiv_pinnedElt (γ : Fin (Tag.rank .E7) → ℤ) (c : ZMod 2) :
    E8Pilot.adjointGroupE7RingEquiv zmodTwoEquivGalois (EPilot.pinnedElt .E7 γ c) =
      ⟨pinnedX .E7 (GaloisField 2 1) γ (zmodTwoEquivGalois c),
        pinnedX_mem_adjointGroup γ (zmodTwoEquivGalois c)⟩ := by
  apply Subtype.ext
  exact baseChangeGL_pinnedX (zmodTwoEquivGalois : ZMod 2 →+* GaloisField 2 1) γ c

theorem e7Incl_injective : Function.Injective e7Incl := by
  unfold e7Incl
  exact (Subgroup.subtype_injective (E8Pilot.e7Levi (GaloisField 2 1))).comp
    (((E8Pilot.e7LeviEquiv (GaloisField 2 1)).symm.injective).comp
      ((E8Pilot.adjointGroupE7RingEquiv zmodTwoEquivGalois).injective))

theorem range_e7Incl : e7Incl.range = Dθ := by
  have hφ : ((E8Pilot.e7LeviEquiv (GaloisField 2 1)).symm.toMonoidHom.comp
      (E8Pilot.adjointGroupE7RingEquiv zmodTwoEquivGalois).toMonoidHom).range = ⊤ :=
    MonoidHom.range_eq_top.mpr
      ((E8Pilot.e7LeviEquiv (GaloisField 2 1)).symm.surjective.comp
        (E8Pilot.adjointGroupE7RingEquiv zmodTwoEquivGalois).surjective)
  unfold e7Incl
  rw [MonoidHom.range_comp, hφ, Subgroup.map_top, Subgroup.range_subtype]
  rfl

theorem e7Incl_pinnedElt {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (c : ZMod 2) :
    e7Incl (EPilot.pinnedElt .E7 γ c) =
      EPilot.pinnedElt .E8 (E8Pilot.e7Embed γ) (zmodTwoEquivGalois c) := by
  unfold e7Incl
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [adjointGroupE7RingEquiv_pinnedElt γ c]
  apply Subtype.ext
  exact E8Pilot.coe_e7LeviEquiv_symm_pinnedX hγ (zmodTwoEquivGalois c)

end E7Model

end CFSG.StandardType.FrameRoute.FS81

end

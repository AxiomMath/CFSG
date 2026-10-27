module

public import CFSG.Quasithin.Recognition.CertU33Wreath
public import CFSG.Quasithin.Recognition.CertU33Psu
public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin

open CFSG.Open

theorem g22p_amalgam_facts
    : ∀ (G : Type) [Group G] [Finite G] (P₁ P₂ : Subgroup G),
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups P₁ P₂)
      (fun Y _ => Nonempty (Y ≃* PSU3 3 1)) →
    Nonempty (↥(P₁ ⊓ P₂) ≃* WreathedTwoGroup 2) := by
  intro G _ _ P₁ P₂ h
  obtain ⟨Y, _, ⟨eY⟩, T, M₁, M₂, hpair, ⟨iso⟩⟩ := h
  obtain ⟨ePres⟩ := u33Pres_mulEquiv_PSU3
  obtain ⟨hfin, -⟩ := u33Pres_finite_card_le
  let f : Y ≃* U33G := eY.trans ePres.symm
  have hY := IsYAmalgamPair.map f hpair
  obtain ⟨e1⟩ := u33Extra.recog hY
  obtain ⟨eT⟩ := u33_T_mulEquiv_wreathed
  have hinf : (M₁ ⊓ M₂).map f.toMonoidHom = M₁.map f.toMonoidHom ⊓ M₂.map f.toMonoidHom :=
    Subgroup.map_inf M₁ M₂ f.toMonoidHom f.injective
  exact ⟨iso.φ12.trans (((Subgroup.equivMapOfInjective _ f.toMonoidHom f.injective).trans
    (MulEquiv.subgroupCongr hinf)).trans (e1.trans eT))⟩

end CFSG.Quasithin

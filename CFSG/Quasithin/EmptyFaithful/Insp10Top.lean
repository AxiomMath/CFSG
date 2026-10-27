module

public import CFSG.Quasithin.EmptyFaithful.Insp10Defs
public import CFSG.Quasithin.EmptyFaithful.Insp10Geom
public import CFSG.Quasithin.EmptyFaithful.Insp10Alpha

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem inspectRemaining153_of_inputs (h113 : StageLemma14113) (hB : InspectB51Rem153)
    (hA : InspectA5Quot153) : InspectRemaining153 := by
  intro G _ _ T Mc M V₁ V₂ E t s c r45 r46 r49 L r66 r67 gl r68 hconc hlist hS3 hO2
  have conf : Conf153 G T Mc M V₁ V₂ E t s := ⟨c, r45, r46, r49, L, r66, r67, gl, r68⟩
  have hcomm : ⁅VZ T M, YF153 Mc M E s⁆ = VZ T M := commutator_VZ_YF c r66 gl
  have hQV : pCoreOf 2 (YF153 Mc M E s) ⊔ pCoreOf 2 (G0_153 T Mc M E s) ≤
      Subgroup.centralizer (VZ T M : Set G) :=
    pCoreOf_YF_sup_pCoreOf_G0_le_centralizer c r49 gl r68
  have hYFX : YF153 Mc M E s ≤ thompsonJ (G0_153 T Mc M E s) ⊔ pCoreOf 2 (G0_153 T Mc M E s) :=
    YF_le_thompsonJ_sup_pCore r68 hO2
  have hG1N : G1_153 T Mc M E s ≤ Subgroup.normalizer (VZ T M : Set G) :=
    (G1_le_M c gl).trans c.hyp.le_normalizer
  have hQ1 : ¬ pCoreOf 2 (G1_153 T Mc M E s) ≤ Subgroup.centralizer (VZ T M : Set G) :=
    not_pCoreOf_G1_le_centralizer c L r66 gl
  have hC : pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (E : Set G) :=
    r68.pCore_le_centralizer.trans (Subgroup.centralizer_le L.le_V)
  have h5 : CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) =
      (pCoreOf 2 (G0_153 T Mc M E s)).subgroupOf (G0_153 T Mc M E s) := by
    rw [r68.pCore_eq]
    exact (Subgroup.comap_map_eq_self_of_injective
      (G0_153 T Mc M E s).subtype_injective _).symm
  have hnp := Insp10.oTwoUpper_ne_top_NR h113 c r49 L r66 r67 r68.le_normalizer hC h5
  obtain ⟨hHat, hcard⟩ := hB G T Mc M V₁ V₂ E t s conf hconc hlist hS3 hO2 hnp hYFX hQV hcomm
    hG1N hQ1
  exact hA G T Mc M V₁ V₂ E t s conf hconc hlist hS3 hO2 hYFX hQV hcomm hHat hcard

end CFSG.Quasithin

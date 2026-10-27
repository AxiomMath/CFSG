module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCover
public import CFSG.LieType.Steinberg.CentralExt.SUEvenFieldTwo

public section

namespace CFSG.StandardType.LineU

section Certificates


theorem unitaryCoverTwoEven_holds : UnitaryCoverTwoEven := by
  unfold UnitaryCoverTwoEven
  intro d K _ _ hK hd hd8
  obtain ⟨r, rfl⟩ : ∃ r, d = 2 * r := ⟨d / 2, by obtain ⟨k, hk⟩ := hd; omega⟩
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, le_rfl, by norm_num [hK]⟩
  haveI : CharP K 2 := hU.charP
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by norm_num [hK]
  refine unitaryCoverAt_of_section (n := 1) ?_ ?_
  · haveI := CFSG.LieType.Steinberg.CentralExt.SUClosed.isPerfect_statedSU hF
      (show 4 ≤ 2 * r by omega)
    exact Group.IsPerfect.commutator_eq_top
  · intro E _ _ π hπ hcen
    exact CFSG.LieType.Steinberg.CentralExt.SUEvenTwo.statedSU_exists_section_of_central_two hF
      (even_two_mul r) hd8 hπ hcen

theorem unitaryUniversalCover_holds : UnitaryUniversalCover :=
  unitaryUniversalCover_of_twoEven unitaryCoverTwoEven_holds

theorem ggLNoInvariantLineInputOn_unitDvd_holds :
    GGLNoInvariantLineInputOn GGUnitDvdLabelNo63 :=
  ggLNoInvariantLineInputOn_unitDvd_of_twoEven unitaryCoverTwoEven_holds

end Certificates

end CFSG.StandardType.LineU

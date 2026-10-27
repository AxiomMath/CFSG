module

public import CFSG.Quasithin.H13.GoldschmidtU3RankL
public import CFSG.Quasithin.H13.U3FinalExclude
public import CFSG.Quasithin.H13.U3Witness
public import CFSG.Quasithin.H13.U3L1312
public import CFSG.Quasithin.H13.U3L15

public section

namespace CFSG.Quasithin.H13.U3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.SteinbergCB

theorem stmt13_3_16_of_inputs_L
    (h1332 : Stmt13_3_2) (h3 : UniqueThreeCaseModelReduction)
    (hex : UniqueModelsExcludeU3Sections) (hexcl : ExcludedMinimalOvergroupTwoRankBoundL)
    (h4 : U3CodimThreeCentralizerControl) (h5 : U3AbelianCentralizerHull)
    (h6 : U3EscapingLocalGenerationWitness) : Stmt13_3_16 :=
  stmt13_3_16_of_producers (u3_internal_frame_producer h1332)
    (u3_six_action_profile_producer h1332)
    (u3_local_uniqueness_and_escape_producer_of_1332_L h1332
      (u3_confined_centralizer_overgroup h1332 h3 hex) hexcl) h4 h5 h6

theorem stmt13_3_16_of_remaining_inputs_L
    (h1332 : Stmt13_3_2)
    (h3 : UniqueThreeCaseModelReduction) (hexcl : ExcludedMinimalOvergroupTwoRankBoundL)
    (h4 : U3CodimThreeCentralizerControl) (h5 : U3AbelianCentralizerHull)
    (h6 : U3EscapingLocalGenerationWitness) : Stmt13_3_16 :=
  stmt13_3_16_of_inputs_L h1332 h3 unique_models_exclude_U3_sections hexcl h4 h5 h6

theorem stmt13_3_16_of_inputs_l15_L
    (h1332 : Stmt13_3_2) (h311 : Theorem311Stmt)
    (h612 : ASInputs.AS_E_6_12) (h12211 : Stmt12_2_11') (h3 : UniqueThreeCaseModelReduction)
    (hexcl : ExcludedMinimalOvergroupTwoRankBoundL) (hA : U3NondegLineCentralizer)
    (h12_4 : U3Stmt13_3_12_4) (h13314 : A6.Stmt13_3_14) : Stmt13_3_16 :=
  have hcod := u3_codim_three_of_claims h1332 h311 h612 hA (u3V3Centralizer_of_13314 h1332 h13314)
  have hesc := u3_local_uniqueness_and_escape_producer_of_1332_L h1332
    (u3_confined_centralizer_overgroup_of_reduction h1332 h3) hexcl
  stmt13_3_16_of_remaining_inputs_L h1332 h3 hexcl hcod
    (u3_abelian_centralizer_hull_of_13314 h1332 h13314 h12_4 hcod)
    (u3_escaping_local_generation_witness h1332 h12211 hesc hcod)

theorem stmt13_3_16_of_inputs_l1312_L
    (h1332 : Stmt13_3_2) (h311 : Theorem311Stmt)
    (h612 : ASInputs.AS_E_6_12) (h12211 : Stmt12_2_11') (h3 : UniqueThreeCaseModelReduction)
    (hexcl : ExcludedMinimalOvergroupTwoRankBoundL) (hA : U3NondegLineCentralizer)
    (h13314 : A6.Stmt13_3_14) : Stmt13_3_16 :=
  stmt13_3_16_of_inputs_l15_L h1332 h311 h612 h12211 h3 hexcl hA (u3Stmt13_3_12_4_of h1332)
    h13314

theorem stmt13_3_16_of_inputs_l1312_of_1227
    (h1332 : Stmt13_3_2) (h311 : Theorem311Stmt)
    (h612 : ASInputs.AS_E_6_12) (h12211 : Stmt12_2_11') (h3 : UniqueThreeCaseModelReduction)
    (h1227 : Stmt12_2_7) (hA : U3NondegLineCentralizer) (h13314 : A6.Stmt13_3_14) :
    Stmt13_3_16 :=
  stmt13_3_16_of_inputs_l1312_L h1332 h311 h612 h12211 h3
    (excludedMinimalOvergroupTwoRankBoundL_of h1332 h1227) hA h13314

end CFSG.Quasithin.H13.U3

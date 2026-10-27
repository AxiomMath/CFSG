module

public import CFSG.RankThree.GF2n.Smith81.S81LaneE3LCert
public import CFSG.RankThree.GF2n.Smith81.S81LaneE3U
public import CFSG.RankThree.GF2n.Smith81.S81YUCase
public import CFSG.RankThree.GF2n.Smith81.S81YE5Case
public import CFSG.RankThree.GF2n.Smith81.S81XE5
public import CFSG.RankThree.GF2n.Smith81.S81YE4Case
public import CFSG.RankThree.GF2n.Smith81.S81XE4
public import CFSG.RankThree.GF2n.Smith81.S81VFe1
public import CFSG.RankThree.GF2n.Smith81.S81KForm
public import CFSG.RankThree.GF2n.Smith81.S81KElemHolds
public import CFSG.RankThree.GF2n.Smith81.S81KNormRed
public import CFSG.RankThree.GF2n.Smith81.S81KNormSylow
public import CFSG.RankThree.GF2n.Smith81.S81ZFe1
public import CFSG.RankThree.GF2n.Smith81.S81HE5
public import CFSG.RankThree.GF2n.Smith81.S81ZFe1E4Final
public import CFSG.RankThree.GF2n.Smith81.S81KInvolHolds
public import CFSG.RankThree.GF2n.Smith81.S81QCoreE4Stmt
public import CFSG.RankThree.GF2n.Smith81.S81HE4G1
public import CFSG.RankThree.GF2n.Smith81.S81E5NormQuot
public import CFSG.RankThree.GF2n.Smith81.S81E5ElemBound
public import CFSG.RankThree.GF2n.Smith81.S81E5Classes
public import CFSG.RankThree.GF2n.Smith81.S81TNonfusedLine
public import CFSG.RankThree.GF2n.Smith81.S81WCountE4
public import CFSG.RankThree.GF2n.Smith81.S81WCountE5
public import CFSG.RankThree.GF2n.Smith81.S81Lane216E
public import CFSG.RankThree.GF2n.Smith81.OrthLaneHolds
public import CFSG.RankThree.GF2n.Smith81.LinTILaneHolds
public import CFSG.RankThree.GF2n.Smith81.Lin216E6

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.RankThree.GF2n.Smith81.MinuscT


theorem smith1981_of_typeE_inputs (hSt : Stroth1980Rel)
    (hFE14 : Smith24E4UniformStatement) (hCl4 : E4InvolClassesStatement) :
    Smith1981Statement := by
  have h34 : Stroth34Statement := stroth34Statement_unconditional
  have hGen : StrothGenByBStatement := strothGenByBStatement_certified
  have hFE1U : Smith24E3UUniformStatement := S81V.smith24E3UUniform_of_inputs h34 hGen
  have hFE15 : Smith24E5UniformStatement := S81Z.smith24E5Uniform_of_inputs
    (fun _ _ _ _ _ _ _ hb hc h5 => exists_lgen_hom_EAut_E5 hSt hb hc h5) h34 hGen
  have hForm4 : Smith24E4FormStatement := smith24E4Form_holds
  have hB4 : ElemBoundE4Statement := SK.elemBoundE4_of_core SK.elemAbelianBoundE4_holds hFE14
  have hNQ4 : NormQuotE4Statement := SK.normQuotE4_of_core (D6Normalizer.normalizerE4_of_sylow
      D6Normalizer.sylowW_holds) hFE14
  have hForm5 : Smith24E5FormStatement := smith24E5Form_holds
  have hNQ5 : NormQuotE5Statement := normQuotE5_of_uniform hFE15
  have hB5 : ElemBoundE5Statement := elemBoundE5_of_uniform hFE15
  have hCl5 : E5InvolClassesStatement := e5InvolClasses_holds
  obtain ⟨-, -, hN3L, h213_3L, hC3L, h28_3L⟩ := laneE3L_certified
  obtain ⟨hN3U, hC3U, h28_3U, hFE2U⟩ := laneE3U_of_fe1 hFE1U h34 hGen
  have h213U : Smith213E3UStatement := smith213E3U_of_inputs hFE1U hFE2U hN3U
  have hN5 : Smith212ENonfusedE5Statement :=
    smith212ENonfusedE5_of_inputs hFE15 hForm5 hNQ5 hB5 hCl5 hGen h34
  have h28_5 : Smith28E5Statement := smith28E5_of_uniform hFE15 hForm5 hNQ5 hB5 hCl5
  have h213_5 : Smith213E5Statement :=
    smith213E5_of_inputs hFE15 (e5RootElt_of_inputs hFE15 hForm5 h28_5 h34 hGen) hN5 h28_5
  have hN4 : Smith212ENonfusedE4Statement :=
    smith212ENonfusedE4_of_inputs hFE14 hForm4 hNQ4 hB4 hCl4 hGen h34
  have h28_4 : Smith28E4Statement := smith28E4_of_uniform hFE14 hForm4 hNQ4 hB4 hCl4
  have h213_4 : Smith213E4Statement :=
    smith213E4_of_inputs hFE14 (e4RootElt_of_inputs hFE14 hForm4 h28_4 h34 hGen) hN4 h28_4
  have hN : Smith212ENonfusedStatement := smith212ENonfused_of_cases hN3U hN3L hN4 hN5
  have h213 : Smith213EStatement := smith213E_of_cases h213U h213_3L h213_4 h213_5
  have hC : Smith216ECountStatement := smith216ECount_of_cases hC3U hC3L
    (smith216ECountE4_of_uniform hFE14 hGen h34) (smith216ECountE5_of_uniform hFE15 hGen h34)
  have h28 : Smith28EStatement := smith28E_of_cases h28_3U h28_3L h28_4 h28_5
  have hInsp : Smith219EInspectionStatement :=
    Insp.smith219EInspection_of hN hSt SubCfg.subConfigE4Statement_holds
      SubCfg.subConfigE5Statement_holds Insp.k1NSL_holds Insp.k2PSL_holds Insp.k2PSp_holds
  exact smith1981_of_steps laneTIStep_holds smithLaneOrth_holds
    (smithLaneE_of_28 timmesfeldOutcomeStatement_of_outcome hN h213 hC h28 smith217_holds hInsp)
    smithLaneLin_holds (smith216_of_E_orth (smith216E_of_28 hN h213 hC h28) smith216Orth_holds)

theorem smith1981_of_E4G1_core (hSt : Stroth1980Rel) (hG14 : E4G1Statement)
    (hcore4 : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], S81Z.E4CoreStatement K) :
    Smith1981Statement :=
  smith1981_of_typeE_inputs hSt
    (S81Z.smith24E4Uniform_of_core hG14 stroth34Statement_unconditional
      strothGenByBStatement_certified hcore4)
    SK.e4InvolClasses_holds

theorem smith1981_of_E4G1 (hSt : Stroth1980Rel) (hG14 : E4G1Statement) : Smith1981Statement :=
  smith1981_of_E4G1_core hSt hG14 fun K _ _ _ => D6Spin.e4Core_holds K

theorem smith1981_of_rel (hSt : Stroth1980Rel) : Smith1981Statement :=
  smith1981_of_E4G1 hSt fun _ _ _ _ _ _ _ hb hc h4 => exists_lgen_hom_EAut0_E4 hSt hb hc h4

end CFSG.RankThree.GF2n.Smith81

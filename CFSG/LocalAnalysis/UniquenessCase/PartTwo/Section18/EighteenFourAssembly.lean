module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourBK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourCaseOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourCaseTwoFinal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourCaseThreeK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourCalOOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThreeProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenNineteenDiag
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaPlusFourTwoNatScalarHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.SignalizerFunctorTheorem.McBride
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}

theorem A5Config18.barSub_ne (c : A5Config18 D V₀ V L K) :
    barSub ⊥ V c.elemAbelian L ≠ barSub ⊥ V c.elemAbelian K := by
  obtain ⟨pair, v0, -, -, -, -, -, hL1, hK1, -⟩ := c
  subst v0
  exact A5Pair18.barSub_L_ne_barSub_K pair rfl hL1 hK1

theorem gapInputs_of_pair
    {D : Data G} {V₀ V L K : Subgroup G}
    (c : A5Data18 D V₀ V L) (P : A5Pair18 D V₀ V L K) (hKc : K_L2SzAutRank) :
    (CFSG.SignalizerFunctorTheorem.McBride.orbitClosure
        (imageBar2 (UC22.conjClosure D.M L ⊔ D.T) L)
        (imageBar2 (UC22.conjClosure D.M L ⊔ D.T) D.T) ⊔
      imageBar2 (UC22.conjClosure D.M L ⊔ D.T) D.T = ⊤) ∧
    (∀ T' : Subgroup (Bar2 (UC22.conjClosure D.M L ⊔ D.T)),
      CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ → CompFactorAutInF (S17.nOf L) ⊤ T') := by
  have hL2base : IsL2 (Bar2 L) 2 := by
    obtain ⟨e⟩ := c.alt
    exact CFSG.Quasithin.H13.A5.lieModel_of_alternating_five e
  have hL2 : IsL2 (Bar2 L) (S17.nOf L) ∨ IsSz (Bar2 L) (S17.nOf L) := by
    rw [S17.nOf_eq_of_isL2 hL2base]
    exact Or.inl hL2base
  rcases P.dichotomy with ⟨hXeq, x, hxM, hKx⟩ | ⟨hXeq, hLn, hKn⟩
  · have hXsup : UC22.conjClosure D.M L = L ⊔ CFSG.Quasithin.conjSubgroup L x := by
      rw [hXeq, hKx]
    have hne : UC22.conjClosure D.M L ≠ L := by
      intro hXL
      have hKle : K ≤ L := by
        calc K ≤ L ⊔ K := le_sup_right
          _ = UC22.conjClosure D.M L := hXeq.symm
          _ = L := hXL
      have hcard : Nat.card ↥K = Nat.card ↥L := by
        rw [hKx, CFSG.Quasithin.conjSubgroup]
        exact Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective
      exact P.ne_L (Subgroup.eq_of_le_of_card_ge hKle (by rw [hcard]))
    refine ⟨orbitClosure_imageBar2_sup_imageBar2_eq_top P.data.hyp.hL.1 hxM hXsup hne rfl, ?_⟩
    intro T' hT'
    have hshapes := hasComponentShapes_bar2_sup P.data.hyp.hL.1 hxM hXsup hne rfl hL2
    have hshapesTop : CFSG.LocalAnalysis.WeakClosure81.HasComponentShapes
        ↥(⊤ : Subgroup (Bar2 (UC22.conjClosure D.M L ⊔ D.T))) (S17.nOf L) :=
      CFSG.LocalAnalysis.WeakClosure81.hasComponentShapes_of_mulEquiv
        Subgroup.topEquiv.symm hshapes
    exact CFSG.LocalAnalysis.WeakClosure81.compFactorAutInF_of_hasComponentShapes
      hT'.isPGroup hshapesTop hKc
  · have hKH : L ≤ L ⊔ D.T := le_sup_left
    have hTsyl : IsSylowIn 2 D.T (L ⊔ D.T) := TwelveShort.isSylowIn_of_le D le_sup_right
    have hKnH : (L.subgroupOf (L ⊔ D.T)).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr ?_
      exact (sup_le P.mem_calC_L.1.le D.sylowM.le).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer P.mem_calC_L.1.le).mp hLn)
    have hperf : ⁅L, L⁆ = L := P.data.hyp.hL.1.2.1
    have hsimple : IsSimpleGroup (Bar2 L) :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.isSimpleGroup_bar2_of_isAlt_five c.alt
    have hgen : orbitClosure (imageBar2 (L ⊔ D.T) L) (imageBar2 (L ⊔ D.T) D.T) ⊔
        imageBar2 (L ⊔ D.T) D.T = ⊤ := by
      have hsupImg : imageBar2 (L ⊔ D.T) L ⊔ imageBar2 (L ⊔ D.T) D.T = ⊤ := by
        rw [← Subgroup.map_sup,
          ← Subgroup.subgroupOf_sup (le_sup_left : L ≤ L ⊔ D.T) (le_sup_right : D.T ≤ L ⊔ D.T),
          Subgroup.subgroupOf_self,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
      have h1 : imageBar2 (L ⊔ D.T) L ⊔ imageBar2 (L ⊔ D.T) D.T ≤
          orbitClosure (imageBar2 (L ⊔ D.T) L) (imageBar2 (L ⊔ D.T) D.T) ⊔
            imageBar2 (L ⊔ D.T) D.T :=
        sup_le_sup (le_orbitClosure _ _) le_rfl
      rw [hsupImg] at h1
      exact top_le_iff.mp h1
    refine ⟨?_, ?_⟩
    · rw [hXeq]
      exact hgen
    · rw [hXeq]
      intro T' hT'
      obtain ⟨⟨e⟩, hCnorm, hCsimple, hCnc, -, hCcent, hquot⟩ :=
        fstar_imageBar2_of_normal hKH hKnH hTsyl rfl hperf hsimple
      have hshapeC : IsL2 ↥(imageBar2 (L ⊔ D.T) L) 2 ∨
          IsSz ↥(imageBar2 (L ⊔ D.T) L) 2 :=
        Or.inl (LieModel.of_mulEquiv e hL2base)
      have hshapes : CFSG.LocalAnalysis.WeakClosure81.HasComponentShapes
          (Bar2 (L ⊔ D.T)) 2 :=
        CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.hasComponentShapes_of_normal_direct
          hCnorm hquot {imageBar2 (L ⊔ D.T) L}
          (fun A hA => by rw [Finset.mem_singleton] at hA; rw [hA])
          (fun A hA => by
            rw [Finset.mem_singleton] at hA; subst hA
            rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top)
          (fun A hA => by rw [Finset.mem_singleton] at hA; rw [hA]; exact hCsimple)
          (fun A hA => by rw [Finset.mem_singleton] at hA; rw [hA]; exact hCnc)
          (fun A hA B hB hne => by
            rw [Finset.mem_singleton] at hA hB
            exact absurd (hA.trans hB.symm) hne)
          (by simp) (fun A hA => by rw [Finset.mem_singleton] at hA; rw [hA]; exact hshapeC)
      rw [S17.nOf_eq_of_isL2 hL2base]
      have hshapesTop : CFSG.LocalAnalysis.WeakClosure81.HasComponentShapes
          ↥(⊤ : Subgroup (Bar2 (L ⊔ D.T))) 2 :=
        CFSG.LocalAnalysis.WeakClosure81.hasComponentShapes_of_mulEquiv
          Subgroup.topEquiv.symm hshapes
      exact CFSG.LocalAnalysis.WeakClosure81.compFactorAutInF_of_hasComponentShapes
        hT'.isPGroup hshapesTop hKc

theorem r18_4At
    (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G) (h : Hyp18 D V₀ V p L)
    (h1768 : S17.R17_68At D V₀ V)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h127 : R127 D)
    (h119 : R119W D) (h77 : W4Lem7_7) (h111 : W3Thm111 G) (h43c : W3Lem45_2Chief)
    (hW144 : W4Thm14_4) (h1214 : F12.R1214 D)
    (hKproper : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G)
    (hSg : UC6S846.SigmaStd D)
    (h76 : UC22.F07.R76Sig D) (h614 : UC6.R6_14 D) (hW612 : W3Lem612 G)
    (h1219 : D.sig = D.sig1)
    (h1513 : R15_13Small D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h8107 : F08.R8107 D) (h919 : Inputs1719.NineNineteenA5.R9_19A5 D)
    (h922 : PartOne.R9_22sp5 D)
    (h914 : PartOne.R9_14S D) :
    R18_4At D V₀ V p L := by
  have hKc : K_L2SzAutRank := k_L2SzAutRank_holds
  have hK1 : K_OmegaPlusFour_twoNat_inv := k_OmegaPlusFour_twoNat_inv_holds
  have hK2 : K_OmegaPlusFour_twoNat_scalar := k_OmegaPlusFour_twoNat_scalar_holds
  intro hA5
  obtain ⟨hp, c⟩ := A5Data18.of_hyp18 h h1768 hA5
  subst hp
  have hV : IsElemAbelian 2 V := c.hyp.hyp125.isElemAbelian
  have hp125 : Hyp125 D V₀ V := c.hyp.hyp125
  obtain ⟨K, ⟨P⟩⟩ := c.exists_second_pair h1768
  have h182 : R18_2At D V₀ V 5 L c.hyp :=
    P.r18_2At hx h61 h127 h1114 h162 h126 hTor h1482 h1669 h77
  obtain ⟨hgen, hcf⟩ := gapInputs_of_pair c P hKc
  have hg : Gap_18_4_Delta D V₀ V L c :=
    gap_18_4_Delta_of_case c h61 h43c hgen hcf hKc h1768 h127
  have hV0 : V₀ = ⊥ := A5Data18.v0_eq_bot c h182 h1669 hg
  have hnum := P.numerics_gen h182 h1669 hg hx h127 h61 h126 h111 h119 h77
  have hNW := P.normalizer_wi_one_gen h182 h1669 hg hx h127 h61 h111 h119 h77
  have hW1 : ⁅E3.wClos V 1 D.T, V⁆ = ⊥ :=
    P.wOne_commute_gen h182 h1669 hg h111 h127 h119 h77
  have hU := P.uniqueMax_sup_wOne_of_inputs hV0 h61 h127 h111 h1669 hSg h8107 h919 h922
    h914 hW1 hNW.2
  have hbne := P.barSub_ne_bot_gen h182 h1669 hg h127 hU hW1
  have hfix := P.fixV_eq_bot_gen h182 h1669 hg h61 hU.1 hW1 hnum.2.2.2
  let C : A5Config18 D V₀ V L K :=
    { pair := P
      v0 := hV0
      numerics := hnum
      normalizerW := hNW.1
      uniqueMaxW := hNW.2
      uniqueMaxL := hU.1
      uniqueMaxK := hU.2
      barSubL := hbne.1
      barSubK := hbne.2
      fixV := hfix }
  subst hV0
  have hMS : D.M ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil hp125.pairFacts.le_normalizer (by simpa using hp125.pairFacts.le_normalizer₀)
  have hKGopen : CFSG.Open.IsKGroup ↥(Mbar D.M (⊥ : Subgroup G) V C.elemAbelian) :=
    isKGroup_mbar D C.elemAbelian hMS
  have hKG : CFSG.IsKGroup ↥(Mbar D.M (⊥ : Subgroup G) V C.elemAbelian) :=
    CFSG.Assembly.kGroupAllSimple_of_kGroupNonab_of_catalogImp
      (fun X _ _ _ _ h => h) CFSG.Assembly.inCatalog_isoInvariant
      CFSG.Assembly.inCatalog_containsAbelianSimple hKGopen
  have hO2 : O2Trivial (Mbar D.M (⊥ : Subgroup G) V C.elemAbelian) :=
    fun Q hQ hN h2 => s15_Kbar_eq_bot_of_normal_isPGroup D hp125 hQ hN h2
  have hYne : Mbar D.M (⊥ : Subgroup G) V C.elemAbelian ≠ ⊥ := by
    intro hbot
    exact C.barSubL (le_bot_iff.mp (hbot ▸
      barSub_mono (⊥ : Subgroup G) V C.elemAbelian P.mem_calC_L.1.le))
  have hBasic : IsBasicModule (Mbar D.M (⊥ : Subgroup G) V C.elemAbelian) :=
    TwelveSeventeen.isBasicModule D hx h61 h127 h1214 hp125 hYne
  have hcompL : IsComponentOf (barSub (⊥ : Subgroup G) V C.elemAbelian L)
      (Mbar D.M (⊥ : Subgroup G) V C.elemAbelian) :=
    barSub_mem_compBar_of_ne_bot hp125 P.mem_calC_L C.barSubL
  have hcompK : IsComponentOf (barSub (⊥ : Subgroup G) V C.elemAbelian K)
      (Mbar D.M (⊥ : Subgroup G) V C.elemAbelian) :=
    barSub_mem_compBar_of_ne_bot hp125 P.mem_calC C.barSubK
  have hne : barSub (⊥ : Subgroup G) V C.elemAbelian L ≠
      barSub (⊥ : Subgroup G) V C.elemAbelian K := C.barSub_ne
  have hLKM : L ⊔ K ≤ D.M := sup_le P.mem_calC_L.1.le P.mem_calC.1.le
  have hXnorm : ((barSub (⊥ : Subgroup G) V C.elemAbelian L ⊔
      barSub (⊥ : Subgroup G) V C.elemAbelian K).subgroupOf
      (Mbar D.M (⊥ : Subgroup G) V C.elemAbelian)).Normal := by
    have hbsup : barSub (⊥ : Subgroup G) V C.elemAbelian (L ⊔ K) =
        barSub (⊥ : Subgroup G) V C.elemAbelian L ⊔
          barSub (⊥ : Subgroup G) V C.elemAbelian K :=
      s16c7_barSub_sup (⊥ : Subgroup G) V C.elemAbelian
        (P.mem_calC_L.1.le.trans hMS) (P.mem_calC.1.le.trans hMS)
    rw [← hbsup]
    exact barSub_subgroupOf_mbar_normal C.elemAbelian hLKM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLKM).mp P.sup_normal)
  rcases C.trichotomy_all hW144 hKG hO2 hBasic hcompL hcompK hne hXnorm hx h61 h126 h111
    h127 h119 h77 with h1 | h2 | h3
  · exact A5Config18.false_of_case_one C h1 h1669 h111 h1513
  · exact A5Config18.false_of_case_two C h2 hK1 hK2 h111 h61 hSg hKproper
  · exact A5Config18.false_of_case_three C h3 k_OmegaFour_scalarOfLine_holds h76 h614 h111
      hW612 h61 hx hSg h1219 h1768

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

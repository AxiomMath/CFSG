module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Assembly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenClosedR
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFifteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenElevenRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFive
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10K101
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourteenD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyOneBorel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSixteenProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenNineteenProof
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenGlueFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenGlueOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.UC22.F10 (LieAutVocab10)
open CFSG.LocalAnalysis.RankThreeTheoremC (KFactCentralOmega)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

section Certificates


theorem sec19_false_of_stages (D : Data G) (hσ : D.sig.Nonempty) {V₀ V : Subgroup G}
    (h125 : Hyp125 D V₀ V) (hbig : 1 < mSub V₀)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h1 : ∀ (p : ℕ) (L : Subgroup G) (h : Hyp19 D V₀ V p L), R19_1At D V₀ V p L h)
    (h9 : ∀ (p : ℕ) (L : Subgroup G) (h : Hyp19 D V₀ V p L), R19_9At D V₀ V p L h)
    (h67 : S17.R17_67At D V₀ V) (h42 : S17.R17_42At D V₀ V)
    (h3 : S17.R17_3At D V₀ V)
    (h57 : S17.R17_57At D V₀ V) (h8107 : F08.R8107 D)
    (h641 : S17.R17_64_1At D V₀ V) (h642 : S17.R17_64_2At D V₀ V)
    (h643 : S17.R17_64_3At D V₀ V) (h661 : S17.R17_66_1At D V₀ V)
    (h171 : ∀ (hV : Hyp125 D V₀ V), (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) →
      S17.R17_1At D V₀ V hV)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) (hDE : DataExt D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h640 : UC6.R6_40_1 D)
    (h638 : UC6.R6_38 D) (h71 : F07.R71 D) (h72 : F07.R72 D)
    (htorus : K_19_glue4_torus) (hK : K_BorelOvergroup)
    (hK1911 : K_19_11_torusFixed) (hK13 : K_19_13_autOmega)
    (hW1 : W7_9_1_4) (hW4 : W7_9_4c) (hmin : K_19_18_minNormal) (hlevi : K_19_18_levi)
    (hoddK : K_19_20_oddAut) (hJ0 : K_19_20_J0shape)
    (hforce : K_19_20_force) (h20b : Gap19_20b D) (hK21 : K_19_21_BN)
    (hL21 : K_19_21_levi) (hBor : K_L2_oddAbelianBorel)
    (hN : CFSG.RankThree.PartTwo.Sec19.Asc81bNineThreeNat)
    (h85 : CFSG.AGLEmbedding.Asc81bEightFive) (hcen : K_19_16_census)
    (hL16 : Gap19_16_L D) (hg19 : Gap19_19 D)
    (h332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hCO : KFactCentralOmega)
    (hK1 : K_19_26_rankOne)
    (hK25 : K_19_25_torusCent) (hKf : K_19_25_noL2SzSection) (hK28 : K_19_28_torusAutomizer)
    (Vaut : LieAutVocab10)
    (hK104 : CFSG.LocalAnalysis.UniquenessCase.UC22.F10.K104 Vaut)
    (hK105 : CFSG.LocalAnalysis.UniquenessCase.UC22.F10.K105)
    (hcat : K_CatalogModels) (hTits : K_TitsOddPrimes)
    (h49 : W10_4_9) (hsmall : K_19_glue7_L2small) (hJR : K_19_JRgen)
    (hCh2 : Chev2StarGen) :
    False := by
  classical
  have h11 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), R19_11At D V₀ V p L A t B r h :=
    nineteen_eleven_of_K D h61 h42 hK1911
  have h21c : Gap19_21c D := gap19_21c_of D hK21 (gap19_21_borel_of_K D hL21 hBor)
  have hgap185 : Gap19_18_5 D := gap19_18_5_of_K D hlevi
  have h15 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_15At D V₀ V p L A t B r Y N Dsub H S h :=
    fun p L A t B r Y N Dsub H S h => nineteen_fifteen D h640 h
  have h16 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_16At D V₀ V p L A t B r Y N Dsub H S h :=
    fun p L A t B r Y N Dsub H S h =>
      nineteen_sixteen h (h11 p L A t B r h.ctx) (h15 p L A t B r Y N Dsub H S h) hN h85 hcen
        hL16
  have A12 := r19_A12 D h1 h42 h641 h642 h643 h8107
  have A13 := r19_A13 D h42 hK13 A12
  have A17 := r19_A17 D (fun p L A t B => h16 p L A t B 3) A13
  have A18 := r19_A18 D h11 h15 A17 A12 hoddK h20b hW1 hW4 hmin hgap185
  have A19 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
      R19_19At D V₀ V p L A t B 3 Y N Dsub H S h :=
    fun p L A t B Y N Dsub H S h =>
      nineteen_nineteen_of D h (A17 p L A t B Y N Dsub H S h) h42 hg19
  have A201 := r19_A201 D (fun p L A t B => h16 p L A t B 3) A17 A18 A19 A12 A13 hoddK hJ0
    hforce h20b
  have A202 := r19_A202 D A17 A19 A201 A12 A13 hoddK hforce h20b
  have A21 := r19_A21c D A12 A17 A201 A19 h21c
  have Aglue : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (h : Ctx19_10 D V₀ V p L A t B 3) (Y N : Subgroup G)
      (hY : Y ∈ muStarSet D B) (hN : N ∈ calMOf Y ∧ N ≠ D.M),
      R19_glue_5At D V₀ V p L A t B 3 h Y N hY hN :=
    fun p L A t B h Y N hY hN =>
      nineteen_glue_five_of_asc81b D h (h11 p L A t B 3 h) hW1 h640
        (CFSG.AGLEmbedding.asc81bEightFour_of_factorization
            CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved) Y N hY hN
  have A14 := r19_A14 D Aglue A18 ⟨A201, A202⟩ A21
  have A22 := r19_A22 D A12 h61 h127 h171 h1669 h42 hK h661
  have A23 := r19_A23 D A14
  have A12wc := r19_A12wc D h1 h42 h641 h642 h643 A12
  have A26 := r19_A26 D A12 A12wc A13 h61 h127 h42 h661 h332 hCO hK1
  have hodd := r19_odd_any D A22 A23 A26
  have C12 := r19_C12 D hodd h1 h42 h641 h642 h643 h8107
  have C13 := r19_C13 D hodd
  have C17 := r19_C17 D h16 C13
  have C18 := r19_C18 D h11 h15 C17 C12 hoddK h20b hW1 hW4 hmin hgap185
  have C19 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_19At D V₀ V p L A t B r Y N Dsub H S h :=
    fun p L A t B r Y N Dsub H S h =>
      nineteen_nineteen_of D h (C17 p L A t B r Y N Dsub H S h) h42 hg19
  have C201 := r19_C201 D h16 C17 C18 C19 C12 C13 hoddK hJ0 hforce h20b
  have C202 := r19_C202 D C17 C19 C201 C12 C13 hoddK hforce h20b
  have C21 := r19_C21c D C12 C17 C201 C19 h21c
  have Cglue : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r) (Y N : Subgroup G)
      (hY : Y ∈ muStarSet D B) (hN : N ∈ calMOf Y ∧ N ≠ D.M),
      R19_glue_5At D V₀ V p L A t B r h Y N hY hN :=
    fun p L A t B r h Y N hY hN =>
      nineteen_glue_five_of_asc81b D h (h11 p L A t B r h) hW1 h640
        (CFSG.AGLEmbedding.asc81bEightFour_of_factorization
            CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved) Y N hY hN
  have C14 := r19_C14 D Cglue C18 ⟨C201, C202⟩ C21
  have C22 := r19_C22 D C12 h61 h127 h171 h1669 h42 hK h661
  have C23 := r19_C23 D C14
  have C26 := r19_C26 D hodd
  have C27 := r19_C27 D C26
  have C28 := r19_C28 D C26 C14 C12 h3 h42 h638 hSg h71 h72 hK25 hKf hK28
  have C29 := r19_C29 Vaut D C12 C26 C27 C28 F10.k101_holds hK104 hK105 hcat hTits
  have Cglue7 := r19_Cglue7 Vaut D C12 C26 C27 C28 h61 h127 h42 h661 h49 hsmall hJR hCh2
  have hglue1 : R19_glue_1At D V₀ V h125 hbig hσ :=
    nineteen_glue_one D (fun _ _ _ => S17.seventeen_sixtyfive D h42 h641 h642 h643) V₀ V
      h125 hbig hσ
  have h10 : ∀ (p : ℕ) (L : Subgroup G) (h : Hyp19 D V₀ V p L),
      R19_10At D V₀ V p L h :=
    fun p L h =>
      nineteen_ten_of D h (h1 p L h) (h9 p L h) h67 h42 h641 h642 h643 h57 hSg hDE
  have hglue4 : ∀ (p : ℕ) (L : Subgroup G) (h : Hyp19 D V₀ V p L)
      (h1910 : Setting1910 D V₀ V p L), R19_glue_4At D V₀ V p L h h1910 :=
    fun p L h h1910 => r19_glue_4At_of_K D h h1910 h42 htorus
  exact sec19_false_at D hσ h125 hbig hglue1 h10 hglue4 C22 C23 Vaut C29 Cglue7

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

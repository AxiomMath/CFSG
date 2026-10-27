module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.AssemblyR
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.GuardedGapsNineteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.UC22.F10 (LieAutVocab10)

variable {G : Type} [Group G] [Finite G]

section Certificates


theorem sec19ContraOf1669_of_guardedStages (D : Data G) (hσ : D.sig.Nonempty)
    (h1 : ∀ (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G) (h : Hyp19 D V₀ V p L),
      (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) → R19_1At D V₀ V p L h)
    (h9 : ∀ (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G) (h : Hyp19 D V₀ V p L),
      (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) → R19_9At D V₀ V p L h)
    (h67 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) →
      S17.R17_67At D V₀ V)
    (h42 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) →
      S17.R17_42At D V₀ V)
    (h57 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) →
      S17.R17_57At D V₀ V)
    (h8107 : F08.R8107 D)
    (h641 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) →
      S17.R17_64_1At D V₀ V)
    (h642 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) →
      S17.R17_64_2At D V₀ V)
    (h643 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) →
      S17.R17_64_3At D V₀ V)
    (h661 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) →
      S17.R17_66_1At D V₀ V)
    (h171 : ∀ (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V),
      (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) → S17.R17_1At D V₀ V hV)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) (hDE : DataExt D)
    (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h640 : UC6.R6_40_1 D)
    (h638 : UC6.R6_38 D) (h71 : F07.R71 D) (h72 : F07.R72 D)
    (htorus : K_19_glue4_torus) (hK : K_BorelOvergroup)
    (hK1911 : K_19_11_torusFixed) (hK13 : K_19_13_autOmega)
    (hW1 : W7_9_1_4) (hW4 : W7_9_4c) (hmin : K_19_18_minNormal)
    (hlevi : K_19_18_levi)
    (hoddK : K_19_20_oddAut) (hJ0 : K_19_20_J0shape)
    (hforce : K_19_20_force)
    (h3 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) →
      S17.R17_3At D V₀ V)
    (hK21 : K_19_21_BN)
    (hL21 : K_19_21_levi) (hBor : K_L2_oddAbelianBorel)
    (hN : CFSG.RankThree.PartTwo.Sec19.Asc81bNineThreeNat)
    (h85 : CFSG.AGLEmbedding.Asc81bEightFive) (hcen : K_19_16_census)
    (hL16 : Gap19_16_L D) (hg19 : Gap19_19 D)
    (h332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hCO : CFSG.LocalAnalysis.RankThreeTheoremC.KFactCentralOmega) (hK1 : K_19_26_rankOne)
    (hK25 : K_19_25_torusCent) (hKf : K_19_25_noL2SzSection) (hK28 : K_19_28_torusAutomizer)
    (Vaut : LieAutVocab10)
    (hK104 : CFSG.LocalAnalysis.UniquenessCase.UC22.F10.K104 Vaut)
    (hK105 : CFSG.LocalAnalysis.UniquenessCase.UC22.F10.K105)
    (hcat : K_CatalogModels) (hTits : K_TitsOddPrimes)
    (h49 : W10_4_9) (hsmall : K_19_glue7_L2small) (hJR : K_19_JRgen)
    (hCh2 : Chev2StarGen) :
    Sec19ContraOf1669 D := by
  intro V₀ V h125 hcard hbound
  have hbig : 1 < mSub V₀ := Nat.lt_of_not_le fun h =>
    absurd ((S18.mSub_le_one_iff (hyp123_pairFacts h125.1).elemAbelian₀).1 h) (by omega)
  exact sec19_false_of_stages D hσ h125 hbig hbound
    (fun p L h => h1 V₀ V p L h hbound) (fun p L h => h9 V₀ V p L h hbound)
    (h67 V₀ V h125 hbound) (h42 V₀ V h125 hbound) (h3 V₀ V h125 hbound)
    (h57 V₀ V h125 hbound) h8107
    (h641 V₀ V h125 hbound) (h642 V₀ V h125 hbound) (h643 V₀ V h125 hbound)
    (h661 V₀ V h125 hbound) (h171 V₀ V) hSg hDE h61 h127 h640 h638 h71 h72 htorus hK hK1911
    hK13 hW1 hW4 hmin hlevi
    hoddK hJ0 hforce (gap19_20b_guarded_of D h3 h42 h1 h641 h642 h643 V₀ V h125 hbig hbound)
    hK21
    hL21 hBor hN h85 hcen hL16 hg19
    h332 hCO hK1 hK25 hKf hK28
    Vaut hK104 hK105 hcat hTits h49 hsmall hJR hCh2

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

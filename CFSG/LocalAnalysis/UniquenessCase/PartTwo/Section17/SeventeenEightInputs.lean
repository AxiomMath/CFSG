module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEightCases
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEightBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourElevenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenDiag
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixFix
public import CFSG.Quasithin.EmptyFaithful.R3c3Rank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_thin8_of_isL3Odd {L : Subgroup G} (hL3 : IsL3Odd (Bar2 L) 3) :
    ¬ F08.Thin8 L :=
  not_thin8_of_two_le_pRank Nat.prime_three (by norm_num)
    (two_le_pRank_of_bar2 Nat.prime_three (by norm_num)
      (CFSG.Quasithin.R3c3.two_le_pRank_three_isPSL_three_three
        (CFSG.Blueprint.LieModel.statedClassicalModel hL3 (by decide))))

theorem inFSq_sup_T_of_isL3Odd (h411 : W4Lem4_11Prime) {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) (hL3 : IsL3Odd (Bar2 L) 3)
    (hTL : D.T ≤ Subgroup.normalizer (L : Set G)) :
    CFSG.LocalAnalysis.WeakClosure81.InFSq 1 (L ⊔ D.T) := by
  classical
  let H : Subgroup G := L ⊔ D.T
  have hLH : L ≤ H := le_sup_left
  have hTH : D.T ≤ H := le_sup_right
  have hHnorm : H ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hTL
  have hLn : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hHnorm
  have hTsyl : IsSylowIn 2 D.T H := TwelveShort.isSylowIn_of_le D hTH
  have hsimple : IsSimpleGroup (Bar2 L) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL3
  obtain ⟨⟨eC⟩, hCnormal, -, hCnab, hFstar, -, -⟩ :=
    S18.fstar_imageBar2_of_normal (H := H) (K := L) (T := D.T)
      hLH hLn hTsyl (by rfl) hL.2.1 hsimple
  have hTsylC : IsSylowIn 2 (S18.imageBar2 H D.T) ⊤ :=
    S18.isSylowIn_imageBar2 hTsyl
  have hsupC : S18.imageBar2 H L ⊔ S18.imageBar2 H D.T = ⊤ := by
    rw [← S18.imageBar2_sup hLH hTH]
    rw [show L ⊔ D.T = H from rfl, S18.imageBar2_self]
  have hCcard : Nat.card ↥(S18.imageBar2 H L) = 5616 := by
    calc Nat.card ↥(S18.imageBar2 H L) = Nat.card (Bar2 L) :=
          (Nat.card_congr eC.toEquiv).symm
      _ = 5616 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_three
          (CFSG.Blueprint.LieModel.statedClassicalModel hL3 (by decide))
  have hCnab' : ∃ a b : ↥(S18.imageBar2 H L), a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hCnab ⟨⟨fun a b => h a b⟩⟩
  have hS : FourElevenSetting (Bar2 H) (S18.imageBar2 H L) 3 :=
    { normal := hCnormal, fstar_eq := hFstar, prime := Nat.prime_three, ne_two := by norm_num,
      isL3 := Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv eC hL3), nonabelian := hCnab',
      not_psu33 := fun _ h33 => by
        have hcard3 : Nat.card ↥(S18.imageBar2 H L) = 6048 :=
          CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three
            (CFSG.Blueprint.LieModel.statedClassicalModel h33 (by decide))
        omega
      sup_eq_top := ⟨_, hTsylC, hsupC⟩ }
  rcases h411 (Bar2 H) (S18.imageBar2 H L) 3 hS with hInF | ⟨h35, -⟩
  · exact CFSG.LocalAnalysis.WeakClosure81.inF_top_of_inFGroup 1 hInF
  · exact absurd h35 (by norm_num)

theorem gap17_8_inFSq_of (h411 : W4Lem4_11Prime) (D : Data G) {V₀ V : Subgroup G} :
    ∀ (hV : Hyp125 D V₀ V) (L : Subgroup G), L ∈ calC D.M → IsL3Odd (Bar2 L) 3 →
      D.T ≤ Subgroup.normalizer (L : Set G) → D.k = 1 →
      CFSG.LocalAnalysis.WeakClosure81.InFSq 1 (L ⊔ D.T) := by
  intro hV L hL hL3 hTL hk
  exact inFSq_sup_T_of_isL3Odd h411 hL hL3 hTL

theorem classicalEvenAltG2_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : CFSG.LocalAnalysis.UniquenessCase.UC22.F12.ClassicalEvenAltG2 Y) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F12.ClassicalEvenAltG2 X := by
  unfold CFSG.LocalAnalysis.UniquenessCase.UC22.F12.ClassicalEvenAltG2 at h ⊢
  rcases h with ⟨hq, t, m, f, ht, hLie⟩ | ⟨hq, a, hAlt⟩ | ⟨g, hG2⟩
  · let ec : (X ⧸ Subgroup.center X) ≃* (Y ⧸ Subgroup.center Y) :=
      QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e
        (Subgroup.map_center_eq e)
    exact Or.inl ⟨CFSG.IsQuasisimple.of_mulEquiv e hq, t, m, f, ht,
      CFSG.Blueprint.LieModel.of_mulEquiv ec.symm hLie⟩
  · obtain ⟨φ⟩ := hAlt
    let ec : (X ⧸ Subgroup.center X) ≃* (Y ⧸ Subgroup.center Y) :=
      QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e
        (Subgroup.map_center_eq e)
    exact Or.inr (Or.inl ⟨CFSG.IsQuasisimple.of_mulEquiv e hq, a,
      ⟨ec.trans φ⟩⟩)
  · exact Or.inr (Or.inr ⟨g, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hG2⟩)

theorem isG2Der_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ}
    (h : F08.IsG2Der Y n) : F08.IsG2Der X n := by
  unfold F08.IsG2Der at h ⊢
  rcases h with ⟨rfl, hLie⟩ | ⟨hn, hG2⟩
  · exact Or.inl ⟨rfl, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hLie⟩
  · exact Or.inr ⟨hn, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hG2⟩

theorem classicalEvenAltG2Der_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : ClassicalEvenAltG2Der Y) : ClassicalEvenAltG2Der X := by
  unfold ClassicalEvenAltG2Der at h ⊢
  rcases h with hcl | ⟨n, hG2Der⟩
  · exact Or.inl (classicalEvenAltG2_of_mulEquiv e hcl)
  · exact Or.inr ⟨n, isG2Der_of_mulEquiv e hG2Der⟩

theorem fixV_dichotomy_of_not_thin (D : Data G) {V₀ V : Subgroup G}
    (h869 : F08.R869 D) (h127 : R127 D) (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    (hV : Hyp125 D V₀ V) {L : Subgroup G} (hL : L ∈ calC D.M) (hnt : ¬ F08.Thin8 L) :
    fixV (barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L)) = ⊥ ∨
      (V₀ = ⊥ ∧ ClassicalEvenAltG2Der (UC22.Bar2 L)) := by
  have hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥ := by
    rcases eq_or_ne V₀ ⊥ with hV0 | hV0
    · subst hV0
      exact barSub_ne_bot_of_not_thin_bot h869 h127 hV hL hnt
    · exact barSub_ne_bot_of_not_thin hV
        (ElevenNine.c117_of_hyp11 D h869 (Hyp125.hyp11 h127 hV)) hL hnt
  have hcomp : F12.IsComponentModO2 D.M (L ⊔ pCoreOf 2 D.M) :=
    isComponentModO2_sup_pCoreOf_of_mem_calC hL
  have hUK : UniqueMax D.M ((L ⊔ pCoreOf 2 D.M) ⊔ D.T) :=
    uc22p22u_uniqueMax_mono D
      (sup_le ((le_sup_left : L ≤ L ⊔ pCoreOf 2 D.M).trans le_sup_left) le_sup_right)
      (sup_le (sup_le hL.1.le (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)) D.sylowM.le)
      (Inputs1719.uniqueMax_sup_T_of_not_thin h869 hL hnt)
  have hbar : barSub V₀ V hV.isElemAbelian
      (UC22.conjClosure D.M (L ⊔ pCoreOf 2 D.M)) =
      barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L) :=
    S18.barSub_conjClosure_sup_pCoreOf hV hL.1.le
  have hH : barSub V₀ V hV.isElemAbelian
      (UC22.conjClosure D.M (L ⊔ pCoreOf 2 D.M)) ≠ ⊥ := by
    rw [hbar]
    exact TwelveTwentyThree.barSub_conjClosure_ne_bot hV.isElemAbelian hL1
  rcases twelve_twentySix D h640 hFF hV hcomp hUK hH with hfix | ⟨hV0, hcl, -⟩
  · left
    rwa [hbar] at hfix
  · right
    refine ⟨hV0, ?_⟩
    obtain ⟨e⟩ := bar2_sup_pCoreOf_mulEquiv_of_mem_calC hL
    exact classicalEvenAltG2Der_of_mulEquiv e.symm hcl

section CertifiedWrapper


theorem gap17_8_normal_of {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h17_1 : R17_1At D V₀ V hC.hyp125)
    (h17_4 : R17_4AtA D V₀ V hC.hyp125)
    (h17_7 : R17_7_1At D V₀ V L r q hC) (h127 : R127 D) (h117 : C117 D V₀ V)
    (hK : Inputs1719.K_U33SThreePair) (hK8 : Inputs1719.K_U33AutE8)
    (hgraph : Gap17_8_graphV0 D V₀ V)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) (hB : B17_8BoundTwo D V₀ V hC.hyp125)
    (h411 : W4Lem4_11Prime)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D) (h1114 : R1114 D)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h183 : W3Thm183 G) (h111 : W3Thm111 G) (h126 : R126 D) :
    Gap17_8_normal D V₀ V L r q hC := by
  have hInFSq := gap17_8_inFSq_of h411 D (V₀ := V₀) (V := V)
  intro hTL hk htype
  have hV := hC.hyp125
  rcases htype with hL3 | hU3
  · by_cases hE9 : ∃ E : Subgroup G,
        E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ Permutes E D.T
    · obtain ⟨E, hEL, hEA, hEcard, hEperm⟩ := hE9
      have hEDM : E ≤ D.M := hEL.trans (CFSG.Quasithin.A3.subnormal_le hC.memL.1)
      have hEne : E ≠ ⊥ := by
        intro hbot
        have h1 : Nat.card E = 1 := by rw [hbot, Subgroup.card_bot]
        omega
      have hEp : IsPGroup 3 ↥E := IsElemAbelian.isPGroup hEA
      have hEexp : ∀ x ∈ E, x ^ 3 = 1 := hEA.2
      have hEnc : ¬ IsCyclic ↥E :=
        CFSG.Quasithin.H13.U3.not_isCyclic_of_exponent_three (by rw [hEcard]) hEexp
      exact false_of_k_eq_one_of_permutes h17_1 hk ⟨E, hEDM, hEne, hEp, hEexp, hEnc, hEperm⟩
    · have hcard : Nat.card V₀ ≤ 4 :=
        hgraph hV L hC.memL hL3 hTL hk
          (fun E hEL hEA hEcard hEperm => hE9 ⟨E, hEL, hEA, hEcard, hEperm⟩)
      have hU : UniqueMax D.M L := h17_7
      have hm3 : MBarGT D.M V₀ V 3 := h1669 hcard
      have hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥ :=
        barSub_ne_bot_of_uniqueMax h127 hV h117 hC.memL hU
      have hU' : UniqueMax D.M (L ⊔ D.T) :=
        uc22p22u_uniqueMax_mono D le_sup_left (sup_le hC.memL.1.le D.sylowM.le) hU
      have hUc : UniqueMax D.M (UC22.conjClosure D.M L) :=
        uc22p22u_uniqueMax_mono D (TwelveTwentyThree.le_conjClosure D.M L)
          (TwelveTwentyThree.conjClosure_le hC.memL.1.le) hU
      have hb : bBar (UC22.conjClosure D.M L) D.M V₀ V hV.isElemAbelian ≤ 2 :=
        hB L hC.memL hL3
      have hInFSq' : CFSG.LocalAnalysis.WeakClosure81.InFSq 1 (L ⊔ D.T) :=
        hInFSq hV L hC.memL hL3 hTL hk
      have hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
        by_contra hns
        have h2 : D.k = 2 := (Data.k_eq_two_iff D).2 hns
        omega
      have hbar3 : 3 ∣ Nat.card (Bar2 L) := by
        have hcl : CFSG.Open.StatedClassicalModel (Bar2 L) .PSL 3 3 1 :=
          CFSG.Blueprint.LieModel.statedClassicalModel hL3 (by decide)
        have h5616 : Nat.card (Bar2 L) = 5616 :=
          CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_three hcl
        rw [h5616]
        norm_num
      have h3H : 3 ∣ Nat.card ↥(L ⊔ D.T) := by
        have h3L : 3 ∣ Nat.card ↥L := by
          rw [card_eq_card_pCoreOf_mul_card_bar2 (G := G) L]
          exact dvd_mul_of_dvd_right hbar3 _
        exact h3L.trans (Subgroup.card_dvd_of_le le_sup_left)
      have hO2 : ∀ g : G, g ∉ D.M → ¬ twoResidual (L ⊔ D.T) ≤ conjSubgroup D.M g :=
        CFSG.GroupTheory.twoResidual_not_le_conjSubgroup_of_isStronglyPEmbedded Nat.prime_three
          (by norm_num) (sup_le hC.memL.1.le D.sylowM.le) h3H hsp3
      exact false_of_bBar_le_two D hx h61 h66 h127 h1114 h162 hTor h1482 h183 h111 h126 hk
        hV hC.memL hL1 hU' hUc hInFSq' hb hm3 hO2
  · exact gap17_8_psu33 hC h17_4 h127 h117 h17_7 hK hK8 hTL hk hU3

theorem seventeen_eight_of {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h880 : F08.R880 D)
    (h17_1 : R17_1At D V₀ V hC.hyp125) (h17_4 : R17_4AtA D V₀ V hC.hyp125)
    (h17_7 : R17_7_1At D V₀ V L r q hC) (h127 : R127 D) (h117 : C117 D V₀ V)
    (hU33 : Inputs1719.K_U33Local) (hL33 : Inputs1719.K_L33Local)
    (hK : Inputs1719.K_U33SThreePair) (hK8 : Inputs1719.K_U33AutE8)
    (hgraph : Gap17_8_graphV0 D V₀ V)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) (hB : B17_8BoundTwo D V₀ V hC.hyp125)
    (h411 : W4Lem4_11Prime)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D) (h1114 : R1114 D)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h183 : W3Thm183 G) (h111 : W3Thm111 G) (h126 : R126 D) :
    R17_8At D V₀ V L r q hC :=
  seventeen_eight hC h880
    (gap17_8_normal_of hC h17_1 h17_4 h17_7 h127 h117 hK hK8 hgraph h1669 hB h411
      hx h61 h66 h1114 h162 hTor h1482 h183 h111 h126)
    (gap17_8_nonnormal_of hC h17_1 hU33 hL33)

end CertifiedWrapper

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

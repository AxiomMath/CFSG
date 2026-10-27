module

public import CFSG.RankThree.PartTwo.Sec8.Hering88NG2TwoResidual
import CFSG.HardMathSupport.Lang.E27Lie.TrialityTwo
public import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofD4N
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPairModels

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem card_projSL_two_eight : Nat.card (projSL 2 (GaloisField 2 3)) = 504 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  obtain ⟨e⟩ := KFacts.nonempty_sl2_mulEquiv_projSL (F := GaloisField 2 3) hF
  rw [← Nat.card_congr e.toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hF]
  decide


variable {Q : Type} [Group Q] [Finite Q]

theorem card_inSubgroup_perfectResidual_of_isoGTwoEven_one {R : Subgroup Q}
    (h : IsoGTwoEven R 1) : Nat.card (inSubgroup perfectResidual R) = 6048 := by
  have h2 := card_eq_two_mul_card_inSubgroup_perfectResidual_of_isoGTwoEven_one h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hR : Nat.card R = 12096 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]
    rfl
  omega


theorem isInnerAut_of_residual_projSL (h47 : Sec4.Inputs47ClassesD4)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {a b : G}
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hb3 : b ^ 3 = 1)
    (hL1 : IsoTrialityD4 (L ⧸ aschbacherSolvableCore 3 L) 1 ∨
      IsoGTwoEven (L ⧸ aschbacherSolvableCore 3 L) (3 * 1))
    (hG2a : IsoGTwoEven (barCentralizer (Subgroup.zpowers a) L) 1)
    (hK : Nonempty (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({b} : Set G))) ≃* projSL 2 (GaloisField 2 3))) :
    KFacts.IsInnerAut (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨b, hbN⟩)) ∧
      Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨b, hbN⟩) ≠ 1 := by
  classical
  obtain ⟨eK⟩ := hK
  have hcard : Nat.card (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers b) L)) =
      504 := by
    rw [← KFacts.imageModTheta_perfectResidual_centralizer_eq hbN ⟨1, by simpa using hb3⟩,
      Nat.card_congr eK.toEquiv, card_projSL_two_eight]
  constructor
  · by_contra hout
    have hO : Sec4.InducesOuterTheta b L := ⟨hbN, hout⟩
    have key : IsoGTwoEven (barCentralizer (Subgroup.zpowers b) L) 1 ∨
        Nat.card (barCentralizer (Subgroup.zpowers b) L) = 216 := by
      rcases hL1 with hD | hG
      · obtain ⟨-, K, _, _, σ, hKc, hσ, ⟨e⟩⟩ := Item812Res7.exists_trialityD4_model hD
        have hK2 : ringChar K = 2 :=
          Item8KFacts3.ringChar_eq_two_of_card (f := 3) (by rw [hKc]; norm_num)
        have hα3 : (KFacts.inducedAutHom L e ⟨b, hbN⟩) ^ 3 = 1 :=
          KFacts.inducedAutHom_pow_eq_one L e hbN hb3
        have hαout : ¬ KFacts.IsInnerAut (KFacts.inducedAutHom L e ⟨b, hbN⟩) :=
          (KFacts.not_isInnerAut_inducedAutHom_iff L e hbN).mpr hO
        rcases h47 1 odd_one K σ hKc hσ _ hα3 hαout with ⟨β, hβ⟩ | ⟨γ, y, -, -, -, -, hPGU⟩
        · left
          obtain ⟨φ⟩ := KFacts.nonempty_barCentralizer_mulEquiv_g2_of_conj_fieldActor hK2 e hbN β hβ
          exact ⟨fixSubfield σ, inferInstance, Subtype.finite,
            KFacts.card_fixSubfield_of_cube le_rfl hKc hσ, ⟨φ⟩⟩
        · right
          have hmap := KFacts.map_barCentralizer_eq hbN e
            (Sec4.autFix (KFacts.inducedAutHom L e ⟨b, hbN⟩)) (fun z => Iff.rfl)
          let eH : ↥(barCentralizer (Subgroup.zpowers b) L) ≃*
              ↥(Sec4.autFix (KFacts.inducedAutHom L e ⟨b, hbN⟩)) :=
            (e.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
          rw [Nat.card_congr eH.toEquiv,
            CFSG.HardMathSupport.Lang.E27Lie.card_isoPGUThree le_rfl hPGU]
          norm_num
      · obtain ⟨K, _, _, hKc, ⟨e⟩⟩ := hG
        obtain ⟨-, k, _, _, hk, ⟨φ⟩⟩ :=
          KFacts.barCentralizer_mulEquiv_g2 (n := 1) one_ne_zero hKc hb3 hO e
        exact Or.inl ⟨k, inferInstance, inferInstance, hk, ⟨φ⟩⟩
    rcases key with hG2b | h216
    · rw [card_inSubgroup_perfectResidual_of_isoGTwoEven_one hG2b] at hcard
      norm_num at hcard
    · have hdvd := Subgroup.card_dvd_of_le
        (Item87Proof.residual_le (barCentralizer (Subgroup.zpowers b) L))
      rw [hcard, h216] at hdvd
      norm_num at hdvd
  · intro h1
    have htop : barCentralizer (Subgroup.zpowers b) L = ⊤ := by
      ext y
      simp only [Subgroup.mem_top, iff_true]
      rw [KFacts.mem_barCentralizer_zpowers_iff hbN, h1]
      rfl
    have hle : inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) L) ≤
        inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers b) L) :=
      KFacts.le_inSubgroup_perfectResidual (Item87Proof.isPerfect_residual _)
        (by rw [htop]; exact le_top)
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcard, card_inSubgroup_perfectResidual_of_isoGTwoEven_one hG2a] at hdvd
    norm_num at hdvd

end CFSG.RankThree.PartTwo.Sec8.Hering88N

end

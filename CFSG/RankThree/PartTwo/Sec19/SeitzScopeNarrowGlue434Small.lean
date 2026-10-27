module

public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeNarrowGlue434Seitz
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIID42
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofL3Pi
import CFSG.RankThree.PartTwo.KFacts.KS12SLCenter
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverSLThree46
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIIKit

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section CertsIII

namespace Item434SmallTwoIII

theorem false_of_d42_nine_narrow (hS : Sec19.Seitz199D4Two) {G : Type} [Group G] [Finite G]
    {A M Q : Subgroup G} (h : Ctx434Core G A M Q)
    (hL : IsSmallTwoD42 (layer G ⧸ Subgroup.center (layer G)))
    (h9 : Nat.card (A.map (layerConj G)) = 9) : False := by
  have hmod := chevalleyExceptionalModel_of_d42 hL
  have hZ : Subgroup.center (layer G) = ⊥ := center_layer_eq_bot_of_cover h
    fun E _ _ _ π hπ hC hodd =>
      CFSG.SectionRank.triality_even_perfect_odd_cover_trivial hmod π hπ hC hodd
  have eL : layer G ≃* layer G ⧸ Subgroup.center (layer G) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hmodL : CFSG.Blueprint.ChevalleyExceptionalModel (layer G) .trialityD4 2 1 :=
    CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv eL hmod
  have hexp : ∀ φ ∈ A.map (layerConj G), φ ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, h.isE27.1.2 a ha, map_one]
  have hgen := hS (layer G) (A.map (layerConj G)) hexp h9 ⟨1, hmodL⟩
  exact h.not_le (layer_le_of_closure_fixed h h9 hgen)

end Item434SmallTwoIII

theorem item434SmallTwoIII_D42_9_of_narrow (hS : Sec19.Seitz199D4Two) :
    Item434SmallTwoIII_D42_9 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h9
  exact (Item434SmallTwoIII.false_of_d42_nine_narrow hS hc hL h9).elim

theorem item434SmallTwoIII_D42_of_narrow (hS : Sec19.Seitz199D4Two)
    (h27 : Item434SmallTwoIII_D42_27) : Item434SmallTwoIII_D42 :=
  item434SecFor_of_card (item434SmallTwoIII_D42_9_of_narrow hS) h27

end CertsIII

section CertsL3

namespace Item434RowsProof

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem false_of_l3Pi_nine_narrow (h199 : Sec19.Seitz199L3) (hgap : Sec19.SeitzL3PiGap)
    (h : Ctx434Core G A M Q) (hL : IsSmallTwoOtherL3Pi (layer G ⧸ Subgroup.center (layer G)))
    (h9 : Nat.card h.layerStar = 9) : False := by
  obtain ⟨e, he, hpi⟩ := isoLThreePi_of_l3Pi hL
  have he1 : 1 ≤ e := by omega
  have hD3 : ∀ φ ∈ h.layerStar, φ ^ 3 = 1 := h.isElemAbelian_layerStar.2
  apply h.not_le
  refine h.layer_le_of_seitzHyperGamma_eq_top (seitzHyperGamma_eq_top_of_closure hD3 h9 ?_)
  by_cases hZ : Subgroup.center (layer G) = ⊥
  ·
    have hpiL : Sec4.IsoLThreePi (layer G) 2 e := by
      rcases hpi with ⟨h1, ⟨φ⟩⟩ | ⟨h2, ⟨φ⟩⟩
      · exact Or.inl ⟨h1, ⟨(layerEquivQuot hZ).trans φ⟩⟩
      · exact Or.inr ⟨h2, ⟨(layerEquivQuot hZ).trans φ⟩⟩
    exact hgap (layer G) 2 e he1 hpiL (Or.inr ⟨rfl, he⟩) h.layerStar
      h.isElemAbelian_layerStar h9
  ·
    have hq3 : 2 ^ e % 3 = 1 ∨ 2 ^ e % 3 = 2 := by
      rcases he with rfl | rfl <;> norm_num
    have hSL : Sec4.IsSLThreePi (layer G) :=
      ⟨2 ^ e, KFacts.isSLThreePiAt_of_isSLThreeEpsAt he1
        (Census.coverSLThree46 (layer G) h.isQuasisimple h.isPGroup_center_layer hZ 2 e he1
          (Or.inl rfl) hpi) hq3 hZ⟩
    refine h199 (layer G) h.layerStar hD3 h9 ⟨h.isQuasisimple, hSL, ?_⟩
    rintro ⟨⟨ψ⟩, -⟩
    have hlt := lt_card_of_isoLThreePi he hpi
    have hK : Nat.card (GaloisField 2 2) = 4 := by
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num
    have hSL4 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) = 60480 := by
      have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
      rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, hK]
      decide
    have hle : Nat.card (layer G ⧸ Subgroup.center (layer G)) ≤ Nat.card (layer G) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    rw [Nat.card_congr ψ.toEquiv, hSL4] at hle
    omega

end Item434RowsProof

theorem item434OtherL3Pi_of_narrow (h199 : Sec19.Seitz199L3) (hgap : Sec19.SeitzL3PiGap)
    (h64 : SeitzL3SixtyFour) (hU : Item434OtherU38TwentySeven) : Item434OtherL3Pi := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  rcases hc.card_layerStar with h9 | ⟨h27, hZ⟩
  · exact (Item434RowsProof.false_of_l3Pi_nine_narrow h199 hgap hc hL h9).elim
  · rcases hL with hL64 | hU38
    · exact (Item434RowsProof.false_of_l364_twentySeven h64 hc hL64 h27 hZ).elim
    · exact hU G₀ hG₀ H G f hf hker A M Q hc hU38 h27

end CertsL3

end CFSG.RankThree.PartTwo.Sec4

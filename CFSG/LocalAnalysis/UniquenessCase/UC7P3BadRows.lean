module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3BadArith

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.AGLEmbedding
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus gammaCore)

variable {L : Type} [Group L] [Finite L]

theorem false_of_card_sylow_nine (R : Sylow 3 L) (h9 : Nat.card ↥((R : Subgroup L) ⊓ ⊤) = 9)
    (h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [inf_top_eq] at h9
  have h2 : CFSG.Open.pRank 3 (R : Subgroup L) ≤ 2 :=
    CFSG.SectionRank.pRank_le (by norm_num) fun E hE _ => by
      have := Subgroup.card_le_of_le hE
      omega
  have := (CFSG.SectionRank.pRank_sylow R).1
  omega

theorem centralizer_top_eq_bot_of_simple (hs : IsSimpleGroup L) (hnab : ∃ a b : L, a * b ≠ b * a) :
    Subgroup.centralizer ((⊤ : Subgroup L) : Set L) = ⊥ := by
  have h : Subgroup.centralizer ((⊤ : Subgroup L) : Set L) = Subgroup.center L := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ]
  rw [h]
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have := Subgroup.mem_center_iff.1 (h1 ▸ Subgroup.mem_top a) b
    exact this.symm

theorem threeHeavy_of_gls3 (hG3 : Gls3StronglyThreeEmbeddedPlus) (hUO : KFactUnitaryOrder)
    (hRO : KFactReeOrder) (hL : CFSG.Open.IsKGroup L) (hs : IsSimpleGroup L)
    (hnab : ∃ a b : L, a * b ≠ b * a) (R : Sylow 3 L)
    (h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L))
    (hΓ : gammaCore 3 1 ⊤ (R : Subgroup L) < ⊤) : ThreeHeavy (Nat.card L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hsT : IsSimpleGroup ↥(⊤ : Subgroup L) := Subgroup.topEquiv.isSimpleGroup
  have hnabT : ∃ a b : ↥(⊤ : Subgroup L), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨⟨a, trivial⟩, ⟨b, trivial⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hrk : 2 ≤ CFSG.Open.pRank 3 (R : Subgroup L) := by
    rw [(CFSG.SectionRank.pRank_sylow R).1]
    omega
  obtain ⟨-, -, hrows⟩ := hG3 L hL ⊤ inferInstance hsT hnabT
    (centralizer_top_eq_bot_of_simple hs hnab) R hrk hΓ
  rcases hrows with ⟨q, hqp, ⟨hv, ⟨e⟩⟩, -⟩ | ⟨q, hqp, ⟨hv, ⟨e⟩⟩, -⟩ | ⟨m, ⟨hv, ⟨e⟩⟩, -⟩ |
      ⟨-, hidx, -⟩ | ⟨-, -, -, hP9, -⟩ | ⟨-, -, -, -, hP9, -⟩ | ⟨-, -, -, hP9, -⟩
  ·
    have eL : L ≃* CatGroup ⟨.A 1 q, hv⟩ := Subgroup.topEquiv.symm.trans e
    have hd : IsLinTwoIndex 3 q.exponent ⟨.A 1 q, hv⟩ := ⟨q, rfl, hqp, rfl⟩
    obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
    refine threeHeavy_linTwo (a := q.exponent) ?_
    rw [Nat.card_congr (eL.trans e₂).toEquiv]
    exact CFSG.SectionRank.OddCover.card_psl_two Nat.prime_three (by norm_num)
      (GaloisField.card 3 q.exponent q.exponent_pos.ne')
  ·
    have eL : L ≃* CatGroup ⟨.twistedA 2 q, hv⟩ := Subgroup.topEquiv.symm.trans e
    have h := hUO L 3 ⟨.twistedA 2 q, hv⟩ ⟨q, hqp, rfl⟩ ⟨eL⟩
    have hfe : (⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.fieldExponent =
        q.exponent := by simp
    rw [hfe] at h
    exact threeHeavy_unitary q.exponent_pos h
  ·
    have eL : L ≃* CatGroup ⟨.reeG2 m, hv⟩ := Subgroup.topEquiv.symm.trans e
    have h := hRO L ⟨.reeG2 m, hv⟩ ⟨rfl, m, rfl⟩ ⟨eL⟩
    have hfe : (⟨TauCeti.LieTypeIndex.reeG2 m, hv⟩ : TauCeti.ValidLieTypeIndex).1.fieldExponent =
        2 * m + 1 := by simp
    rw [hfe] at h
    exact threeHeavy_ree (by omega) h
  ·
    simp at hidx
  · exact (false_of_card_sylow_nine R hP9 h4).elim
  · exact (false_of_card_sylow_nine R hP9 h4).elim
  · exact (false_of_card_sylow_nine R hP9 h4).elim

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

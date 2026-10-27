module

public import CFSG.RankThree.PartTwo.Sec13.Item13Res4ProofCensus
public import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofTools
import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.Sec4.Item47CasesAlt
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartOne.S12K.Rigidity
import CFSG.RankThree.PartTwo.Sec6.BThreeCensusOrders
import CFSG.Sporadic.Ru

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace Res5Proof

variable {X : Type} [Group X]

theorem three_dvd_card_of_G2
    {p f : ℕ}
    (h : Blueprint.ChevalleyExceptionalModel X .G2 p f) : 3 ∣ Nat.card X := by
  obtain ⟨K, _, _, -, ⟨e⟩⟩ := Sec4.exists_mulEquiv_adjointGroup_G2 h
  rw [Nat.card_congr e.toEquiv, Timmesfeld.ExceptionalOrders.card_adjointGroup_G2]
  exact three_dvd_ordG2 _

theorem three_dvd_card_carrier
    {s : TauCeti.SporadicName} (hs : s ∈ Sec4.sporadics46) :
    3 ∣ Nat.card (Blueprint.NativeSporadic.Carrier s) := by
  by_cases hRu : s = .Ru
  · subst hRu
    rw [show Nat.card (Blueprint.NativeSporadic.Carrier .Ru) = 145926144000 from
      CFSG.Sporadic.Ru.card_Ru]
    norm_num
  · have hm := Sec6.BThreeCensus.card_carrier_of_mem (Or.inl hs) hRu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> norm_num

theorem three_dvd_card_of_alternating {n : ℕ} (hn : n ≤ 9) (hq : IsQuasisimple X)
    (e : X ≃* alternatingGroup (Fin n)) : 3 ∣ Nat.card X := by
  by_cases h4 : n ≤ 4
  · exfalso
    have hs := alternatingGroup.isSolvable (α := Fin n) (by rwa [Nat.card_fin])
    exact Sec4.false_of_isQuasisimple_of_isSolvable hq
      (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
  · rw [Nat.card_congr e.toEquiv]
    interval_cases n <;> rw [nat_card_alternatingGroup, Nat.card_fin] <;> decide

theorem three_dvd_card_or_suzuki_chevTwo
    (h : Sec4.IsChevTwoRankTwoModel X) :
    3 ∣ Nat.card X ∨ ∃ f, Blueprint.SuzukiModel X 2 f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h with ⟨n, hn, ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩⟩ |
      ⟨f, hG2 | hD4 | hSz | hF4 | hTits⟩
  · exact Or.inl (three_dvd_card_of_mulEquiv e (three_dvd_card_projSL_two _))
  · exact Or.inl (KFacts.three_dvd_card_of_mulEquiv_projSL e)
  · exact Or.inl (KFacts.three_dvd_card_of_mulEquiv_projSU (by omega) e)
  · exact Or.inl (three_dvd_card_of_mulEquiv e (three_dvd_card_projSp_two _))
  · exact Or.inl (three_dvd_card_of_mulEquiv e (three_dvd_card_projSU_four 2 n))
  · exact Or.inl (three_dvd_card_of_G2 hG2)
  · obtain ⟨-, -, hc⟩ := Sec19.Step1911Proof.card_of_trialityD4 hD4
    exact Or.inl (hc ▸ three_dvd_ordTrialityD4 _)
  · exact Or.inr ⟨f, hSz⟩
  · exact Or.inl ((PartOne.S12K.card_of_reeTitsModel_twistedF4 hF4) ▸ three_dvd_ordTwistedF4 _)
  · refine Or.inl ?_
    rw [PartOne.S12K.card_of_reeTitsModel_Tits hTits, CFSG.Open.ordTits]
    norm_num

theorem three_dvd_card_or_suzukiModel
    (hl : Sec4.IsList46 X) (hq : IsQuasisimple X) :
    3 ∣ Nat.card X ∨ ∃ f, Blueprint.SuzukiModel X 2 f := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hl with ⟨p, e, _, -, -, ⟨φ⟩⟩ | ⟨p, e, hp, hp3, he1, -, hSL | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ |
      ⟨p, hp, hp3, hG2 | ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩⟩ |
      (⟨n, hn, ⟨φ⟩⟩ | hA6 | hA7) | (⟨s, hs, ⟨φ⟩⟩ | ⟨s, -, hext⟩) |
      (hchev | ⟨n, hn, hSL⟩) | (⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩) |
      ((⟨e, he1, -, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩) | ⟨⟨φ⟩⟩ | ⟨-, hG23 | ⟨⟨φ⟩⟩⟩)
  · exact Or.inl (three_dvd_card_of_mulEquiv φ (three_dvd_card_projSL_two _))
  · exact Or.inl (three_dvd_card_of_isSLThreeEpsAt hp.out he1 hSL)
  · exact Or.inl (KFacts.three_dvd_card_of_mulEquiv_projSL φ)
  · exact Or.inl (KFacts.three_dvd_card_of_mulEquiv_projSU (by omega) φ)
  · exact Or.inl (three_dvd_card_of_G2 hG2)
  · exact Or.inl (three_dvd_card_of_mulEquiv φ (three_dvd_card_projSp_two _))
  · exact Or.inl (three_dvd_card_of_mulEquiv φ (three_dvd_card_projSU_four p 1))
  · exact Or.inl (three_dvd_card_of_mulEquiv φ (three_dvd_card_projSL_four _))
  · exact Or.inl (three_dvd_card_of_alternating hn hq φ)
  · exact Or.inl (three_dvd_card_of_isExtOf hA6)
  · exact Or.inl (three_dvd_card_of_isExtOf hA7)
  · exact Or.inl (three_dvd_card_of_mulEquiv φ (three_dvd_card_carrier hs))
  · exact Or.inl (three_dvd_card_of_isExtOf hext)
  · exact three_dvd_card_or_suzuki_chevTwo hchev
  · exact Or.inl (three_dvd_card_of_isSLThreeEpsAt Nat.prime_two hn hSL)
  · exact Or.inl (three_dvd_card_of_mulEquiv φ (three_dvd_card_projSL_five _))
  · refine Or.inl (three_dvd_card_of_mulEquiv φ ?_)
    rw [Sec6.BThreeCensus.card_projSp_three_two]
    norm_num
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Or.inl (three_dvd_card_of_mulEquiv φ (three_dvd_card_projSU_five 2 2))
  · exact Or.inl (KFacts.three_dvd_card_of_mulEquiv_projSL φ)
  · exact Or.inl (KFacts.three_dvd_card_of_mulEquiv_projSU (by omega) φ)
  · exact Or.inl (three_dvd_card_of_mulEquiv φ (three_dvd_card_projSL_four _))
  · exact Or.inl ((three_dvd_card_of_G2 hG23).trans (Subgroup.card_quotient_dvd_card _))
  · exact Or.inl ((three_dvd_card_of_mulEquiv φ (three_dvd_card_projSU_four 3 1)).trans
      (Subgroup.card_quotient_dvd_card _))

end Res5Proof

open Res5Proof

theorem ks131ThreeFreeNoE9 :
    KS131ThreeFreeNoE9 := by
  intro X _ _ hl hq h3 B hB hB9
  rcases three_dvd_card_or_suzukiModel hl hq with h | ⟨f, hSz⟩
  · exact h3 h
  · have h := KFacts.KP7.card_dvd_three_of_pow_three hSz (E := B) hB.2
    rw [hB9] at h
    norm_num at h

end CFSG.RankThree.PartTwo.Sec13

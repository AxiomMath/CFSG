module

public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofDefs
import CFSG.RankThree.PartTwo.KFacts.KS14Sz
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools
import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofSol
import CFSG.RankThree.PartTwo.Sec17.Item17Res12ProofSolv

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16


namespace Proof17Res14

theorem exists_suzukiModel_of_mem_thetaComponentsIn {G : Type} [Group G] [Finite G]
    (hG : TheoremFourHyp G) {X K : Subgroup G} (hXtop : X ≠ ⊤) (hX3 : ¬ 3 ∣ Nat.card X)
    (hK : K ∈ thetaComponentsIn X) :
    ∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n := by
  have hKX : K ≤ X := le_of_mem_thetaComponentsIn hK
  have h3K : ¬ 3 ∣ Nat.card K := fun h3 => hX3 (h3.trans (Subgroup.card_dvd_of_le hKX))
  have hs := Steps166.isSimpleGroup_thetaQuot_of_not_three_dvd hK h3K
  have hq := Proof1423.isQuasisimple_of_mem_thetaComponentsIn1423 hK
  have hnab : ∃ a b : ↥K ⧸ aschbacherSolvableCore 3 ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective _ a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective _ b
    exact ⟨a', b', fun h => hab (by rw [← map_mul, ← map_mul, h])⟩
  have hKtop : K ≠ ⊤ := fun h => hXtop (eq_top_iff.mpr (h ▸ hKX))
  have hcat := Steps166.inCatalog_thetaQuot hG hKtop hs hnab
  have h3Q : ¬ 3 ∣ Nat.card (↥K ⧸ aschbacherSolvableCore 3 ↥K) := fun h =>
    h3K (h.trans (Subgroup.card_quotient_dvd_card _))
  exact KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd _ hnab hcat h3Q

end Proof17Res14

theorem kFact174_holds : KFact174 := by
  intro G _ _ A c L Y₀ h X _ hX3 hns
  obtain ⟨K', hK'⟩ := Proof1423.exists_mem_thetaComponents_of_not_isSolvable hX3 hns
  exact ⟨K'.map X.subtype, ⟨K', hK', rfl⟩,
    Proof17Res14.exists_suzukiModel_of_mem_thetaComponentsIn h.toTheoremFourHyp
      (Proof17Res12.ne_top_of_not_three_dvd h hX3) hX3 ⟨K', hK', rfl⟩⟩

end CFSG.RankThree.PartTwo.Sec17

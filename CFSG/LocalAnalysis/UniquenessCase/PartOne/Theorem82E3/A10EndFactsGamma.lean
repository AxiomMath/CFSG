module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndFactsOne
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndFactsA
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndFactsSix
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndFactsNine
import CFSG.GroupTheory.ElemAbelianRank
import CFSG.RankThree.PartOne.S12.Sec159Tools
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D}

private theorem relPPrimeCore_centralizer_le (F : A10Frame c)
    (hΓ : CFSG.Open.rankThreeGamma 2 3 F.A ≤ D.M) {B : Subgroup G} (hBA : B ≤ F.A) :
    CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)) ≤ D.M := by
  have hAC : F.A ≤ Subgroup.centralizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (congrArg (fun z : ↥F.A => (z : G))
      (F.elemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨b, hBA hb⟩)).symm
  have hAZ : F.A ≤ Subgroup.normalizer
      (CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)) : Set G) := by
    refine le_trans hAC ?_
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (relPPrimeCore_le (Subgroup.centralizer (B : Set G)))).mp
      (relPPrimeCore_normal Nat.prime_three (Subgroup.centralizer (B : Set G)))
  have hN : ∀ B' : Subgroup G, B' ≤ F.A → ¬ IsCyclic ↥B' →
      Subgroup.normalizer (B' : Set G) ≤ D.M := by
    intro B' hB'A hB'nc
    refine (le_trans ?_ hΓ)
    rw [CFSG.Open.rankThreeGamma, CFSG.Open.GLBCore]
    exact le_sSup ⟨B', hB'A,
      CFSG.LocalAnalysis.UniquenessCase.UCK.N588T.two_le_pRank_of_not_isCyclic
        (F.elemAbelian.mono hB'A).isPGroup hB'nc, rfl⟩
  have hZp : ¬ 3 ∣ Nat.card
      (CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (coprime_card_relPPrimeCore Nat.prime_three (Subgroup.centralizer (B : Set G)))
  exact CFSG.RankThree.PartOne.Sec159.le_of_pPrime_normalized Nat.prime_three
    F.elemAbelian.isElementaryAbelian (by rw [F.card_A]; norm_num) hN hAZ hZp

private theorem centralizer_le_of_card_three (F : A10Frame c) (hK : UC22.InS3.UC326.K326P2S)
    (hK332 : UCK.K332ThreeAb)
    (hN1 : ∀ B ≤ F.A, Nat.card B = 3 → F.deg B = 3 → Subgroup.normalizer (B : Set G) ≤ D.M)
    (hNA : Subgroup.normalizer (F.A : Set G) ≤ D.M)
    (hΓ : CFSG.Open.rankThreeGamma 2 3 F.A ≤ D.M) :
    ∀ B ≤ F.A, Nat.card B = 3 → Subgroup.centralizer (B : Set G) ≤ D.M := by
  intro B hBA hB3
  have hcle : Subgroup.centralizer (B : Set G) ≤
      (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
        CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)) := by
    by_cases hdeg : F.deg B = 9
    · exact F.centralizer_le_of_deg_nine_of_normalizer hK hN1 hNA hBA hB3 hdeg
    · exact F.centralizer_le_of_deg_ne_nine hK332 hN1 hNA hBA hB3 hdeg
  exact hcle.trans (sup_le inf_le_right (relPPrimeCore_centralizer_le F hΓ hBA))

theorem not_rankThreeGamma_two_le (F : A10Frame c) (hK : UC22.InS3.UC326.K326P2S)
    (hK332 : UCK.K332ThreeAb)
    (hN1 : ∀ B ≤ F.A, Nat.card B = 3 → F.deg B = 3 → Subgroup.normalizer (B : Set G) ≤ D.M)
    (hNA : Subgroup.normalizer (F.A : Set G) ≤ D.M) :
    ¬ CFSG.Open.rankThreeGamma 2 3 F.A ≤ D.M := by
  intro hΓ
  have hC3 := centralizer_le_of_card_three F hK hK332 hN1 hNA hΓ
  have hΓ1 : CFSG.Open.rankThreeGamma 1 3 F.A ≤ D.M := by
    rw [CFSG.Open.rankThreeGamma, CFSG.Open.GLBCore]
    refine sSup_le ?_
    rintro N ⟨Q, hQA, h1, rfl⟩
    by_cases h2 : 2 ≤ CFSG.Open.pRank 3 Q
    · refine (le_trans ?_ hΓ)
      rw [CFSG.Open.rankThreeGamma, CFSG.Open.GLBCore]
      exact le_sSup ⟨Q, hQA, h2, rfl⟩
    · have hpR : CFSG.Open.pRank 3 Q = 1 := by omega
      have hQcard : Nat.card Q = 3 := by
        rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three
          (F.elemAbelian.mono hQA), hpR]
        norm_num
      exact F.normalizer_le_of_centralizer_le_of_normalizer_A hNA hQA (hC3 Q hQA hQcard)
  exact F.toCase811Sylow.not_rankThreeGamma_le hΓ1

theorem a10Facts_of_kFacts (F : A10Frame c) (hKF7 : UC22.KF7Use D)
    (hK : UC22.InS3.UC326.K326P2S) (hK332 : UCK.K332ThreeAb) : A10Facts F := by
  have hN1 : ∀ B ≤ F.A, Nat.card B = 3 → F.deg B = 3 →
      Subgroup.normalizer (B : Set G) ≤ D.M :=
    fun B hBA hB3 hdeg => F.normalizer_le_of_deg_three hKF7 hBA hB3 hdeg
  have hNA : Subgroup.normalizer (F.A : Set G) ≤ D.M := F.normalizer_A_le_of hN1
  exact ⟨hN1, hNA,
    fun B hBA hB3 h9 => F.centralizer_le_of_deg_ne_nine hK332 hN1 hNA hBA hB3 h9,
    F.not_rankThreeGamma_two_le hK hK332 hN1 hNA⟩

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

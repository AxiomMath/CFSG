module

public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofTools
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofTools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13

public section

namespace CFSG.RankThree.PartTwo.Sec15.LempkenL3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

theorem meetsY4_of_omegaA_eq (hMP : Step1513MeetsPoint) {A L : Subgroup G} {c : G}
    (hR : Sec15R G A c L) (hΩ : omegaA A = {Subgroup.zpowers c}) {p e : ℕ} [Fact p.Prime]
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    {K : Subgroup G} (hK : K ∈ scriptY0 A (lB A)) : MeetsY4 A (lB A) L K := by
  have hS : Sec14Std G A c L := hR.toSec14Std
  have h3L : 3 ∣ Nat.card L := Sec16.Proof1613.three_dvd_card_L hS
  have hpt : ∀ {b : G} {Lb : Subgroup G}, Subgroup.zpowers b ∈ omegaA A → Lb ∈ lA A b →
      Lb = L := fun hb hLb =>
    Proof1515.eq_of_mem_lA_of_zpowers_eq hS h3L (by rw [hΩ] at hb; exact hb) hLb
  obtain ⟨c', L', hc', hL', hm⟩ := hMP G A c L hR (fun b Lb hb hLb => by
    obtain rfl := hpt hb hLb
    exact Proof15Res6.isEmpty_j2_of_isoLThreePi hiso) K hK
  obtain rfl := hpt hc' hL'
  exact hm

end CFSG.RankThree.PartTwo.Sec15.LempkenL3

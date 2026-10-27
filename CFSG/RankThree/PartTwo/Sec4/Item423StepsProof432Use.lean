module

public import CFSG.RankThree.PartTwo.Sec4.Item423StepsProof432
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail22
public import CFSG.RankThree.PartTwo.Sec17.Item176ProofOne
import CFSG.RankThree.PartTwo.Sec4.Item422Proof
import CFSG.RankThree.PartTwo.Sec4.Census.Transfer

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item432Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem sectionFourHyp_component_quot (h1 : Item4_1LargePrime) {M : Type} [Group M] [Finite M]
    (hM : SectionFourHyp M) (N : Subgroup M) [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    {K : Subgroup (M ⧸ N)} (hK : IsComponent K) : SectionFourHyp K := by
  set e := Item422Proof.comapQuotientEquiv N K
  have hq := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hK.1
  exact Census.sectionFourHyp_of_mulEquiv e (Item41Narrow.sectionFourHyp_section h1 hM _ _
    (fun h => hN (h.trans (Item41Narrow.card_subgroupOf_dvd _ _))) hq)

theorem sectionFourHyp_component_quot_pPrimeCore (h1 : Item4_1LargePrime) {M : Type} [Group M]
    [Finite M] (hM : SectionFourHyp M) {K : Subgroup (M ⧸ CFSG.pPrimeCore 3 M)}
    (hK : IsComponent K) : SectionFourHyp K :=
  sectionFourHyp_component_quot h1 hM _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    CFSG.pPrimeCore_coprime_card) hK

end CFSG.RankThree.PartTwo.Sec4.Item432Proof

namespace CFSG.RankThree.PartTwo.Sec16.Proof1622

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

theorem rank3II_16_22_of_comp
    {A L : Subgroup G} {c : G} (h : Ctx169 G A c L)
    (h1617 : ∀ x ∈ Subgroup.normalizer (A : Set G), x ^ 3 = 1 → x ∈ A)
    (h1618 : ∀ g : G, g * c * g⁻¹ ∈ A → Subgroup.zpowers (g * c * g⁻¹) = Subgroup.zpowers c)
    (h432 : Sec4.Item4_32Comp) (hG2 : KS1622GTwo) {M : Subgroup G} (hcM : c ∈ M)
    (hcomp : ∀ K : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M), IsComponent K → SectionFourHyp K) :
    ∀ P : Sylow 3 ↥(normalClosureSub M (Subgroup.zpowers c)),
      IsCyclic ↥(P : Subgroup ↥(normalClosureSub M (Subgroup.zpowers c))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : orderOf c = 3 := h.orderOf_eq
  have hweak := weaklyClosed_of_steps h h1617 h1618
  have hrank : CFSG.Open.pRank 3 (normalClosureSub M (Subgroup.zpowers c)) ≤ 1 := by
    rcases h432 (↥M ⧸ CFSG.pPrimeCore 3 ↥M) hcomp
        (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3) _
        (Sec17.Proof176.card_map_zpowers hc hcM)
        (Sec17.Proof176.weaklyClosed_quot hc hweak hcM) with h1 | h2 | h3
    · calc CFSG.Open.pRank 3 (normalClosureSub M (Subgroup.zpowers c))
          ≤ CFSG.Open.pRank 3 (normalClosureIn M c) :=
            CFSG.SectionRank.pRank_mono (by norm_num) (normalClosureSub_le_normalClosureIn M c)
        _ ≤ _ := Sec17.Proof176.pRank_le_quot hcM
        _ = 1 := h1
    · exact (false_of_noncomm_quot h h1617 (hG2 _ h2)).elim
    · exact (false_of_noncomm_quot h h1617 (exists_noncomm_three_of_j2 h3)).elim
  exact isCyclic_of_open_pRank_le_one hrank

end CFSG.RankThree.PartTwo.Sec16.Proof1622

namespace CFSG.RankThree.PartTwo.Sec16

theorem step1622_of_comp
    (h1617 : Step1617) (h1618 : Step1618)
    (h432 : Sec4.Item4_32Comp) (h41 : Sec4.Item4_1LargePrime) (hG2 : KS1622GTwo) : Step1622 :=
  fun G _ _ A c L h _ hcM hM => Proof1622.rank3II_16_22_of_comp h (h1617 G A c L h)
    (h1618 G A c L h) h432 hG2 hcM (fun _ hK =>
      Sec4.Item432Proof.sectionFourHyp_component_quot_pPrimeCore h41
        (h.toTheoremFourHyp.sectionFourHyp hM) hK)

end CFSG.RankThree.PartTwo.Sec16

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late

section Item176One

variable {G : Type} [Group G] [Finite G]

open Proof176 in
theorem rank3II_17_6_one_of_comp {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (h175 : Item175 A c) (h432 : Sec4.Item4_32Comp)
    (h41 : Sec4.Item4_1LargePrime) (hexcl : Step176Excl)
    (hΩ : omegaA A = {Subgroup.zpowers c}) :
    ∀ K : Subgroup G, K ≠ ⊤ → c ∈ K → CFSG.Open.pRank 3 (normalClosureIn K c) = 1 := by
  intro K hK hcK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : orderOf c = 3 := h.toSec13Data.orderOf_eq
  obtain ⟨hG2, hJ2⟩ := hexcl G A c L Y₀ h h175 hΩ K hK hcK
  rcases h432 (↥K ⧸ CFSG.pPrimeCore 3 ↥K)
      (fun _ hX => Sec4.Item432Proof.sectionFourHyp_component_quot_pPrimeCore h41
        (h.toTheoremFourHyp.sectionFourHyp hK) hX)
      (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3) _ (card_map_zpowers hc hcK)
      (weaklyClosed_quot hc (h175 hΩ) hcK) with h1 | h2 | h3
  · exact le_antisymm ((pRank_le_quot hcK).trans h1.le) (one_le_pRank hc)
  · exact absurd h2 hG2
  · exact (hJ2.false h3.some).elim

end Item176One

end CFSG.RankThree.PartTwo.Sec17

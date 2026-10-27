module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Setup
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SL3FourRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
public import CFSG.LocalAnalysis.StronglyEmbedded.OfCentralizers
public import CFSG.LocalAnalysis.StronglyEmbedded.GammaOne
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (R8_108 IsSL3Four)

variable {G : Type} [Group G] [Finite G]

theorem three_dvd_card_of_mem_calC {M L : Subgroup G} (hL : L ∈ calC M)
    (hSL : IsSL3Four (Bar2 L)) : 3 ∣ Nat.card M := by
  have hbar : 3 ∣ Nat.card (Bar2 L) := three_dvd_card_of_isSL3Four hSL
  have hquot : Nat.card (Bar2 L) ∣ Nat.card ↥L := Subgroup.card_quotient_dvd_card _
  have hLcard : 3 ∣ Nat.card ↥L := hbar.trans hquot
  exact hLcard.trans (Subgroup.card_dvd_of_le (CFSG.Open.IsSubnormal.le hL.1))

theorem three_not_mem_uniqueFourBeta_of_not_strong (hU : uniqueFourUnique G) (S : Setup4 G)
    (hσ : S.InMSigma) (hnot : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M) :
    3 ∉ CFSG.Open.uniqueFourBeta G :=
  fun h3 =>
    hnot (CFSG.LocalAnalysis.UniquenessCase.UC22.isStronglyPEmbedded_three_of_mem_uniqueFourBeta
      hU S hσ h3)

theorem r8_108_of_normalizer_sylow_le (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (S₃ : Subgroup G) (hS₃ : CFSG.ABGLocalTools.IsSylowOf 3 S₃ S.M)
    (hNS : Subgroup.normalizer (S₃ : Set G) ≤ S.M)
    (hC : ∀ x ∈ S₃, orderOf x = 3 → Subgroup.centralizer ({x} : Set G) ≤ S.M) :
    R8_108 (CFSG.LocalAnalysis.UniquenessCase.UC6.dataOfSetup4 hS hU S) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup G := hS.simple
  intro L hL hSL _
  have h3M : 3 ∣ Nat.card S.M := three_dvd_card_of_mem_calC hL hSL
  have hS₃ne : S₃ ≠ ⊥ := by
    intro hbot
    have hcard := hS₃.card_eq
    have hpos : 0 < (Nat.card S.M).factorization 3 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' h3M
    have hge : 3 ≤ 3 ^ (Nat.card S.M).factorization 3 := by
      calc (3 : ℕ) = 3 ^ 1 := (pow_one 3).symm
        _ ≤ 3 ^ (Nat.card S.M).factorization 3 := Nat.pow_le_pow_right (by norm_num) hpos
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  have hMtop : S.M ≠ ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top hS.nonab S.M S.maxLocal.1
  exact CFSG.RankThree.PartOne.isStronglyPEmbedded_of_normalizer_sylow_le hMtop hS₃ hS₃ne hNS hC

theorem centralizer_le_of_mem_of_gamma {M P Q : Subgroup G}
    (hΓ : CFSG.Open.rankThreeGamma 1 3 Q ≤ M)
    (hA : ∀ A : Subgroup G, A ≤ P → Nat.card A = 3 → A ⊓ Q = ⊥ →
      Subgroup.centralizer (A : Set G) ≤ M)
    {x : G} (hxP : x ∈ P) (hx : orderOf x = 3) :
    Subgroup.centralizer ({x} : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hxQ : x ∈ Q
  · exact CFSG.RankThree.PartOne.centralizer_le_of_rankThreeGamma_le hΓ hxQ hx
  · let A : Subgroup G := Subgroup.zpowers x
    have hAP : A ≤ P := Subgroup.zpowers_le.mpr hxP
    have hAcard : Nat.card A = 3 := by
      show Nat.card (Subgroup.zpowers x) = 3
      rw [Nat.card_zpowers, hx]
    have hAQ : A ⊓ Q = ⊥ := by
      have hdvd : Nat.card (A ⊓ Q : Subgroup G) ∣ 3 := by
        rw [← hAcard]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact Subgroup.eq_bot_of_card_eq (A ⊓ Q) h
      · exfalso
        have hE : A ⊓ Q = A :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hAcard])
        have hxAQ : x ∈ A ⊓ Q := by
          rw [hE]
          exact Subgroup.mem_zpowers x
        exact hxQ hxAQ.2
    have hcent : Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer (A : Set G) := by
      show Subgroup.centralizer ({x} : Set G) =
        Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hcent]
    exact hA A hAP hAcard hAQ

theorem r8_108_of_gamma_and_normalizer (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (P Q : Subgroup G) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P S.M)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 Q ≤ S.M)
    (hA : ∀ A : Subgroup G, A ≤ P → Nat.card A = 3 → A ⊓ Q = ⊥ →
      Subgroup.centralizer (A : Set G) ≤ S.M)
    (hNS : Subgroup.normalizer (P : Set G) ≤ S.M) :
    R8_108 (CFSG.LocalAnalysis.UniquenessCase.UC6.dataOfSetup4 hS hU S) :=
  r8_108_of_normalizer_sylow_le hS hU S P hP hNS fun x hxP hx =>
    centralizer_le_of_mem_of_gamma hΓ hA hxP hx

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

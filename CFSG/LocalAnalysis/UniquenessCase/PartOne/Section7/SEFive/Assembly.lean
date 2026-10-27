module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsIdent
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableKID
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Tits
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Fi22KIB
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Sz32
public import CFSG.LocalAnalysis.AGLEmbeddingD2.BorelLocal
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.FixedFree
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.LinTwo
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Unitary
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.AltKIB
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.AltTenGood
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.HeisKIB
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.HeisGood
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.RankThree.PartOne.CTP.OutEmbed
import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.AGLEmbeddingD2 (D2HeisLocalAt)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem coverActsTriviallyOnSmall_and_good_of_isLinTwoIndex {p n : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hn : 2 ≤ n) {d : TauCeti.ValidLieTypeIndex}
    (hd : CFSG.AGLEmbedding.IsLinTwoIndex p n d) {X : Type} [Group X] [Finite X]
    [IsSimpleGroup ↥(CFSG.generalizedFitting X)] (hO : CFSG.pPrimeCore p X = ⊥)
    {N : Subgroup X} (hN : IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.CatGroup d) :
    CoverActsTriviallyOnSmall p ↥(CFSG.generalizedFitting X) ∧ Good p N := by
  obtain ⟨f⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  exact ⟨coverActsTriviallyOnSmall_of_fixedFreeFive (Or.inr rfl)
      ((fixedFreeFive_psl2GF hp5 hn).of_mulEquiv (e.trans f).symm),
    good_psl2GF (by omega) (by omega) hO hN (e.trans f)⟩

theorem card_eq_of_mulEquiv_of_card_outer_eq_one {X : Type} [Group X] [Finite X] {K : Subgroup X}
    [K.Normal] (hKC : Subgroup.centralizer (K : Set X) = ⊥) {L : Type} [Group L] (e : ↥K ≃* L)
    (hout : Nat.card (Outer L) = 1) : Nat.card X = Nat.card L := by
  have hq : Nat.card (X ⧸ K) ≤ 1 := by
    have h := CFSG.RankThree.PartOne.CTP.card_quotient_le_outer K hKC
    rwa [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv,
      hout] at h
  have hq1 : Nat.card (X ⧸ K) = 1 := le_antisymm hq Nat.card_pos
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K, hq1, one_mul, Nat.card_congr e.toEquiv]

section Certificates


theorem stronglyEmbeddedFive_of_kFacts (hId : CFSG.AGLEmbedding.KFactSmallIdent)
    (hLie : CFSG.AGLEmbedding.KFactOneLieIdent)
    (hCyc : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact)
    (hMcL : D2HeisLocalAt (.sporadic .McL) fun q => q = 5)
    (hJ4 : D2HeisLocalAt (.sporadic .J4) fun q => q = 11)
    (hMcL9 : 9 ∣ Nat.card (TauCeti.CFSGIndex.sporadic .McL).Group)
    (hJ49 : 9 ∣ Nat.card (TauCeti.CFSGIndex.sporadic .J4).Group)
    (hJ425 : ¬ 25 ∣ Nat.card (TauCeti.CFSGIndex.sporadic .J4).Group)
    (hJ4out : Nat.card (Outer (TauCeti.CFSGIndex.sporadic .J4).Group) = 1) :
    StronglyEmbeddedFive := by
  intro p hp hp5 X _ _ hX hO h2 N hN
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hKs, -, hKn, hKC⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar hp hO hN
  haveI : IsSimpleGroup ↥(CFSG.generalizedFitting X) := hKs
  haveI : (CFSG.generalizedFitting X).Normal := hKn
  rcases identification_of_isStronglyPEmbedded hId hLie hCyc hp hp5 hX hO h2 hN with
    hS | ⟨d, hd, ⟨e⟩⟩ | ⟨rfl, hSz⟩
  · rcases hS with ⟨d, hd, ⟨e⟩⟩ | ⟨d, ⟨q, hqp, -, hdq⟩, ⟨e⟩⟩ | hA | ⟨rfl, -⟩ |
      ⟨rfl, hT | hM | hF⟩ | ⟨rfl, hJ⟩
    ·
      obtain ⟨hB, hG⟩ := coverActsTriviallyOnSmall_and_good_of_isLinTwoIndex hp5 le_rfl hd hO hN e
      exact ⟨hB, Or.inl hG⟩
    ·
      have hU : CFSG.AGLEmbedding.IsUnitaryIndex p d := ⟨q, hqp, hdq⟩
      exact ⟨coverActsTriviallyOnSmall_unitary hp5 hU e, Or.inl (good_unitary hU hO hN e)⟩
    ·
      obtain ⟨e⟩ : Nonempty (↥(CFSG.generalizedFitting X) ≃* alternatingGroup (Fin (2 * p))) := hA
      have hB : CoverActsTriviallyOnSmall p ↥(CFSG.generalizedFitting X) :=
        coverActsTriviallyOnSmall_of_fixedFreeFive (q := 2) (Or.inl rfl)
          ((fixedFreeFive_alternatingGroup (by omega)).of_mulEquiv e.symm)
      by_cases h7 : 7 ≤ p
      · exact ⟨hB, Or.inr (coverHasLargeTwoLocal_of_mulEquiv_alternatingGroup (by omega) e)⟩
      · obtain rfl : p = 5 := by
          interval_cases p
          · rfl
          · exact absurd hp (by norm_num)
        exact ⟨hB, Or.inl (good_altTen hO hN e)⟩
    ·
      omega
    ·
      exact ⟨coverActsTriviallyOnSmall_of_fixedFreeFive (Or.inr rfl) (fixedFreeFive_tits hT),
        Or.inl (good_tits hO hN hT)⟩
    ·
      obtain ⟨e⟩ : Nonempty (↥(CFSG.generalizedFitting X) ≃*
        (TauCeti.CFSGIndex.sporadic .McL).Group) := hM
      have h9 : 9 ∣ Nat.card X :=
        (by rw [Nat.card_congr e.toEquiv]; exact hMcL9 :
          9 ∣ Nat.card ↥(CFSG.generalizedFitting X)).trans (Subgroup.card_subgroup_dvd_card _)
      exact ⟨coverActsTriviallyOnSmall_of_d2Heis hp5 hMcL e,
        Or.inl (good_of_heis (Or.inl rfl) hMcL hO hN e h9 (fun h => absurd h (by norm_num)))⟩
    ·
      exact ⟨coverActsTriviallyOnSmall_of_fixedFreeFive (Or.inr rfl) (fixedFreeFive_fi22 hKs hF),
        Or.inr (coverHasLargeTwoLocal_of_isFi22 hKs hF)⟩
    ·
      obtain ⟨e⟩ : Nonempty (↥(CFSG.generalizedFitting X) ≃*
        (TauCeti.CFSGIndex.sporadic .J4).Group) := hJ
      have hXJ : Nat.card X = Nat.card (TauCeti.CFSGIndex.sporadic .J4).Group :=
        card_eq_of_mulEquiv_of_card_outer_eq_one hKC e hJ4out
      exact ⟨coverActsTriviallyOnSmall_of_d2Heis hp5 hJ4 e,
        Or.inl (good_of_heis (Or.inr rfl) hJ4 hO hN e (hXJ ▸ hJ49) fun _ => hXJ ▸ hJ425)⟩
  · rcases hd with ⟨n, hn, hdn⟩ | ⟨hU, -⟩ | ⟨rfl, -⟩
    ·
      obtain ⟨hB, hG⟩ :=
        coverActsTriviallyOnSmall_and_good_of_isLinTwoIndex hp5 (by omega) hdn hO hN e
      exact ⟨hB, Or.inl hG⟩
    ·
      exact ⟨coverActsTriviallyOnSmall_unitary hp5 hU e, Or.inl (good_unitary hU hO hN e)⟩
    ·
      omega
  ·
    exact ⟨coverActsTriviallyOnSmall_sz32 hSz, Or.inl (good_sz32 hO h2 hN hSz)⟩

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive

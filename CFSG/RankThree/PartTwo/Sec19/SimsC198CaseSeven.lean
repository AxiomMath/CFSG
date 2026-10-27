module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Cases
import CFSG.RankThree.PartTwo.Sec19.SimsC198Close
import CFSG.RankThree.PartTwo.Sec19.SimsC198L3
import CFSG.RankThree.PartTwo.Sec19.SimsC198PSL2
import CFSG.RankThree.PartTwo.Sec19.SimsC198Rank2
import CFSG.RankThree.PartTwo.Sec19.SimsC198Sp4
import CFSG.RankThree.PartTwo.Sec19.SimsC198U48Close
import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofOuterPair

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

section G2Even

variable {S : Type} [Group S] [Finite S]


theorem noAutDatum_of_isoGTwo [IsSimpleGroup S] {q : TauCeti.PrimePower} (hq2 : q.p = 2)
    (h : Sec4.IsoGTwo S q) : NoAutDatum S := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := Sec8.Item8KFactsProof.isoGTwoEven_of_isoGTwo hq2 rfl h
  have hq3 : 3 ≤ q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 h.1).1
  rw [TauCeti.PrimePower.card_def, hq2] at hq3
  have hexp2 : 2 ≤ q.exponent := by
    by_contra hlt
    have : 2 ^ q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hexp2
  have hK2 : ringChar K = 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 :=
      charP_of_card_eq_prime_pow (f := q.exponent) (by rw [← Nat.card_eq_fintype_card, hK])
    exact ringChar.eq K 2
  exact noAutDatum_of_G2 hK2 hK4 e

end G2Even

section ReeF4Even

variable {S : Type} [Group S] [Finite S]


theorem noAutDatum_of_reeF4 [IsSimpleGroup S] {m : ℕ} (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group) : NoAutDatum S := by
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e'⟩⟩ :=
    Sec4.exists_mulEquiv_reeGamma (CFSG.LieType.SeitzGeneration.reeTitsModel_cat_reeF4 hm)
  exact noAutDatum_of_reeGamma ha hK (e.trans e')

end ReeF4Even

theorem caseHolds_seven :
    CaseHolds Alt42Seven := by
  intro X _ _ hX c L 𝒟 hD h
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.quasisimple.2.1
  rcases h with ⟨n, hn, ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩⟩ | ⟨q, hq2, hG⟩ |
    ⟨q, hv, hq2, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨ht, ⟨e⟩⟩
  ·
    exact absurd hD ((NoLocalDatum.of_mulEquiv e
      (noLocalDatum_projSL_two (GaloisField 2 n))).noAutDatum c L 𝒟)
  ·
    have h3 : ringChar (GaloisField 2 n) ≠ 3 := by
      rw [ringChar.eq (GaloisField 2 n) 2]
      norm_num
    exact absurd hD ((NoLocalDatum.of_mulEquiv e
      (noLocalDatum_projSL_three (GaloisField 2 n) h3)).noAutDatum c L 𝒟)
  ·
    exact absurd hD ((NoLocalDatum.of_mulEquiv e
      (noLocalDatum_projSU_three 2 n (by norm_num) hn)).noAutDatum c L 𝒟)
  ·
    exact absurd hD ((NoLocalDatum.of_mulEquiv e
      (noLocalDatum_projSp_two_even n hn)).noAutDatum c L 𝒟)
  ·
    by_cases h1 : n = 1
    · subst h1
      exact absurd hD ((noLocalDatum_of_U42 e).noAutDatum c L 𝒟)
    · by_cases h3 : n = 3
      · subst h3
        exact absurd hD (noAutDatum_of_U48 e c L 𝒟)
      · exact (false_of_rankHyp_PSU4_two hX hn h1 h3 e).elim
  ·
    exact absurd hD (noAutDatum_of_isoGTwo hq2 hG c L 𝒟)
  ·
    exact ⟨⟨q, hv, hq2, ⟨e⟩⟩, outerAutDatum_of_trialityD4 (by omega) e c L 𝒟 hD⟩
  ·
    exact absurd hD ((noLocalDatum_of_suzuki hm e).noAutDatum c L 𝒟)
  ·
    exact absurd hD (noAutDatum_of_reeF4 hm e c L 𝒟)
  ·
    exact absurd hD ((noLocalDatum_of_tits ht e).noAutDatum c L 𝒟)

end CFSG.RankThree.PartTwo.Sec19.SimsC198

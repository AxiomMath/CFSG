module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.RadSzCore
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.OddSz
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParSuzuki
import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem false_of_suzukiModel_of_ne {S : Type} [Group S] [Finite S]
    {f : ℕ} (h : CFSG.Blueprint.SuzukiModel S 2 f) (T : Sylow 2 S) {P : Subgroup S}
    (hTP : normalizer ((T : Subgroup S) : Set S) ≤ P) (hPtop : P ≠ ⊤)
    (hPT : P ≠ normalizer ((T : Subgroup S) : Set S)) : False := by
  obtain ⟨-, a, ha, K, hKfld, hKfin, hf, hcard, ⟨e⟩⟩ := h
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hcard, hf]
  have hnode : CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.OneNode
      (↥(CFSG.Blueprint.suzukiGroup a K)) (CFSG.LieType.Ree.suzukiU a K) :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.suzuki_oneNode hK
  have hnode' : CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.OneNode S
      ((CFSG.LieType.Ree.suzukiU a K).map e.symm.toMonoidHom) := hnode.map e.symm
  have hSylU : CFSG.QuasithinUnique.IsSylowTwoOf (CFSG.LieType.Ree.suzukiU a K) ⊤ :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.suzukiU_isSylowTwoOf hK
  have hSylU' : CFSG.QuasithinUnique.IsSylowTwoOf
      ((CFSG.LieType.Ree.suzukiU a K).map e.symm.toMonoidHom) ⊤ :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen.isSylowTwoOf_top_map_equiv
      e.symm hSylU
  have hSylT : CFSG.QuasithinUnique.IsSylowTwoOf (T : Subgroup S) ⊤ := by
    refine ⟨le_top, T.isPGroup', ?_⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [show ((T : Subgroup S).subgroupOf ⊤).index = (T : Subgroup S).index from
      Subgroup.relIndex_top_right _]
    exact Sylow.not_dvd_index T
  have hnT : CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.OneNode S
      (T : Subgroup S) := hnode'.of_sylow hSylU' hSylT
  rcases (IsCoatom.le_iff hnT.coatom).mp hTP with h | h
  · exact hPtop h
  · exact hPT h

theorem false_of_lieModel_tits_of_isSz
    {S : Type} [Group S] {f : ℕ} (h : CFSG.Blueprint.LieModel S .Tits 0 2 f) {B : Type} [Group B]
    {n : ℕ} (hB : IsSz B n) (hdvd : Nat.card B ∣ Nat.card S) : False := by
  obtain ⟨-, hodd, hn3, hBcard, -, -, -⟩ := isSz_facts hB
  have hree : CFSG.Blueprint.ReeTitsModel S .Tits 2 f := by
    rcases h with ⟨hcl, -⟩ | ⟨-, hch, -⟩ | ⟨-, -, hree⟩ | ⟨-, hsz, -⟩
    · exact absurd hcl (by decide)
    · exact absurd hch (by decide)
    · exact hree
    · exact absurd hsz (by decide)
  have hS : Nat.card S = CFSG.Open.ordTits :=
    CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_Tits hree
  have hpow : 2 ^ n - 1 ≠ 1 := by
    have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  obtain ⟨r, hrprime, hrdvd⟩ := Nat.exists_prime_and_dvd hpow
  have hr : r = 7 ∨ 17 ≤ r := seven_or_seventeen_le_of_dvd hodd hrprime hrdvd
  have hrB : r ∣ Nat.card B := by
    rw [hBcard]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hrdvd _) _
  have hrS : r ∣ Nat.card S := hrB.trans hdvd
  have hrS' : r ∣ 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 := by
    simpa [CFSG.Open.ordTits, hS] using hrS
  have hmem : r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 13 := by
    rcases hrprime.dvd_mul.mp hrS' with h | h
    · rcases hrprime.dvd_mul.mp h with h | h
      · rcases hrprime.dvd_mul.mp h with h | h
        · left
          exact (Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_two).mp
            (hrprime.dvd_of_dvd_pow h)
        · right; left
          exact (Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_three).mp
            (hrprime.dvd_of_dvd_pow h)
      · right; right; left
        exact (Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_five).mp
          (hrprime.dvd_of_dvd_pow h)
    · right; right; right
      exact (Nat.prime_dvd_prime_iff_eq hrprime (by norm_num : Nat.Prime 13)).mp h
  rcases hr with h7 | h17 <;> rcases hmem with h | h | h | h <;> omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

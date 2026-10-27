module

public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec15.Notation
import CFSG.RankThree.PartTwo.Sec15.Praeger155R1LeKA7

public section

namespace CFSG.RankThree.PartTwo.Sec15.LempkenL3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

theorem le_of_eq_inf_sup_of_pCoreOf_two_le_normalizer
    {A : Subgroup G} {c : G} {L K : Subgroup G} (h : Sec15R G A c L)
    (hK4 : K ∈ scriptY4 A (lB A)) (hLK : L = (L ⊓ K) ⊔ CFSG.Open.pCoreOf 2 L)
    (hO2N : CFSG.Open.pCoreOf 2 L ≤ Subgroup.normalizer (K : Set G)) : L ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM : L ⊔ K = K ⊔ CFSG.Open.pCoreOf 2 L :=
    Sylow155R1.sup_eq_sup_theta hLK (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
  have hcop : Nat.Coprime 3 (Nat.card ↥(CFSG.Open.pCoreOf 2 L)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L)
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hL3 : L = oPrimeResidualOf 3 L := Sec16.eq_oPrimeResidualOf_of_sec15R h
  have hM3 : L ⊔ K = oPrimeResidualOf 3 (L ⊔ K) :=
    le_antisymm (sup_le (hL3.le.trans (Sec15.oPrimeResidualOf_mono 3 le_sup_left))
      (hK4.2.1.le.trans (Sec15.oPrimeResidualOf_mono 3 le_sup_right)))
      (Sec14.oPrimeResidualOf_le_self 3 _)
  exact le_sup_left.trans
    (hM3.le.trans (Sylow155R1.oPrimeResidualOf_le_of_eq_sup hM hO2N hcop))

end CFSG.RankThree.PartTwo.Sec15.LempkenL3

module

public import CFSG.RankThree.SubgroupLists.MitchellPairOrder
public import CFSG.RankThree.SubgroupLists.SymplecticGamma
import CFSG.RankThree.SubgroupLists.MitchellEleven
import CFSG.RankThree.SubgroupLists.MitchellTen

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module
open scoped MatrixGroups

local notation "V₄" => Fin 2 ⊕ Fin 2

theorem mitchellPartThree_of_noFourPair :
    MitchellPartThree := by
  have h4 := mitchellNoFourPair_holds
  intro p _ hp5 G hGS hq hC hirr hZ hneg hU0 t ht g
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_charP (by omega)
  obtain ⟨k, hk1, hk6, hk⟩ := exists_pow_mul_conj_eq_one_or_neg hp5 hGS hq hZ hneg hU0 ht g
  rcases isThreePair_or_of_pow_eq_one_or_neg h2 ht (conj_isNCInv hGS ht g) hk1 hk6 hk with
    h | h | h
  · exact h
  · exact absurd h (h4 p hp5 G hGS hq hC hirr hZ hneg hU0 t ht g)
  ·
    have h1 := cliffB_sq_eq_one_of_quartic hp5 hGS hq hZ hneg hU0 ht g h
    have hB := mul_self_eq_one_iff.mp ((sq _).symm.trans h1)
    rcases eq_or_eq_neg_of_cliffB_eq_one h2 hU0 hneg t.2 (g * t * g⁻¹).2 ht
        (conj_isNCInv hGS ht g) hB with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')

theorem mitchellPartThree_holds : MitchellPartThree :=
  mitchellPartThree_of_noFourPair

end CFSG.RankThree.SubgroupLists

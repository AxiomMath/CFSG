module

public import CFSG.LocalAnalysis.StandardType.GGTwAutDefs
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSU
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypEigen
public import CFSG.RankThree.PartOne.CTP.SeitzUSplit
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypFrame
public import CFSG.LocalAnalysis.StandardType.GGTwSURank
public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned
import CFSG.LocalAnalysis.StandardType.GGKGForkLinNsB
import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitE
import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitOddE
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHyperbolic
import CFSG.LocalAnalysis.StandardType.GGStdPosC24HypDescent
import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggTorusSignedEltSC_unitary_split {K : Type} [Field K] [Finite K] [CharP K 2]
    {n d p : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 4 ≤ d)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1) :
    GGTorusSignedEltSC p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
  intro E hE h3 hsc
  have hEne : E ≠ ⊥ := by
    intro he
    rw [he, Subgroup.card_bot] at h3
    have hbig : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hrank : p ^ (d / 2) ≤ Nat.card E :=
    pow_le_card_of_selfCent_unitary_split hK hn (by omega) hp hp2 hpq hE hsc hEne
  have hdim : d = 2 * (d / 2) ∨ d = 2 * (d / 2) + 1 := by omega
  rcases hdim with hd0 | hd1
  · have hs := ggTorusSignedElt_unitary_split_even (r := d / 2) hK hn (by omega) hp hp2 hpq
    rw [← hd0] at hs
    exact hs E hE hrank h3
  · have hs := ggTorusSignedElt_unitary_split_odd (r := d / 2) hK hn (by omega) hp hp2 hpq
    rw [← hd1] at hs
    exact hs E hE hrank h3

theorem ggTwSU_signed_rec {K : Type} [Field K] [Finite K] [CharP K 2] {n d r : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hr : 3 ≤ r)
    (hd : 2 * r ≤ d ∧ d ≤ 2 * r + 1) (h3 : 3 ∣ 2 ^ n - 1) :
    GGTorusSignedEltSC 3 (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) :=
  ggTorusSignedEltSC_unitary_split hK hn (by omega) Nat.prime_three (by norm_num) h3

end CFSG.StandardType

end

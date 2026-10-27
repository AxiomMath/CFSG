module

public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkSignedPow
public import CFSG.LocalAnalysis.StandardType.GGKGForkLinNsC
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenTypeA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTorusSignedEltSC_linear_nonsplit {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (hd : 2 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) :
    GGTorusSignedEltSC p (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) := by
  haveI : CharP K 2 := NbrInnerMore.charP_two_of_card_pow hn hK
  have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  have hpK0 : (p : K) ≠ 0 := fun hzero =>
    hp2 (((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      ((CharP.cast_eq_zero_iff K 2 p).mp hzero)).symm)
  exact ggKGLn_signedEltSC_linearNonsplit hp hp2 hpK0 hpK (by omega)

theorem ggKGTwoOn_linearNonsplit :
    GGKGTwoOn fun p lab => (lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3)) ∧ p ∣ 2 ^ lab.n + 1 :=
  ggKGLn_kgTwoOn_linearNonsplit

end CFSG.StandardType

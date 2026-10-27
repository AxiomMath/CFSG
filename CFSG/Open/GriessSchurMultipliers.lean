module

public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type

public section

universe u v w

namespace CFSG.Open.Open

open scoped MatrixGroups in
theorem griess_schur_multipliers_psl
    (p k n : ℕ) [Fact p.Prime] (hk : 0 < k) (hn : 2 ≤ n) (hsmall : n = 2 → 4 ≤ p ^ k) :
    commutator PSL(n, GaloisField p k) = ⊤ ∧
      Nonempty (griessHopfMultiplier PSL(n, GaloisField p k) ≃*
        Multiplicative (ZMod (Nat.gcd n (p ^ k - 1)) ×
          ZMod (griessPSLExceptional n (p ^ k)).1 × ZMod (griessPSLExceptional n (p ^ k)).2)) :=
  _root_.CFSG.Milestones.cl_lit_griess_schur_multipliers_lie_type p k n hk hn hsmall

end CFSG.Open.Open

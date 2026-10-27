module

public import CFSG.Sporadic.Co1.Module.OddCentCard
public import CFSG.Sporadic.Co1.Module.Involutions
public import CFSG.Sporadic.Co1.Module.OddFacts

public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint

theorem orderOf_rho3 :
    orderOf rho3 = 2 := by
  have h1 : rho3 ≠ 1 := by
    intro h
    have h2 := rho3_ncard_fix
    rw [h] at h2
    have h3 : CFSG.Monster.GMS.co1Fix (1 : NativeSporadic.Co1) = Set.univ := by
      ext v
      simp [CFSG.Monster.GMS.co1Fix]
    rw [h3, Set.ncard_univ] at h2
    simp [Nat.card_eq_fintype_card, ZMod.card] at h2
  exact orderOf_eq_prime (by rw [pow_two]; exact rho3_sq) h1

theorem isCo1TwoA_rho3 :
    CFSG.Monster.GMS.IsCo1TwoA rho3 := by
  have hord := orderOf_rho3
  have hup := (CFSG.Monster.GMS.co1InvolutionFacts.1 rho3 hord).1
  have hge := card_cent_rho3_ge
  rw [rho3_ncard_fix] at hup
  refine ⟨hord, ?_⟩
  rw [rho3_ncard_fix]
  norm_num at hup ⊢
  omega

theorem co1OddPairFacts :
    CFSG.Monster.GMS.Co1OddPairFacts :=
  co1OddPairFacts_of CFSG.Monster.GMS.co1InvolutionFacts isCo1TwoA_rho3

end CFSG.Sporadic.Co1.Module.Odd

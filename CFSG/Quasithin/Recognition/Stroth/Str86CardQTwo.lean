module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoBound

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G]

theorem str86_card_q2_and_card_s
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2))
    (hQ1card : Nat.card (Q1 L1 L2 S) = (2 ^ k) ^ 7) :
    Nat.card (Q2 L1 L2 S) = (2 ^ k) ^ 8 ∧ Nat.card S = (2 ^ k) ^ 10 := by
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hrelQ1 : (Q1 L1 L2 S).relIndex S = (2 ^ k) ^ 3 :=
    str86_relIndex_q1_s hF hSB hk hFc hU3
  have hrelQ2 : (Q2 L1 L2 S).relIndex S = (2 ^ k) ^ 2 := by
    rw [str86_relIndex_q2_s hF.toW hSB (by omega) hL2, ← pow_mul, mul_comm]
  have hS : Nat.card S = (2 ^ k) ^ 10 := by
    have hmul := Subgroup.relIndex_mul_card (H := Q1 L1 L2 S) (K := S)
    rw [inf_eq_left.mpr hQ1S, hrelQ1, hQ1card] at hmul
    rw [← hmul, ← pow_add]
  have hQ2 : Nat.card (Q2 L1 L2 S) = (2 ^ k) ^ 8 := by
    have hmul := Subgroup.relIndex_mul_card (H := Q2 L1 L2 S) (K := S)
    rw [inf_eq_left.mpr hQ2S, hrelQ2, hS] at hmul
    have hpow : (2 ^ k) ^ 10 = (2 ^ k) ^ 2 * (2 ^ k) ^ 8 := by
      rw [← pow_add]
    rw [hpow] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul
  exact ⟨hQ2, hS⟩

end CFSG.Quasithin.Stroth

end

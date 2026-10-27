
module

public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Certificates.NativeSchreierCard

@[expose] public section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem mem_fi22P_of_siftA
    {g : Array ℕ} {G : Equiv.Perm (Fin 3510)} (hG : Rep 3510 g G)
    (h : siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0 g = true) :
    G ∈ fi22P :=
  (siftA_iff_mem_originalSubgroup fi22ChainArrays (by norm_num) fi22Order_check.1 hG).1 h

theorem card_fi22P_inf_stabilizer :
    Nat.card (fi22P ⊓ MulAction.stabilizer (Equiv.Perm (Fin 3510)) (0 : Fin 3510) :
      Subgroup (Equiv.Perm (Fin 3510))) = 18393661440 := by
  rw [← card_fi22P_stabilizer, ← MulAction.stabilizer_subgroupOf, ← Subgroup.inf_subgroupOf_left]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm

theorem factorization_card_fi22P_two :
    (Nat.card fi22P).factorization 2 = 17 := by
  rw [card_fi22P, show (64561751654400 : ℕ) = 2 ^ 17 * 492567075 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

end CFSG.Monster.B.Fischer

module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoChain
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_chief_count_eq_one
    {L1 L2 S : Subgroup G} {k c : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2)) (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hser : IsChiefSeriesFrom (L1 ⊔ S) (u3X1 L1 L2 S) (u3X1 L1 L2 S) c) :
    c = 1 := by
  have hn : 2 ≤ 2 * k := by omega
  obtain ⟨hcpos, hcbound⟩ :=
    str86_chief_count_bound hF hSB hk hFc hU3 hn hL2 hZQ hser
  have hpow : ((2 ^ k) ^ 2) ^ c ≤ ((2 ^ k) ^ 2) ^ 1 := by
    rw [pow_one]
    refine hcbound.trans (le_of_eq ?_)
    rw [Nat.mul_comm 2 k, pow_mul]
  have hbase : 1 < (2 ^ k) ^ 2 := by
    have h2 : (2 : ℕ) ≤ 2 ^ k := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc (1 : ℕ) < 2 ^ 2 := by norm_num
      _ ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left h2 2
  have hc : c ≤ 1 := (Nat.pow_le_pow_iff_right hbase).mp hpow
  omega

end CFSG.Quasithin.Stroth

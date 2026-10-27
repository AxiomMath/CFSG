module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.GoldschmidtC137S6Fin3

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

theorem card_mul_two_pow_rkIdx {W : Type*} [CommGroup W] [Finite W] {n : ℕ}
    (hW : Nat.card W = 2 ^ n) (H : Subgroup W) : Nat.card H * 2 ^ rkIdx H = 2 ^ n := by
  have h1 := Subgroup.card_mul_index H
  rw [hW] at h1
  have hdvd : H.index ∣ 2 ^ n := ⟨Nat.card H, by rw [← h1, mul_comm]⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hrk : rkIdx H = j := by
    unfold rkIdx
    rw [hj, padicValNat.prime_pow]
  rw [hrk, ← hj]
  exact h1

theorem card_fixV_Z1 : Nat.card (fixV (Z1.map (Mod.act 6 Mod.ut0))) = 8 := by
  have h := card_mul_two_pow_rkIdx (W := Mod.V 6 Mod.ut0) (n := 4) (by rw [card_V6]; norm_num)
    (fixV (Z1.map (Mod.act 6 Mod.ut0)))
  rw [rank_Z1.2] at h
  omega

end CFSG.Quasithin.H13.U3.GC137

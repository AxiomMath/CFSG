module

public import CFSG.Quasithin.EmptyFaithful.S153G93DOrthInner
public import CFSG.Quasithin.EmptyFaithful.S153G93DOrthCent
public import CFSG.Quasithin.EmptyFaithful.S153G93DCases
public import CFSG.Quasithin.Background.F918Z3CbReal

public section

namespace CFSG.Quasithin

namespace S153G93D

namespace Orth

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {W : Type} [CommGroup W] [Finite W]

theorem false_of_card_fixed_sq {a : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hrk : Nat.card ↥(commV (Subgroup.zpowers a)) = 2 ^ 2) (hbig : 2 ^ 6 ≤ Nat.card W)
    (hsq : Nat.card {w : W // a w = w} ^ 2 = Nat.card W) : False := by
  have hfix : Nat.card {w : W // a w = w} = Nat.card ↥(fixV (Subgroup.zpowers a)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun w => mem_fixV_zpowers_iff.symm)
  have hidx : (fixV (Subgroup.zpowers a)).index = 4 := by
    rw [B1.index_eq_two_pow hW, rkIdx_fixV_eq_two hrk]
    norm_num
  have hcard : Nat.card W = 4 * Nat.card ↥(fixV (Subgroup.zpowers a)) := by
    rw [B1.card_eq_index_mul (Subgroup.zpowers a), hidx]
  have hpos : 0 < Nat.card ↥(fixV (Subgroup.zpowers a)) := B1.card_fixV_pos _
  rw [hfix, hcard] at hsq
  have hc4 : Nat.card ↥(fixV (Subgroup.zpowers a)) = 4 := by
    have h : Nat.card ↥(fixV (Subgroup.zpowers a)) *
        Nat.card ↥(fixV (Subgroup.zpowers a)) = 4 * Nat.card ↥(fixV (Subgroup.zpowers a)) := by
      rw [← pow_two]
      exact hsq
    exact Nat.eq_of_mul_eq_mul_right hpos h
  rw [hcard, hc4] at hbig
  norm_num at hbig

theorem oneOrth4_of_sl2Cent (hSL2 : SL2Cent) : OneOrth4 := by
  intro W _ _ G₀ K S a z hC hO
  obtain ⟨m, hm1, F, _, _, _, hF, π, hπ⟩ := hO
  obtain ⟨R⟩ := OrthMinus.nonempty_hermReal hπ
  have ha2 : a * a = 1 := by rw [← pow_two]; exact hC.a2
  let θ : ↥(StatedSL 2 F) ≃* ↥K := MulEquiv.ofBijective R.π R.bij
  obtain ⟨q, hqS, hinner⟩ := exists_inner_of_sylow_cent θ ha2 hC.aN hC.syl hC.cent (hSL2 F)
  have haS : a ∈ S := mem_of_inner hC.toCtx2 ⟨q, hqS, hinner⟩
  have haK : a ∈ K := hC.syl.1 haS
  exact false_of_card_fixed_sq hC.exp hC.rk hC.big (R.card_fixed_sq hF hm1 haK hC.a1 ha2)

end Orth

end S153G93D

end CFSG.Quasithin

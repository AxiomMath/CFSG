module

public import CFSG.LocalAnalysis.StandardType.GGL45TALinRk

public section

namespace CFSG.StandardType.GGL45TA

open CFSG CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA

namespace LinSetting

variable {d : ℕ} {k : Type} [Field k] [Finite k] {K : Type} [Group K] {p q₀ : ℕ}
  {ψ : MulAut K} {E : Subgroup (MulAut K)}

theorem map_tau_of_isLift (S : LinSetting p q₀ d k K ψ E) {x : GL (Fin d) k} (hx : S.IsLift x) :
    Matrix.GeneralLinearGroup.map S.τ.toRingHom x = x := by
  obtain ⟨c, hcp, hc⟩ := S.exists_map_tau_of_isLift hx
  by_cases hc1 : c = 1
  · rw [hc, hc1, map_one, one_mul]
  exfalso
  haveI : Fact p.Prime := ⟨S.hp⟩
  have hprim : IsPrimitiveRoot c p :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hcp hc1)
  have h1 := S.card_E_mul_le
  have h2 := S.card_lifts_le hx hprim hc
  have h3 := S.card_fixedLifts_le hx hprim hc
  have h4 := S.rk_bound
  have hp1 : 1 < p := S.hp.one_lt
  have hE : Nat.card E ≤ p ^ (d / p) := by
    have : Nat.card E * p ≤ p ^ (d / p) * p := by
      calc Nat.card E * p ≤ _ := h1
        _ ≤ p * _ := h2
        _ ≤ p * p ^ (d / p) := Nat.mul_le_mul_left p h3
        _ = p ^ (d / p) * p := mul_comm _ _
    exact Nat.le_of_mul_le_mul_right this S.hp.pos
  have hdp2 : 2 ≤ d / p :=
    (Nat.pow_le_pow_iff_right hp1).mp (S.card_E.trans hE)
  have hd1 : d - 2 + 1 ≤ d / p + 2 := by
    have : p ^ (d - 2 + 1) ≤ p ^ (d / p + 2) := by
      rw [pow_succ, pow_add]
      exact h4.trans (Nat.mul_le_mul_right _ hE)
    exact (Nat.pow_le_pow_iff_right hp1).mp this
  obtain ⟨m, hm⟩ := S.dvd_d
  have hmd : d / p = m := by rw [hm, Nat.mul_div_cancel_left m S.hp.pos]
  rw [hmd] at hdp2 hd1
  have hp3 : 3 ≤ p := by have := S.hp.two_le; have := S.hp2; omega
  have : 3 * m ≤ p * m := Nat.mul_le_mul_right m hp3
  have hd3 := S.three_le
  omega

end LinSetting

end CFSG.StandardType.GGL45TA

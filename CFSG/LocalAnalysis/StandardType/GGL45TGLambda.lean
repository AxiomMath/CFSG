module

public import CFSG.LocalAnalysis.StandardType.GGL45TGRank

public section

namespace CFSG.StandardType.GGL45TG

open CFSG CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA

namespace GSetting

variable {d : ℕ} {k : Type} [Field k] [Finite k] {K : Type} [Group K] {D : GData d k} {p q₀ : ℕ}
  {ψ : MulAut K} {E : Subgroup (MulAut K)}

theorem map_tau_of_isLift (S : GSetting p q₀ d k D K ψ E) {x : GL (Fin d) k} (hx : S.IsLift x) :
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
  have hE : Nat.card E ≤ p ^ (d / p) := by
    have : Nat.card E * p ≤ p ^ (d / p) * p := by
      calc Nat.card E * p ≤ _ := h1
        _ ≤ p * _ := h2
        _ ≤ p * p ^ (d / p) := Nat.mul_le_mul_left p h3
        _ = p ^ (d / p) * p := mul_comm _ _
    exact Nat.le_of_mul_le_mul_right this S.hp.pos
  exact absurd S.big_E (Nat.not_lt.mpr hE)

end GSetting

end CFSG.StandardType.GGL45TG

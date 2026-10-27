module

public import CFSG.Quasithin.Background.D36GluedNDBase
import CFSG.Quasithin.Background.F918Z4bPrime
import CFSG.Quasithin.Background.F918Z4c1Sz
import CFSG.Quasithin.Background.F918Z4c1J1
import CFSG.Quasithin.Background.F918Z4e
import CFSG.Quasithin.Background.D36GluedL231

public section

namespace CFSG.Quasithin

variable {Y : Type} [CommGroup Y] [Finite Y] {X A L₀ : Subgroup (MulAut Y)} {U U' : Subgroup Y}

namespace NDSetup

variable (S : NDSetup X A L₀ U U')

include S

theorem false_of_sz {n : ℕ} (hn : 3 ≤ n) (hL : IsSz n ↥L₀) :
    False := by
  obtain ⟨ρ, hρ⟩ := S.exists_gl
  have hu := S.ubar_le (autRankLe_sz hn hL)
  have hF : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod]; norm_num
  have h4 := four_mul_le_of_isSz hn hL hF ρ hρ
  omega

theorem false_of_j1
    (hL : IsSporadic .J1 ↥L₀) : False := by
  obtain ⟨ρ, hρ⟩ := S.exists_gl
  have hu := S.ubar_le (autRankLe_j1 hL)
  have hF : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod]; norm_num
  have h18 := eighteen_le_of_j1 hL hF ρ hρ
  omega

theorem false_of_psl2_prime {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) (h31 : p ≠ 31)
    (hL : IsPSL 2 p 1 ↥L₀) : False := by
  obtain ⟨ρ, hρ⟩ := S.exists_gl
  have hu := S.ubar_le (autRankLe_psl2_prime hp (by omega) hL)
  have hF : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod]; norm_num
  have hcard : p ∣ Nat.card ↥L₀ := by
    have h2 := Z4e.two_mul_card_of_isPSL_two_odd hp (by omega) hL
    have hdvd : p ∣ 2 * Nat.card ↥L₀ := by rw [h2]; exact dvd_mul_right _ _
    have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
    exact hcop.dvd_of_dvd_mul_left hdvd
  have hord := orderOf_two_le_of_prime_dvd_card hF ρ hρ hp (by omega) hcard
  exact not_orderOf_two_le_five hp h11 h31 (by omega)

theorem false_of_psl2_31 (hL : IsPSL 2 31 1 ↥L₀) : False := by
  obtain ⟨ρ, hρ⟩ := S.exists_gl
  have hu := S.ubar_le (autRankLe_psl2_prime (by norm_num) (by norm_num) hL)
  exact no_embedding_psl2_31 hL (by omega) ρ hρ

end NDSetup

end CFSG.Quasithin

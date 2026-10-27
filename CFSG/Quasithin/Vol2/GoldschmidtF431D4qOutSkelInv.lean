module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructAut

public section

namespace CFSG.Quasithin.H13.F431.D4q.Out

open CFSG.Quasithin.H13.F431.D4q.Struct CFSG.LieType.Chevalley CFSG.QuasithinUnique

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
  (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ.toRingHom c = c ^ (2 ^ f))

include hf hK hσ in
theorem exists_field_involution {Kb : Subgroup (MulAut (Cm σ))}
    (hinn : (MulAut.conj : Cm σ →* MulAut (Cm σ)).range ≤ Kb)
    (hev : ¬ Odd (Nat.card Kb / Nat.card (Cm σ))) {S2 : Subgroup (K ≃+* K)}
    (hS2 : IsSylowTwoOf S2 (Kb.map (theta σ hf hK hσ))) :
    ∃ e : ℕ, f = 2 * e ∧ ∃ δ ∈ S2, δ ≠ 1 ∧ δ ^ 2 = 1 ∧ ∀ c, δ c = c ^ 2 ^ (3 * e) := by
  have hcard := card_eq_of_inn_le σ hf hK hσ hinn
  have hpos : 0 < Nat.card (Cm σ) := Nat.card_pos
  have hdiv : Nat.card Kb / Nat.card (Cm σ) = Nat.card (Kb.map (theta σ hf hK hσ)) := by
    rw [hcard, Nat.mul_div_cancel_left _ hpos]
  have hev' : 2 ∣ Nat.card (Kb.map (theta σ hf hK hσ)) := by
    rw [← hdiv]
    exact even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hev)
  have h1 := Subgroup.relIndex_mul_card S2 (Kb.map (theta σ hf hK hσ))
  rw [inf_of_le_left hS2.1] at h1
  have h2S : 2 ∣ Nat.card S2 := by
    rw [← h1] at hev'
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hev' with h | h
    · exact absurd h hS2.2.2
    · exact h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun φ : K ≃+* K => (φ : K → K)) fun a b h => RingEquiv.ext (congrFun h)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2S
  have hord : orderOf (x : K ≃+* K) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hτ2 : (x : K ≃+* K) ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hτ1 : (x : K ≃+* K) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨hev3, hτ, -⟩ := ringEquiv_sq_eq_one_facts Nat.prime_two (by omega : 1 ≤ 3 * f) hK3
    hτ2 hτ1
  have hevf : Even f := by
    rcases Nat.even_mul.1 hev3 with h | h
    · exact absurd h (by decide)
    · exact h
  obtain ⟨e, he⟩ := hevf
  refine ⟨e, by omega, x, x.2, hτ1, hτ2, fun c => ?_⟩
  rw [hτ c]
  congr 2
  omega

end CFSG.Quasithin.H13.F431.D4q.Out

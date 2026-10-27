module

public import CFSG.Quasithin.Background.H11Plus
public import CFSG.Quasithin.Background.H11Minus

public section

namespace CFSG.Quasithin.H11Proof

open CFSG.Quasithin

theorem h11_main :
    ∀ (n : ℕ), 2 ≤ n → ∀ (ε : ℤ), (ε = 1 ∨ ε = -1) →
    ∀ (F : Type) [Field F], Nat.card F = 2 ^ n →
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (M : Subgroup (MulAut V)) (e : V ≃* Multiplicative (Fin 4 → F)),
      IsOrthOmega F ε e (perfectCore M) →
    ∀ A : Subgroup (MulAut V), IsA2 M A →
      (rk ↥A + n ≤ rkIdx (fixV A) + 1) ∧
      (rk ↥A + 2 ≤ rkIdx (fixV A) ∨
        (n = 2 ∧ ∃ t ∈ A, IsFTransvection F (Fin 4) (MulAut.congr e t))) ∧
      (A ≤ perfectCore M → rk ↥A + n ≤ rkIdx (fixV A)) := by
  intro n hn ε hε F _ hF V _ _ hV2 M e hO A hA
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n) (by rw [← Nat.card_eq_fintype_card, hF])
  rcases hε with rfl | rfl
  · rcases hO with ⟨-, hO⟩ | ⟨h, -⟩
    · exact h11_plus hV2 hn hF M e hO A hA
    · exact absurd h (by norm_num)
  · rcases hO with ⟨h, -⟩ | ⟨-, a, ha, hO⟩
    · exact absurd h (by norm_num)
    · exact h11_minus hV2 hn hF M e a ha hO A hA

end CFSG.Quasithin.H11Proof

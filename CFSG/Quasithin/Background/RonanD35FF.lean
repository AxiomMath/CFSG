module

public import CFSG.Quasithin.Background.RonanD35SL
public import CFSG.Quasithin.Background.RonanD35Sp4
public import CFSG.Quasithin.Background.RonanD35A6
public import CFSG.Quasithin.Background.RonanD35A7

public section

namespace CFSG.Quasithin.RonanD35

open CFSG.Quasithin CFSG.Open

private theorem ff_charP_two {K : Type} [Field K] [Finite K] {n : ℕ} (h : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, h])

theorem isFFModule_of_d35List {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L : Subgroup (MulAut W)} {V : Subgroup W} (hLs : L ≤ stabSub V)
    (h : (∃ n, BinaryNaturalSL L V (V ⊓ fixV L) 3 n) ∨ (∃ n, BinaryNaturalSp4 L V (V ⊓ fixV L) n) ∨
      AlternatingNatural L V (V ⊓ fixV L) 6 ∨ BinaryNaturalSL L V (V ⊓ fixV L) 4 1 ∨
      BinaryNaturalSL L V (V ⊓ fixV L) 5 1 ∨ A7Four L V ⊥) :
    IsFFModule (autSub L V) := by
  have hZ : ∀ g ∈ L, ∀ z ∈ V ⊓ fixV L, g z = z := fun g hg z hz => hz.2 g hg
  rcases h with ⟨n, K, _, _, hK, π, hπ⟩ | ⟨n, K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ |
    ⟨K, _, _, hK, π, hπ⟩ | ⟨α, π, hπ⟩
  · have := ff_charP_two hK
    exact isFFModule_of_natSL hW hLs hZ le_rfl hπ
  · have := ff_charP_two hK
    exact isFFModule_of_natSp4 hW hLs hZ hπ
  · exact isFFModule_of_altDn6 hW hLs hZ hπ
  · have := ff_charP_two hK
    exact isFFModule_of_natSL hW hLs hZ (by norm_num) hπ
  · have := ff_charP_two hK
    exact isFFModule_of_natSL hW hLs hZ (by norm_num) hπ
  · exact isFFModule_of_a7Four hLs hπ

end CFSG.Quasithin.RonanD35

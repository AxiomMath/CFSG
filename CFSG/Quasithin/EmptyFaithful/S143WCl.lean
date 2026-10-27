module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Kempf
public import CFSG.Quasithin.Background.G10Basic
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11

namespace S143W

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem rank_le_of_ne_bot {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
    {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (GLV V)} (hyp : G101Hyp B Γ v₁ W X X₀)
    (hX₀ : X₀ ≠ ⊥) {k : ℕ} (hk : Nat.card X = 2 ^ k) :
    Module.finrank (ZMod 2) V ≤ 2 * k := by
  have hrank := hyp.rank
  have hiso := hyp.finrank_isotropic_le
  have hd1 : 1 ≤ Module.finrank (ZMod 2) V := by
    have : 0 < Module.finrank (ZMod 2) V :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v₁, hyp.point⟩
    omega
  have hmul := Subgroup.relIndex_mul_card X₀ X
  rw [inf_eq_left.mpr hyp.X₀_le, hk] at hmul
  have hX₀card : 2 ≤ Nat.card X₀ := by
    have := (Subgroup.one_lt_card_iff_ne_bot X₀).mpr hX₀
    omega
  have hdvd : X₀.relIndex X ∣ 2 ^ k := ⟨Nat.card X₀, hmul.symm⟩
  obtain ⟨j, hj, hrj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hrj, Nat.log_pow Nat.one_lt_two] at hrank
  rw [hrj] at hmul
  have h2 : 2 ^ (j + 1) ≤ 2 ^ k := by
    rw [← hmul, pow_succ]
    exact Nat.mul_le_mul_left _ hX₀card
  have hjk : j + 1 ≤ k := (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp h2
  omega

end S143W

end CFSG.Quasithin

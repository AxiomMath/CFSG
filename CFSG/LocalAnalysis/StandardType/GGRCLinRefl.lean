module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nK7a_nat_add {a b c : ℕ} (hb : b + 1 = c) (hab : a + b = c) : a = 1 := by
  omega

private lemma l05nK7a_nat_ker {a b c : ℕ} (ha : a = 1) (hab : a + b = c) : b + 1 = c := by
  omega

private lemma l05nK7a_card_fix_eq {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] (r : V ≃ₗ[ZMod p] V) :
    Nat.card {v : V // r v = v} =
      p ^ Module.finrank (ZMod p) (LinearMap.ker ((r : V →ₗ[ZMod p] V) - LinearMap.id)) := by
  rw [FiniteField.pow_finrank_eq_natCard p
    (LinearMap.ker ((r : V →ₗ[ZMod p] V) - LinearMap.id))]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun v => by
    simp [LinearMap.mem_ker, sub_eq_zero])

private lemma l05nK7a_card_iff_move_finrank {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] (r : V ≃ₗ[ZMod p] V) :
    (p ^ Module.finrank (ZMod p) (LinearMap.ker ((r : V →ₗ[ZMod p] V) - LinearMap.id)) * p =
        p ^ Module.finrank (ZMod p) V) ↔
      Module.finrank (ZMod p) (ggLinMove r) = 1 := by
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  constructor
  · intro hcard
    have hker : Module.finrank (ZMod p)
        (LinearMap.ker ((r : V →ₗ[ZMod p] V) - LinearMap.id)) + 1 =
        Module.finrank (ZMod p) V := by
      apply Nat.pow_right_injective hp2
      show p ^ (Module.finrank (ZMod p)
          (LinearMap.ker ((r : V →ₗ[ZMod p] V) - LinearMap.id)) + 1) =
          p ^ Module.finrank (ZMod p) V
      rw [pow_succ]
      exact hcard
    have hrn := LinearMap.finrank_range_add_finrank_ker ((r : V →ₗ[ZMod p] V) - LinearMap.id)
    show Module.finrank (ZMod p)
      (LinearMap.range ((r : V →ₗ[ZMod p] V) - LinearMap.id)) = 1
    exact l05nK7a_nat_add hker hrn
  · intro hrank
    have hrange : Module.finrank (ZMod p)
        (LinearMap.range ((r : V →ₗ[ZMod p] V) - LinearMap.id)) = 1 := hrank
    have hrn := LinearMap.finrank_range_add_finrank_ker ((r : V →ₗ[ZMod p] V) - LinearMap.id)
    have hker : Module.finrank (ZMod p)
        (LinearMap.ker ((r : V →ₗ[ZMod p] V) - LinearMap.id)) + 1 =
        Module.finrank (ZMod p) V := l05nK7a_nat_ker hrange hrn
    rw [← pow_succ, hker]

theorem ggRC_isReflection_iff_linRefl {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs : Subgroup G} [Finite Bs] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V)
    (φ : MulAut ↥Bs) :
    GGIsReflection p φ ↔ GGLinRefl (ggLin (p := p) ι φ) := by
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  constructor
  · rintro ⟨h2, hcard⟩
    constructor
    · rw [← pow_two, ← map_pow, h2]
      simp
    · have hcard' : Nat.card {v : V // ggLin (p := p) ι φ v = v} * p = Nat.card V := by
        rw [← card_fixed_ggLin (p := p) ι φ, ← card_eq_of_ggLin ι]
        exact hcard
      have hpow : p ^ Module.finrank (ZMod p)
            (LinearMap.ker (((ggLin (p := p) ι φ) : V →ₗ[ZMod p] V) - LinearMap.id)) * p =
          p ^ Module.finrank (ZMod p) V := by
        rw [← l05nK7a_card_fix_eq (p := p) (ggLin (p := p) ι φ),
          FiniteField.pow_finrank_eq_natCard p V]
        exact hcard'
      exact (l05nK7a_card_iff_move_finrank (p := p) (ggLin (p := p) ι φ)).mp hpow
  · rintro ⟨h2lin, hrank⟩
    constructor
    · apply ggLin_injective (p := p) ι
      simpa [map_pow, pow_two] using h2lin
    · have hcard' : Nat.card {v : V // ggLin (p := p) ι φ v = v} * p = Nat.card V := by
        have hpow : p ^ Module.finrank (ZMod p)
              (LinearMap.ker (((ggLin (p := p) ι φ) : V →ₗ[ZMod p] V) - LinearMap.id)) * p =
            p ^ Module.finrank (ZMod p) V :=
          (l05nK7a_card_iff_move_finrank (p := p) (ggLin (p := p) ι φ)).mpr hrank
        rw [l05nK7a_card_fix_eq (p := p) (ggLin (p := p) ι φ),
          ← FiniteField.pow_finrank_eq_natCard p V]
        exact hpow
      rw [card_fixed_ggLin (p := p) ι φ, card_eq_of_ggLin ι]
      exact hcard'

end CFSG.StandardType

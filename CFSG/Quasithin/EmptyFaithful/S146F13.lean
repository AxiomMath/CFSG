module

public import CFSG.Quasithin.EmptyFaithful.S146F6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

@[expose] def Input14614Solv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ Hp : Subgroup G, H ≤ Hp → Hp ≤ mcOf T → Group.IsSolvable ↥Hp →
        (p = 3 → ∀ r : ℕ, r.Prime → r ∣ Nat.card Hp → r = 2 ∨ r = 3) ∧
          (p = 5 → ∀ r : ℕ, r.Prime → r ∣ Nat.card Hp → r = 2 ∨ r = 3 ∨ r = 5)

@[expose] def Input14614Sol : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → p = 3 →
      conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H → Group.IsSolvable ↥(mcOf T)

@[expose] def Input14614Shape : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      conjClosure (oTwoUpper H) (mcOf T) ≠ oTwoUpper H → Stage14614At T H p

theorem stage14614_of_named_inputs (i0 : Input14614Solv) (i1 : Input14614Sol)
    (i2 : Input14614Shape) : Stage14614 := by
  intro G _ _ T M S H PQ p hred hmax
  by_cases hKz : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H
  · left
    refine ⟨hKz, fun hp3 r hr hdvd => ?_⟩
    have hsolv := i1 G T M S H PQ p hred hmax hp3 hKz
    exact (i0 G T M S H PQ p hred hmax (mcOf T) (S.le_mcOf hred.isHTM) le_rfl hsolv).1 hp3 r hr hdvd
  · exact i2 G T M S H PQ p hred hmax hKz

end CFSG.Quasithin

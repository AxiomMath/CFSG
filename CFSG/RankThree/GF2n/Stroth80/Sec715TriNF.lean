module

public import CFSG.LieType.D4Small.Weights

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tri

open CFSG.LieType.D4Small

@[expose] def IsNatWt {N : ℕ} (s : ZMod N) (a : Fin 4 → ZMod N) : Prop :=
  ∃ i : Fin 4, a = Pi.single i s ∨ a = Pi.single i (-s)

@[expose] def IsSpinWt {N : ℕ} (b₀ : ZMod N) (e : ℕ) (a : Fin 4 → ZMod N) : Prop :=
  (∀ i, a i = b₀ ∨ a i = -b₀) ∧ (Finset.univ.filter fun i => a i = -b₀).card % 2 = e % 2

@[expose] def NFType {N : ℕ} (j : ℕ) (C : Finset (Fin 4 → ZMod N)) : Prop :=
  (∀ a, a ∈ C ↔ IsNatWt ((2 : ZMod N) ^ j) a) ∨
    ∃ (b₀ : ZMod N) (e : ℕ), 2 * b₀ = 2 ^ j ∧ e < 2 ∧ ∀ a, a ∈ C ↔ IsSpinWt b₀ e a

structure NF {G : Type*} [Group G] {K : Type*} [Field K] (D : D4Datum G K) {X : Type*}
    [AddCommGroup X] [Module K X] (ρ : Representation K G X) (j : ℕ)
    (C : Finset (Fin 4 → ZMod (Nat.card Kˣ))) (b : (Fin 4 → ZMod (Nat.card Kˣ)) → X) : Prop where
  ne_zero : ∀ a ∈ C, b a ≠ 0
  mem_wtSpace : ∀ a ∈ C, b a ∈ D.wtSpace ρ a
  span_eq : Submodule.span K (b '' C) = ⊤
  root : ∀ α, IsD4Root α → ∀ c : K, ∀ a ∈ C, ρ (D.x α c) (b a) =
    b a + if a + (2 : ZMod (Nat.card Kˣ)) ^ j • castW (Nat.card Kˣ) α ∈ C then
      c ^ (2 ^ j) • b (a + (2 : ZMod (Nat.card Kˣ)) ^ j • castW (Nat.card Kˣ) α) else 0

end CFSG.RankThree.GF2n.Stroth80.Tri

end

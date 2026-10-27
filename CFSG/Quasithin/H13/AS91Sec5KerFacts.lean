module

public import CFSG.Quasithin.H13.AS91Sec5Eker
public import CFSG.Quasithin.H13.AS91Sec5Stmt54Defs

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

structure KerFacts : Prop where
  card_inf_one : ∀ {m n : G ⧸ c.G2}, c.OnL c.x0 m → c.OnL c.x0 n → n ∈ c.deltaAt 1 c.x0 m →
    Nat.card ↥(c.Eker m ⊓ c.Eker n) = 2 ^ 8
  card_inf_two : ∀ {m n : G ⧸ c.G2}, c.OnL c.x0 m → c.OnL c.x0 n →
    (n ∈ c.deltaAt 2 c.x0 m ∨ n ∈ c.deltaAt 3 c.x0 m ∨ n ∈ c.deltaAt 4 c.x0 m) →
    Nat.card ↥(c.Eker m ⊓ c.Eker n) = 2 ^ 7
  smul_two : ∀ {m n : G ⧸ c.G2}, c.OnL c.x0 m → c.OnL c.x0 n →
    (n ∈ c.deltaAt 2 c.x0 m ∨ n ∈ c.deltaAt 3 c.x0 m ∨ n ∈ c.deltaAt 4 c.x0 m) →
    ∀ {p q : G ⧸ c.G1}, c.OnL p n → p ≠ c.x0 → c.OnL q n → q ≠ c.x0 → ∃ e ∈ c.Eker m, e • p = q
  orbit_one : ∀ {m n : G ⧸ c.G2}, c.OnL c.x0 m → c.OnL c.x0 n → n ∈ c.deltaAt 1 c.x0 m →
    ∀ {p : G ⧸ c.G1}, c.OnL p n → p ≠ c.x0 →
      ∃ q, c.OnL q n ∧ q ≠ c.x0 ∧ q ≠ p ∧ (∃ e ∈ c.Eker m, e • p = q) ∧
        ∀ e ∈ c.Eker m, e • p = p ∨ e • p = q
  not_le : ∀ {m n : G ⧸ c.G2}, c.OnL c.x0 m → c.OnL c.x0 n → m ≠ n → ¬ c.Eker n ≤ c.Eker m
  card_Epl : ∀ {σ : G ⧸ c.G3}, c.OnP c.x0 σ → Nat.card (c.Epl σ) = 2 ^ 7
  Epl_inj : ∀ {σ σ' : G ⧸ c.G3}, c.OnP c.x0 σ → c.OnP c.x0 σ' → c.Epl σ = c.Epl σ' → σ = σ'

theorem mem_delta_iff_mem_deltaAt (i : Fin 5) {n : G ⧸ c.G2} :
    n ∈ c.delta i ↔ n ∈ c.deltaAt i c.x0 c.l0 := by
  rw [c.mem_deltaAt_iff_frame (g := 1) (one_smul G c.x0) (one_smul G c.l0), inv_one, one_smul]

end Loc49

theorem stmt5_4_6_of_kerFacts
    (hker : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      c.KerFacts) : Stmt5_4_6 := by
  intro G _ _ z hJ c y hy hyx i hi k hk p hp q hq hpx hqx
  have hkx : c.OnL c.x0 k := hk.1.symm'
  have hk' : k ∈ c.deltaAt i c.x0 c.l0 := (c.mem_delta_iff_mem_deltaAt i).1 hk
  have hi' : k ∈ c.deltaAt 2 c.x0 c.l0 ∨ k ∈ c.deltaAt 3 c.x0 c.l0 ∨ k ∈ c.deltaAt 4 c.x0 c.l0 := by
    fin_cases i
    · exact absurd hi (by decide)
    · exact absurd hi (by decide)
    · exact Or.inl hk'
    · exact Or.inr (Or.inl hk')
    · exact Or.inr (Or.inr hk')
  obtain ⟨e, he, hep⟩ := (hker G z hJ c).smul_two (cInc_mk c.G1 c.G2 1) hkx hi' hp hpx hq hqx
  refine ⟨e, ?_, hep⟩
  rw [c.E_inf_stab_eq_Eker (cInc_mk c.G1 c.G2 1) hy hyx]
  exact he

end CFSG.Quasithin.H13.AS91

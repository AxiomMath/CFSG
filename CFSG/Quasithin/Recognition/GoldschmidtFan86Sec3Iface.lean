module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Arcs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Setting

public section

namespace CFSG.Quasithin.Fan86

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

structure LocalFacts (_F : FanTree Γ G) : Prop where
  pow_smul_eq : ∀ {v : V} {x : G} {a b : V}, x ∈ MulAction.stabilizer G v →
    orderOf x = valence Γ v → Γ.Adj v a → Γ.Adj v b → ∃ i : ℕ, x ^ i • a = b
  conj_mem : ∀ {v : V} {x g : G}, x ∈ MulAction.stabilizer G v → orderOf x = valence Γ v →
    g ∈ MulAction.stabilizer G v →
    ∃ (i : ℕ) (k : G), k ∈ nbrStab Γ G v ∧ g * x * g⁻¹ = x ^ i * k
  cyc : ∀ {v a : V}, Γ.Adj v a → ∀ S : Subgroup G,
    S ≤ MulAction.stabilizer G v ⊓ MulAction.stabilizer G a →
    ∃ g ∈ S, g ^ 4 ∈ nbrStab Γ G v ∧ ∀ s ∈ S, ∃ n : ℤ, g ^ n * s⁻¹ ∈ nbrStab Γ G v
  perm3 : ∀ {v : V}, valence Γ v = 3 → ∃ φ : ↥(MulAction.stabilizer G v) →* Equiv.Perm (Fin 3),
    Function.Surjective φ ∧ ∀ g : ↥(MulAction.stabilizer G v), φ g = 1 ↔ (g : G) ∈ nbrStab Γ G v

end CFSG.Quasithin.Fan86

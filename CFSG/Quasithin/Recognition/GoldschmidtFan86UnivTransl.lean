module

public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.Fan86.Univ

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def LocTrans (Γ : SimpleGraph V) (G : Type*) [Group G] [MulAction G V] (v : V) : Prop :=
  ∀ a b : V, Γ.Adj v a → Γ.Adj v b → ∃ g ∈ MulAction.stabilizer G v, g • a = b

@[expose] def FrobTwo (Γ : SimpleGraph V) (G : Type*) [Group G] [MulAction G V] (v : V) : Prop :=
  ∀ a b : V, Γ.Adj v a → Γ.Adj v b → a ≠ b → ∀ g ∈ MulAction.stabilizer G v,
    g • a = a → g • b = b → ∀ c : V, Γ.Adj v c → g • c = c

@[expose] def FrobNonreg (Γ : SimpleGraph V) (G : Type*) [Group G] [MulAction G V] (v : V) : Prop :=
  ∀ a : V, Γ.Adj v a → ∃ g ∈ MulAction.stabilizer G v, g • a = a ∧
    ∃ c : V, Γ.Adj v c ∧ g • c ≠ c

theorem mem_stabilizer_smul_iff (g k : G) (v : V) :
    k ∈ MulAction.stabilizer G (g • v) ↔ g⁻¹ * k * g ∈ MulAction.stabilizer G v := by
  simp only [MulAction.mem_stabilizer_iff, mul_smul]
  rw [inv_smul_eq_iff]

section Translate

variable (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
include hadj

theorem adj_inv_smul {g : G} {v a : V} (h : Γ.Adj (g • v) a) : Γ.Adj v (g⁻¹ • a) := by
  have := (hadj g⁻¹ (g • v) a).2 h
  rwa [inv_smul_smul] at this

theorem LocTrans.smul {v : V} (h : LocTrans Γ G v) (g : G) : LocTrans Γ G (g • v) := by
  intro a b ha hb
  obtain ⟨k, hk, hka⟩ := h (g⁻¹ • a) (g⁻¹ • b) (adj_inv_smul hadj ha) (adj_inv_smul hadj hb)
  refine ⟨g * k * g⁻¹, ?_, ?_⟩
  · rw [mem_stabilizer_smul_iff]
    simpa [mul_assoc] using hk
  · rw [mul_smul, mul_smul, hka, smul_inv_smul]

theorem FrobTwo.smul {v : V} (h : FrobTwo Γ G v) (g : G) : FrobTwo Γ G (g • v) := by
  intro a b ha hb hab k hk hka hkb c hc
  have hk' : g⁻¹ * k * g ∈ MulAction.stabilizer G v := (mem_stabilizer_smul_iff g k v).1 hk
  have hfix : ∀ w : V, k • w = w → (g⁻¹ * k * g) • (g⁻¹ • w) = g⁻¹ • w := fun w hw => by
    rw [mul_smul, mul_smul, smul_inv_smul, hw]
  have := h (g⁻¹ • a) (g⁻¹ • b) (adj_inv_smul hadj ha) (adj_inv_smul hadj hb)
    (fun e => hab (MulAction.injective g⁻¹ e)) _ hk' (hfix a hka) (hfix b hkb) (g⁻¹ • c)
    (adj_inv_smul hadj hc)
  have h2 : g • ((g⁻¹ * k * g) • (g⁻¹ • c)) = g • (g⁻¹ • c) := congrArg (g • ·) this
  rw [mul_smul, mul_smul, smul_inv_smul, smul_inv_smul] at h2
  simpa using h2

theorem FrobNonreg.smul {v : V} (h : FrobNonreg Γ G v) (g : G) : FrobNonreg Γ G (g • v) := by
  intro a ha
  obtain ⟨k, hk, hka, c, hc, hkc⟩ := h (g⁻¹ • a) (adj_inv_smul hadj ha)
  refine ⟨g * k * g⁻¹, ?_, ?_, g • c, (hadj g v c).2 hc, ?_⟩
  · rw [mem_stabilizer_smul_iff]
    simpa [mul_assoc] using hk
  · rw [mul_smul, mul_smul, hka, smul_inv_smul]
  · intro e
    rw [mul_smul, mul_smul, inv_smul_smul] at e
    exact hkc (MulAction.injective g e)

theorem frobTwo_of_card_three {v : V} (hv : Nat.card (Γ.neighborSet v) = 3) :
    FrobTwo Γ G v := by
  intro a b ha hb hab k hk hka hkb c hc
  by_cases hca : c = a
  · rw [hca]; exact hka
  by_cases hcb : c = b
  · rw [hcb]; exact hkb
  have hk0 : k • v = v := MulAction.mem_stabilizer_iff.1 hk
  have hkc : Γ.Adj v (k • c) := by
    have := (hadj k v c).2 hc
    rwa [hk0] at this
  have hcard : (Γ.neighborSet v).ncard = 3 := by rwa [← Nat.card_coe_set_eq]
  have hfin : (Γ.neighborSet v).Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hsub : ({a, b, c} : Set V) ⊆ Γ.neighborSet v := by
    intro w hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have h3 : ({a, b, c} : Set V).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨a, b, c, hab, fun e => hca e.symm, fun e => hcb e.symm, rfl⟩
  have heq : ({a, b, c} : Set V) = Γ.neighborSet v :=
    Set.eq_of_subset_of_ncard_le hsub (by omega) hfin
  have hmem : k • c ∈ ({a, b, c} : Set V) := by
    rw [heq]
    exact hkc
  rcases hmem with h1 | h1 | h1
  · exact absurd (MulAction.injective k (h1.trans hka.symm)) hca
  · exact absurd (MulAction.injective k (h1.trans hkb.symm)) hcb
  · exact h1

end Translate

end CFSG.Quasithin.Fan86.Univ

module

public import CFSG.Quasithin.H13.A6Setting134
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def InW1 (x : P6) : Prop :=
  Multiplicative.toAdd x 0 = Multiplicative.toAdd x 1 ∧
    Multiplicative.toAdd x 1 = Multiplicative.toAdd x 2 ∧
    Multiplicative.toAdd x 2 = Multiplicative.toAdd x 3 ∧
    Multiplicative.toAdd x 4 = Multiplicative.toAdd x 5

instance : DecidablePred InW1 := fun x =>
  inferInstanceAs (Decidable (Multiplicative.toAdd x 0 = Multiplicative.toAdd x 1 ∧
    Multiplicative.toAdd x 1 = Multiplicative.toAdd x 2 ∧
    Multiplicative.toAdd x 2 = Multiplicative.toAdd x 3 ∧
    Multiplicative.toAdd x 4 = Multiplicative.toAdd x 5))

theorem inW1_of_fixed : ∀ x : P6,
    G6.permAct 6 (swap 0 1 * swap 2 3) x = x → G6.permAct 6 (swap 0 2 * swap 1 3) x = x →
    G6.permAct 6 (swap 0 1 * swap 4 5) x = x → InW1 x := by
  decide +kernel

theorem fixed_of_inW1 : ∀ σ : Perm (Fin 6), InD6 σ → ∀ x : P6, InW1 x →
    G6.permAct 6 σ x = x := by
  decide +kernel

theorem gens_DA :
    (InD6 (swap 0 1 * swap 2 3) ∧ swap (0 : Fin 6) 1 * swap 2 3 ∈ alternatingGroup (Fin 6)) ∧
    (InD6 (swap 0 2 * swap 1 3) ∧ swap (0 : Fin 6) 2 * swap 1 3 ∈ alternatingGroup (Fin 6)) ∧
    (InD6 (swap 0 1 * swap 4 5) ∧ swap (0 : Fin 6) 1 * swap 4 5 ∈ alternatingGroup (Fin 6)) := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide

theorem sq_P6 : ∀ y : P6, y ^ 2 = 1 := by decide

@[expose] def e0123 : P6 := Multiplicative.ofAdd ![1, 1, 1, 1, 0, 0]

@[expose] def e45 : P6 := Multiplicative.ofAdd ![0, 0, 0, 0, 1, 1]

theorem e0123_mem : e0123 ∈ G6.coreMod 6 := G6.mem_coreMod.2 (by decide)

theorem e45_mem : e45 ∈ G6.coreMod 6 := G6.mem_coreMod.2 (by decide)

theorem W1_cases : ∀ y : P6, y ∈ G6.coreMod 6 → InW1 y →
    y = 1 ∨ y = G6.allOnes 6 ∨ y = e0123 ∨ y = e45 := by
  intro y hy
  rw [G6.mem_coreMod] at hy
  revert y
  decide +kernel

@[expose] def W1sub : Subgroup ↥(G6.coreMod 6) where
  carrier := {y | InW1 (y : P6)}
  one_mem' := by decide
  mul_mem' := fun {a b} ha hb => (by
    have key : ∀ a b : P6, InW1 a → InW1 b → InW1 (a * b) := by decide +kernel
    exact key _ _ ha hb)
  inv_mem' := fun {a} ha => (by
    have key : ∀ a : P6, InW1 a → InW1 a⁻¹ := by decide +kernel
    exact key _ ha)

theorem mem_W1sub {y : ↥(G6.coreMod 6)} : y ∈ W1sub ↔ InW1 (y : P6) := Iff.rfl

theorem card_W1sub : Nat.card ↥W1sub = 4 := by
  have : Fintype.card {y : ↥(G6.coreMod 6) // InW1 (y : P6)} = 4 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

namespace Setting134

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting134 G T L V)
include S

theorem fixed_of_centralizes {x : G} (hxV : x ∈ V)
    (hx : ∀ t ∈ T, t * x = x * t) {σ : Perm (Fin 6)} (hσD : InD6 σ)
    (hσA : σ ∈ alternatingGroup (Fin 6)) :
    G6.permAct 6 σ (S.frame.ψ ⟨x, hxV⟩ : P6) = S.frame.ψ ⟨x, hxV⟩ := by
  obtain ⟨g, hgT, rfl⟩ := S.frame.DA_T σ hσD hσA
  have hc : (g : G) * x * (g : G)⁻¹ = x := by
    rw [hx (g : G) hgT, mul_inv_cancel_right]
  have := congrArg Subtype.val ((S.conj_eq_iff g ⟨x, hxV⟩).1 hc)
  rwa [G6.coreAct_coe] at this

theorem mem_V1_iff {x : G} :
    x ∈ fsuV1 T V ↔ ∃ h : x ∈ V, InW1 (S.frame.ψ ⟨x, h⟩ : P6) := by
  constructor
  · rintro ⟨hxV, hxZ⟩
    obtain ⟨-, hxC, -⟩ := mem_quasithinOmegaOneCenter_iff.1 hxZ
    have hx : ∀ t ∈ T, t * x = x * t := fun t ht =>
      (Subgroup.mem_centralizer_iff.1 hxC t ht)
    obtain ⟨⟨d1, a1⟩, ⟨d2, a2⟩, ⟨d3, a3⟩⟩ := gens_DA
    exact ⟨hxV, inW1_of_fixed _ (S.fixed_of_centralizes hxV hx d1 a1)
      (S.fixed_of_centralizes hxV hx d2 a2) (S.fixed_of_centralizes hxV hx d3 a3)⟩
  · rintro ⟨hxV, hW⟩
    refine ⟨hxV, mem_quasithinOmegaOneCenter_iff.2 ⟨S.V_le_T hxV, ?_, ?_⟩⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have hfix := fixed_of_inW1 _ (S.frame.T_D ⟨t, S.frame.T_le ht⟩ ht) _ hW
      have hc : t * x * t⁻¹ = x := (S.conj_eq_iff ⟨t, S.frame.T_le ht⟩ ⟨x, hxV⟩).2
        (Subtype.ext (by rw [G6.coreAct_coe]; exact hfix))
      calc t * x = t * x * t⁻¹ * t := by group
        _ = x * t := by rw [hc]
    · have h : (⟨x, hxV⟩ : ↥V) ^ 2 = 1 := by
        apply S.frame.ψ.injective
        rw [map_pow, map_one]
        exact Subtype.ext (by rw [Subgroup.coe_pow]; exact sq_P6 _)
      exact congrArg Subtype.val h

theorem card_pre (Y : Subgroup ↥(G6.coreMod 6)) : Nat.card ↥(S.pre Y) = Nat.card ↥Y := by
  rw [Setting134.pre, Subgroup.card_map_of_injective V.subtype_injective,
    Subgroup.comap_equiv_eq_map_symm',
    Subgroup.card_map_of_injective (f := S.frame.ψ.symm.toMonoidHom) S.frame.ψ.symm.injective]

theorem V1_eq_pre : fsuV1 T V = S.pre W1sub := by
  ext x
  rw [S.mem_pre, S.mem_V1_iff]
  rfl

theorem card_V1 : Nat.card ↥(fsuV1 T V) = 4 := by
  rw [S.V1_eq_pre, S.card_pre, card_W1sub]

end Setting134

end CFSG.Quasithin.H13.A6

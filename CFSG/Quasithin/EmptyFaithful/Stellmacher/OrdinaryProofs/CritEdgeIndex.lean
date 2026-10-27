module

public import CFSG.Quasithin.EmptyFaithful.SzF53BasC

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

open CFSG.Quasithin.F53 CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem relIndex_Qv_three (hA : F53Amalgam H M S) {μ : Geo H M} (hμ : vtype μ = true) :
    (Qv μ).relIndex (stab μ) = 6 := by
  obtain ⟨φ⟩ := quot_stab_three hA hμ
  have hc : Nat.card (OTwoQuot (stab μ)) = 6 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_perm]
    simp [Nat.factorial]
  have h := S152Fin.card_OTwoQuot (stab μ)
  rw [hc] at h
  exact h.symm

theorem relIndex_inf_three (hA : F53Amalgam H M S) {δ μ : Geo H M} (h : μ ∈ nbrs δ)
    (hμ : vtype μ = true) :
    (stab δ ⊓ stab μ).relIndex (stab μ) = 3 := by
  obtain ⟨φ⟩ := quot_stab_three hA hμ
  have hc : Nat.card (OTwoQuot (stab μ)) = 2 ^ 1 * 3 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_perm]
    simp [Nat.factorial]
  exact index_sylow_eq_of_card_quot (sylow_stab_inf_right hA h) (by decide) hc

theorem relIndex_Qv_inf (hA : F53Amalgam H M S) {δ μ : Geo H M} (h : μ ∈ nbrs δ)
    (hμ : vtype μ = true) :
    (Qv μ).relIndex (stab δ ⊓ stab μ) = 2 := by
  have hQ : Qv μ ≤ stab δ ⊓ stab μ :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (sylow_stab_inf_right hA h)
  have hm := Subgroup.relIndex_mul_relIndex (Qv μ) (stab δ ⊓ stab μ) (stab μ) hQ inf_le_right
  rw [relIndex_inf_three hA h hμ, relIndex_Qv_three hA hμ] at hm
  omega

theorem Qv_le_or_sup_eq (hA : F53Amalgam H M S) {δ μ : Geo H M} (h : μ ∈ nbrs δ)
    (hμ : vtype μ = true) :
    Qv δ ≤ Qv μ ∨ Qv δ ⊔ Qv μ = stab δ ⊓ stab μ := by
  have hQδ : Qv δ ≤ stab δ ⊓ stab μ :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (sylow_stab_inf_left hA h)
  have hQμ : Qv μ ≤ stab δ ⊓ stab μ :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (sylow_stab_inf_right hA h)
  by_cases hle : Qv δ ≤ Qv μ
  · exact Or.inl hle
  · right
    have hK : Qv μ ≤ Qv δ ⊔ Qv μ := le_sup_right
    rcases eq_or_eq_of_le_of_index_prime hK (sup_le hQδ hQμ) Nat.prime_two
        (relIndex_Qv_inf hA h hμ) with h1 | h1
    · have hl : Qv δ ≤ Qv δ ⊔ Qv μ := le_sup_left
      rw [h1] at hl
      exact absurd hl hle
    · exact h1

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

end

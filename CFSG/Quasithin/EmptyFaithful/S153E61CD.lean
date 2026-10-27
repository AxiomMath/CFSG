module

public import CFSG.Quasithin.EmptyFaithful.S153E61CC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement Pointwise MatrixGroups

namespace S153E61C

section Nat

variable {G : Type} [Group G]

theorem sl2_trans : ∀ u w : Fin 2 → ZMod 2, u ≠ 0 → w ≠ 0 → ∃ A : SL(2, ZMod 2), A • u = w := by
  decide +kernel

theorem component_ne_zero (x : Multiplicative (Fin 1 → Fin 2 → ZMod 2)) (hx : x ≠ 1) :
    Multiplicative.toAdd x 0 ≠ 0 := by
  intro h0
  apply hx
  have : Multiplicative.toAdd x = 0 := by
    funext j
    rw [Subsingleton.elim j 0]
    exact h0
  rw [← ofAdd_toAdd x, this]
  rfl

theorem exists_conj_of_nat {M Si S S₂ : Subgroup G} (h : IsSumOfNatSL2ModulesN153 1 M Si S S₂)
    (hM : ∀ m ∈ M, ∀ x ∈ Si, m * x * m⁻¹ ∈ Si) :
    ∀ a ∈ Si, a ∉ S₂ → ∀ b ∈ Si, b ∉ S₂ → ∃ m ∈ M, m * a * m⁻¹ * b⁻¹ ∈ S₂ := by
  obtain ⟨β, φ, hβs, -, -, hφk, hφN⟩ := h
  intro a ha haV b hb hbV
  have ha1 : φ ⟨a, ha⟩ ≠ 1 := fun h1 => haV ((hφk _).1 h1)
  have hb1 : φ ⟨b, hb⟩ ≠ 1 := fun h1 => hbV ((hφk _).1 h1)
  obtain ⟨A, hA⟩ := sl2_trans _ _ (component_ne_zero _ ha1) (component_ne_zero _ hb1)
  obtain ⟨m, hm⟩ := hβs A
  refine ⟨(m : G), m.2, ?_⟩
  have hy : (m : G) * a * (m : G)⁻¹ ∈ Si := hM _ m.2 a ha
  have hφy := hφN m ⟨a, ha⟩ ⟨_, hy⟩ rfl
  have heq : φ ⟨_, hy⟩ = φ ⟨b, hb⟩ := by
    rw [hφy, ← ofAdd_toAdd (φ ⟨b, hb⟩)]
    congr 1
    funext j
    rw [Subsingleton.elim j 0, hm]
    exact hA
  have h1 : φ (⟨_, hy⟩ * ⟨b, hb⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, heq]
    exact mul_inv_cancel _
  exact (hφk _).1 h1

theorem exists_not_mem_of_nat {M Si S S₂ : Subgroup G} (h : IsSumOfNatSL2ModulesN153 1 M Si S S₂) :
    ∃ a ∈ Si, a ∉ S₂ := by
  obtain ⟨β, φ, -, -, hφs, hφk, -⟩ := h
  obtain ⟨⟨a, ha⟩, hax⟩ := hφs (Multiplicative.ofAdd (fun _ _ => 1))
  refine ⟨a, ha, fun haV => ?_⟩
  have h1 := (hφk ⟨a, ha⟩).2 haV
  rw [hax] at h1
  have h2 := congrFun (congrFun (ofAdd_eq_one.1 h1) 0) 0
  revert h2
  decide

end Nat

section Chain

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem inv_P_mem_Pi_of_chain (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15359 cx N₁ N₂ g s y t₁) :
    ∀ x ∈ Pgp153 T M V₁ Mc g, x * x = 1 →
      x ∈ Pi153 T Mc M V₁ N₁ g ∨ x ∈ Pi153 T Mc M V₁ N₂ g := by
  obtain rfl := c.h58.two_s
  have pd := S153E55.pdecomp cx c.toChain15354
  have hsq := Pi_sq_eq_one cx c.toChain15354
  refine inv_mem_P₁_or_P₂ pd hsq.1 hsq.2 ?_ ?_ ?_ ?_
  · exact exists_conj_of_nat c.h54.four_nat₁ fun m hm x hx => pd.conj_P₁ (pd.N₁_le_I hm) hx
  · exact exists_conj_of_nat c.h54.four_nat₂ fun m hm x hx => pd.conj_P₂ (pd.N₂_le_I hm) hx
  · exact exists_not_mem_of_nat c.h54.four_nat₁
  · intro x hxP hxc
    have hx : x ∈ centerOf (Pgp153 T M V₁ Mc g) := ⟨hxP, Subgroup.mem_centralizer_iff.2 hxc⟩
    rw [← c.h55.2] at hx
    exact hx

end Chain

end S153E61C

end CFSG.Quasithin

module

public import CFSG.Milestones.ASVolI.F7

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.CosetGeom CFSG.ASVolI.ChF

variable {G : Type} [Group G]

section Off

variable [Finite G]

@[expose] noncomputable def off (X Y : Subgroup G) : ℕ :=
  mIdx X (X ⊓ Subgroup.centralizer (Y : Set G))

theorem mIdx_conjSub (g : G) (X Y : Subgroup G) : mIdx (conjSub g X) (conjSub g Y) = mIdx X Y := by
  unfold mIdx conjSub
  rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

theorem off_conjSub (g : G) (X Y : Subgroup G) : off (conjSub g X) (conjSub g Y) = off X Y := by
  unfold off
  rw [conjSub_centralizer, ← conjSub_inf, mIdx_conjSub]

theorem noOffender_conj {G₁ G₂ V : Subgroup G} (hN : G₁ ≤ Subgroup.normalizer (V : Set G))
    (hD1 : ∀ A : Subgroup G, A ≤ pCoreOf 2 (G₁ ⊓ G₂) → ¬ A ≤ Subgroup.centralizer (V : Set G) →
      off A V < off V A)
    {y : G} (hy : y ∈ G₁) {A : Subgroup G} (hA : A ≤ pCoreOf 2 (conjSub y (G₁ ⊓ G₂)))
    (hAV : ¬ A ≤ Subgroup.centralizer (V : Set G)) : off A V < off V A := by
  have hVy : conjSub y V = V := F7.conjSub_eq_of_mem_normalizer (hN hy)
  have hA₀ : conjSub y⁻¹ A ≤ pCoreOf 2 (G₁ ⊓ G₂) := by
    rw [pCoreOf_conjSub] at hA
    exact (le_conjSub_iff y).mp hA
  have hA₀V : ¬ conjSub y⁻¹ A ≤ Subgroup.centralizer (V : Set G) := by
    intro h
    apply hAV
    have h1 := conjSub_mono y h
    rwa [conjSub_inv_conjSub, ← conjSub_centralizer, hVy] at h1
  have h2 := hD1 _ hA₀ hA₀V
  have e1 := off_conjSub y (conjSub y⁻¹ A) V
  have e2 := off_conjSub y V (conjSub y⁻¹ A)
  rw [conjSub_inv_conjSub, hVy] at e1 e2
  rw [e1, e2]
  exact h2

end Off

section Geometry

variable {G₀ G₁ G₂ T V : Subgroup G}

theorem stab_nbr_inf (hyp : AmalgamHypV G₀ G₁ G₂ T V) {β : CosetGeom G₀ G₁ G₂}
    (hβ : β ∈ nbrs (γ₀ G₀ G₁ G₂)) :
    ∃ y ∈ G₁, stab β ⊓ stab (γ₀ G₀ G₁ G₂) = conjSub y (G₁ ⊓ G₂) := by
  have hγ₁ : γ₁ G₀ G₁ G₂ ∈ nbrs (γ₀ G₀ G₁ G₂) := adj_γ₀_γ₁
  obtain ⟨x, hx, hxβ⟩ := stab_transitive_on_nbrs hγ₁ hβ
  have hxG₁ : (x : G) ∈ G₁ := by rwa [stab_γ₀ hyp.le₁] at hx
  refine ⟨x, hxG₁, ?_⟩
  rw [← hxβ, stab_smul, stab_γ₁ hyp.le₂, stab_γ₀ hyp.le₁, conjSub_inf,
    F7.conjSub_eq_of_mem hxG₁, inf_comm]

end Geometry

variable [Finite G]

theorem leaf_E3 :
    ∀ (G : Type) [Group G] [Finite G] (G₀ G₁ G₂ T V : Subgroup G), AmalgamHypV G₀ G₁ G₂ T V →
      V ≠ ⊥ →
      (∀ A : Subgroup G, A ≤ pCoreOf 2 (G₁ ⊓ G₂) → ¬ A ≤ Subgroup.centralizer (V : Set G) →
        mIdx A (A ⊓ Subgroup.centralizer (V : Set G)) <
          mIdx V (V ⊓ Subgroup.centralizer (A : Set G))) →
      Odd (critDist G₀ G₁ G₂ V) := by
  intro G _ _ G₀ G₁ G₂ T V hyp hV hD1
  by_contra hodd
  have heven : Even (critDist G₀ G₁ G₂ V) := Nat.not_odd_iff_even.mp hodd
  have hN := hyp.normalizes
  obtain ⟨hb0, -, -⟩ := critDist_spec hyp hV
  obtain ⟨γ, hγd, hγV⟩ := exists_dist_eq_critDist_not_le hyp hV
  have hvt : vtype γ = false := vtype_eq_false_of_even hyp.gen (by rw [hγd]; exact heven)
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hvt
  obtain ⟨hne, -, -, -⟩ := commutator_V_Vv_of_even hyp hV heven hγd hγV
  rw [Vv_smul_γ₀ hN] at hne
  have hWV : ¬ conjSub (g : G) V ≤ Subgroup.centralizer (V : Set G) := fun h =>
    hne (by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h)
  have hI : off (conjSub (g : G) V) V < off V (conjSub (g : G) V) := by
    obtain ⟨β, hβ, hdβ⟩ := exists_adj_dist_eq hyp.gen (α := g • γ₀ G₀ G₁ G₂)
      (δ := γ₀ G₀ G₁ G₂) (d := critDist G₀ G₁ G₂ V - 1)
      (by rw [CFSG.Quasithin.CosetGeom.dist_comm, hγd]; omega)
    have hlt : dist (g • γ₀ G₀ G₁ G₂) β < critDist G₀ G₁ G₂ V := by omega
    have hW := (conjSub_V_le_pCoreOf hyp hV g hlt (mem_nbrs_symm hβ)).2
    obtain ⟨y, hy, hyeq⟩ := stab_nbr_inf hyp hβ
    rw [hyeq] at hW
    exact noOffender_conj hN hD1 hy hW hWV
  have hII : off V (conjSub (g : G) V) < off (conjSub (g : G) V) V := by
    obtain ⟨δ, hδ, hdδ⟩ := exists_adj_dist_eq hyp.gen (α := γ₀ G₀ G₁ G₂)
      (δ := g • γ₀ G₀ G₁ G₂) (d := critDist G₀ G₁ G₂ V - 1) (by rw [hγd]; omega)
    have hlt : δ ∈ ballLT (critDist G₀ G₁ G₂ V) (γ₀ G₀ G₁ G₂) := by
      show dist (γ₀ G₀ G₁ G₂) δ < _
      omega
    have hVδ := (V_le_pCoreOf_of_dist_lt hyp hV hlt (mem_nbrs_symm hδ)).2
    have hV' : conjSub (g : G)⁻¹ V ≤ pCoreOf 2 (stab (g⁻¹ • δ) ⊓ stab (γ₀ G₀ G₁ G₂)) := by
      have h1 := conjSub_mono (g : G)⁻¹ hVδ
      rw [← pCoreOf_conjSub, conjSub_inf] at h1
      have e1 : conjSub (g : G)⁻¹ (stab δ) = stab (g⁻¹ • δ) := by
        rw [stab_smul, Subgroup.coe_inv]
      have e2 : conjSub (g : G)⁻¹ (stab (g • γ₀ G₀ G₁ G₂)) = stab (γ₀ G₀ G₁ G₂) := by
        have := stab_smul g⁻¹ (g • γ₀ G₀ G₁ G₂)
        rw [inv_smul_smul, Subgroup.coe_inv] at this
        exact this.symm
      rw [e1, e2] at h1
      exact h1
    have hadj : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) (g⁻¹ • δ) := by
      have := (smul_adj g⁻¹).mpr hδ
      rwa [inv_smul_smul] at this
    obtain ⟨y, hy, hyeq⟩ := stab_nbr_inf hyp (show g⁻¹ • δ ∈ nbrs (γ₀ G₀ G₁ G₂) from hadj)
    rw [hyeq] at hV'
    have hV'C : ¬ conjSub (g : G)⁻¹ V ≤ Subgroup.centralizer (V : Set G) := by
      intro h
      apply hne
      have h1 := conjSub_mono (g : G) h
      rw [conjSub_inv_conjSub, ← conjSub_centralizer] at h1
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1
    have h2 := noOffender_conj hN hD1 hy hV' hV'C
    have e1 := off_conjSub (g : G) (conjSub (g : G)⁻¹ V) V
    have e2 := off_conjSub (g : G) V (conjSub (g : G)⁻¹ V)
    rw [conjSub_inv_conjSub] at e1 e2
    rw [e1, e2]
    exact h2
  omega

end CFSG.Quasithin.H13.NFa2

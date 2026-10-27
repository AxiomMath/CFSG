module

public import CFSG.Quasithin.Background.F7

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G]

section Amalgam

variable [Finite G] {G₀ G₁ G₂ T V : Subgroup G}

theorem exists_even_pair (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    (hb : Even (critDist G₀ G₁ G₂ V)) :
    ∃ y : G, conjSub y V ≤ pCoreOf 2 (G₁ ⊓ G₂) ∧ conjSub y⁻¹ V ≤ pCoreOf 2 (G₁ ⊓ G₂) ∧
      ⁅V, conjSub y V⁆ ≠ ⊥ := by
  have hN := hyp.normalizes
  obtain ⟨γ, hγ⟩ := exists_isCriticalVertex hyp hV
  have hb0 := (critDist_spec hyp hV).1
  have hgeo := hγ.geodesic
  have hvt : vtype γ = false := vtype_eq_false_of_even hyp.gen (by rw [hγ.dist_eq]; exact hb)
  obtain ⟨x, rfl⟩ := exists_smul_eq_γ₀ hvt
  have hne := (commutator_V_Vv_of_even hyp hV hb hγ.dist_eq hγ.not_le).1
  rw [Vv_smul_γ₀ hN] at hne
  have hA : conjSub (x : G) V ≤ pCoreOf 2 (G₁ ⊓ G₂) := by
    have h1 := (conjSub_V_le_pCoreOf hyp hV x (γ := γ₁ G₀ G₁ G₂) (δ := γ₀ G₀ G₁ G₂)
      (by rw [CosetGeom.dist_comm]; omega) (mem_nbrs_symm adj_γ₀_γ₁)).2
    rwa [stab_γ₁ hyp.le₂, stab_γ₀ hyp.le₁, inf_comm] at h1
  obtain ⟨γ', hγ'adj, hγ'd⟩ := exists_adj_dist_eq hyp.gen (α := γ₀ G₀ G₁ G₂)
    (δ := x • γ₀ G₀ G₁ G₂) (d := critDist G₀ G₁ G₂ V - 1) (by rw [hγ.dist_eq]; omega)
  have hV' := (conjSub_V_le_pCoreOf hyp hV 1 (γ := γ') (δ := x • γ₀ G₀ G₁ G₂)
    (by rw [one_smul, hγ'd]; omega) (mem_nbrs_symm hγ'adj)).2
  rw [Subgroup.coe_one, conjSub_one] at hV'
  have hδ : x⁻¹ • γ' ∈ nbrs (γ₀ G₀ G₁ G₂) := by
    have h1 := (smul_adj x⁻¹).mpr hγ'adj
    rwa [inv_smul_smul] at h1
  have hγ₁γ₀ : γ₁ G₀ G₁ G₂ ∈ nbrs (γ₀ G₀ G₁ G₂) := adj_γ₀_γ₁
  obtain ⟨k, hk, hkγ⟩ := stab_transitive_on_nbrs hγ₁γ₀ hδ
  have hkG₁ : (k : G) ∈ G₁ := by rwa [stab_γ₀ hyp.le₁] at hk
  have hγ'eq : γ' = (x * k) • γ₁ G₀ G₁ G₂ := by rw [mul_smul, hkγ, smul_inv_smul]
  have hγeq : x • γ₀ G₀ G₁ G₂ = (x * k) • γ₀ G₀ G₁ G₂ := by
    rw [mul_smul, smul_eq_of_mem_stab hk]
  rw [hγ'eq, hγeq, stab_smul, stab_smul, ← conjSub_inf, pCoreOf_conjSub, stab_γ₁ hyp.le₂,
    stab_γ₀ hyp.le₁, inf_comm] at hV'
  have hy : conjSub ((x * k : ↥G₀) : G) V = conjSub (x : G) V := by
    rw [Subgroup.coe_mul, conjSub_mul, F7.conjSub_eq_of_mem_normalizer (hN hkG₁)]
  refine ⟨((x * k : ↥G₀) : G), hy ▸ hA, ?_, hy ▸ hne⟩
  rw [conjSub_le_iff, inv_inv]
  exact hV'

theorem exists_odd_data (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    (hb : Odd (critDist G₀ G₁ G₂ V)) (hb2 : 2 ≤ critDist G₀ G₁ G₂ V) :
    ∃ g : G, V ≤ conjSub g G₂ ∧ ¬ V ≤ conjSub g (pCoreOf 2 G₂) ∧
      (∃ h ∈ G₂, conjSub g (conjClosure V G₂) ≤ conjSub h (pCoreOf 2 (G₁ ⊓ G₂))) ∧
      ∃ h ∈ G₂, conjClosure V G₂ ≤ conjSub (g * h) (pCoreOf 2 (G₁ ⊓ G₂)) := by
  have hN := hyp.normalizes
  obtain ⟨γ, hγ⟩ := exists_isCriticalVertex hyp hV
  have hvt : vtype γ = true := vtype_eq_true_of_odd hyp.gen (by rw [hγ.dist_eq]; exact hb)
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hvt
  have hstab : stab (g • γ₁ G₀ G₁ G₂) = conjSub (g : G) G₂ := by rw [stab_smul, stab_γ₁ hyp.le₂]
  have hγ₀γ₁ : γ₀ G₀ G₁ G₂ ∈ nbrs (γ₁ G₀ G₁ G₂) := mem_nbrs_symm adj_γ₀_γ₁
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · rw [← hstab]
    exact V_le_stab_of_dist_le hyp hV hγ.dist_eq.le
  · intro hle
    apply hγ.not_le
    refine le_trans ?_ (pCoreOf_stab_le_ballStab_one hyp.toAmalgamHyp _)
    rw [hstab, pCoreOf_conjSub]
    exact hle
  · obtain ⟨-, γ₂, hγ₂, hd₂⟩ := exists_nbrs_of_geodesic hyp.gen hγ.geodesic hb2
    have h1 := Vv_le_pCoreOf_stab_inf hyp hV hγ₂ hd₂
    rw [Vv_smul hN, Vv_γ₁ hyp.le₂ hN] at h1
    obtain ⟨k, hk, hkγ⟩ := stab_transitive_on_nbrs hγ₀γ₁ hγ₂
    have hkG₂ : (k : G) ∈ G₂ := by rwa [stab_γ₁ hyp.le₂] at hk
    have e : stab (γ₁ G₀ G₁ G₂) ⊓ stab γ₂ = conjSub (k : G) (G₁ ⊓ G₂) := by
      rw [← hkγ, stab_smul, stab_γ₀ hyp.le₁, stab_γ₁ hyp.le₂, conjSub_inf,
        F7.conjSub_eq_of_mem hkG₂, inf_comm]
    rw [e, pCoreOf_conjSub] at h1
    exact ⟨k, hkG₂, h1⟩
  · obtain ⟨⟨γ', hγ', hd'⟩, -⟩ := exists_nbrs_of_geodesic hyp.gen hγ.geodesic hb2
    have h1 := Vv_γ₁_le_pCoreOf_stab_inf hyp hV hγ' hd'
    rw [Vv_γ₁ hyp.le₂ hN] at h1
    have hδ : g⁻¹ • γ' ∈ nbrs (γ₁ G₀ G₁ G₂) := by
      have h2 := (smul_adj g⁻¹).mpr hγ'
      rw [inv_smul_smul] at h2
      exact mem_nbrs_symm h2
    obtain ⟨k, hk, hkγ⟩ := stab_transitive_on_nbrs hγ₀γ₁ hδ
    have hkG₂ : (k : G) ∈ G₂ := by rwa [stab_γ₁ hyp.le₂] at hk
    have hγ'eq : γ' = (g * k) • γ₀ G₀ G₁ G₂ := by rw [mul_smul, hkγ, smul_inv_smul]
    have hγeq : g • γ₁ G₀ G₁ G₂ = (g * k) • γ₁ G₀ G₁ G₂ := by
      rw [mul_smul, smul_eq_of_mem_stab hk]
    rw [hγ'eq, hγeq, stab_smul, stab_smul, ← conjSub_inf, pCoreOf_conjSub, stab_γ₀ hyp.le₁,
      stab_γ₁ hyp.le₂, Subgroup.coe_mul] at h1
    exact ⟨k, hkG₂, h1⟩

end Amalgam

end CFSG.Quasithin.Vol2.Ch11.SecG

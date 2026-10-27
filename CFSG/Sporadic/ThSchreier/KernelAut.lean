
module


public import CFSG.Sporadic.ThSchreier.FullAutCore

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.ComponentClassification.OuterAutomorphisms Pointwise

variable (h : Kernel.KernelFacts)
include h

theorem stabilizer_planeStar_kernel :
    MulAction.stabilizer J planeStar = localH.map (MulAut.conj transporterV).toMonoidHom := by
  rw [planeStar, MulAction.stabilizer_smul_eq_stabilizer_map_conj, Kernel.stabilizer_planeWSet h]

theorem isCoatom_stabilizer_planeStar_kernel : IsCoatom (MulAction.stabilizer J planeStar) := by
  have := Kernel.isPreprimitive_planeX h
  have hnt : Nontrivial planeX := by
    rw [Set.nontrivial_coe_sort, ← Set.one_lt_ncard_iff_nontrivial, Kernel.ncard_planeX h]
    norm_num
  have hmem : planeStar ∈ planeX := ⟨transporterV, rfl⟩
  have hc := MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := J)
    (⟨planeStar, hmem⟩ : planeX)
  have e : MulAction.stabilizer J (⟨planeStar, hmem⟩ : planeX) =
      MulAction.stabilizer J planeStar := by
    ext g
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, Subtype.ext_iff]
    rfl
  rwa [e] at hc

theorem twoM1_eq_centralizer_kernel :
    twoM1 = Subgroup.centralizer {twoR} := by
  rw [twoM1, ← Kernel.centralizer_a_eq_M h, centralizer_map_conj]
  rfl

theorem sup_twoM1_eq_top_kernel :
    M ⊔ twoM1 = ⊤ := by
  have hK := isCoatom_stabilizer_planeStar_kernel h
  rw [stabilizer_planeStar_kernel h] at hK
  have hCa := Kernel.centralizer_a_eq_M h
  have hle : localH.map (MulAut.conj transporterV).toMonoidHom ≤ M ⊔ twoM1 := by
    rw [localH_eq_twoH4, twoH4, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have h0 : transporterV * twoC0 * transporterV⁻¹ ∈ M := by
      rw [← hCa]
      exact conj_mem_centralizer_a twoC_comm.1
    have h1 : transporterV * twoC1 * transporterV⁻¹ ∈ M := by
      rw [← hCa]
      exact conj_mem_centralizer_a twoC_comm.2
    have hk (y : J) (hy : transporterV * y * transporterV⁻¹ ∈ M) :
        transporterV * (twoK * y * twoK⁻¹) * transporterV⁻¹ ∈ twoM1 := by
      refine ⟨_, hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, twoG]
      group
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_left h0
    · exact Subgroup.mem_sup_left h1
    · exact Subgroup.mem_sup_right (hk _ h0)
    · exact Subgroup.mem_sup_right (hk _ h1)
  have hMK : ¬ M ≤ localH.map (MulAut.conj transporterV).toMonoidHom := by
    intro hMle
    have hd := Subgroup.card_dvd_of_le hMle
    rw [card_M, Subgroup.card_map_of_injective (conj_injective _), localH_eq,
      Kernel.card_H h] at hd
    norm_num at hd
  rcases hK.le_iff.1 hle with h' | h'
  · exact h'
  · exact absurd (h' ▸ le_sup_left) hMK

theorem inner_J_eq_top_kernel
    (hInv : ∀ u : J, orderOf u = 2 → IsConj a u) : inner J = ⊤ := by
  have hcore := (ctuc_Th_core_hyperplane_centralizers twoR twoR_mem_Q twoR_not_mem_center).2
  rw [z_eq_a] at hcore
  have hL : M ⊓ twoM1 = Subgroup.centralizer {twoR} ⊓ M := by
    rw [twoM1_eq_centralizer_kernel h, inf_comm]
  have hZ : ∀ s ∈ M ⊓ twoM1, (∀ l ∈ M ⊓ twoM1, s * l = l * s) →
      s ∈ Subgroup.closure {a, twoR} := by
    intro s hs hsc
    rw [hL] at hs hsc
    rw [← hcore]
    exact ⟨Subgroup.mem_centralizer_iff.2 fun l hl => (hsc l hl).symm, hs⟩
  have h1 : ∀ α : MulAut ↥M, ∃ m : ↥M, α = MulAut.conj m := max3_aut_eq_conj
  have h2 : twoR = twoG * a * twoG⁻¹ := rfl
  have h3 : twoM1 = M.map (MulAut.conj twoG).toMonoidHom := rfl
  have hA := aut_inner_of_two_centralizers a twoR twoG M twoM1 hInv (Kernel.orderOf_a h)
    (Kernel.centralizer_a_eq_M h) h1 twoR_mem_M h2 h3 hZ (sup_twoM1_eq_top_kernel h)
  exact inner_eq_top_of_allInner hA

end CFSG.Sporadic.ThSchreier

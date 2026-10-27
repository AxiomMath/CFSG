module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentSylowT
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentExcluded
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.Transfer

public section

namespace CFSG.OddTranspositions.PartThree.Wong.SplitData

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] (D : SplitData G)

theorem index_two_centralizer_kernel :
    ∃ K0 : Subgroup D.X, K0.Normal ∧ K0.index = 2 ∧ K0.map D.X.subtype ⊓ D.T = D.M := by
  have hPex : ∃ P : Sylow 2 D.X, (P : Subgroup D.X).map D.X.subtype = D.T :=
    D.second_centralizer_sylow_presentation.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨P, hPmap⟩ := hPex
  have hcos' : ∀ x ∈ D.T, x ∈ D.M ∨ x ∈ D.r • (D.W : Set G) ∨
      x ∈ (D.r * D.a * D.w) • (D.W : Set G) :=
    D.transfer_subgroup_data.2.2.2.2.2.2.2.2.2
  obtain ⟨hr2, hs2, hrM', hsM'⟩ := D.transfer_excluded_involutions
  have hTleX : D.T ≤ D.X := D.T_le_X
  have hMleX : D.M ≤ D.X := D.M_le_T.trans hTleX
  let r₀ : D.X := ⟨D.r, hTleX D.r_mem_T⟩
  let s₀ : D.X := ⟨D.r * D.a * D.w,
    hTleX (mul_mem (mul_mem D.r_mem_T D.a_mem_T) D.w_mem_T)⟩
  have hMP : D.M.subgroupOf D.X ≤ (P : Subgroup D.X) := by
    intro m hm
    have hmT : (m : G) ∈ D.T := D.M_le_T (Subgroup.mem_subgroupOf.mp hm)
    rw [← hPmap] at hmT
    obtain ⟨p, hpP, hpm⟩ := Subgroup.mem_map.mp hmT
    have hpm' : p = m := Subtype.ext hpm
    rwa [hpm'] at hpP
  have hMmap : (D.M.subgroupOf D.X).map D.X.subtype = D.M :=
    Subgroup.map_subgroupOf_eq_of_le hMleX
  have hidx : (D.M.subgroupOf D.X).relIndex (P : Subgroup D.X) = 2 := by
    rw [← Subgroup.relIndex_map_map_of_injective (D.M.subgroupOf D.X) (P : Subgroup D.X)
      D.X.subtype_injective, hMmap, hPmap, D.relIndex_M_T]
  have hA_le_X : D.A ≤ D.X := by
    rintro _ ⟨x, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (D.d_commute_u x).eq
  have hcommT : closure {D.u, D.v} = ⁅D.T, D.T⁆ :=
    D.commutator_T_eq.symm.trans (Subgroup.map_subtype_commutator D.T)
  have hcommA : D.A = ⁅D.A, D.A⁆ :=
    D.toSwapData.commutator_A_eq.symm.trans (Subgroup.map_subtype_commutator D.A)
  have hwA : D.w ∈ D.A := ⟨cM, rfl⟩
  have hWle : D.W ≤ ⁅D.X, D.X⁆ := by
    rw [show D.W = closure {D.u, D.v, D.w} from rfl]
    refine (closure_le _).mpr ?_
    rintro x (rfl | rfl | rfl)
    · exact (Subgroup.commutator_mono hTleX hTleX) (hcommT ▸ subset_closure (by simp))
    · exact (Subgroup.commutator_mono hTleX hTleX) (hcommT ▸ subset_closure (by simp))
    · exact (Subgroup.commutator_mono hA_le_X hA_le_X) (hcommA ▸ hwA)
  have hW : D.W.subgroupOf D.X ≤ commutator D.X := by
    intro x hx
    have hxW : (x : G) ∈ D.W := Subgroup.mem_subgroupOf.mp hx
    have hxX : D.X.subtype x ∈ (commutator D.X).map D.X.subtype := by
      rw [Subgroup.map_subtype_commutator D.X]
      exact hWle hxW
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hxX
    have hcx' : c = x := Subtype.ext hcx
    rwa [hcx'] at hc
  have hcos : ∀ x ∈ (P : Subgroup D.X),
      x ∈ D.M.subgroupOf D.X ∨ (∃ y ∈ D.W.subgroupOf D.X, x = r₀ * y) ∨
        ∃ y ∈ D.W.subgroupOf D.X, x = s₀ * y := by
    intro x hxP
    have hxT : (x : G) ∈ D.T := by
      simpa [hPmap] using Subgroup.mem_map_of_mem D.X.subtype hxP
    rcases hcos' (x : G) hxT with hxM | hxr | hxs
    · exact Or.inl (Subgroup.mem_subgroupOf.mpr hxM)
    · obtain ⟨y, hyW, hyx⟩ := Set.mem_smul_set.mp hxr
      exact Or.inr (Or.inl ⟨⟨y, hMleX (D.W_le_M hyW)⟩,
        Subgroup.mem_subgroupOf.mpr hyW, Subtype.ext hyx.symm⟩)
    · obtain ⟨y, hyW, hyx⟩ := Set.mem_smul_set.mp hxs
      exact Or.inr (Or.inr ⟨⟨y, hMleX (D.W_le_M hyW)⟩,
        Subgroup.mem_subgroupOf.mpr hyW, Subtype.ext hyx.symm⟩)
  have hr : orderOf r₀ = 2 := by
    change orderOf (⟨D.r, hTleX D.r_mem_T⟩ : D.X) = 2
    rw [Subgroup.orderOf_mk]
    exact hr2
  have hs : orderOf s₀ = 2 := by
    change orderOf (⟨D.r * D.a * D.w,
      hTleX (mul_mem (mul_mem D.r_mem_T D.a_mem_T) D.w_mem_T)⟩ : D.X) = 2
    rw [Subgroup.orderOf_mk]
    exact hs2
  have hrM : ∀ g : D.X, g⁻¹ * r₀ * g ∉ D.M.subgroupOf D.X := by
    intro g hg
    exact hrM' (g : G) g.2 (by simpa using Subgroup.mem_subgroupOf.mp hg)
  have hsM : ∀ g : D.X, g⁻¹ * s₀ * g ∉ D.M.subgroupOf D.X := by
    intro g hg
    exact hsM' (g : G) g.2 (by simpa using Subgroup.mem_subgroupOf.mp hg)
  obtain ⟨K0, hK0, hindex, hinf⟩ :=
    exists_normal_index_two_of_transfer P hMP hidx hW hr hs hcos hrM hsM
  refine ⟨K0, hK0, hindex, ?_⟩
  have h := congrArg (Subgroup.map D.X.subtype) hinf
  rw [Subgroup.map_inf K0 (P : Subgroup D.X) D.X.subtype D.X.subtype_injective, hPmap,
    hMmap] at h
  exact h

end CFSG.OddTranspositions.PartThree.Wong.SplitData

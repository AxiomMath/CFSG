module

public import CFSG.LocalAnalysis.WeakClosure81.W172Frat
public import CFSG.LocalAnalysis.WeakClosure81.W172Local

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace MinCex172

variable {D : Data G} {V₀ V H : Subgroup G}

theorem w172_comm_centralizer_le_pCoreOf (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) 1 g) {u a : G}
    (hu : u ∈ H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) (ha : a ∈ vInH V H g) :
    ⁅u, a⁆ ∈ pCoreOf 2 H := by
  classical
  set E := eOmegaZ H D.T with hE
  set A := vInH V H g with hA
  set C : Subgroup G := H ⊓ Subgroup.centralizer (E : Set G) with hC
  have hAH : A ≤ H := inf_le_right
  have hAV : A ≤ conjSubgroup V g := inf_le_left
  have hAab : IsElemAbelian 2 A :=
    (E3.isElemAbelian_conjSubgroup c.hyp.setting.isElemAbelian g).mono inf_le_left
  have hCnormH : H ≤ Subgroup.normalizer (C : Set G) := by
    have hEC : Subgroup.normalizer (E : Set G) ≤
        Subgroup.normalizer (Subgroup.centralizer (E : Set G) : Set G) :=
      Subgroup.le_normalizer_of_normal_subgroupOf (H := Subgroup.centralizer (E : Set G))
        (K := Subgroup.normalizer (E : Set G)) (Subgroup.centralizer_le_normalizer (E : Set G))
    exact (le_inf H.le_normalizer ((Hyp183.normalizer_eOmegaZ H D.T).trans hEC)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have huH : u ∈ H := hu.1
  have haH : a ∈ H := hAH ha
  have huM : u ∈ conjSubgroup D.M g :=
    w172_centralizer_le_conj_M h162 c hg hu.2
  have hMn : Subgroup.normalizer (conjSubgroup V g : Set G) = conjSubgroup D.M g := by
    rw [← E3.conjSubgroup_normalizer, c.hyp.setting.normalizer_eq]
  have huV : u * a * u⁻¹ ∈ conjSubgroup V g :=
    (Subgroup.mem_normalizer_iff.mp (hMn ▸ huM) a).mp (hAV ha)
  have huA : u * a * u⁻¹ ∈ A := ⟨huV, H.mul_mem (H.mul_mem huH haH) (H.inv_mem huH)⟩
  have hcommA : ⁅u, a⁆ ∈ A := by
    rw [commutatorElement_def]
    exact A.mul_mem huA (A.inv_mem ha)
  have hauC : a * u * a⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp (hCnormH haH) u).mp hu
  have hcommC : ⁅u, a⁆ ∈ C := by
    have : ⁅u, a⁆ = u * (a * u * a⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact C.mul_mem hu (C.inv_mem hauC)
  have hX : IsPGroup 2 ↥(A ⊓ C) := hAab.isPGroup.to_inf_left
  exact c.le_pCoreOf_of_isPGroup hX inf_le_right ⟨hcommA, hcommC⟩

end MinCex172

end CFSG.LocalAnalysis.WeakClosure81

end

module

public import CFSG.CharacterTheory.Semidihedral.PrimeResidual
public import Mathlib.GroupTheory.Focal
public import Mathlib.GroupTheory.Sylow
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open CFSG.Semidihedral

section Aux

variable {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]

private theorem sup_commutator_le_ker_transferFocal (M : Sylow p K) :
    primeResidual p K ⊔ commutator K ≤ (M : Subgroup K).transferFocal.ker :=
  sup_le (primeResidual_le_ker (M.isPGroup'.to_quotient _) _)
    (Abelianization.commutator_subset_ker _)

private theorem index_ker_transferFocal (M : Sylow p K) :
    (M : Subgroup K).transferFocal.ker.index = (commutator K).relIndex (M : Subgroup K) := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (Subgroup.transferFocal_surjective M),
    Subgroup.card_top, ← Subgroup.index_eq_card, Subgroup.focalSubgroupOf_def,
    ← Subgroup.commutator_inf_eq_focalSubgroup M, Subgroup.inf_subgroupOf_right]
  rfl

private theorem relIndex_sylow_eq_index {N : Subgroup K} [N.Normal]
    (hN : primeResidual p K ≤ N) (M : Sylow p K) :
    N.relIndex (M : Subgroup K) = N.index :=
  CFSG.GorensteinWalter.normal_relIndex_sylow_eq_index_of_quotient_isPGroup M N inferInstance
    (Glauberman.isPGroup_quotient_of_pPrime_order_elements_mem N fun _ hx =>
      hN (pPrime_element_mem_primeResidual hx))

end Aux

theorem primeResidual_sup_commutator_eq_ker_transferFocal {K : Type*} [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime] (M : Sylow p K) :
    primeResidual p K ⊔ commutator K = (M : Subgroup K).transferFocal.ker := by
  refine Subgroup.eq_of_index_dvd_index (sup_commutator_le_ker_transferFocal M) ?_
  rw [index_ker_transferFocal M,
    ← relIndex_sylow_eq_index (N := primeResidual p K ⊔ commutator K) le_sup_left M]
  exact Subgroup.relIndex_dvd_of_le_left _ le_sup_right

theorem primeResidual_sup_commutator_characteristic_inf_sylow {K : Type*} [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime] (M : Sylow p K) :
    (primeResidual p K ⊔ commutator K).Characteristic ∧
      commutator K ≤ primeResidual p K ⊔ commutator K ∧
      (M : Subgroup K) ⊓ (primeResidual p K ⊔ commutator K) = (M : Subgroup K) ⊓ commutator K ∧
      (primeResidual p K ⊔ commutator K).index = (commutator K).relIndex (M : Subgroup K) := by
  have hL := primeResidual_sup_commutator_eq_ker_transferFocal M
  refine ⟨inferInstance, le_sup_right, ?_, ?_⟩
  · rw [hL, inf_comm, Subgroup.ker_transferFocal_inf_eq_focalSubgroup, inf_comm,
      Subgroup.commutator_inf_eq_focalSubgroup]
  · rw [hL, index_ker_transferFocal M]

theorem exists_characteristic_inf_sylow_eq_commutator {K : Type*} [Group K] [Finite K] {p : ℕ}
    [Fact p.Prime] (M : Sylow p K) :
    ∃ L : Subgroup K, L.Characteristic ∧ commutator K ≤ L ∧
      (M : Subgroup K) ⊓ L = (M : Subgroup K) ⊓ commutator K ∧
      L.index = (commutator K).relIndex (M : Subgroup K) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := primeResidual_sup_commutator_characteristic_inf_sylow M
  exact ⟨_, h₁, h₂, h₃, h₄⟩

end CFSG.OddTranspositions.PartThree.Wong

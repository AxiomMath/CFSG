module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseHNotLeM
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FittingNormalizerGrowth
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Second-case conjugator  (source: refs/bender-dihedral-sylow.tex L691) -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- `U = O(H)` is normal in `H = C_G(t)`. -/
private theorem centralizerSetup_U_isNormalIn_H
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : IsNormalIn c.U c.H := by
  refine ⟨?_, ?_⟩
  · exact Subgroup.map_subtype_le (pPrimeCore 2 c.H)
  · intro h hh x hx
    rcases (Subgroup.mem_map).1 hx with ⟨p, hp, rfl⟩
    have hconj : (⟨h, hh⟩ : ↥c.H) * p * (⟨h, hh⟩ : ↥c.H)⁻¹ ∈
        pPrimeCore 2 c.H :=
      (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem
        p hp (⟨h, hh⟩ : ↥c.H)
    exact Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : ↥c.H) * p * (⟨h, hh⟩ : ↥c.H)⁻¹, hconj, by simp⟩

/-- Repairs the source's "as we can choose `g ∈ N_H(K₀F)`" (L691): an
element of `H` which normalizes `F(U) ∩ M` but lies outside `M`.  If
`F(U) ≤ M`, then `F(U) ∩ M = F(U)` is normal in `H`, so `H ∖ M` supplies
such a `g` (S4-03).  Otherwise `D := F(U) ∩ M` is a proper subgroup of the
nilpotent group `F(U)`, and the normalizer-condition witness from S4-02
normalizes `D` while lying outside `M`. -/
public theorem secondCase_exists_conjugator_not_mem_M
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (c : CentralizerSetup G)
    (w : SecondCaseWitness c) :
    ∃ g : G,
      g ∈ Subgroup.normalizer ((fittingSubgroupOf c.U ⊓ w.M : Subgroup G) : Set G) ∧
      g ∉ w.M := by
  classical
  by_cases hFU_le_M : fittingSubgroupOf c.U ≤ w.M
  · have hU_normalH : IsNormalIn c.U c.H := centralizerSetup_U_isNormalIn_H c
    have hFUnormalH : IsNormalIn (fittingSubgroupOf c.U) c.H := by
      change IsNormalIn ((fittingSubgroup (↥c.U)).map c.U.subtype) c.H
      exact map_characteristic_isNormalIn_of_isNormalIn
        (K := fittingSubgroup (↥c.U)) (hKchar := by infer_instance)
        (hHnormal := hU_normalH)
    have hg : ∃ g : G, g ∈ c.H ∧ g ∉ w.M := by
      exact (Set.not_subset.mp (by simpa using (secondCase_H_not_le_M hmin c w)))
    rcases hg with ⟨g, hgH, hgnotM⟩
    refine ⟨g, ?_, hgnotM⟩
    have hEq : fittingSubgroupOf c.U ⊓ w.M = fittingSubgroupOf c.U :=
      (inf_eq_left.mpr hFU_le_M)
    simpa [hEq] using (le_normalizer_of_isNormalIn hFUnormalH hgH)
  · let D : Subgroup G := fittingSubgroupOf c.U ⊓ w.M
    have hDleFU : D ≤ fittingSubgroupOf c.U := by
      exact inf_le_left
    have hDne : D ≠ fittingSubgroupOf c.U := by
      intro hEq
      apply hFU_le_M
      calc
        fittingSubgroupOf c.U = D := hEq.symm
        _ ≤ w.M := inf_le_right
    obtain ⟨g, hgFU, hgN, hgnotD⟩ :=
      exists_mem_normalizer_not_mem_of_lt_fitting c.U D hDleFU hDne
    refine ⟨g, ?_, ?_⟩
    · simpa [D] using hgN
    · intro hgM
      apply hgnotD
      exact ⟨hgFU, hgM⟩

end CFSG.GorensteinWalter

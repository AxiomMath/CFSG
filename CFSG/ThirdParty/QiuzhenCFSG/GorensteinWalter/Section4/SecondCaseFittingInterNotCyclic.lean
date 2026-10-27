module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CyclicSubgroupCharacteristic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FittingNormalizerGrowth
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseHNotLeM
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # The Fitting intersection is not cyclic  (source: refs/bender-dihedral-sylow.tex L685–693) -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- `F(U)` is normal in `H`: `F(U)` is characteristic in `U`, and `U` is
normal in `H`. -/
private theorem fittingSubgroupOf_isNormalIn_H {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : IsNormalIn (fittingSubgroupOf c.U) c.H := by
  have hU_normalH : IsNormalIn c.U c.H := by
    refine ⟨?_, ?_⟩
    · exact Subgroup.map_subtype_le (pPrimeCore 2 c.H)
    · intro h hh x hx
      rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
      have hconj : (⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹ ∈
          pPrimeCore 2 c.H :=
        (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem
          p hp (⟨h, hh⟩ : c.H)
      exact Subgroup.mem_map.mpr
        ⟨(⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹, hconj, by simp⟩
  change IsNormalIn ((fittingSubgroup (↥c.U)).map c.U.subtype) c.H
  exact map_characteristic_isNormalIn_of_isNormalIn
    (K := fittingSubgroup (↥c.U)) (hKchar := by infer_instance)
    (hHnormal := hU_normalH)

/-- The Fitting intersection `F(U) ⊓ M` is never cyclic. -/
public theorem secondCase_fitting_inter_M_not_cyclic
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (c : CentralizerSetup G)
    (w : SecondCaseWitness c) :
    ¬ IsCyclic (fittingSubgroupOf c.U ⊓ w.M : Subgroup G) := by
  intro hC
  let C : Subgroup G := fittingSubgroupOf c.U ⊓ w.M
  have hX_le_C : w.X ≤ C := by
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (w.X : Set G) :=
      Subgroup.le_normalizer (H := w.X) hx
    refine ⟨?_, w.normalizer_X_le_M hxN⟩
    simpa [CentralizerSetup.FU] using w.X_le_FU hx
  have hNC_le_NX : Subgroup.normalizer (C : Set G) ≤
      Subgroup.normalizer (w.X : Set G) :=
    normalizer_le_normalizer_of_le_cyclic (by simpa [C] using hC) hX_le_C
  have hNC_le_M : Subgroup.normalizer (C : Set G) ≤ w.M :=
    hNC_le_NX.trans w.normalizer_X_le_M
  have hNC_FU_le_C : Subgroup.normalizer (C : Set G) ⊓ fittingSubgroupOf c.U ≤ C := by
    intro x hx
    exact ⟨hx.2, hNC_le_M hx.1⟩
  have hCleFU : C ≤ fittingSubgroupOf c.U := by
    intro x hx
    exact hx.1
  have hCeq : C = fittingSubgroupOf c.U := by
    by_contra hne
    obtain ⟨g, hgFU, hgN, hgC⟩ :=
      exists_mem_normalizer_not_mem_of_lt_fitting c.U C hCleFU hne
    exact hgC (hNC_FU_le_C ⟨hgN, hgFU⟩)
  have hFU_cyc : IsCyclic (fittingSubgroupOf c.U) := by
    exact hCeq ▸ hC
  have hNFU_le_NX : Subgroup.normalizer (fittingSubgroupOf c.U : Set G) ≤
      Subgroup.normalizer (w.X : Set G) :=
    normalizer_le_normalizer_of_le_cyclic hFU_cyc w.X_le_FU
  have hNFU_le_M : Subgroup.normalizer (fittingSubgroupOf c.U : Set G) ≤ w.M :=
    hNFU_le_NX.trans w.normalizer_X_le_M
  have hH_le_M : c.H ≤ w.M :=
    (le_normalizer_of_isNormalIn (fittingSubgroupOf_isNormalIn_H c)).trans hNFU_le_M
  exact secondCase_H_not_le_M hmin c w hH_le_M

end CFSG.GorensteinWalter

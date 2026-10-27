module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommParts
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3Axis
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3Plumb

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Bridge

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sc_model3
    (hSel : CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootSelector fun D _ => CFSG.Blueprint.Catalog D)
    (hS : SCSetting L K n φ t i) :
    Model3Concl ↥(Ytor φ i) ((Vtor φ t i i).subgroupOf (Ytor φ i)) (Nat.card K) := by
  have h := hS.fc
  have hne := hS.ne_bot
  have hbot := hS.eq_bot
  obtain ⟨htH, _, hd⟩ := PrincipalLayers.axisData h i hne hbot hS.kproper hS.nonabelian i
  obtain ⟨hWV, hWc, hUW, hWU, hW1, hV3⟩ := PrincipalLayers.nontrivial_data h i hne hbot
  have hK : Nat.card K = 2 ^ n := hd.card_K
  have hV3' : Nat.card ((Vtor φ t i i).subgroupOf (centralizer (J φ i : Set G))) =
      (2 ^ n) ^ 3 := hV3.trans (by rw [hK])
  have hc := hd.nontrivialAxisConclusion hWV hWc hUW hWU hW1 hV3'
  have hVC : (Vtor φ t i i).subgroupOf (centralizer (J φ i : Set G)) ⊓
      centralizer ({⟨t, htH⟩} : Set ↥(centralizer (J φ i : Set G))) ≤
        (U φ i).subgroupOf (centralizer (J φ i : Set G)) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
    rw [mem_subgroupOf] at hx1 ⊢
    have hxt : (x : G) ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hx2 ⊢
      exact congrArg Subtype.val hx2
    exact (RootStandard.V_inf_C h i hne hbot).le (mem_inf.2 ⟨hx1, hxt⟩)
  have hmod := hd.nontrivialModel hSel hVC hV3' hc
  obtain ⟨R, hR, hM⟩ := model3_of_axis_conclusions hd.two_le hmod hc
  rw [hK]
  exact Model3Concl.of_subgroupOf (RootStandard.Y_le_H (φ := φ) i) hR hM

theorem sc_model3_sub
    (hSel : CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootSelector fun D _ => CFSG.Blueprint.Catalog D)
    (hS : SCSetting L K n φ t i) :
    Model3Sub (Ytor φ i) (Vtor φ t i i) (Nat.card K) :=
  Model3Concl.toSub (RootStandard.V_le_Y hS.fc i hS.ne_bot hS.eq_bot i) (sc_model3 hSel hS)

end Bridge

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard

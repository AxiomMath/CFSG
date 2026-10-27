module

public import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Defs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Transport
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Group
public import CFSG.GroupTheory.PCore.PCoreOfMulEquiv

public section
namespace CFSG.StandardType.RCKC1

open CFSG.Open CFSG.Assembly CFSG.StandardType

theorem k2At_self_of_coreCommAt
    {X : Type} [Group X] {J V : Subgroup X} {r : X}
    (hrV : r ∈ V) (hCore : CoreCommAt J V r) : K2At J V r := by
  have hr : Subgroup.zpowers r ≤ V := Subgroup.zpowers_le.mpr hrV
  have hConj {y : X}
      (hy : y ∈ pCoreOf 2 (J ⊓ Subgroup.centralizer ({r} : Set X)))
      {v : X} (hv : v ∈ V) : y * v * y⁻¹ ∈ V := by
    have h := V.mul_mem (V.inv_mem (hr (hCore v hv y hy))) hv
    convert h using 1 <;> group
  intro y hy
  apply Subgroup.mem_normalizer_iff.mpr
  intro v
  constructor
  · exact hConj hy
  · intro hv
    have h := hConj ((pCoreOf 2 (J ⊓ Subgroup.centralizer ({r} : Set X))).inv_mem hy) hv
    have heq : y⁻¹ * (y * v * y⁻¹) * (y⁻¹)⁻¹ = v := by group
    rwa [heq] at h

theorem map_involution_centralizer_pCoreOf_of_odd_central_ker
    {U X : Type} [Group U] [Finite U] [Group X] [Finite X]
    (π : U →* X) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center U) (hodd : Odd (Nat.card π.ker))
    {r : U} (hr : r ^ 2 = 1) :
    (pCoreOf 2 (Subgroup.centralizer ({r} : Set U))).map π =
      pCoreOf 2 (Subgroup.centralizer ({π r} : Set X)) := by
  have hC : (Subgroup.centralizer ({r} : Set U)).map π =
      Subgroup.centralizer ({π r} : Set X) := by
    refine le_antisymm ?_
      (CFSG.LocalAnalysis.RankThreeTheoremC.centralizer_le_map_centralizer π hπ hodd hr)
    simpa only [Set.image_singleton] using
      Subgroup.map_centralizer_le_centralizer_image ({r} : Set U) π
  have hK : π.ker ≤ Subgroup.centralizer ({r} : Set U) := by
    intro z hz
    exact (Subgroup.center_le_centralizer ({r} : Set U)) (hker hz)
  rw [LieKnownR2.map_pCoreOf_eq_of_odd_central_ker hker hodd hK, hC]

theorem k2At_map_of_odd_central_ker
    {U X : Type} [Group U] [Finite U] [Group X] [Finite X]
    (π : U →* X) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center U) (hodd : Odd (Nat.card π.ker))
    {V : Subgroup U} {r : U} (hr : r ^ 2 = 1)
    (hK2 : K2At (⊤ : Subgroup U) V r) :
    K2At (⊤ : Subgroup X) (V.map π) (π r) := by
  have h : pCoreOf 2 (Subgroup.centralizer ({r} : Set U)) ≤
      Subgroup.normalizer (V : Set U) := by simpa only [K2At, top_inf_eq] using hK2
  simpa only [K2At, top_inf_eq,
    map_involution_centralizer_pCoreOf_of_odd_central_ker π hπ hker hodd hr] using
    (Subgroup.map_mono h).trans (Subgroup.le_normalizer_map π)

theorem fourAt_map_subtype
    {U : Type} [Group U] {J : Subgroup U} {V : Subgroup J} {r : J}
    (h : FourAt (⊤ : Subgroup J) V r) :
    FourAt J (V.map J.subtype) (r : U) := by
  obtain ⟨hr, _, hV, hcard, hr1, hConj⟩ := h
  refine ⟨Subgroup.mem_map_of_mem _ hr, Subgroup.map_subtype_le _, hV.map J.subtype, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective J.subtype_injective]
    exact hcard
  · intro h1
    exact hr1 (Subtype.ext h1)
  · intro v hv hv1
    obtain ⟨vJ, hvJ, rfl⟩ := Subgroup.mem_map.mp hv
    have hv1' : vJ ≠ 1 := by
      intro h1
      exact hv1 (congrArg Subtype.val h1)
    obtain ⟨j, _, hj⟩ := hConj vJ hvJ hv1'
    refine ⟨j, j.2, ?_⟩
    simpa only [map_mul, map_inv, Subgroup.coe_subtype] using congrArg J.subtype hj

theorem coreCommAt_map_subtype
    {U : Type} [Group U] {J : Subgroup U} {V : Subgroup J} {r : J}
    (h : CoreCommAt (⊤ : Subgroup J) V r) :
    CoreCommAt J (V.map J.subtype) (r : U) := by
  intro v hv y hy
  obtain ⟨vJ, hvJ, rfl⟩ := Subgroup.mem_map.mp hv
  have hyJ : y ∈ J := (GGRootNorm.pCoreOf_le _ hy).1
  have hyInner : (⟨y, hyJ⟩ : J) ∈ pCoreOf 2 (Subgroup.centralizer ({r} : Set J)) := by
    have hMap := CFSG.GroupTheory.map_pCoreOf_inf_centralizer_mulEquiv (MulEquiv.refl J) r.2
    simp only [MulEquiv.refl_apply] at hMap
    rw [← hMap]
    exact Subgroup.mem_map_of_mem _ hy
  have hComm := h vJ hvJ ⟨y, hyJ⟩ (by simpa only [top_inf_eq] using hyInner)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hComm
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨k, ?_⟩
  simpa only [map_mul, map_inv, map_zpow, Subgroup.coe_subtype] using congrArg J.subtype hk

end CFSG.StandardType.RCKC1

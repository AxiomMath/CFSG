module

public import CFSG.RankThree.PartOne.S9.Defs
import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaMixedBalance
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha

public section

namespace CFSG.RankThree.PartOne.Vanish

open CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

variable {G : Type*} [Group G]

theorem map_twoPrimeResidual_le {K : Subgroup G} (W : Subgroup K) :
    (CFSG.Quasithin.twoPrimeResidual W).map K.subtype ≤
      CFSG.Quasithin.twoPrimeResidual (W.map K.subtype) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe] at hx
  unfold CFSG.Quasithin.twoPrimeResidual at hx ⊢
  simp only [Subgroup.mem_iInf] at hx ⊢
  intro N hN
  obtain ⟨hNW, hWN, hodd⟩ := hN
  refine hx (N.comap K.subtype) ⟨?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨w, hw, hwy⟩ := hNW hy
    exact K.subtype_injective hwy ▸ hw
  · intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact Subgroup.mem_normalizer_iff.mp (hWN (Subgroup.mem_map_of_mem K.subtype hw)) (y : G)
  · rw [Subgroup.relIndex_comap]
    exact hodd

theorem map_thetaT_subgroupOf [Finite G] {p : ℕ} (hp : p.Prime) {K D : Subgroup G} (hDK : D ≤ K)
    {t : G} (htD : t ∈ D) (ht1 : t ≠ 1) :
    (thetaT p (D.subgroupOf K)).map K.subtype =
      ⨅ d ∈ D, ⨅ (_ : d ≠ 1),
        inSubgroup (aschbacherSolvableCore p) (K ⊓ Subgroup.centralizer ({d} : Set G)) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_iInf, thetaT, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩ d hd hd1
    have hy' := hy ⟨d, hDK hd⟩ hd (fun h => hd1 (congrArg Subtype.val h))
    have := Subgroup.mem_map_of_mem K.subtype hy'
    rwa [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp,
      RankThreeEvenClassification.Helpers.thetaCoreOf_element_centralizer_subtype_map p hp K d
        (hDK hd), ← inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp] at this
  · intro hx
    have hxt := hx t htD ht1
    have hxK : x ∈ K := (inf_le_left : K ⊓ _ ≤ K) (Subgroup.map_subtype_le _ hxt)
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    intro b' hb' hb'1
    have hb1 : (b' : G) ≠ 1 := fun h => hb'1 (Subtype.ext h)
    have hxb := hx b' hb' hb1
    rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp,
      ← RankThreeEvenClassification.Helpers.thetaCoreOf_element_centralizer_subtype_map p hp K b'
        b'.2] at hxb
    obtain ⟨z, hz, hzx⟩ := hxb
    have hzK : z = ⟨x, hxK⟩ := Subtype.ext hzx
    rw [← hzK, inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
    exact hz

theorem map_residualGroup_eq [Finite G] {p : ℕ} (hp : p.Prime) {K D : Subgroup G} (hDK : D ≤ K)
    (t : K) (htD : (t : G) ∈ D) (ht1 : (t : G) ≠ 1) :
    (⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set K)),
          D.subgroupOf K⁆ ⊔ thetaT p (D.subgroupOf K)).map K.subtype =
      residualGroup p K D (t : G) := by
  have hθ : (inSubgroup (aschbacherSolvableCore p)
      (Subgroup.centralizer ({t} : Set K))).map K.subtype =
      inSubgroup (aschbacherSolvableCore p) (K ⊓ Subgroup.centralizer ({(t : G)} : Set G)) := by
    rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp,
      inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
    exact RankThreeEvenClassification.Helpers.thetaCoreOf_element_centralizer_subtype_map p hp K
      (t : G) t.2
  unfold residualGroup
  rw [Subgroup.map_sup, Subgroup.map_commutator, hθ, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hDK, map_thetaT_subgroupOf hp hDK htD ht1]

theorem residual_inside_of_residual [Finite G] {p : ℕ} (hp : p.Prime) {K D : Subgroup G}
    (hDK : D ≤ K) (t : K) (htD : (t : G) ∈ D) (ht1 : (t : G) ≠ 1)
    (h : CFSG.Quasithin.twoPrimeResidual (residualGroup p K D (t : G)) ≤
      inSubgroup (aschbacherSolvableCore p) K) :
    CFSG.Quasithin.twoPrimeResidual
        (⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set K)),
          D.subgroupOf K⁆ ⊔ thetaT p (D.subgroupOf K)) ≤ aschbacherSolvableCore p K := by
  intro x hx
  have h1 := Subgroup.mem_map_of_mem K.subtype hx
  have h2 := map_twoPrimeResidual_le _ h1
  rw [map_residualGroup_eq hp hDK t htD ht1] at h2
  obtain ⟨y, hy, hyx⟩ := h h2
  have hyx' : y = x := Subtype.ext hyx
  exact hyx' ▸ hy

end CFSG.RankThree.PartOne.Vanish

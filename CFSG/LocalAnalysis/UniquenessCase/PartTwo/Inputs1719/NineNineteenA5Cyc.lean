module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Cyc
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddCyc
import CFSG.Quasithin.H13.NQCoreFixedSpaceGlue

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (pRank_map_subtype_eq
  isSylowOf_subgroupOf_top)

variable {G : Type} [Group G] [Finite G]

theorem pRank_iSup_map_conj_eq_one (hK : UCK.K332Cyc) {H P Z : Subgroup G}
    (hHK : CFSG.Open.IsKGroup ↥H) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P H)
    (hP3 : CFSG.Open.pRank 3 P ≤ 3) (hZP : Z ≤ P) (hZ : Nat.card Z = 3)
    (hwc : ∀ h ∈ H, Z.map (MulAut.conj h).toMonoidHom ≤ P →
      Z.map (MulAut.conj h).toMonoidHom = Z)
    {Q : Type} [Group Q] (hQ : IsCyclic Q) (φ : ↥P →* Q)
    (hφ : ∀ x : ↥P, (x : G) ∈ Z → φ x = 1 → x = 1) :
    CFSG.Open.pRank 3 (⨆ h : ↥H, Z.map (MulAut.conj (h : G)).toMonoidHom) = 1 := by
  classical
  have hZH : Z ≤ H := hZP.trans hP.le
  let ψ : ↥(P.subgroupOf H) →* Q := φ.comp (Subgroup.subgroupOfEquivOfLe hP.le).toMonoidHom
  have hrank : CFSG.Open.pRank 3 (P.subgroupOf H) ≤ 3 := by
    rw [← pRank_map_subtype_eq H, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hP.le]
    exact hP3
  have hwc' : CFSG.ASVolI.ChIJK.IsWeaklyClosedIn (Z.subgroupOf H) (P.subgroupOf H) := by
    intro g hg
    unfold CFSG.conjugate at hg ⊢
    have hZg : Z.map (MulAut.conj ((g⁻¹ : ↥H) : G)).toMonoidHom ≤ P := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
      exact Subgroup.mem_subgroupOf.1 (hg (Subgroup.mem_map.2
        ⟨⟨z, hZH hz⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩))
    have hEq := hwc ((g⁻¹ : ↥H)) (g⁻¹).2 hZg
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
      rw [Subgroup.mem_subgroupOf] at hz ⊢
      have h1 : (((MulAut.conj g⁻¹).toMonoidHom z : ↥H) : G) ∈
          Z.map (MulAut.conj ((g⁻¹ : ↥H) : G)).toMonoidHom :=
        Subgroup.mem_map.2 ⟨z, hz, by simp⟩
      rwa [hEq] at h1
    · intro hx
      have hx' : (x : G) ∈ Z := Subgroup.mem_subgroupOf.1 hx
      rw [← hEq] at hx'
      obtain ⟨e, he, hex⟩ := Subgroup.mem_map.1 hx'
      refine Subgroup.mem_map.2 ⟨⟨e, hZH he⟩, Subgroup.mem_subgroupOf.2 he, Subtype.ext ?_⟩
      simpa [MulAut.conj_apply] using hex
  have hdisj : Disjoint ((Z.subgroupOf H).subgroupOf (P.subgroupOf H)) ψ.ker := by
    rw [Subgroup.disjoint_def]
    intro x hx hψx
    have hxZ : ((x : ↥H) : G) ∈ Z := hx
    have hy : φ (Subgroup.subgroupOfEquivOfLe hP.le x) = 1 := hψx
    have hy1 := hφ (Subgroup.subgroupOfEquivOfLe hP.le x) hxZ hy
    exact (MulEquiv.map_eq_one_iff _).1 hy1
  have hcl := hK ↥H hHK (P.subgroupOf H) (isSylowOf_subgroupOf_top hP) hrank (Z.subgroupOf H)
    (fun x hx => Subgroup.mem_subgroupOf.2 (hZP (Subgroup.mem_subgroupOf.1 hx)))
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv]; exact hZ) hwc' Q hQ ψ hdisj
  set N' : Subgroup ↥H := Subgroup.normalClosure ((Z.subgroupOf H : Subgroup ↥H) : Set ↥H)
    with hN'
  have hmap : N'.map H.subtype = ⨆ h : ↥H, Z.map (MulAut.conj (h : G)).toMonoidHom := by
    rw [hN', CFSG.Quasithin.H13.NQCore.map_normalClosure_eq_iSup hZH]
    exact iSup_subtype'
  rw [← hmap, pRank_map_subtype_eq H, hN']
  exact hcl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5

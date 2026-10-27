module

public import CFSG.CGT.PushingUpLit.ThmOne.ThreeOneFStar
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFORankLift
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionLift
public import CFSG.Quasithin.Vol2.Ch4Sec2InspM22Red

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem odd_card_fittingSubgroupOf {X : Subgroup G} (hX2 : pCoreOf 2 X = ⊥) :
    Odd (Nat.card (CFSG.fittingSubgroupOf X)) := by
  have hX2' : CFSG.pCore 2 ↥X = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective (H := CFSG.pCore 2 ↥X) X.subtype_injective).1
    simpa [pCoreOf] using hX2
  have hOdd := CFSG.CGT.PushingUpLit.ThmOne.odd_card_fittingSubgroup_of_pCore_two_eq_bot hX2'
  have hcard : Nat.card (CFSG.fittingSubgroupOf X) = Nat.card (fittingSubgroup ↥X) := by
    rw [CFSG.fittingSubgroupOf, Subgroup.card_map_of_injective X.subtype_injective]
  rwa [hcard]

theorem odd_card_center_of_isComponentOf {X Y : Subgroup G} (hX2 : pCoreOf 2 X = ⊥)
    (hY : CFSG.Open.IsComponentOf Y X) : Odd (Nat.card (center ↥Y)) := by
  have hX2' : CFSG.pCore 2 ↥X = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective (H := CFSG.pCore 2 ↥X) X.subtype_injective).1
    simpa [pCoreOf] using hX2
  have hY' : CFSG.Open.IsComponentOf (Y.subgroupOf X) ⊤ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.isComponentOf_subgroupOf hY
  have hOdd :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.RankCore.odd_card_center_of_component hX2' hY'
  have hcard : Nat.card (center ↥(Y.subgroupOf X)) = Nat.card (center ↥Y) := by
    let e : ↥(Y.subgroupOf X) ≃* ↥Y := Subgroup.subgroupOfEquivOfLe hY.1
    have hc : (Subgroup.center ↥(Y.subgroupOf X)).map e.toMonoidHom = Subgroup.center ↥Y :=
      CFSG.Quasithin.H13.Ch4.center_map_equiv e
    rw [← hc, Subgroup.card_map_of_injective e.injective]
  rwa [← hcard]

theorem exists_isComponentOf_not_le_centralizer {X V : Subgroup G} (hX2 : pCoreOf 2 X = ⊥)
    (hVX : V ≤ X) (hV2 : IsPGroup 2 V) (hV1 : V ≠ ⊥)
    (hVF : V ≤ centralizer (CFSG.fittingSubgroupOf X : Set G)) :
    ∃ Y : Subgroup G, CFSG.Open.IsComponentOf Y X ∧ ¬ V ≤ centralizer (Y : Set G) := by
  by_contra h
  push Not at h
  have h2 : CFSG.pCore 2 ↥X = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective (H := CFSG.pCore 2 ↥X) X.subtype_injective).1
    simpa [pCoreOf] using hX2
  have hP : IsPGroup 2 (V.subgroupOf X) :=
    hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVX).symm
  have hE : ∀ J : Subgroup ↥X, CFSG.IsComponent J → ⁅J, V.subgroupOf X⁆ = ⊥ := by
    intro J hJ
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hJ' : CFSG.Open.IsComponentOf J ⊤ := (CFSG.isComponent_iff_open J).mp hJ
    have hJX : CFSG.Open.IsComponentOf (J.map X.subtype) X :=
      CFSG.LocalAnalysis.RankThreeTheoremC.isComponentOf_map_subtype hJ'
    have hVY := h (J.map X.subtype) hJX
    have hjY : (j : G) ∈ J.map X.subtype := Subgroup.mem_map_of_mem X.subtype hj
    have hvV : (v : G) ∈ V := hv
    have hcomm := Subgroup.mem_centralizer_iff.mp (hVY hvV) (j : G) hjY
    exact Subtype.ext (by simpa using hcomm.symm)
  have hF : ⁅fittingSubgroup ↥X, V.subgroupOf X⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hfv : (f : G) ∈ CFSG.fittingSubgroupOf X := Subgroup.mem_map_of_mem X.subtype hf
    have hvV : (v : G) ∈ V := hv
    have hcomm := Subgroup.mem_centralizer_iff.mp (hVF hvV) (f : G) hfv
    exact Subtype.ext (by simpa using hcomm.symm)
  have hbot := CFSG.CGT.PushingUpLit.ThmOne.eq_bot_of_commutator_eq_bot h2 hP hE hF
  have hVbot : V = ⊥ := by
    have hcard : Nat.card V = 1 := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVX).toEquiv]
      rw [hbot]
      simp
    exact Subgroup.card_eq_one.mp hcard
  exact hV1 hVbot

theorem le_centralizer_of_isComponentOf_le {X V M Y : Subgroup G} (hX2 : pCoreOf 2 X = ⊥)
    (hVX : V ≤ X) (hVM : V ≤ M) (hV2 : IsPGroup 2 V) (hN : X ⊓ M ≤ normalizer (V : Set G))
    (hY : CFSG.Open.IsComponentOf Y X) (hYM : Y ≤ M) : V ≤ centralizer (Y : Set G) := by
  have hJ : CFSG.IsComponent (Y.subgroupOf X) :=
    (CFSG.isComponent_iff_open _).2
      (CFSG.LocalAnalysis.RankThreeTheoremC.isComponentOf_subgroupOf hY)
  have hP : IsPGroup 2 (V.subgroupOf X) :=
    hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVX).symm
  have hJP : Y.subgroupOf X ≤ Subgroup.normalizer (V.subgroupOf X : Set ↥X) := by
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      have hjY : (j : G) ∈ Y := Subgroup.mem_subgroupOf.mp hj
      have hpV : (p : G) ∈ V := Subgroup.mem_subgroupOf.mp hp
      have hYnorm : (j : G) ∈ normalizer (V : Set G) :=
        hN (Subgroup.mem_inf.mpr ⟨hY.1 hjY, hYM hjY⟩)
      rw [Subgroup.mem_normalizer_iff] at hYnorm
      exact Subgroup.mem_subgroupOf.mpr ((hYnorm (p : G)).mp hpV)
    · intro hp
      have hjY : (j : G) ∈ Y := Subgroup.mem_subgroupOf.mp hj
      have hYnorm : (j : G) ∈ normalizer (V : Set G) :=
        hN (Subgroup.mem_inf.mpr ⟨hY.1 hjY, hYM hjY⟩)
      rw [Subgroup.mem_normalizer_iff] at hYnorm
      have hmem : (j : G) * (p : G) * (j : G)⁻¹ ∈ V := Subgroup.mem_subgroupOf.mp hp
      exact Subgroup.mem_subgroupOf.mpr ((hYnorm (p : G)).mpr hmem)
  have hcomm :=
    CFSG.CGT.PushingUpLit.ThmOne.commutator_eq_bot_of_isComponent_of_le_normalizer hJ hP hJP
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  let yX : ↥X := ⟨y, hY.1 hy⟩
  let vX : ↥X := ⟨v, hVX hv⟩
  have hyJ : yX ∈ Y.subgroupOf X := Subgroup.mem_subgroupOf.mpr hy
  have hvP : vX ∈ V.subgroupOf X := Subgroup.mem_subgroupOf.mpr hv
  have hcomm_elem : yX * vX = vX * yX := by
    have hh : yX ∈ Subgroup.centralizer (V.subgroupOf X : Set ↥X) := hcomm hyJ
    have := Subgroup.mem_centralizer_iff.mp hh vX hvP
    exact this.symm
  exact congrArg Subtype.val hcomm_elem

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

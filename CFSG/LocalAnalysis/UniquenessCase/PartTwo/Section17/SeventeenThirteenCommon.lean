module

public import CFSG.GroupTheory.ComponentOrbit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirteenDiagonal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81 CFSG.Quasithin
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

@[expose] def OddComponentShapeCore (q : ℕ) (X : Type) [Group X] : Prop :=
  (∃ q' : ℕ, IsL2Over17 X q' ∧ (q' = q ∨ q' = q ^ 3) ∧ 3 < q') ∨
    (IsL3EpsOdd17 X q ∧ 3 < q)

theorem oddComponentShapeCore_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {q : ℕ} (h : OddComponentShapeCore q X) : OddComponentShapeCore q Y := by
  rcases h with ⟨q', hL2, hq', h3⟩ | ⟨hL3, h3⟩
  · exact Or.inl ⟨q', isL2Over17_of_mulEquiv e.symm hL2, hq', h3⟩
  · refine Or.inr ⟨?_, h3⟩
    rcases hL3 with hL3 | hL3
    · exact Or.inl (LieModel.of_mulEquiv e hL3)
    · exact Or.inr (LieModel.of_mulEquiv e hL3)

theorem hasOddComponentShapes_of_component {Q : Type} [Group Q] [Finite Q] {K T : Subgroup Q}
    (hK : CFSG.IsComponent K) (hT : IsPGroup 2 T) (hKT : orbitClosure K T ⊔ T = ⊤) {q : ℕ}
    (hcore : OddComponentShapeCore q (↥K ⧸ Subgroup.center ↥K)) :
    HasOddComponentShapes Q q := by
  intro Y hY X hXn hXne hXmin hXnc L hL
  have : Y.Normal := hY
  obtain ⟨hs, hnc, ⟨e⟩⟩ :=
    CFSG.GroupTheory.isComponentOf_minimalNormal_quotient hK hT hKT Y X hXn hXne hXmin hXnc L hL
  exact ⟨hs, hnc, oddComponentShapeCore_of_mulEquiv e.symm hcore⟩

theorem hasOddComponentShapes_of_mulEquiv {Q Q' : Type} [Group Q] [Finite Q] [Group Q']
    [Finite Q'] {q : ℕ} (e : Q ≃* Q') (h : HasOddComponentShapes Q q) :
    HasOddComponentShapes Q' q := by
  intro Y' hY' X' hXn' hXne' hXmin' hXnc' L' hL'
  let Y : Subgroup Q := Y'.comap e.toMonoidHom
  have hYn : Y.Normal := hY'.comap e.toMonoidHom
  have hYmap : Y.map e.toMonoidHom = Y' := by
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr e.surjective, top_inf_eq]
  let φ : (Q ⧸ Y) ≃* (Q' ⧸ Y') := QuotientGroup.congr Y Y' e hYmap
  let X : Subgroup (Q ⧸ Y) := X'.map φ.symm.toMonoidHom
  let L : Subgroup (Q ⧸ Y) := L'.map φ.symm.toMonoidHom
  have hXn : X.Normal := hXn'.map φ.symm.toMonoidHom φ.symm.surjective
  have hXmap : X.map φ.toMonoidHom = X' := by
    simp [X, Subgroup.map_map]
  have hXne : X ≠ ⊥ := by
    intro hbot
    apply hXne'
    have h1 := congrArg (Subgroup.map φ.toMonoidHom) hbot
    rw [Subgroup.map_bot, hXmap] at h1
    exact h1
  have hXmin : ∀ N : Subgroup (Q ⧸ Y), N.Normal → N ≤ X → N = ⊥ ∨ N = X := by
    intro N hNn hNle
    have hN'n : (N.map φ.toMonoidHom).Normal := hNn.map φ.toMonoidHom φ.surjective
    have hN'le : N.map φ.toMonoidHom ≤ X' := by
      rw [← hXmap]
      exact Subgroup.map_mono hNle
    rcases hXmin' (N.map φ.toMonoidHom) hN'n hN'le with h0 | htop
    · left
      have h1 : (N.map φ.toMonoidHom).map φ.symm.toMonoidHom = ⊥ := by
        rw [h0, Subgroup.map_bot]
      rw [Subgroup.map_map] at h1
      simpa using h1
    · right
      have h1 : (N.map φ.toMonoidHom).map φ.symm.toMonoidHom = X := by
        rw [htop]
      rw [Subgroup.map_map] at h1
      simpa using h1
  have hXnc : ¬ IsMulCommutative X := by
    intro hc
    apply hXnc'
    have e' : ↥X' ≃* ↥X := X'.equivMapOfInjective φ.symm.toMonoidHom φ.symm.injective
    refine IsMulCommutative.of_comm fun a b => ?_
    apply e'.injective
    rw [map_mul, map_mul, IsMulCommutative.is_comm.comm]
  have eL : ↥L' ≃* ↥L := L'.equivMapOfInjective φ.symm.toMonoidHom φ.symm.injective
  have hLc : CFSG.Open.IsComponentOf L X :=
    ⟨Subgroup.map_mono hL'.1,
      CFSG.Open.IsSubnormal.map φ.symm.toMonoidHom hL'.2.1,
      CFSG.Open.IsQuasisimple.of_mulEquiv eL.symm hL'.2.2⟩
  obtain ⟨hs, hnc, hcore⟩ := h Y hYn X hXn hXne hXmin hXnc L hLc
  refine ⟨(MulEquiv.isSimpleGroup_congr eL).mpr hs, ?_,
    oddComponentShapeCore_of_mulEquiv eL.symm hcore⟩
  obtain ⟨a, b, hab⟩ := hnc
  exact ⟨eL.symm a, eL.symm b, fun h => hab (by simpa using congrArg eL h)⟩

theorem hasOddComponentShapes_top_of_component {Q : Type} [Group Q] [Finite Q]
    {K T : Subgroup Q} (hK : CFSG.IsComponent K) (hT : IsPGroup 2 T)
    (hKT : orbitClosure K T ⊔ T = ⊤) {q : ℕ}
    (hcore : OddComponentShapeCore q (↥K ⧸ Subgroup.center ↥K)) :
    HasOddComponentShapes (↥(⊤ : Subgroup Q)) q :=
  hasOddComponentShapes_of_mulEquiv Subgroup.topEquiv.symm
    (hasOddComponentShapes_of_component hK hT hKT hcore)

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_M_le_of_T_le {D : Data G} {H : Subgroup G} (hTH : D.T ≤ H)
    (hHM : H ≤ D.M) :
    CFSG.Open.pCoreOf 2 D.M ≤ CFSG.Open.pCoreOf 2 H := by
  have hO2T : CFSG.Open.pCoreOf 2 D.M ≤ D.T := uc22p22e_pCoreOf_le_T D
  have hleH : CFSG.Open.pCoreOf 2 D.M ≤ H := hO2T.trans hTH
  refine CFSG.LieType.BorelTits.le_pCoreOf 2 hleH ?_ ?_
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hleH).mpr
      (hHM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M))
  · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M

theorem comm_conj_of_not_mem_normalizer {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    {X : Subgroup G} (hXL : X ≤ L) {t : G} (ht : t ∈ D.T)
    (hnt : t ∉ Subgroup.normalizer (L : Set G)) :
    ⁅X, X.map (MulAut.conj t).toMonoidHom⁆ ≤ CFSG.Open.pCoreOf 2 D.M := by
  have htM : t ∈ D.M := D.sylowM.le ht
  have hMt : D.M.map (MulAut.conj t).toMonoidHom = D.M :=
    UC6S846.mem_normalizer_iff_map_conj.mp (Subgroup.le_normalizer htM)
  have hLt : L.map (MulAut.conj t).toMonoidHom ∈ calC D.M :=
    UC6S846.calC_map D.M (MulAut.conj t) hMt hL
  have hne : L ≠ L.map (MulAut.conj t).toMonoidHom := by
    intro h
    exact hnt (UC6S846.mem_normalizer_iff_map_conj.mpr h.symm)
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  exact commutator_mem_pCoreOf_of_ne hL hLt hne (hXL hx)
    (Subgroup.mem_map_of_mem _ (hXL hz))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

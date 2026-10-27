module

import CFSG.HardMathSupport.Seitz.Proving.SL2OrderThree
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.GF2n.Stroth80.Sec41iii
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_conj_lbar_isSLn
    (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    {x : G} (hxM : x ∈ D.M) :
    IsSLn ↥(lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) 2 2 := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hxstab : x ∈ stabTil ⊥ V := hMs hxM
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hrow.1
  refine ⟨K, hKf, hKfin, hKcard, ⟨?_⟩⟩
  have hmap : (barSub ⊥ V hV L).map
      (MulAut.conj (actTil ⊥ V hV ⟨x, hxstab⟩)⁻¹).toMonoidHom =
      barSub ⊥ V hV (conjSubgroup L x) :=
    (s15_Infra_barSub_conjSubgroup (⊥ : Subgroup G) V hV hxstab L).symm
  have hiso : ↥(barSub ⊥ V hV L) ≃* ↥(barSub ⊥ V hV (conjSubgroup L x)) :=
    (Subgroup.equivMapOfInjective (barSub ⊥ V hV L)
      (MulAut.conj (actTil ⊥ V hV ⟨x, hxstab⟩)⁻¹).toMonoidHom
      (MulAut.conj (actTil ⊥ V hV ⟨x, hxstab⟩)⁻¹).injective).trans
      (MulEquiv.subgroupCongr hmap)
  exact hiso.symm.trans e

theorem s16h_sl4_conj_lbar_exists_order_three
    (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    {x : G} (hxM : x ∈ D.M) :
    ∃ a ∈ lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x), orderOf a = 3 := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := s16h_sl4_conj_lbar_isSLn D h hrow hxM
  letI : Field K := hKf
  letI : Finite K := hKfin
  have h3 : 3 ∣ Nat.card K ^ 2 - 1 := by
    rw [hKcard]
    norm_num
  obtain ⟨y, hy⟩ := CFSG.HardMathSupport.Seitz.Proving.exists_orderOf_three_SL2 K h3
  let f : Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥(StatedSL 2 K) :=
    CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K
  let g : ↥(lBar ⊥ V hV (conjSubgroup L x)) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    e.trans f.symm
  refine ⟨((g.symm y : ↥(lBar ⊥ V hV (conjSubgroup L x))) : MulAut (Vtil ⊥ V hV)),
    (g.symm y).2, ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy]

theorem s16h_sl4_conj_lbar_center_eq_bot
    (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    {x : G} (hxM : x ∈ D.M) :
    Subgroup.center ↥(lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) = ⊥ := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := s16h_sl4_conj_lbar_isSLn D h hrow hxM
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : Fintype K := Fintype.ofFinite K
  have hKeven : Fintype.card K % 2 = 0 := by
    rw [Fintype.card_eq_nat_card, hKcard]
    norm_num
  have hchar : ringChar K = 2 :=
    (FiniteField.even_card_iff_char_two (F := K)).mpr hKeven
  haveI : CharP K 2 := hchar ▸ ringChar.charP K
  have hKcenter : Subgroup.center ↥(StatedSL 2 K) = ⊥ :=
    CFSG.RankThree.GF2n.Stroth80.center_statedSL_two_eq_bot
  have hcard : Nat.card ↥(Subgroup.center
      ↥(lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x))) = 1 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hKcenter]
    simp
  exact Subgroup.card_eq_one.mp hcard

theorem s16h_sl4_closure_rank_two
    (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    {φ : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hφM : φ ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian) (hφ3 : orderOf φ = 3)
    (hcentx : ∀ a ∈ lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x), φ * a = a * φ)
    (hfix : ∀ z ∈ wTil ⊥ V h.hyp151.isElemAbelian L, φ z = z) :
    ∃ Ebar : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)),
      Ebar ≤ Mbar D.M ⊥ V h.hyp151.isElemAbelian ∧
      Ebar ≤ centSub (wTil ⊥ V h.hyp151.isElemAbelian L) ∧
      IsElemAbelian 3 Ebar ∧ 9 ≤ Nat.card ↥Ebar := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hconjL : lBar ⊥ V hV (conjSubgroup L x) ≤ centSub (wTil ⊥ V hV L) := by
    have hbot := (h.hyp151.commute x hxM hxn).2
    have hle : wTil ⊥ V hV L ≤ fixV (lBar ⊥ V hV (conjSubgroup L x)) :=
      (commSub_eq_bot_iff (W := wTil ⊥ V hV L)
        (X := lBar ⊥ V hV (conjSubgroup L x))).1 hbot
    intro c hc
    rw [mem_centSub]
    intro z hz
    exact hle hz c hc
  have hconj_le : conjSubgroup L x ≤ D.M := by
    intro g hg
    rw [mem_conjSubgroup_iff] at hg
    have hmem : x⁻¹ * (x * g * x⁻¹) * x ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hxM) (h.hyp151.le hg)) hxM
    convert hmem using 1
    group
  obtain ⟨c, hc_mem, hc_ord⟩ := s16h_sl4_conj_lbar_exists_order_three D h hrow hxM
  have hcenter := s16h_sl4_conj_lbar_center_eq_bot D h hrow hxM
  have hcM : (c : MulAut (Vtil ⊥ V hV)) ∈ Mbar D.M ⊥ V hV :=
    (barSub_mono ⊥ V hV hconj_le) hc_mem
  have hφ_not : φ ∉ Subgroup.zpowers (c : MulAut (Vtil ⊥ V hV)) := by
    intro hmem
    have hφL : φ ∈ lBar ⊥ V hV (conjSubgroup L x) :=
      Subgroup.zpowers_le.mpr hc_mem hmem
    have hφcenter : (⟨φ, hφL⟩ : ↥(lBar ⊥ V hV (conjSubgroup L x))) ∈
        Subgroup.center ↥(lBar ⊥ V hV (conjSubgroup L x)) := by
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext (hcentx b b.2).symm
    rw [hcenter, Subgroup.mem_bot] at hφcenter
    have hφone : φ = 1 := congrArg Subtype.val hφcenter
    rw [hφone, orderOf_one] at hφ3
    exact absurd hφ3 (by norm_num)
  have hcomm : ∀ b ∈ Subgroup.zpowers (c : MulAut (Vtil ⊥ V hV)),
      b * φ = φ * b := by
    intro b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_left (show Commute (c : MulAut (Vtil ⊥ V hV)) φ from
      (hcentx c hc_mem).symm) n).eq
  have hcardc : Nat.card (Subgroup.zpowers (c : MulAut (Vtil ⊥ V hV))) = 3 := by
    rw [Nat.card_zpowers, hc_ord]
  obtain ⟨hEab, hEcard⟩ :=
    CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute (r := 3)
      (X := Subgroup.zpowers (c : MulAut (Vtil ⊥ V hV))) hcardc hφ3 hφ_not hcomm
  refine ⟨Subgroup.zpowers (c : MulAut (Vtil ⊥ V hV)) ⊔ Subgroup.zpowers φ, ?_, ?_, hEab, ?_⟩
  · exact sup_le (Subgroup.zpowers_le.mpr hcM) (Subgroup.zpowers_le.mpr hφM)
  · exact sup_le (Subgroup.zpowers_le.mpr (hconjL hc_mem))
      (Subgroup.zpowers_le.mpr (mem_centSub.mpr hfix))
  · rw [hEcard]
    norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

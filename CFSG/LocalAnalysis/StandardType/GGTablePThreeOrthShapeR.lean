module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTLabel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTAOne
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTATwo
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTDFour
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInOrthTransModel
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldMark
import CFSG.LocalAnalysis.StandardType.GGTPNDefs
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPDMinus
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryPower
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaOuterMinus
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPCAlign
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.Classical2

private theorem orthShapeR_congr_conj {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) (g : X) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

private theorem orthShapeR_congr_symm_congr {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) (σ : MulAut X) :
    MulAut.congr e.symm (MulAut.congr e σ) = σ := by
  ext x
  simp [MulAut.congr_apply]

private theorem orthShapeR_fixed_map_congr {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) (σ : MulAut X) :
    (ggAutFixedSubgroup σ).map e.toMonoidHom = ggAutFixedSubgroup (MulAut.congr e σ) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [mem_ggAutFixedSubgroup] at hx ⊢
    rw [MulAut.congr_apply]
    simp [hx]
  · intro hy
    refine Subgroup.mem_map.mpr ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [mem_ggAutFixedSubgroup] at hy ⊢
    rw [MulAut.congr_apply] at hy
    exact e.injective (by simpa using hy)

private theorem orthShapeR_mem_innSet_map {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) {A : Subgroup (MulAut X)}
    (hA : ∀ a ∈ A, a ∈ LargeEvenInnSet X) :
    ∀ a ∈ A.map (MulAut.congr e).toMonoidHom, a ∈ LargeEvenInnSet Y := by
  intro a ha
  obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
  have h := hA a₀ ha₀
  rw [LargeEvenInnSet, Set.mem_range] at h
  obtain ⟨g, hg⟩ := h
  refine ⟨e g, ?_⟩
  rw [← hg]
  exact (orthShapeR_congr_conj e g).symm

private theorem orthShapeR_rdatum_map {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {Ā : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X} (hR : RDatum Ā δ J) :
    RDatum (Ā.map (MulAut.congr e).toMonoidHom) (MulAut.congr e δ) (J.map e.toMonoidHom) where
  elem := CFSG.Open.IsElemAbelian.map hR.elem (MulAut.congr e).toMonoidHom
  mem := Subgroup.mem_map.mpr ⟨δ, hR.mem, rfl⟩
  ne_one := by
    intro h
    refine hR.ne_one ((MulAut.congr e).injective ?_)
    rw [h, map_one]
  comp := by
    have h := isComponentOf_map_mulEquiv e hR.comp
    rwa [orthShapeR_fixed_map_congr e δ] at h
  uniq := by
    intro Q hQ
    have hQ' := isComponentOf_map_mulEquiv e.symm hQ
    rw [orthShapeR_fixed_map_congr e.symm (MulAut.congr e δ),
      orthShapeR_congr_symm_congr e δ] at hQ'
    have huniq := hR.uniq (Q.map e.symm.toMonoidHom) hQ'
    have hmap : (Q.map e.symm.toMonoidHom).map e.toMonoidHom = Q := by
      have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y := by
        ext x
        simp
      rw [Subgroup.map_map, hcomp, Subgroup.map_id]
    rw [huniq] at hmap
    exact hmap.symm
  norm := by
    intro a ha j hj
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨j₀, hj₀, rfl⟩ := Subgroup.mem_map.mp hj
    exact ⟨a₀ j₀, hR.norm a₀ ha₀ j₀ hj₀, by simp [MulAut.congr_apply]⟩
  ker := by
    intro a ha hfix
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    have ha₀fix : ∀ j ∈ J, a₀ j = j := by
      intro j hj
      have hje : e j ∈ J.map e.toMonoidHom := Subgroup.mem_map.mpr ⟨j, hj, rfl⟩
      have h := hfix (e j) hje
      have h2 : e (a₀ j) = e j := by simpa [MulAut.congr_apply] using h
      exact e.injective h2
    have hz := hR.ker a₀ ha₀ ha₀fix
    have hmem : MulAut.congr e a₀ ∈ (Subgroup.zpowers δ).map (MulAut.congr e).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨a₀, hz, rfl⟩
    rw [MonoidHom.map_zpowers] at hmem
    simpa using hmem
  card := by
    have hc : Nat.card (Ā.map (MulAut.congr e).toMonoidHom) = Nat.card Ā :=
      Subgroup.card_map_of_injective (K := Ā) (f := (MulAut.congr e).toMonoidHom)
        (MulAut.congr e).injective
    rw [hc]
    exact hR.card

theorem orthR_shape
    {K : Type} [Field K] [Finite K] [CharP K 2] {n r : ℕ} (hK : Nat.card K = 2 ^ n)
    (hr : 4 ≤ r) (hsplit : 3 ∣ 2 ^ n - 1 ∨ n = 1)
    {Ā : Subgroup (MulAut (POmPlusG r K))} {δ' : MulAut (POmPlusG r K)}
    {J' : Subgroup (POmPlusG r K)} (hR : RDatum Ā δ' J')
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenInnSet (POmPlusG r K)) :
    OrthShapeConcl n r Ā J' := by
  let e : POmPlusG r K ≃* ProjOrthDerived (CFSG.LieType.Universal.Spin.quadPlus r K) :=
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.orthModelEquivPlus r K
  let Q : QuadraticForm K (Fin r ⊕ Fin r → K) := CFSG.LieType.Universal.Spin.quadPlus r K
  have hR' : RDatum (Ā.map (MulAut.congr e).toMonoidHom) (MulAut.congr e δ')
      (J'.map e.toMonoidHom) := orthShapeR_rdatum_map e hR
  have hĀI' : ∀ a ∈ Ā.map (MulAut.congr e).toMonoidHom,
      a ∈ LargeEvenInnSet (ProjOrthDerived Q) := orthShapeR_mem_innSet_map e hĀI
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus r K
  have hT : ∃ U : Submodule K (Fin r ⊕ Fin r → K), Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0 :=
    CFSG.SeitzReduction.SymplecticPilot.pd_exists_totallySingular_quadPlus (n := r)
      (by omega) K
  obtain ⟨lab, hΛ, hHasLabel', hcases⟩ :=
    orthT_label (K := K) (n := n) (V := Fin r ⊕ Fin r → K) (Q := Q) hK hQ hT hR' hĀI'
  let eJ : ↥J' ≃* ↥(J'.map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective J' e.toMonoidHom e.injective
  have hHasLabel : GGHasLabel lab (J' ⧸ Subgroup.center J') :=
    ggHasLabel_quotCenter_of_mulEquiv eJ.symm hHasLabel'
  refine ⟨lab, hΛ, hHasLabel, ?_⟩
  rcases lab with ⟨tag, rank, nlab⟩
  rcases hcases with hA | htwA | hB | hC | hD
  · subst hA
    refine Or.inl ⟨rfl, ?_, ?_⟩
    · intro hr1
      have hlab1 : GGHasLabel (⟨.A, 1, nlab⟩ : LargeEvenLabel)
          ((J'.map e.toMonoidHom) ⧸ Subgroup.center (J'.map e.toMonoidHom)) := by
        rw [← hr1]
        exact hHasLabel'
      have hcard := orthT_A1 hK hQ hT hR' hĀI' hlab1
      have hc : Nat.card (Ā.map (MulAut.congr e).toMonoidHom) = Nat.card Ā :=
        Subgroup.card_map_of_injective (K := Ā) (f := (MulAut.congr e).toMonoidHom)
          (MulAut.congr e).injective
      rwa [hc] at hcard
    · intro hr2
      have hlab2 : GGHasLabel (⟨.A, 2, nlab⟩ : LargeEvenLabel)
          ((J'.map e.toMonoidHom) ⧸ Subgroup.center (J'.map e.toMonoidHom)) := by
        rw [← hr2]
        exact hHasLabel'
      have hcent := orthT_A2 hK hQ hT hR' hĀI' hlab2
      intro hbot
      apply hcent
      rw [← Subgroup.map_center_eq eJ, hbot]
      exact Subgroup.map_bot _
  · rcases htwA with ⟨htwA, hrank2⟩
    subst htwA
    change 1 ≤ nlab ∧ (2 ≤ rank ∧ (rank = 2 → 2 ≤ nlab)) at hΛ
    change rank = 2 → nlab = n ∧ 3 ∣ 2 ^ n + 1 at hrank2
    refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    change 3 ≤ rank
    by_contra hlt
    have hrank_eq : rank = 2 := by have := hΛ.2.1; omega
    have hnlab : nlab = n := (hrank2 hrank_eq).1
    have hdiv : 3 ∣ 2 ^ n + 1 := (hrank2 hrank_eq).2
    have hn2 : 2 ≤ n := by have := hΛ.2.2 hrank_eq; omega
    rcases hsplit with hdvd | hn1
    · have h2n : 0 < 2 ^ n := pow_pos (by norm_num) n
      have hsub := Nat.dvd_sub hdiv hdvd
      have heq : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by omega
      rw [heq] at hsub
      exact absurd hsub (by norm_num)
    · omega
  · exact Or.inr (Or.inr (Or.inl hB))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hC)))
  · rcases hD with ⟨htagD, hrank4, hnlab⟩
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨htagD, hrank4, hnlab, ?_⟩)))
    intro hDtag hr4 hn1
    have hDtag' : tag = .D := hDtag
    subst hDtag'
    have hr4' : rank = 4 := hr4
    subst hr4'
    change nlab = n at hnlab
    rw [hnlab] at hHasLabel'
    have hnOdd : Odd n := by rw [hn1]; exact ⟨0, by norm_num⟩
    have hdim : Module.finrank K (Fin r ⊕ Fin r → K) = 2 * r := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      ring
    have hD4 := orthT_D4 hK hQ hT hR' hĀI' hdim hnOdd hHasLabel'
    have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q :=
      CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus K r
    have heven : Even (r - 4) := hD4.2.1.mp hplus
    have hge5 : 5 ≤ r := hD4.1
    have hle7 : r ≤ 7 := hD4.2.2.2
    obtain ⟨k, hk⟩ := heven
    omega

end CFSG.StandardType.TablePThreeKG

end

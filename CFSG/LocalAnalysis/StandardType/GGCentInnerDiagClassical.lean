module

public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagModel
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSp
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSpin
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
public import CFSG.LocalAnalysis.StandardType.GGGraphInvInputModelCore
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
public import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
public import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal
open CFSG.Open (StatedSp StatedOmega)

theorem ggE0Concl_centralizer_spinGroup_quadPlus {n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (hn : 4 ≤ n) (u : spinGroup (Spin.quadPlus n K)) (hu : Odd (orderOf u))
    (C : Subgroup (spinGroup (Spin.quadPlus n K)))
    (hC : IsComponentOf C (Subgroup.centralizer {u})) :
    GGE0Concl (Subgroup.centralizer {u}) C := by
  have hker : (Spin.spinMatrix (Spin.quadPlus n K)).ker = ⊥ :=
    Spin.ker_spinMatrix_quadPlus_eq_bot CharTwo.two_eq_zero
  have hR : (Spin.spinMatrix (Spin.quadPlus n K)).range = StatedOmega ⇑(Spin.quadPlus n K) := by
    rw [Spin.range_spinMatrix_quadPlus (by omega), Spin.coe_quadPlus]
  let e := CFSG.SectionRank.EvenCover.spinMatrixEquiv hker hR
  refine ggE0Concl_centralizer_of_mulEquiv e u ?_ C hC
  refine ggE0Concl_centralizer_statedOmega (Spin.quadPlus n K)
    (Spin.nondegenerate_polarBilin_quadPlus n K)
    (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) (e u) ?_
  rwa [show e u = e.toMonoidHom u from rfl, orderOf_injective e.toMonoidHom e.injective]

theorem ggE0Concl_centralizer_spinGroup_quadMinus {n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n)
    (u : spinGroup (Spin.quadMinus n K b c)) (hu : Odd (orderOf u))
    (C : Subgroup (spinGroup (Spin.quadMinus n K b c)))
    (hC : IsComponentOf C (Subgroup.centralizer {u})) :
    GGE0Concl (Subgroup.centralizer {u}) C := by
  have hker : (Spin.spinMatrix (Spin.quadMinus n K b c)).ker = ⊥ :=
    Spin.ker_spinMatrix_quadMinus_eq_bot hirr CharTwo.two_eq_zero
  have hR : (Spin.spinMatrix (Spin.quadMinus n K b c)).range =
      StatedOmega ⇑(Spin.quadMinus n K b c) := by
    rw [Spin.range_spinMatrix_quadMinus hn hirr, Spin.coe_quadMinus]
  let e := CFSG.SectionRank.EvenCover.spinMatrixEquiv hker hR
  refine ggE0Concl_centralizer_of_mulEquiv e u ?_ C hC
  refine ggE0Concl_centralizer_statedOmega (Spin.quadMinus n K b c)
    (Spin.nondegenerate_polarBilin_quadMinus_of_finite n K hirr)
    (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) (e u) ?_
  rwa [show e u = e.toMonoidHom u from rfl, orderOf_injective e.toMonoidHom e.injective]

theorem ggCentInnerDiagAt_PSp :
    GGCentInnerDiagAt .PSp := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 b hb hb1 C₀ hC₀
  have hbG0 : b ∈ ggG0 p B x L D J :=
    ggG1_le_ggG0_of_diagInner (ggPsiDiagInner_PSp : GGPsiDiagInnerAt .PSp) hctx s1
      (ggBs_le_ggG1 hctx hb)
  have hodd : Odd (orderOf b) :=
    ggGraphInv_odd_orderOf hctx.prime hctx.ne_two hb1 (hctx.bstar.2.1.2 b hb)
  obtain ⟨-, -, hn, -⟩ := hctx.2.2.2.1.1
  exact ggE0Concl_inf_centralizer_of_presents (U := ↥(StatedSp n (GaloisField 2 f))) ψ
    hctx.2.2.2.2.1.2
    (CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (by omega))
    hctx.range_eq hbG0 hodd (fun u hu C hC => ggE0Concl_centralizer_statedSp u hu C hC) hC₀

theorem ggCentInnerDiagAt_POmegaPlus :
    GGCentInnerDiagAt .POmegaPlus := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 b hb hb1 C₀ hC₀
  have hbG0 : b ∈ ggG0 p B x L D J :=
    ggG1_le_ggG0_of_diagInner (ggPsiDiagInner_POmegaPlus : GGPsiDiagInnerAt .POmegaPlus) hctx
      s1 (ggBs_le_ggG1 hctx hb)
  have hodd : Odd (orderOf b) :=
    ggGraphInv_odd_orderOf hctx.prime hctx.ne_two hb1 (hctx.bstar.2.1.2 b hb)
  obtain ⟨-, -, hn⟩ := hctx.2.2.2.1.1
  have hn3 : 3 ≤ n := by omega
  have hker := hctx.2.2.2.2.1.2
  have hrange := hctx.range_eq
  clear hctx s1
  revert ψ
  rw [show ggU .POmegaPlus n f = ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
      Spin.plusDatum n (GaloisField 2 f) hn3⟩ from dite_eq_left hn3]
  intro ψ hker hrange
  exact ggE0Concl_inf_centralizer_of_presents ψ hker
    (RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn3) hrange hbG0 hodd
    (fun u hu C hC => ggE0Concl_centralizer_spinGroup_quadPlus hn u hu C hC) hC₀

theorem ggCentInnerDiagAt_POmegaMinus :
    GGCentInnerDiagAt .POmegaMinus := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 b hb hb1 C₀ hC₀
  have hbG0 : b ∈ ggG0 p B x L D J :=
    ggG1_le_ggG0_of_diagInner ggPsiDiagInnerAt_POmegaMinus hctx s1 (ggBs_le_ggG1 hctx hb)
  have hodd : Odd (orderOf b) :=
    ggGraphInv_odd_orderOf hctx.prime hctx.ne_two hb1 (hctx.bstar.2.1.2 b hb)
  obtain ⟨-, -, hn⟩ := hctx.2.2.2.1.1
  exact ggE0Concl_inf_centralizer_of_presents
    (U := ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2))) ψ hctx.2.2.2.2.1.2
    (PsiDiag.SpinM.center_eq_bot (minusCoeffs_irr 2 f) hn) hctx.range_eq hbG0 hodd
    (fun u hu C hC =>
      ggE0Concl_centralizer_spinGroup_quadMinus (minusCoeffs_irr 2 f) hn u hu C hC) hC₀

theorem ggE0At_PSp :
    GGE0At .PSp :=
  ggE0At_of_centInnerDiag (ggPsiDiagInner_PSp : GGPsiDiagInnerAt .PSp) ggCentInnerDiagAt_PSp

theorem ggE0At_POmegaPlus :
    GGE0At .POmegaPlus :=
  ggE0At_of_centInnerDiag (ggPsiDiagInner_POmegaPlus : GGPsiDiagInnerAt .POmegaPlus)
    ggCentInnerDiagAt_POmegaPlus

theorem ggE0At_POmegaMinus :
    GGE0At .POmegaMinus :=
  ggE0At_of_centInnerDiag ggPsiDiagInnerAt_POmegaMinus ggCentInnerDiagAt_POmegaMinus

end CFSG.StandardType

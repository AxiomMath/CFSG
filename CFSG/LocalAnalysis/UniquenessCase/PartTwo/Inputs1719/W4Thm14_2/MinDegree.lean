module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.Rep
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.CGT.Timmesfeld75.MultPrime
public import CFSG.Quasithin.Background.HL42Aut
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltFin
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

theorem k_SL3MinDegree_holds :
    ∀ (X : Type) [Group X] [Finite X],
      (CFSG.LocalAnalysis.UniquenessCase.UC22.IsSL3 X 2 ∨
        CFSG.LocalAnalysis.UniquenessCase.UC22.IsSL3 X 4) → 5 ≤ dMinDeg X := by
  intro X _ _ hX
  have hQ : CFSG.Open.IsQuasisimple X := by rcases hX with h | h <;> exact h.1
  haveI : Nontrivial X := nontrivial_of_isQuasisimple hQ
  refine le_dMinDeg (D := 5) ?_
  intro d f hf
  by_contra h5
  have hd4 : d ≤ 4 := by omega
  have hker : f.ker ≤ Subgroup.center X := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hQ f.ker with h | h
    · exact h
    · exfalso
      apply hf
      apply MonoidHom.ext
      intro x
      simpa using MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x)
  have hdiv : Nat.card (X ⧸ Subgroup.center X) ∣ Nat.card f.range := by
    have hcard1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
    have hcard2 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hker
    refine ⟨m, ?_⟩
    have hkpos : 0 < Nat.card f.ker := Nat.card_pos
    have hq : Nat.card (X ⧸ f.ker) = Nat.card f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    have heq : Nat.card (X ⧸ Subgroup.center X) * m = Nat.card f.range := by
      apply Nat.eq_of_mul_eq_mul_right hkpos
      calc (Nat.card (X ⧸ Subgroup.center X) * m) * Nat.card f.ker
          = Nat.card (X ⧸ Subgroup.center X) * (Nat.card f.ker * m) := by ring
        _ = Nat.card (X ⧸ Subgroup.center X) * Nat.card (Subgroup.center X) := by rw [← hm]
        _ = Nat.card X := hcard1.symm
        _ = Nat.card (X ⧸ f.ker) * Nat.card f.ker := hcard2
        _ = Nat.card f.range * Nat.card f.ker := by rw [hq]
    exact heq.symm
  have hdvdGL : Nat.card (X ⧸ Subgroup.center X) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2)) := by
    have h := hdiv.trans (Subgroup.card_dvd_of_le (le_top : f.range ≤ ⊤))
    simpa [Subgroup.card_top] using h
  have hGLle : Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2)) ≤ 20160 := by
    interval_cases d <;> rw [Matrix.card_GL_field, ZMod.card] <;> decide
  rcases hX with ⟨-, hL⟩ | ⟨-, hL⟩
  ·
    have hsc : CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (X ⧸ Subgroup.center X) .PSL 3 2 2 :=
      CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hL
    have hcardX : Nat.card (X ⧸ Subgroup.center X) = 20160 :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four hsc
    have h20160dvd : 20160 ∣ Nat.card f.range := by
      rw [← hcardX]
      exact hdiv
    have hrangeLe : Nat.card f.range ≤ 20160 := by
      have h := Nat.le_of_dvd Nat.card_pos
        (Subgroup.card_dvd_of_le (le_top : f.range ≤ ⊤))
      rw [Subgroup.card_top] at h
      exact h.trans hGLle
    have hrangeCard : Nat.card f.range = 20160 :=
      le_antisymm hrangeLe (Nat.le_of_dvd Nat.card_pos h20160dvd)
    have hGLeq : Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2)) = 20160 := by
      refine le_antisymm hGLle (Nat.le_of_dvd Nat.card_pos ?_)
      have h := h20160dvd.trans (Subgroup.card_dvd_of_le (le_top : f.range ≤ ⊤))
      simpa [Subgroup.card_top] using h
    have hd : d = 4 := by
      by_contra hne
      have hd3 : d ≤ 3 := by omega
      have hlt : Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2)) < 20160 := by
        interval_cases d <;> rw [Matrix.card_GL_field, ZMod.card] <;> decide
      omega
    have hrangeTop : f.range = ⊤ := by
      apply Subgroup.eq_of_le_of_card_ge le_top
      rw [Subgroup.card_top, hGLeq, hrangeCard]
    have hquot : Nat.card (X ⧸ f.ker) = Nat.card (X ⧸ Subgroup.center X) := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrangeCard, hcardX]
    have hZcard : Nat.card (Subgroup.center X) = Nat.card f.ker := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
      have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
      rw [hquot] at h2
      have hpos : 0 < Nat.card (X ⧸ Subgroup.center X) := by rw [hcardX]; norm_num
      exact Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans h2)
    have hkerEq : f.ker = Subgroup.center X :=
      Subgroup.eq_of_le_of_card_ge hker (le_of_eq hZcard)
    have eGLd : (X ⧸ Subgroup.center X) ≃*
        Matrix.GeneralLinearGroup (Fin d) (ZMod 2) :=
      (QuotientGroup.quotientMulEquivOfEq hkerEq.symm).trans
        ((QuotientGroup.quotientKerEquivRange f).trans
          ((MulEquiv.subgroupCongr hrangeTop).trans Subgroup.topEquiv))
    have eGL4 : (X ⧸ Subgroup.center X) ≃*
        Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) := by
      rw [← hd]
      exact eGLd
    have eA8 : (X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 8) :=
      eGL4.trans CFSG.Quasithin.H.L4.alpha8.symm
    obtain ⟨-, K, _, _, hKcard, ⟨eStated⟩⟩ := hsc
    have hK4 : Nat.card K = 4 := by
      rw [hKcard]
      norm_num
    have eProj : projectiveSL 3 K ≃* alternatingGroup (Fin 8) :=
      (CFSG.CGT.Timmesfeld75.projectiveSLMulEquivStatedProj 3 K).trans
        (eStated.symm.trans eA8)
    exact CFSG.HardMathSupport.Solomon.Coordinator.false_of_projectiveSL_alt_eight hK4 eProj
  ·
    have hsc : CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (X ⧸ Subgroup.center X) .PSL 3 2 4 :=
      CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hL
    have hcardX : Nat.card (X ⧸ Subgroup.center X) = 1425715200 :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_sixteen hsc
    have hle : Nat.card (X ⧸ Subgroup.center X) ≤ 20160 :=
      (Nat.le_of_dvd Nat.card_pos hdvdGL).trans hGLle
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

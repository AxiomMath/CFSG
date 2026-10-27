module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CCoordDefs
public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpFrame
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoKey
public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpComp
import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpNsComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeFixed2
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel
import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel
import CFSG.LocalAnalysis.SteinbergCCPowerTwoDegreeTransport
import CFSG.LocalAnalysis.ComponentClassification.TBLitL34P
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs
import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank
import CFSG.Goldschmidt75.WeakClosure
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverInvModel
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicGen
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealModelBase
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandard
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsReal
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Normal
import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
import CFSG.SignalizerFunctorTheorem.NonLocal.SpData

public section

namespace CFSG.StandardType.HdRo7C

open CFSG.StandardType
open CFSG.Open
open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7CKCoordAux_zeroSet_card_zero_false
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L] [Module.Finite (GaloisField 2 1) L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (hdim : Module.finrank (GaloisField 2 1) L = 2)
    {m : ℕ} (hm : 5 ≤ m) {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (J' : Subgroup (StatedSp m (GaloisField 2 1)))
    (hJ' : CFSG.Assembly.IsComponentOf J'
      (Subgroup.centralizer ({F.tor c} : Set (StatedSp m (GaloisField 2 1)))))
    (hfix : J' ≤ CFSG.RankThree.PartOne.spFixedFactor (F.tor c))
    (h0 : (F.zeroSet c).card = 0) : False := by
  have hdim0 : CFSG.RankThree.PartOne.spFixedDim (F.tor c) = 0 := by
    rw [F.spFixedDim_tor hζ hdim c, h0]
  have hbot : CFSG.RankThree.PartOne.spFixedFactor (F.tor c) = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremA.T173O.spFixedFactor_eq_bot_of_spFixedDim_eq_zero
      (F.tor_pow_three hζ.pow_eq_one c) hdim0
  have hJq : CFSG.IsQuasisimple ↥J' :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J').1 hJ'.2.2
  exact CFSG.StandardType.ClNonsplit.not_isQuasisimple_of_le
    (show Group.IsSolvable ↥(⊥ : Subgroup (StatedSp m (GaloisField 2 1))) from inferInstance)
    (hfix.trans (le_of_eq hbot)) hJq

theorem hdRo7CKCoordAux_zeroSet_card_one_false
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L] [Module.Finite (GaloisField 2 1) L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (hdim : Module.finrank (GaloisField 2 1) L = 2)
    {m : ℕ} (hm : 5 ≤ m) {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (J' : Subgroup (StatedSp m (GaloisField 2 1)))
    (hJ' : CFSG.Assembly.IsComponentOf J'
      (Subgroup.centralizer ({F.tor c} : Set (StatedSp m (GaloisField 2 1)))))
    (hfix : J' ≤ CFSG.RankThree.PartOne.spFixedFactor (F.tor c))
    (h1 : (F.zeroSet c).card = 1) : False := by
  haveI : NeZero m := ⟨by omega⟩
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [CFSG.ComponentClassification.TBLit.L34P.card_galoisField (p := 2) (n := 1)
      (by norm_num)]
    norm_num
  have hc : c ≠ 0 := by
    intro hc
    subst hc
    have hzero : F.zeroSet (0 : Fin F.s → ZMod 3) = Finset.univ := by
      ext i; simp [ChoiceTwo.SpFrame.zeroSet]
    rw [hzero, Finset.card_univ, Fintype.card_fin, A6InsideSp.s_eq F hdim] at h1
    omega
  have hdim2 : CFSG.RankThree.PartOne.spFixedDim (F.tor c) = 2 := by
    rw [F.spFixedDim_tor hζ hdim c, h1]
  have hblocks : CFSG.RankThree.Classical.SpPrimaryBlocks 2 1 3 (F.tor c)
      ((CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m (GaloisField 2 1))
        (F.tor c)) :=
    F.blocks_tor hK hζ hc
  have hcard : Nat.card ↥(CFSG.RankThree.PartOne.spFixedFactor (F.tor c)) = 6 := by
    rw [CFSG.RankThree.PartOne.card_spFixedFactor_of_dim_two (x := F.tor c) hblocks hdim2, hK]
    norm_num
  have hsolv : Group.IsSolvable ↥(CFSG.RankThree.PartOne.spFixedFactor (F.tor c)) :=
    CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
      (by rw [hcard]; exact CFSG.StandardType.SevSpNs.card_primeFactors_six)
  have hJq : CFSG.IsQuasisimple ↥J' :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J').1 hJ'.2.2
  exact CFSG.StandardType.ClNonsplit.not_isQuasisimple_of_le hsolv hfix hJq

theorem hdRo7CKCoordAux_zeroSet_card_two_false
    (hRig : GGLabelRigidInput)
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L] [Module.Finite (GaloisField 2 1) L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (hdim : Module.finrank (GaloisField 2 1) L = 2)
    {m : ℕ} (hm : 5 ≤ m) {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (J' : Subgroup (StatedSp m (GaloisField 2 1)))
    (hJ' : CFSG.Assembly.IsComponentOf J'
      (Subgroup.centralizer ({F.tor c} : Set (StatedSp m (GaloisField 2 1)))))
    {tag : LargeEvenLieTag} (htag : tag = .B ∨ tag = .C)
    (hlabel : GGHasLabel ⟨tag, m - 2, 1⟩ (↥J' ⧸ Subgroup.center ↥J'))
    (hfix : J' ≤ CFSG.RankThree.PartOne.spFixedFactor (F.tor c))
    (h2 : (F.zeroSet c).card = 2) : False := by
  haveI : NeZero m := ⟨by omega⟩
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [CFSG.ComponentClassification.TBLit.L34P.card_galoisField (p := 2) (n := 1)
      (by norm_num)]
    norm_num
  have hc : c ≠ 0 := by
    intro hc
    subst hc
    have hzero : F.zeroSet (0 : Fin F.s → ZMod 3) = Finset.univ := by
      ext i; simp [ChoiceTwo.SpFrame.zeroSet]
    rw [hzero, Finset.card_univ, Fintype.card_fin, A6InsideSp.s_eq F hdim] at h2
    omega
  have hdim4 : CFSG.RankThree.PartOne.spFixedDim (F.tor c) = 4 := by
    rw [F.spFixedDim_tor hζ hdim c, h2]
  have hblocks : CFSG.RankThree.Classical.SpPrimaryBlocks 2 1 3 (F.tor c)
      ((CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m (GaloisField 2 1))
        (F.tor c)) :=
    F.blocks_tor hK hζ hc
  set H := CFSG.RankThree.PartOne.spFixedFactor (F.tor c) with hH
  set D : Subgroup (StatedSp m (GaloisField 2 1)) := ⁅H, H⁆ with hD
  have hDq : CFSG.IsQuasisimple ↥D :=
    (CFSG.RankThree.PartOne.spFixed_four_two hK hblocks hdim4).1
  have hDalt : Nonempty (↥D ≃* ↥(alternatingGroup (Fin 6))) :=
    (CFSG.RankThree.PartOne.spFixed_four_two_alt hK hblocks hdim4).1
  have hJq : CFSG.IsQuasisimple ↥J' :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J').1 hJ'.2.2
  have hJD : J' ≤ D := by
    rw [← LayerFacts.ggCommutator_eq_of_isQuasisimple hJq]
    exact Subgroup.commutator_mono hfix hfix
  have hDle : D ≤ Subgroup.centralizer ({F.tor c} : Set (StatedSp m (GaloisField 2 1))) :=
    (Subgroup.commutator_le_self H).trans
      (CFSG.RankThree.PartOne.spFixedFactor_le_centralizer (F.tor c))
  have hDcomp : CFSG.Assembly.IsComponentOf D
      (Subgroup.centralizer ({F.tor c} : Set (StatedSp m (GaloisField 2 1)))) := by
    refine CFSG.StandardType.SpNonsplitComp.isComponentOf_of_normalizes hDle ?_ hDq
    intro y hy g hg
    have hHnorm : ∀ z ∈ H, y * z * y⁻¹ ∈ H := fun z hz =>
      CFSG.RankThree.PartOne.spFixedFactor_normalized (F.tor c) y hy z hz
    have hHnorm' : ∀ z ∈ H, y⁻¹ * z * (y⁻¹)⁻¹ ∈ H := fun z hz =>
      CFSG.RankThree.PartOne.spFixedFactor_normalized (F.tor c) y⁻¹
        (Subgroup.inv_mem _ hy) z hz
    have hHmap : H.map (MulAut.conj y).toMonoidHom = H := by
      refine le_antisymm ?_ ?_
      · rintro z ⟨w, hw, rfl⟩
        simpa [MulAut.conj_apply] using hHnorm w hw
      · have hle' : H.map (MulAut.conj y⁻¹).toMonoidHom ≤ H := by
          rintro z ⟨w, hw, rfl⟩
          simpa [MulAut.conj_apply] using hHnorm' w hw
        have hcomp : (MulAut.conj y).toMonoidHom.comp (MulAut.conj y⁻¹).toMonoidHom =
            MonoidHom.id _ := by
          ext z
          simp [MulAut.conj_apply, mul_assoc]
        calc H = (H.map (MulAut.conj y⁻¹).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
              rw [Subgroup.map_map, hcomp]; simp
          _ ≤ H.map (MulAut.conj y).toMonoidHom := Subgroup.map_mono hle'
    have hDmap : D.map (MulAut.conj y).toMonoidHom = D := by
      rw [hD, Subgroup.map_commutator, hHmap]
    have : (MulAut.conj y) g ∈ D := by
      rw [← hDmap]
      exact Subgroup.mem_map_of_mem _ hg
    simpa [MulAut.conj_apply] using this
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hJ' hDcomp with
    heq | hcomm
  · obtain ⟨e⟩ := hDalt
    obtain ⟨e'⟩ : Nonempty (↥J' ⧸ Subgroup.center ↥J' ≃* ↥(alternatingGroup (Fin 6))) := by
      rw [heq]
      haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
        alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 6))
      have hDna : ∃ a b : ↥D, a * b ≠ b * a := by
        by_contra h
        push Not at h
        obtain ⟨a, b, hab⟩ := hDq.2.2
        obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥D) a
        obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥D) b
        exact hab (by rw [← map_mul, ← map_mul, h a' b'])
      have hZ : Subgroup.center ↥(alternatingGroup (Fin 6)) = ⊥ :=
        center_eq_bot_of_simple_nonabelian (nonabelian_of_mulEquiv e hDna)
      refine ⟨(QuotientGroup.congr (Subgroup.center ↥D)
        (Subgroup.center ↥(alternatingGroup (Fin 6))) e ?_).trans ?_⟩
      · rw [CFSG.LocalAnalysis.PowerTwoDegree.map_center_eq e, hZ]
      · exact (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    have hB2 : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J' ⧸ Subgroup.center ↥J') :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GSympLabel.ggHasLabel_b2der e'
    have hΛ : LargeEvenInLambda2 (⟨tag, m - 2, 1⟩ : LargeEvenLabel) := by
      rcases htag with rfl | rfl <;> simp [LargeEvenInLambda2] <;> omega
    have hΛB : LargeEvenInLambda2 (⟨.B2der, 0, 1⟩ : LargeEvenLabel) := by
      simp [LargeEvenInLambda2]
    have hiso := hRig _ _ _ hΛ hΛB hlabel hB2
    rcases hiso with h | h | h | h | h | h | h | h
    all_goals (exfalso; rcases htag with rfl | rfl <;>
      (try rcases h with ⟨h1, h2⟩) <;> simp_all)
  · exfalso
    have hJc : J' ≤ Subgroup.centralizer (↑D : Set (StatedSp m (GaloisField 2 1))) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hc' : Subgroup.centralizer (↑D : Set (StatedSp m (GaloisField 2 1))) ≤
        Subgroup.centralizer (↑J' : Set (StatedSp m (GaloisField 2 1))) :=
      Subgroup.centralizer_le (fun g hg => hJD hg)
    exact CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple
      hJ'.2.2 (hJc.trans hc')

end CFSG.StandardType.HdRo7C

end

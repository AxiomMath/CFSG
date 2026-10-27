module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CCoordDefs
public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpFrame
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoKey
public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpComp
import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoordBCoreS
import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpNsComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeFixed2
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel
import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel
import CFSG.LocalAnalysis.SteinbergCCPowerTwoDegreeTransport
import CFSG.LocalAnalysis.ComponentClassification.TBLitL34P
import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoordBCoreSmall
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

private theorem hdRo7CKCoordAux_supp_card_eq_two
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L] [Module.Finite (GaloisField 2 1) L]
    {ζ : L} {m : ℕ} (hm : 5 ≤ m) {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (hdim : Module.finrank (GaloisField 2 1) L = 2)
    (h : (F.zeroSet c).card = m - 2) : (F.suppSet c).card = 2 := by
  have hs : F.s = m := A6InsideSp.s_eq F hdim
  have hsum : (F.zeroSet c).card + (F.suppSet c).card = m := by
    have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => c i = 0)
    simpa [ChoiceTwo.SpFrame.zeroSet, ChoiceTwo.SpFrame.suppSet, hs] using hcard
  omega

private theorem hdRo7CKCoordAux_split
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L] [Module.Finite (GaloisField 2 1) L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (hdim : Module.finrank (GaloisField 2 1) L = 2)
    {m : ℕ} (hm : 5 ≤ m) {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (J' : Subgroup (StatedSp m (GaloisField 2 1)))
    (hJ' : CFSG.Assembly.IsComponentOf J'
      (Subgroup.centralizer ({F.tor c} : Set (StatedSp m (GaloisField 2 1))))) :
    J' ≤ CFSG.RankThree.PartOne.spFixedFactor (F.tor c) ∨
      J' ≤ CFSG.RankThree.Classical.spSupported (F.tor c) {ChoiceTwo.phi3 (GaloisField 2 1)} := by
  haveI : NeZero m := ⟨by omega⟩
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [CFSG.ComponentClassification.TBLit.L34P.card_galoisField (p := 2) (n := 1) (by norm_num)]
    norm_num
  have hQ : CFSG.Assembly.IsComponentOf J'
      (Subgroup.centralizer (↑(Subgroup.closure ({F.tor c} : Set (StatedSp m (GaloisField 2 1))))
        : Set (StatedSp m (GaloisField 2 1)))) := by
    rw [Subgroup.centralizer_closure]
    exact hJ'
  refine A6InsideSp.le_spFixedFactor_or_le_spSupported (F := F) (f := c)
    (D := Subgroup.closure ({F.tor c} : Set (StatedSp m (GaloisField 2 1)))) (Q := J') hK hζ ?_ ?_ hQ
  · rw [Subgroup.closure_le]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · rw [Subgroup.centralizer_closure]

private theorem hdRo7CKCoordAux_rank_eq_of_ggLabelIso
    {t₁ t₂ : LargeEvenLieTag} (h₁ : t₁ = .B ∨ t₁ = .C) (h₂ : t₂ = .B ∨ t₂ = .C)
    {r₁ r₂ : ℕ} (h : GGLabelIso ⟨t₁, r₁, 1⟩ ⟨t₂, r₂, 1⟩) : r₁ = r₂ := by
  rcases h with h | h | h | h | h | h | h | h
  · exact congrArg LargeEvenLabel.rank h
  · exact h.2.2.1
  all_goals (exfalso; rcases h with ⟨h1, h2⟩; rcases h₁ with rfl | rfl <;> simp_all)

private theorem hdRo7CKCoordAux_ggHasLabel_B_of_proj_iso
    {k : ℕ} {X : Type} [Group X]
    (hX : Nonempty (X ≃* StatedProj (StatedSp k (GaloisField 2 1)))) :
    GGHasLabel ⟨.B, k, 1⟩ X := by
  obtain ⟨e⟩ := hX
  exact CFSG.LocalAnalysis.GLTheoremA.Y10GSympLabel.ggHasLabel_typeB (E := GaloisField 2 1)
    (by rw [CFSG.ComponentClassification.TBLit.L34P.card_galoisField (p := 2) (n := 1)
      (by norm_num)]) e

private theorem hdRo7CKCoordAux_spFixedFactor_one_eq_top
    {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} (hK : Nat.card K = 2) :
    CFSG.RankThree.PartOne.spFixedFactor (1 : StatedSp m K) = ⊤ := by
  refine le_antisymm le_top fun g _ => ?_
  rw [CFSG.RankThree.PartOne.spFixedFactor]
  refine ChoiceTwo.mem_spSupported_of hK (by simp) (by simp)
    (fun h => absurd (Set.mem_singleton (Polynomial.X - 1)) h) ?_
  intro _ v hv
  rw [ChoiceTwo.spEnd_one_apply, ChoiceTwo.spEnd_one_apply] at hv
  have hv0 : v = 0 := by
    rw [ChoiceTwo.add_self_eq_zero_of_charTwo (K := K), zero_add] at hv
    exact hv
  rw [hv0, map_zero]

private theorem hdRo7CKCoordAux_fixed_proj_iso_zero
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L] [Module.Finite (GaloisField 2 1) L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (hdim : Module.finrank (GaloisField 2 1) L = 2)
    {m : ℕ} (hm : 5 ≤ m) {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (J' : Subgroup (StatedSp m (GaloisField 2 1)))
    (heq : J' = CFSG.RankThree.PartOne.spFixedFactor (F.tor c))
    (hc : c = 0) :
    Nonempty (↥J' ⧸ Subgroup.center ↥J' ≃*
      StatedProj (StatedSp (F.zeroSet c).card (GaloisField 2 1))) := by
  subst c
  haveI : NeZero m := ⟨by omega⟩
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [CFSG.ComponentClassification.TBLit.L34P.card_galoisField (p := 2) (n := 1)
      (by norm_num)]
    norm_num
  rw [F.tor_zero, hdRo7CKCoordAux_spFixedFactor_one_eq_top hK] at heq
  subst J'
  have hzero : F.zeroSet (0 : Fin F.s → ZMod 3) = Finset.univ := by
    ext i; simp [ChoiceTwo.SpFrame.zeroSet]
  have hcard : (F.zeroSet (0 : Fin F.s → ZMod 3)).card = m := by
    rw [hzero, Finset.card_univ, Fintype.card_fin, A6InsideSp.s_eq F hdim]
  rw [hcard]
  refine ⟨QuotientGroup.congr
    (Subgroup.center ↥(⊤ : Subgroup (StatedSp m (GaloisField 2 1))))
    ((StatedScalars (Fin m ⊕ Fin m) (GaloisField 2 1)).subgroupOf
      (StatedSp m (GaloisField 2 1))) Subgroup.topEquiv ?_⟩
  rw [CFSG.LocalAnalysis.PowerTwoDegree.map_center_eq Subgroup.topEquiv, AutPSp.center_eq_bot,
    CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.statedScalars_subgroupOf_eq_bot hK]

private theorem hdRo7CKCoordAux_fixed_proj_iso
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L] [Module.Finite (GaloisField 2 1) L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (hdim : Module.finrank (GaloisField 2 1) L = 2)
    {m : ℕ} (hm : 5 ≤ m) {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (J' : Subgroup (StatedSp m (GaloisField 2 1)))
    (hz : (F.zeroSet c).Nonempty)
    (heq : J' = CFSG.RankThree.PartOne.spFixedFactor (F.tor c)) :
    Nonempty (↥J' ⧸ Subgroup.center ↥J' ≃*
      StatedProj (StatedSp (F.zeroSet c).card (GaloisField 2 1))) := by
  by_cases hc : c = 0
  · exact hdRo7CKCoordAux_fixed_proj_iso_zero hζ hdim hm F c J' heq hc
  · haveI : NeZero m := ⟨by omega⟩
    have hK : Nat.card (GaloisField 2 1) = 2 := by
      rw [CFSG.ComponentClassification.TBLit.L34P.card_galoisField (p := 2) (n := 1)
        (by norm_num)]
      norm_num
    obtain ⟨e⟩ := A6InsideSp.nonempty_spFixedFactor_equiv F hK hζ hdim hc hz
    subst J'
    have hk1 : 1 ≤ (F.zeroSet c).card := Nat.succ_le_of_lt (Finset.card_pos.mpr hz)
    refine ⟨QuotientGroup.congr
      (Subgroup.center ↥(CFSG.RankThree.PartOne.spFixedFactor (F.tor c)))
      ((StatedScalars (Fin (F.zeroSet c).card ⊕ Fin (F.zeroSet c).card)
        (GaloisField 2 1)).subgroupOf
        (StatedSp (F.zeroSet c).card (GaloisField 2 1))) e ?_⟩
    rw [CFSG.LocalAnalysis.PowerTwoDegree.map_center_eq e,
      CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (F := GaloisField 2 1)
        (m := (F.zeroSet c).card) hk1,
      CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.statedScalars_subgroupOf_eq_bot
        hK]

private theorem hdRo7CKCoordAux_fixed_label
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L] [Module.Finite (GaloisField 2 1) L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (hdim : Module.finrank (GaloisField 2 1) L = 2)
    {m : ℕ} (hm : 5 ≤ m) {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (J' : Subgroup (StatedSp m (GaloisField 2 1)))
    (hz : (F.zeroSet c).Nonempty)
    (heq : J' = CFSG.RankThree.PartOne.spFixedFactor (F.tor c)) :
    GGHasLabel ⟨.B, (F.zeroSet c).card, 1⟩ (↥J' ⧸ Subgroup.center ↥J') :=
  hdRo7CKCoordAux_ggHasLabel_B_of_proj_iso
    (hdRo7CKCoordAux_fixed_proj_iso hζ hdim hm F c J' hz heq)

private theorem hdRo7CKCoordAux_fixed_eq_zero
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L] [Module.Finite (GaloisField 2 1) L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (hdim : Module.finrank (GaloisField 2 1) L = 2)
    {m : ℕ} (hm : 5 ≤ m) {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (J' : Subgroup (StatedSp m (GaloisField 2 1)))
    (hJ' : CFSG.Assembly.IsComponentOf J'
      (Subgroup.centralizer ({F.tor c} : Set (StatedSp m (GaloisField 2 1)))))
    (hfix : J' ≤ CFSG.RankThree.PartOne.spFixedFactor (F.tor c))
    (hc : c = 0) :
    J' = CFSG.RankThree.PartOne.spFixedFactor (F.tor c) := by
  subst c
  haveI : NeZero m := ⟨by omega⟩
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [CFSG.ComponentClassification.TBLit.L34P.card_galoisField (p := 2) (n := 1)
      (by norm_num)]
    norm_num
  have hC1 : Subgroup.centralizer ({1} : Set (StatedSp m (GaloisField 2 1))) = ⊤ := by
    refine le_antisymm le_top fun x _ => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp
  rw [F.tor_zero, hC1] at hJ'
  rw [F.tor_zero, hdRo7CKCoordAux_spFixedFactor_one_eq_top hK]
  have hqS : CFSG.IsQuasisimple (StatedSp m (GaloisField 2 1)) :=
    CFSG.LieType.Universal.Symplectic.isQuasisimple (n := m)
      (hF := Or.inr (Or.inr ⟨hK, by omega⟩)) (hn := by omega)
  have hq : CFSG.IsQuasisimple ↥(⊤ : Subgroup (StatedSp m (GaloisField 2 1))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hqS
  have hcomp : CFSG.Assembly.IsComponentOf (⊤ : Subgroup (StatedSp m (GaloisField 2 1))) ⊤ :=
    CFSG.StandardType.SpNonsplitComp.isComponentOf_of_normalizes le_top
      (fun a _ b _ => Subgroup.mem_top _) hq
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hJ' hcomp with
    heq | hcomm
  · exact heq
  · exfalso
    have hJc : J' ≤ Subgroup.centralizer
        (↑(⊤ : Subgroup (StatedSp m (GaloisField 2 1))) :
          Set (StatedSp m (GaloisField 2 1))) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hc' : Subgroup.centralizer
        (↑(⊤ : Subgroup (StatedSp m (GaloisField 2 1))) :
          Set (StatedSp m (GaloisField 2 1))) ≤
        Subgroup.centralizer (↑J' : Set (StatedSp m (GaloisField 2 1))) :=
      Subgroup.centralizer_le (fun a _ => Subgroup.mem_top a)
    exact CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple
      hJ'.2.2 (hJc.trans hc')

private theorem hdRo7CKCoordAux_fixed_eq
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L] [Module.Finite (GaloisField 2 1) L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (hdim : Module.finrank (GaloisField 2 1) L = 2)
    {m : ℕ} (hm : 5 ≤ m) {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (J' : Subgroup (StatedSp m (GaloisField 2 1)))
    (hJ' : CFSG.Assembly.IsComponentOf J'
      (Subgroup.centralizer ({F.tor c} : Set (StatedSp m (GaloisField 2 1)))))
    (hfix : J' ≤ CFSG.RankThree.PartOne.spFixedFactor (F.tor c))
    (h3 : 3 ≤ (F.zeroSet c).card) :
    J' = CFSG.RankThree.PartOne.spFixedFactor (F.tor c) := by
  by_cases hc : c = 0
  · exact hdRo7CKCoordAux_fixed_eq_zero hζ hdim hm F c J' hJ' hfix hc
  · haveI : NeZero m := ⟨by omega⟩
    have hK : Nat.card (GaloisField 2 1) = 2 := by
      rw [CFSG.ComponentClassification.TBLit.L34P.card_galoisField (p := 2) (n := 1)
        (by norm_num)]
      norm_num
    have hz : (F.zeroSet c).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨e⟩ := A6InsideSp.nonempty_spFixedFactor_equiv F hK hζ hdim hc hz
    have hqS : CFSG.IsQuasisimple ↥(StatedSp (F.zeroSet c).card (GaloisField 2 1)) :=
      CFSG.LieType.Universal.Symplectic.isQuasisimple (n := (F.zeroSet c).card)
        (hF := Or.inr (Or.inr ⟨hK, h3⟩)) (hn := by omega)
    have hq : CFSG.IsQuasisimple ↥(CFSG.RankThree.PartOne.spFixedFactor (F.tor c)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hqS
    have hle := CFSG.RankThree.PartOne.spFixedFactor_le_centralizer (F.tor c)
    have hnorm : ∀ y ∈ Subgroup.centralizer
          ({F.tor c} : Set (StatedSp m (GaloisField 2 1))),
        ∀ g ∈ CFSG.RankThree.PartOne.spFixedFactor (F.tor c), y * g * y⁻¹ ∈
          CFSG.RankThree.PartOne.spFixedFactor (F.tor c) :=
      fun y hy g hg => CFSG.RankThree.PartOne.spFixedFactor_normalized (F.tor c) y hy g hg
    have hcomp := CFSG.StandardType.SpNonsplitComp.isComponentOf_of_normalizes hle hnorm hq
    rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hJ' hcomp with
      heq | hcomm
    · exact heq
    · exfalso
      have hJc : J' ≤ Subgroup.centralizer
          (↑(CFSG.RankThree.PartOne.spFixedFactor (F.tor c)) :
            Set (StatedSp m (GaloisField 2 1))) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      have hc' : Subgroup.centralizer
          (↑(CFSG.RankThree.PartOne.spFixedFactor (F.tor c)) :
            Set (StatedSp m (GaloisField 2 1))) ≤
          Subgroup.centralizer (↑J' : Set (StatedSp m (GaloisField 2 1))) :=
        Subgroup.centralizer_le (fun g hg => hfix hg)
      exact CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple
        hJ'.2.2 (hJc.trans hc')


private theorem hdRo7CKCoordAux_zeroSet_ge_three
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
    (hfix : J' ≤ CFSG.RankThree.PartOne.spFixedFactor (F.tor c)) :
    3 ≤ (F.zeroSet c).card := by
  have hcases : (F.zeroSet c).card = 0 ∨ (F.zeroSet c).card = 1 ∨
      (F.zeroSet c).card = 2 ∨ 3 ≤ (F.zeroSet c).card := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · exact (hdRo7CKCoordAux_zeroSet_card_zero_false hζ hdim hm F c J' hJ' hfix h0).elim
  · exact (hdRo7CKCoordAux_zeroSet_card_one_false hζ hdim hm F c J' hJ' hfix h1).elim
  · exact (hdRo7CKCoordAux_zeroSet_card_two_false hRig hζ hdim hm F c J' hJ' htag hlabel hfix
      h2).elim
  · exact h3

private theorem hdRo7CKCoordAux_fixed_rank
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
    (hfix : J' ≤ CFSG.RankThree.PartOne.spFixedFactor (F.tor c)) :
    (F.zeroSet c).card = m - 2 := by
  have h3 := hdRo7CKCoordAux_zeroSet_ge_three hRig hζ hdim hm F c J' hJ' htag hlabel hfix
  have heq := hdRo7CKCoordAux_fixed_eq hζ hdim hm F c J' hJ' hfix h3
  have hz : (F.zeroSet c).Nonempty := Finset.card_pos.mp (by omega)
  have hB := hdRo7CKCoordAux_fixed_label hζ hdim hm F c J' hz heq
  have hΛ : LargeEvenInLambda2 ⟨tag, m - 2, 1⟩ := by
    rcases htag with rfl | rfl <;> simp [LargeEvenInLambda2] <;> omega
  have hΛB : LargeEvenInLambda2 ⟨.B, (F.zeroSet c).card, 1⟩ := by
    simp [LargeEvenInLambda2]; omega
  exact (hdRo7CKCoordAux_rank_eq_of_ggLabelIso htag (Or.inl rfl)
    (hRig _ _ _ hΛ hΛB hlabel hB)).symm

theorem hdRo7CKCoordAux_supp_frame_core (hRig : GGLabelRigidInput)
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L] [Module.Finite (GaloisField 2 1) L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (hdim : Module.finrank (GaloisField 2 1) L = 2)
    {m : ℕ} (hm : 5 ≤ m) {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (J' : Subgroup (StatedSp m (GaloisField 2 1)))
    (hJ' : CFSG.Assembly.IsComponentOf J'
      (Subgroup.centralizer ({F.tor c} : Set (StatedSp m (GaloisField 2 1)))))
    {tag : LargeEvenLieTag} (htag : tag = .B ∨ tag = .C)
    (hlabel : GGHasLabel ⟨tag, m - 2, 1⟩ (↥J' ⧸ Subgroup.center ↥J')) :
    (F.suppSet c).card = 2 := by
  rcases hdRo7CKCoordAux_split hζ hdim hm F c J' hJ' with hfix | hsup
  · exact hdRo7CKCoordAux_supp_card_eq_two hm F c hdim
      (hdRo7CKCoordAux_fixed_rank hRig hζ hdim hm F c J' hJ' htag hlabel hfix)
  · exact (hdRo7CKCoordAux_supported_false_core hRig hζ hdim hm F c J' hJ' htag hlabel hsup).elim

end CFSG.StandardType.HdRo7C

end

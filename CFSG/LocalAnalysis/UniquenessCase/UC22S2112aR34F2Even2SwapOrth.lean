module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Defs
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step23
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpinBridge
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2SwapRows
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitOrthogonalGeometry
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitOrthogonalAction
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CSpin
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountTwo
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcModel
import CFSG.ClassicalInvolution.Asc77.AscR10E23
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomy
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.LargeExtraspecial.Types
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQO
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFun
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aF
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open QuadraticMap
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.ComponentClassification.AS81.Sec2 (conjSetStab conjPermHom)
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.RouteD
open CFSG.HardMathSupport.Meierfrankenfeld.LieOdd (eq_three_or_five_le_of_odd_prime_pow)

theorem uc22s2112r34_exists_spin_swap_toFrame {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (h2 : (2 : K) ≠ 0) {m : ℕ} (F₀ : HypFrame Q m)
    {i j : Fin m} (hij : i ≠ j) {k : Fin m} (hik : i ≠ k) (hjk : j ≠ k) (s t : Bool) :
    ∃ x : spinGroup Q,
      (F₀.toFrame hij s t).La.range.map (MulAut.conj (spinAction Q x)).toMonoidHom =
        (F₀.toFrame hij s t).swap.La.range ∧
      (F₀.toFrame hij s t).swap.La.range.map (MulAut.conj (spinAction Q x)).toMonoidHom =
        (F₀.toFrame hij s t).La.range := by
  let : Invertible (2 : K) := invertibleOfNonzero h2
  let a : V := F₀.vec j t - F₀.vec j (!t)
  let b : V := F₀.vec k true - F₀.vec k false
  have hQa : Q a = -1 := by
    dsimp only [a]
    have h : Q (F₀.vec j t - F₀.vec j (!t)) =
        Q (F₀.vec j t) + Q (F₀.vec j (!t)) - polar Q (F₀.vec j t) (F₀.vec j (!t)) := by
      rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg Q,
        QuadraticMap.polar_neg_right]
      ring
    rw [h]
    simp
  have hQb : Q b = -1 := by
    dsimp only [b]
    have h : Q (F₀.vec k true - F₀.vec k false) =
        Q (F₀.vec k true) + Q (F₀.vec k false) -
          polar Q (F₀.vec k true) (F₀.vec k false) := by
      rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg Q,
        QuadraticMap.polar_neg_right]
      ring
    rw [h, F₀.map_vec k true, F₀.map_vec k false, F₀.polar_vec_vec k k true false]
    norm_num
  have hQa_ne : Q a ≠ 0 := by rw [hQa]; norm_num
  have hab : Q a * Q b = 1 := by rw [hQa, hQb]; norm_num
  have hab0 : polar Q a b = 0 := by
    dsimp only [a, b]
    simp [QuadraticMap.polar_sub_left, QuadraticMap.polar_sub_right,
      F₀.polar_vec_of_ne hjk]
  have hb_e1 : CFSG.ClassicalGroups.Orthogonal.reflect Q b (F₀.vec i s) = F₀.vec i s := by
    apply CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
    dsimp only [b]
    simp [QuadraticMap.polar_sub_left, F₀.polar_vec_of_ne (Ne.symm hik)]
  have hb_f1 : CFSG.ClassicalGroups.Orthogonal.reflect Q b (F₀.vec i (!s)) = F₀.vec i (!s) := by
    apply CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
    dsimp only [b]
    simp [QuadraticMap.polar_sub_left, F₀.polar_vec_of_ne (Ne.symm hik)]
  have hb_e2 : CFSG.ClassicalGroups.Orthogonal.reflect Q b (F₀.vec j t) = F₀.vec j t := by
    apply CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
    dsimp only [b]
    simp [QuadraticMap.polar_sub_left, F₀.polar_vec_of_ne hjk.symm]
  have hb_f2 : CFSG.ClassicalGroups.Orthogonal.reflect Q b (F₀.vec j (!t)) = F₀.vec j (!t) := by
    apply CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
    dsimp only [b]
    simp [QuadraticMap.polar_sub_left, F₀.polar_vec_of_ne hjk.symm]
  have ha_e1 : CFSG.ClassicalGroups.Orthogonal.reflect Q a (F₀.vec i s) = F₀.vec i s := by
    apply CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
    dsimp only [a]
    simp [QuadraticMap.polar_sub_left, F₀.polar_vec_of_ne hij.symm]
  have ha_f1 : CFSG.ClassicalGroups.Orthogonal.reflect Q a (F₀.vec i (!s)) = F₀.vec i (!s) := by
    apply CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
    dsimp only [a]
    simp [QuadraticMap.polar_sub_left, F₀.polar_vec_of_ne hij.symm]
  have hpe : polar Q a (F₀.vec j t) = -1 := by
    dsimp only [a]
    rw [QuadraticMap.polar_sub_left, F₀.polar_vec_self, F₀.polar_not_vec]
    norm_num
  have hpf : polar Q a (F₀.vec j (!t)) = 1 := by
    dsimp only [a]
    rw [QuadraticMap.polar_sub_left, F₀.polar_vec_not, F₀.polar_vec_self]
    norm_num
  have ha_e2 : CFSG.ClassicalGroups.Orthogonal.reflect Q a (F₀.vec j t) = F₀.vec j (!t) := by
    rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hQa_ne, hpe, hQa]
    rw [show ((-1 : K) / (-1)) = 1 by rw [neg_div_neg_eq, div_one], one_smul]
    dsimp only [a]
    abel
  have ha_f2 : CFSG.ClassicalGroups.Orthogonal.reflect Q a (F₀.vec j (!t)) = F₀.vec j t := by
    rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hQa_ne, hpf, hQa]
    rw [show ((1 : K) / (-1)) = -1 by rw [div_neg, div_one], neg_one_smul]
    dsimp only [a]
    abel
  let x : spinGroup Q := CFSG.ComponentClassification.GSThmB.Cent516.pairElt a b hab
  let g : V ≃ₗ[K] V := spinAction Q x
  have hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun z =>
      CFSG.LieType.Universal.Spin.map_spinAction Q x z
  have hge1 : g (F₀.vec i s) = F₀.vec i s := by
    dsimp only [g, x]
    rw [CFSG.ComponentClassification.GSThmB.Cent516.spinAction_pairElt hab,
      LinearEquiv.mul_apply, hb_e1, ha_e1]
  have hgf1 : g (F₀.vec i (!s)) = F₀.vec i (!s) := by
    dsimp only [g, x]
    rw [CFSG.ComponentClassification.GSThmB.Cent516.spinAction_pairElt hab,
      LinearEquiv.mul_apply, hb_f1, ha_f1]
  have hge2 : g (F₀.vec j t) = F₀.vec j (!t) := by
    dsimp only [g, x]
    rw [CFSG.ComponentClassification.GSThmB.Cent516.spinAction_pairElt hab,
      LinearEquiv.mul_apply, hb_e2, ha_e2]
  have hgf2 : g (F₀.vec j (!t)) = F₀.vec j t := by
    dsimp only [g, x]
    rw [CFSG.ComponentClassification.GSThmB.Cent516.spinAction_pairElt hab,
      LinearEquiv.mul_apply, hb_f2, ha_f2]
  have hA : (F₀.toFrame hij s t).map hg = (F₀.toFrame hij s t).swap :=
    CFSG.ClassicalInvolution.ModelFacts.Frame.ext_vec hge1 hgf1 hge2 hgf2
  have hA' : (F₀.toFrame hij s t).swap.map hg = F₀.toFrame hij s t :=
    CFSG.ClassicalInvolution.ModelFacts.Frame.ext_vec hge1 hgf1 hgf2 hge2
  have map_group : ∀ B : CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame Q,
      B.La.range.map (MulAut.conj g).toMonoidHom = (B.map hg).La.range := by
    intro B
    ext z
    simp only [Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨_, ⟨M, rfl⟩, rfl⟩
      exact ⟨M, B.map_La hg M⟩
    · rintro ⟨M, rfl⟩
      exact ⟨B.La M, ⟨M, rfl⟩, (B.map_La hg M).symm⟩
  refine ⟨x, ?_, ?_⟩
  · rw [map_group (F₀.toFrame hij s t), hA]
  · rw [map_group (F₀.toFrame hij s t).swap, hA']


private theorem uc22s2112r34_swaporth_ne_bot_of_frame
    {X V F : Type} [Group X] [Finite X] [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {t : StatedLieTag} {n p e : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (π : (modelUniv t n p e hp.out).K →* (V ≃ₗ[F] V))
    (hπker : π.ker ≤ center (modelUniv t n p e hp.out).K)
    (A : Fin 1 → CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame Q)
    (ho : ∀ i j : Fin 1, i ≠ j → SpanOrth (A i) (A j))
    (R : Fin 1 × Bool → Subgroup (modelUniv t n p e hp.out).K)
    (hR : ∀ k, R k ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D ∧
      (R k).map π = if k.2 then (A k.1).swap.La.range else (A k.1).La.range)
    (φ : (modelUniv t n p e hp.out).K →* X)
    (hkerφ : φ.ker ≤ center (modelUniv t n p e hp.out).K) (P : Sylow 2 X)
    (hc : FunSet (fundPred (p ^ e)) X (P : Subgroup X) =
      Set.range (fun k => (R k).map φ))
    (x : (modelUniv t n p e hp.out).K)
    (hx : (A 0).La.range.map (MulAut.conj (π x)).toMonoidHom = (A 0).swap.La.range)
    (hx' : (A 0).swap.La.range.map (MulAut.conj (π x)).toMonoidHom = (A 0).La.range) :
    (conjPermHom (le_refl (conjSetStab (FunSet (fundPred (p ^ e)) X
      (P : Subgroup X))))).range ≠ ⊥ := by
  classical
  let L : Fin 1 × Bool → Subgroup X := fun k => (R k).map φ
  have hL : Function.Injective L :=
    injective_map_paired_model_family hp2 hfund hadm π hπker A ho R hR φ hkerφ
  have hR0F : (R (0, false)).map π = (A 0).La.range := by
    simpa using (hR (0, false)).2
  have hR0T : (R (0, true)).map π = (A 0).swap.La.range := by
    simpa using (hR (0, true)).2
  have hconjF : (R (0, false)).map (MulAut.conj x).toMonoidHom = R (0, true) := by
    refine eq_modelFund_of_map_eq hp2 hfund hadm π hπker
      (conjSub_mem_fundamentalSubgroups (hR (0, false)).1 x) (hR (0, true)).1 ?_
    rw [CFSG.ClassicalInvolution.ModelFacts.map_conj_map, hR0F, hx, hR0T]
  have hconjT : (R (0, true)).map (MulAut.conj x).toMonoidHom = R (0, false) := by
    refine eq_modelFund_of_map_eq hp2 hfund hadm π hπker
      (conjSub_mem_fundamentalSubgroups (hR (0, true)).1 x) (hR (0, false)).1 ?_
    rw [CFSG.ClassicalInvolution.ModelFacts.map_conj_map, hR0T, hx', hR0F]
  have hLgF : (L (0, false)).map (MulAut.conj (φ x)).toMonoidHom = L (0, true) := by
    dsimp only [L]
    rw [← CFSG.ClassicalInvolution.ModelFacts.map_conj_map (θ := φ) (x := x), hconjF]
  have hLgT : (L (0, true)).map (MulAut.conj (φ x)).toMonoidHom = L (0, false) := by
    dsimp only [L]
    rw [← CFSG.ClassicalInvolution.ModelFacts.map_conj_map (θ := φ) (x := x), hconjT]
  have hstab : φ x ∈ conjSetStab (Set.range L) := by
    apply mem_conjSetStab_of_paired_conjugation L (Equiv.refl (Fin 1)) (φ x)
    intro i
    rw [show i = 0 from Subsingleton.elim i 0]
    rw [hLgF, hLgT]
    exact Set.pair_comm _ _
  rw [hc]
  intro hbot
  let N := conjSetStab (Set.range (fun k => (R k).map φ))
  have hρg : conjPermHom (le_refl N) ⟨φ x, hstab⟩ = 1 := by
    have hmem : conjPermHom (le_refl N) ⟨φ x, hstab⟩ ∈
        (conjPermHom (le_refl N)).range := ⟨⟨φ x, hstab⟩, rfl⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hLne : L (0, false) ≠ L (0, true) := by
    intro h
    exact Bool.false_ne_true (congrArg (fun k : Fin 1 × Bool => k.2) (hL h))
  have hval : ((conjPermHom (le_refl N) ⟨φ x, hstab⟩
      ⟨L (0, false), ⟨(0, false), rfl⟩⟩ : ↥(Set.range L)) : Subgroup X) = L (0, true) := by
    rw [CFSG.ComponentClassification.AS81.Sec2.conjPermHom_apply]
    simp only [CFSG.ComponentClassification.AschbacherTightEmbedding.rightConjugate, inv_inv]
    exact hLgF
  have hval2 : ((conjPermHom (le_refl N) ⟨φ x, hstab⟩
      ⟨L (0, false), ⟨(0, false), rfl⟩⟩ : ↥(Set.range L)) : Subgroup X) = L (0, false) := by
    rw [hρg]
    rfl
  exact hLne (hval2.symm.trans hval)

private theorem uc22s2112r34_conjPermHom_range_ne_bot_orth_aux {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {t : StatedLieTag} {n p f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hX : LieModel X t n p f)
    (hrow : (t = .POmegaOdd ∧ n = 3) ∨ (t = .POmegaMinus ∧ n = 4)) (P : Sylow 2 X) :
    (conjPermHom (le_refl (conjSetStab (FunSet (fundPred (p ^ f)) X (P : Subgroup X))))).range ≠
      ⊥ := by
  rcases hrow with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    let F := GaloisField p f
    let Q := quadOdd 3 F
    have h2 : (2 : F) ≠ 0 :=
      CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
    obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
      .POmegaOdd 3 p f Fact.out hp2 (by trivial) hadm X hX
    let A := oddOrthogonalPairFrame F 3
    obtain ⟨R, c₀, hR, hc⟩ :=
      exists_full_paired_frame_funSet_pOmegaOdd hp2 hadm hX ψ hψ hker P
    let φ := (MulAut.conj c₀).toMonoidHom.comp ψ
    have hkerφ : φ.ker ≤ center (modelUniv .POmegaOdd 3 p f Fact.out).K := by
      intro y hy
      apply hker
      rw [MonoidHom.mem_ker] at hy ⊢
      exact (MulAut.conj c₀).injective (by simpa [φ] using hy)
    obtain ⟨x, hx₁, hx₂⟩ := uc22s2112r34_exists_spin_swap_toFrame h2
      (oddFrame 3 F).toHypFrame (i := 0) (j := 1) (by decide) (k := 2)
      (by decide) (by decide) true false
    refine uc22s2112r34_swaporth_ne_bot_of_frame (t := .POmegaOdd) (n := 3) (p := p) (e := f)
      hp2 (show IsFundTag .POmegaOdd from trivial) hadm
      (spinAction Q) (ker_spinAction_le_center Q) A ?_ R hR φ hkerφ P hc x ?_ ?_
    · intro i j hij
      exact (hij (Subsingleton.elim i j)).elim
    · dsimp only [A, Q, F, oddOrthogonalPairFrame]
      exact hx₁
    · dsimp only [A, Q, F, oddOrthogonalPairFrame]
      exact hx₂
  ·
    let F := GaloisField p f
    let b := (CFSG.LieType.Universal.minusCoeffs p f).1
    let ccoef := (CFSG.LieType.Universal.minusCoeffs p f).2
    let Q := quadMinus 4 F b ccoef
    have h2 : (2 : F) ≠ 0 :=
      CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
    have hodd : Odd (Nat.card F) :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField hp2 hadm.2.1
    obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
      .POmegaMinus 4 p f Fact.out hp2 (by trivial) hadm X hX
    let π : (modelUniv .POmegaMinus 4 p f Fact.out).K →* (_ ≃ₗ[F] _) := spinAction Q
    have hπker : π.ker ≤ center (modelUniv .POmegaMinus 4 p f Fact.out).K :=
      ker_spinAction_le_center Q
    let A := minusOrthogonalPairFrame F 4 b ccoef
    have hcorr :
        (∀ R ∈ fundamentalSubgroups .POmegaMinus
            (modelUniv .POmegaMinus 4 p f Fact.out).D,
          R.map π ∈ Gaps.fundSet Q) ∧
        ∀ L ∈ Gaps.fundSet Q,
          ∃ R ∈ fundamentalSubgroups .POmegaMinus
              (modelUniv .POmegaMinus 4 p f Fact.out).D,
            R.map π = L := by
      by_cases hq : 5 ≤ p ^ f
      · exact Exotic.fundCorr_minus hp2 hq hadm
      · have hq3 := (eq_three_or_five_le_of_odd_prime_pow Fact.out hp2 hadm.2.1).resolve_right hq
        exact Exotic.fundCorr_minus3 hq3 hadm
    have hπmap : ∀ R ∈ fundamentalSubgroups .POmegaMinus
        (modelUniv .POmegaMinus 4 p f Fact.out).D,
        ∃ H : CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame Q,
          R.map π = H.La.range := by
      intro R hR
      obtain ⟨i, H, hH, -⟩ := hcorr.1 R hR
      exact ⟨H, hH⟩
    have hex : ∀ k : Fin ((4 - 1) / 2) × Bool,
        ∃ R ∈ fundamentalSubgroups .POmegaMinus
            (modelUniv .POmegaMinus 4 p f Fact.out).D,
          R.map π = if k.2 then (A k.1).swap.La.range else (A k.1).La.range := by
      intro k
      apply hcorr.2
      cases k.2
      · exact ⟨_, CFSG.ClassicalInvolution.Models.OrthogonalPairs.IsFundamental.of_frame _⟩
      · exact ⟨_, CFSG.ClassicalInvolution.Models.OrthogonalPairs.IsFundamental.of_frame_swap _⟩
    choose R hR hmap using hex
    obtain ⟨c₀, hc⟩ := exists_full_paired_model_frame_funSet hp2 (by trivial) hadm hX
      (by simp) (by omega : 0 < (4 - 1) / 2) π hπker hπmap A
      (fun i j hij => spanOrth_minusOrthogonalPairFrame F 4 b ccoef hij)
      (fun H h => not_spanOrth_all_minusOrthogonalPairFrame F 4 (by omega)
        (CFSG.LieType.Universal.minusCoeffs_irr p f) hodd H h)
      R (fun k => ⟨hR k, hmap k⟩) h2 ψ hψ hker P
    let φ := (MulAut.conj c₀).toMonoidHom.comp ψ
    have hkerφ : φ.ker ≤ center (modelUniv .POmegaMinus 4 p f Fact.out).K := by
      intro y hy
      apply hker
      rw [MonoidHom.mem_ker] at hy ⊢
      exact (MulAut.conj c₀).injective (by simpa [φ] using hy)
    obtain ⟨x, hx₁, hx₂⟩ := uc22s2112r34_exists_spin_swap_toFrame h2
      (CFSG.LieType.Universal.Spin.Twisted.minusFrame 4 b ccoef).toHypFrame
      (i := 0) (j := 1) (by decide) (k := 2) (by decide) (by decide) true false
    refine uc22s2112r34_swaporth_ne_bot_of_frame (t := .POmegaMinus) (n := 4) (p := p) (e := f)
      hp2 (show IsFundTag .POmegaMinus from trivial) hadm π hπker A ?_
      R (fun k => ⟨hR k, hmap k⟩) φ hkerφ P hc x ?_ ?_
    · intro i j hij
      exact (hij (Subsingleton.elim i j)).elim
    · dsimp only [A, π, Q, F, minusOrthogonalPairFrame]
      exact hx₁
    · dsimp only [A, π, Q, F, minusOrthogonalPairFrame]
      exact hx₂

theorem uc22s2112r34_conjPermHom_range_ne_bot_orth {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hX : LieModel X t n p f)
    (hrow : (t = .POmegaOdd ∧ n = 3) ∨ (t = .POmegaMinus ∧ n = 4)) (P : Sylow 2 X) :
    (conjPermHom (le_refl (conjSetStab (FunSet (fundPred (p ^ f)) X (P : Subgroup X))))).range ≠
      ⊥ := by
  exact uc22s2112r34_conjPermHom_range_ne_bot_orth_aux (hp := ⟨hp⟩) hp2 hadm hX hrow P

theorem uc22s2112r34_exists_swap_of_lieModel_orth {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hX : LieModel X t n p f)
    (hrow : (t = .POmegaOdd ∧ n = 3) ∨ (t = .POmegaMinus ∧ n = 4))
    (P : Sylow 2 X) {K₁ K₂ : Subgroup X}
    (h₁ : K₁ ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X))
    (h₂ : K₂ ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X)) (hne : K₁ ≠ K₂) :
    ∃ w ∈ (P : Subgroup X), K₁.map (MulAut.conj w).toMonoidHom = K₂ := by
  have htwo : FunTwoType t n := by
    rcases hrow with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [FunTwoType]
  exact uc22s2112r34_exists_swap_of_ne_bot P
    (uc22s2112r34_conjPermHom_range_ne_bot_orth hp hp2 hadm hX hrow P)
    (ncard_funSet_eq_two_of_funTwoType hp hp2 hadm hX htwo P) h₁ h₂ hne

end CFSG.LocalAnalysis.UniquenessCase.UC22

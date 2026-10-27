module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.CensusDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.BlocksSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Parabolic
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpCover
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.SymplecticTwo
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTwelveSolvSigmaBlockRest
import CFSG.Quasithin.Vol2.Ch7Prop711Grp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
open CFSG.AGLEmbedding.LeviBlock
open CFSG.HardMathSupport.RichardWeiss.Proving.PLType
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem false_of_subsingleton_isQuasisimple {X : Type} [Group X]
    (hq : CFSG.Open.IsQuasisimple X) (h : Subsingleton X) : False := by
  have := h
  have hsub : Subsingleton (X ⧸ Subgroup.center X) :=
    (QuotientGroup.mk'_surjective (Subgroup.center X)).subsingleton
  exact (not_subsingleton_iff_nontrivial.mpr hq.2.toNontrivial) hsub

omit [Finite K] [CharP K 2] in
private theorem subsingleton_statedSp_zero : Subsingleton (StatedSp 0 K) :=
  ⟨fun _ _ => Subtype.ext (Subsingleton.elim (α := GL (Fin 0 ⊕ Fin 0) K) _ _)⟩

private noncomputable def resEquiv {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3) (t : ℕ)
    {j : Fin 4} (hj : (j : ℕ) = 0) :
    ↥(spFlagLeviCoordBlock (K := K) hI t j) ≃* StatedSp (3 - t) K :=
  (MulEquiv.subgroupCongr (spFlagLeviCoordBlock_of_eq_zero hI t hj)).trans
    (MonoidHom.ofInjective (f := spFlagResEmb (r := 3) (K := K) t)
      (spFlagResEmb_injective t)).symm

private noncomputable def resPermThree {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3)
    (hK : Nat.card K = 2) {t : ℕ} (ht : t = 2) {j : Fin 4} (hj : (j : ℕ) = 0) :
    ↥(spFlagLeviCoordBlock (K := K) hI t j) ≃* Equiv.Perm (Fin 3) := by
  subst ht
  have hj' : j = 0 := Fin.ext hj
  subst hj'
  exact (resEquiv (K := K) hI 2 (j := 0) rfl).trans
    ((CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.statedSpCongr
        (CFSG.LargeExtraspecial.A2Mod.ringEquivZModTwo K hK) 1).trans
      nonempty_statedSp_one_mulEquiv_perm_three.some)

private noncomputable def resPermSix {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3)
    (hK : Nat.card K = 2) {t : ℕ} (ht : t = 1) {j : Fin 4} (hj : (j : ℕ) = 0) :
    ↥(spFlagLeviCoordBlock (K := K) hI t j) ≃* Equiv.Perm (Fin 6) := by
  subst ht
  have hj' : j = 0 := Fin.ext hj
  subst hj'
  let : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  exact (resEquiv (K := K) hI 1 (j := 0) rfl).trans
    (CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm
      (k := K) hF).some

private noncomputable def cutEquiv {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3)
    (hK : Nat.card K = 2) {t : ℕ} {j : Fin 4} (hj0 : (j : ℕ) ≠ 0)
    (hj : (j : ℕ) ∈ I) :
    ↥(spFlagLeviCoordBlock (K := K) hI t j) ≃*
      Matrix.SpecialLinearGroup (Fin ((j : ℕ) - spFlagPrev I (j : ℕ))) (ZMod 2) := by
  let m := (j : ℕ) - spFlagPrev I (j : ℕ)
  let hb : (j : ℕ) ≤ 3 := hI j hj
  let e1 : ↥(spFlagCutEmb (K := K) (spFlagPrev I (j : ℕ)) (j : ℕ) hb).range ≃*
      GL (Fin m) K :=
    (MonoidHom.ofInjective
      (f := spFlagCutEmb (K := K) (spFlagPrev I (j : ℕ)) (j : ℕ) hb)
      (spFlagCutEmb_injective _ _ hb)).symm
  let e2 : GL (Fin m) K ≃* GL (Fin m) (ZMod 2) :=
    CFSG.GH74.Exceptional.glEquivZModTwoOfCardTwo hK m
  let e3 : GL (Fin m) (ZMod 2) ≃* Matrix.SpecialLinearGroup (Fin m) (ZMod 2) :=
    (CFSG.Quasithin.FLc.slEquivGLt m).symm
  exact (MulEquiv.subgroupCongr (spFlagLeviCoordBlock_of_mem hI t hj0 hj)).trans
    (e1.trans (e2.trans e3))

omit [CharP K 2] in
private theorem not_isQuasisimple_res {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3)
    (hI1 : ∀ i ∈ I, 1 ≤ i) {t : ℕ} (htI : t ∈ I) (hK : Nat.card K = 2) :
    ¬ CFSG.Open.IsQuasisimple
      ↥(spFlagLeviCoordBlock (K := K) hI t (0 : Fin 4)) := by
  intro hq
  have ht1 : 1 ≤ t := hI1 t htI
  have ht3 : t ≤ 3 := hI t htI
  interval_cases t
  · have e := resEquiv (K := K) hI 1 (j := 0) rfl
    have hq2 : CFSG.Open.IsQuasisimple (StatedSp 2 K) := hq.of_mulEquiv e.symm
    exact CFSG.Quasithin.H13.Prop711.not_isPerfect_statedSp_two hK ⟨hq2.1⟩
  · have e := resPermThree (K := K) hI hK (t := 2) rfl (j := 0) rfl
    have hq3 : CFSG.Open.IsQuasisimple (Equiv.Perm (Fin 3)) := hq.of_mulEquiv e.symm
    exact CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TwelveSigma.not_isPerfect_perm_fin_three
      ⟨hq3.1⟩
  · have hsub : Subsingleton
        ↥(spFlagLeviCoordBlock (K := K) hI 3 (0 : Fin 4)) := by
      rw [spFlagLeviCoordBlock_of_eq_zero hI 3 rfl]
      have : Subsingleton (StatedSp (3 - 3) K) := subsingleton_statedSp_zero
      exact (MonoidHom.ofInjective (f := spFlagResEmb (r := 3) (K := K) 3)
        (spFlagResEmb_injective 3)).symm.injective.subsingleton
    exact false_of_subsingleton_isQuasisimple hq hsub

omit [CharP K 2] in
private theorem block_eq_bot_or_isLeviBlock {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3)
    (hI1 : ∀ i ∈ I, 1 ≤ i) {t : ℕ} (htI : t ∈ I) (hK : Nat.card K = 2) (j : Fin 4) :
    spFlagLeviCoordBlock (K := K) hI t j = ⊥ ∨
      IsLeviBlock ↥(spFlagLeviCoordBlock (K := K) hI t j) := by
  by_cases hj0 : (j : ℕ) = 0
  · by_cases ht1 : t = 1
    · right
      have e := resPermSix (K := K) hI hK ht1 (j := j) hj0
      exact IsLeviBlock.of_mulEquiv e.symm (Or.inr (Or.inl ⟨MulEquiv.refl _⟩))
    · by_cases ht2 : t = 2
      · right
        have e := resPermThree (K := K) hI hK ht2 (j := j) hj0
        exact IsLeviBlock.of_mulEquiv e.symm (Or.inl ⟨MulEquiv.refl _⟩)
      · left
        have ht3 : t = 3 := by
          have h1 := hI1 t htI
          have h3 := hI t htI
          omega
        subst ht3
        rw [spFlagLeviCoordBlock_of_eq_zero hI 3 hj0]
        have : Subsingleton (StatedSp (3 - 3) K) := subsingleton_statedSp_zero
        have : Subsingleton ↥(spFlagResEmb (r := 3) (K := K) 3).range :=
          (MonoidHom.ofInjective (f := spFlagResEmb (r := 3) (K := K) 3)
            (spFlagResEmb_injective 3)).symm.injective.subsingleton
        exact Subgroup.eq_bot_of_subsingleton _
  · by_cases hj : (j : ℕ) ∈ I
    · let m := (j : ℕ) - spFlagPrev I (j : ℕ)
      let eB : ↥(spFlagLeviCoordBlock (K := K) hI t j) ≃*
          ↥(Matrix.SpecialLinearGroup.toGL :
            Matrix.SpecialLinearGroup (Fin m) (ZMod 2) →* GL (Fin m) (ZMod 2)).range :=
        (cutEquiv (K := K) hI hK hj0 hj).trans
          (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective)
      rcases range_toGL_eq_bot_or_isLeviBlock (K := ZMod 2) m with hbot | hlev
      · left
        have : Subsingleton ↥(Matrix.SpecialLinearGroup.toGL :
            Matrix.SpecialLinearGroup (Fin m) (ZMod 2) →* GL (Fin m) (ZMod 2)).range := by
          rw [hbot]
          infer_instance
        have : Subsingleton ↥(spFlagLeviCoordBlock (K := K) hI t j) :=
          eB.injective.subsingleton
        exact Subgroup.eq_bot_of_subsingleton _
      · right
        exact IsLeviBlock.of_mulEquiv eB.symm hlev
    · left
      exact spFlagLeviCoordBlock_of_not_mem hI t hj0 hj

omit [CharP K 2] in
private theorem block_not_isL2 {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3)
    (hI1 : ∀ i ∈ I, 1 ≤ i) {t : ℕ} (htI : t ∈ I) (hK : Nat.card K = 2) (j : Fin 4)
    (hB : spFlagLeviCoordBlock (K := K) hI t j ≠ ⊥)
    (hq : CFSG.Open.IsQuasisimple ↥(spFlagLeviCoordBlock (K := K) hI t j))
    {n : ℕ} (hn : 3 ≤ n) :
    ¬ IsL2 (↥(spFlagLeviCoordBlock (K := K) hI t j) ⧸
      center ↥(spFlagLeviCoordBlock (K := K) hI t j)) n := by
  by_cases hj0 : (j : ℕ) = 0
  · have hj' : j = 0 := Fin.ext hj0
    subst hj'
    exact absurd hq (not_isQuasisimple_res (K := K) hI hI1 htI hK)
  · by_cases hj : (j : ℕ) ∈ I
    · let m := (j : ℕ) - spFlagPrev I (j : ℕ)
      let eB : ↥(spFlagLeviCoordBlock (K := K) hI t j) ≃*
          ↥(Matrix.SpecialLinearGroup.toGL :
            Matrix.SpecialLinearGroup (Fin m) (ZMod 2) →* GL (Fin m) (ZMod 2)).range :=
        (cutEquiv (K := K) hI hK hj0 hj).trans
          (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective)
      have hqR : CFSG.Open.IsQuasisimple ↥(Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin m) (ZMod 2) →* GL (Fin m) (ZMod 2)).range :=
        hq.of_mulEquiv eB.symm
      intro hL2
      have hnot := not_isL2_range_toGL (K := ZMod 2) (by simp) m hqR hn
      let eQ := QuotientGroup.congr
        (Subgroup.center ↥(spFlagLeviCoordBlock (K := K) hI t j))
        (Subgroup.center ↥(Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin m) (ZMod 2) →* GL (Fin m) (ZMod 2)).range)
        eB (CFSG.AGLEmbedding.LeviBlock.map_center_mulEquiv eB)
      exact hnot (CFSG.Blueprint.LieModel.of_mulEquiv eQ hL2)
    · exact absurd (spFlagLeviCoordBlock_of_not_mem hI t hj0 hj) hB

private noncomputable def flagBlock {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3) (t : ℕ)
    (j : Fin 4) : Subgroup (StatedSp 3 K) :=
  spFlagLeviCoordBlock (K := K) hI t j

private noncomputable def flagLevi {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3) (t : ℕ)
    (j : Fin 4) : Subgroup ↥(flagBlock (K := K) hI t j) := by
  classical
  exact if flagBlock (K := K) hI t j = ⊥ then ⊥ else ⊤

omit [Finite K] [CharP K 2] in
private theorem flagLevi_eq_top {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3) (t : ℕ) :
    ∀ j, flagLevi (K := K) hI t j = ⊤ := by
  intro j
  by_cases h : flagBlock (K := K) hI t j = ⊥
  · have hsub : Subsingleton ↥(flagBlock (K := K) hI t j) := by
      rw [h]
      infer_instance
    have hbottop : (⊥ : Subgroup ↥(flagBlock (K := K) hI t j)) = ⊤ :=
      (Subgroup.eq_bot_of_subsingleton (⊤ : Subgroup _)).symm
    rw [flagLevi, if_pos h]
    exact hbottop
  · rw [flagLevi, if_neg h]

omit [CharP K 2] in
private theorem flagLevi_eq_bot_or_isLeviBlock {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3)
    (hI1 : ∀ i ∈ I, 1 ≤ i) {t : ℕ} (htI : t ∈ I) (hK : Nat.card K = 2) :
    ∀ j, flagLevi (K := K) hI t j = ⊥ ∨
      IsLeviBlock ↥(flagLevi (K := K) hI t j) := by
  classical
  intro j
  rcases block_eq_bot_or_isLeviBlock (K := K) hI hI1 htI hK j with hbot | hlev
  · left
    rw [flagLevi]
    change (if spFlagLeviCoordBlock (K := K) hI t j = ⊥ then ⊥ else ⊤) = ⊥
    rw [if_pos hbot]
  · right
    rw [flagLevi_eq_top (K := K) hI t j]
    exact IsLeviBlock.of_mulEquiv Subgroup.topEquiv.symm hlev

omit [CharP K 2] in
private theorem censusAlt_flagLevi {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3)
    (hI1 : ∀ i ∈ I, 1 ≤ i) {t : ℕ} (htI : t ∈ I) (hK : Nat.card K = 2) :
    CensusAlt (flagLevi (K := K) hI t) := by
  right
  intro j hq n hn hL2
  let B := flagBlock (K := K) hI t j
  let eSub : ↥(flagLevi (K := K) hI t j) ≃* ↥(⊤ : Subgroup B) :=
    MulEquiv.subgroupCongr (flagLevi_eq_top (K := K) hI t j)
  let eTop := Subgroup.topEquiv (G := B)
  let eQ1 : (↥(flagLevi (K := K) hI t j) ⧸ center ↥(flagLevi (K := K) hI t j)) ≃*
      (↥(⊤ : Subgroup B) ⧸ center ↥(⊤ : Subgroup B)) :=
    QuotientGroup.congr _ _ eSub (CFSG.AGLEmbedding.LeviBlock.map_center_mulEquiv eSub)
  let eQ2 : (↥(⊤ : Subgroup B) ⧸ center ↥(⊤ : Subgroup B)) ≃*
      (B ⧸ center B) :=
    QuotientGroup.congr _ _ eTop (CFSG.AGLEmbedding.LeviBlock.map_center_mulEquiv eTop)
  have hL2' : IsL2 (B ⧸ center B) n :=
    CFSG.Blueprint.LieModel.of_mulEquiv (eQ1.trans eQ2) hL2
  have hqTop : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup B) := hq.of_mulEquiv eSub.symm
  have hqB : CFSG.Open.IsQuasisimple B := hqTop.of_mulEquiv eTop.symm
  have hBne : B ≠ ⊥ := by
    intro h
    have hsub : Subsingleton B := by
      rw [h]
      infer_instance
    exact false_of_subsingleton_isQuasisimple hqB hsub
  exact block_not_isL2 (K := K) hI hI1 htI hK j hBne hqB hn hL2'

omit [CharP K 2] in
private theorem two_le_gap_of_coordBlock_ne_bot {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3)
    (hK : Nat.card K = 2) {t : ℕ} {j : Fin 4} (hj0 : (j : ℕ) ≠ 0) (hj : (j : ℕ) ∈ I)
    (hne : spFlagLeviCoordBlock (K := K) hI t j ≠ ⊥) :
    2 ≤ (j : ℕ) - spFlagPrev I (j : ℕ) := by
  by_contra hgap
  have hm1 : (j : ℕ) - spFlagPrev I (j : ℕ) ≤ 1 := by omega
  let e : ↥(spFlagLeviCoordBlock (K := K) hI t j) ≃*
      Matrix.SpecialLinearGroup (Fin ((j : ℕ) - spFlagPrev I (j : ℕ))) (ZMod 2) :=
    cutEquiv (K := K) hI hK hj0 hj
  have hbot : (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin ((j : ℕ) - spFlagPrev I (j : ℕ))) (ZMod 2) →*
        GL (Fin ((j : ℕ) - spFlagPrev I (j : ℕ))) (ZMod 2)).range = ⊥ :=
    (range_toGL_eq_bot_iff (K := ZMod 2) _).mpr hm1
  have hsub : Subsingleton ↥(Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin ((j : ℕ) - spFlagPrev I (j : ℕ))) (ZMod 2) →*
        GL (Fin ((j : ℕ) - spFlagPrev I (j : ℕ))) (ZMod 2)).range := by
    rw [hbot]
    infer_instance
  have hsubSL : Subsingleton (Matrix.SpecialLinearGroup
      (Fin ((j : ℕ) - spFlagPrev I (j : ℕ))) (ZMod 2)) :=
    @Equiv.subsingleton _ _ (MonoidHom.ofInjective
      Matrix.SpecialLinearGroup.toGL_injective).toEquiv hsub
  have hsubB : Subsingleton ↥(spFlagLeviCoordBlock (K := K) hI t j) :=
    @Equiv.subsingleton _ _ e.toEquiv hsubSL
  exact hne (@Subgroup.eq_bot_of_subsingleton _ _ _ hsubB)

omit [CharP K 2] in
private theorem coordBlock_eq_of_ne_bot_of_ne_zero {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3)
    (hI1 : ∀ i ∈ I, 1 ≤ i) (hK : Nat.card K = 2) {t : ℕ} {j k : Fin 4}
    (hj0 : (j : ℕ) ≠ 0) (hk0 : (k : ℕ) ≠ 0)
    (hj : spFlagLeviCoordBlock (K := K) hI t j ≠ ⊥)
    (hk : spFlagLeviCoordBlock (K := K) hI t k ≠ ⊥) : j = k := by
  have hjm : (j : ℕ) ∈ I := by
    by_contra h
    exact hj (spFlagLeviCoordBlock_of_not_mem hI t hj0 h)
  have hkm : (k : ℕ) ∈ I := by
    by_contra h
    exact hk (spFlagLeviCoordBlock_of_not_mem hI t hk0 h)
  have hj2 := two_le_gap_of_coordBlock_ne_bot (K := K) hI hK hj0 hjm hj
  have hk2 := two_le_gap_of_coordBlock_ne_bot (K := K) hI hK hk0 hkm hk
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hkp : (j : ℕ) ≤ spFlagPrev I (k : ℕ) :=
      le_spFlagPrev (b := (k : ℕ)) (c := (j : ℕ)) hjm hlt
    have hkgap : (k : ℕ) - spFlagPrev I (k : ℕ) ≤ (k : ℕ) - (j : ℕ) :=
      Nat.sub_le_sub_left hkp _
    have hjgap : (j : ℕ) - spFlagPrev I (j : ℕ) ≤ (j : ℕ) := Nat.sub_le _ _
    have hj1 : 1 ≤ (j : ℕ) := hI1 _ hjm
    have hkr : (k : ℕ) ≤ 3 := hI _ hkm
    omega
  · have hjp : (k : ℕ) ≤ spFlagPrev I (j : ℕ) :=
      le_spFlagPrev (b := (j : ℕ)) (c := (k : ℕ)) hkm hlt
    have hjgap : (j : ℕ) - spFlagPrev I (j : ℕ) ≤ (j : ℕ) - (k : ℕ) :=
      Nat.sub_le_sub_left hjp _
    have hkgap : (k : ℕ) - spFlagPrev I (k : ℕ) ≤ (k : ℕ) := Nat.sub_le _ _
    have hk1 : 1 ≤ (k : ℕ) := hI1 _ hkm
    have hjr : (j : ℕ) ≤ 3 := hI _ hjm
    omega

omit [Finite K] [CharP K 2] in
private theorem flagBlock_ne_bot_of_flagLevi_ne_bot {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3)
    (t : ℕ) {j : Fin 4} (h : flagLevi (K := K) hI t j ≠ ⊥) :
    flagBlock (K := K) hI t j ≠ ⊥ := by
  intro hbot
  have hle : flagLevi (K := K) hI t j = ⊥ := by
    rw [flagLevi, if_pos hbot]
  exact h hle

omit [CharP K 2] in
private theorem card_nontrivial_flagLevi_le_two {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3)
    (hI1 : ∀ i ∈ I, 1 ≤ i) (hK : Nat.card K = 2) {t : ℕ} :
    Nat.card {j : Fin 4 // flagLevi (K := K) hI t j ≠ ⊥} ≤ 2 := by
  let f : {j : Fin 4 // flagLevi (K := K) hI t j ≠ ⊥} → Fin 2 :=
    fun x => if (x.1 : ℕ) = 0 then 0 else 1
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx0 : (x.1 : ℕ) = 0
    · by_cases hy0 : (y.1 : ℕ) = 0
      · exact Subtype.ext (Fin.ext (by rw [hx0, hy0]))
      · have hxval : (f x : ℕ) = 0 := by
          dsimp only [f]
          rw [if_pos hx0]
          rfl
        have hyval : (f y : ℕ) = 1 := by
          dsimp only [f]
          rw [if_neg hy0]
          rfl
        have := congrArg Fin.val hxy
        omega
    · by_cases hy0 : (y.1 : ℕ) = 0
      · have hxval : (f x : ℕ) = 1 := by
          dsimp only [f]
          rw [if_neg hx0]
          rfl
        have hyval : (f y : ℕ) = 0 := by
          dsimp only [f]
          rw [if_pos hy0]
          rfl
        have := congrArg Fin.val hxy
        omega
      · have hxB : flagBlock (K := K) hI t x.1 ≠ ⊥ :=
          flagBlock_ne_bot_of_flagLevi_ne_bot (K := K) hI t x.2
        have hyB : flagBlock (K := K) hI t y.1 ≠ ⊥ :=
          flagBlock_ne_bot_of_flagLevi_ne_bot (K := K) hI t y.2
        exact Subtype.ext
          (coordBlock_eq_of_ne_bot_of_ne_zero (K := K) hI hI1 hK hx0 hy0 hxB hyB)
  exact (Nat.card_le_card_of_injective f hf).trans (by simp)

omit [CharP K 2] in
private theorem three_dvd_card_quotient_center_flagLevi {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3)
    (hI1 : ∀ i ∈ I, 1 ≤ i) {t : ℕ} (htI : t ∈ I) (hK : Nat.card K = 2) (j : Fin 4)
    (hq : CFSG.Open.IsQuasisimple ↥(flagLevi (K := K) hI t j)) :
    3 ∣ Nat.card (↥(flagLevi (K := K) hI t j) ⧸
      center ↥(flagLevi (K := K) hI t j)) := by
  let B := flagBlock (K := K) hI t j
  let eS : ↥(flagLevi (K := K) hI t j) ≃* B :=
    (MulEquiv.subgroupCongr (flagLevi_eq_top (K := K) hI t j)).trans
      (Subgroup.topEquiv (G := B))
  have hqB : CFSG.Open.IsQuasisimple B := hq.of_mulEquiv eS.symm
  have hBne : B ≠ ⊥ := by
    intro hbot
    exact false_of_subsingleton_isQuasisimple hqB (by rw [hbot]; infer_instance)
  have hj0 : (j : ℕ) ≠ 0 := by
    intro hj0
    have hj' : j = 0 := Fin.ext hj0
    subst hj'
    exact not_isQuasisimple_res (K := K) hI hI1 htI hK hqB
  have hj : (j : ℕ) ∈ I := by
    by_contra hj
    exact hBne (spFlagLeviCoordBlock_of_not_mem hI t hj0 hj)
  let m := (j : ℕ) - spFlagPrev I (j : ℕ)
  let eB : ↥(spFlagLeviCoordBlock (K := K) hI t j) ≃*
      ↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) (ZMod 2) →* GL (Fin m) (ZMod 2)).range :=
    (cutEquiv (K := K) hI hK hj0 hj).trans
      (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective)
  have hm : 2 ≤ m := by
    by_contra hm
    have hbot : (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) (ZMod 2) →* GL (Fin m) (ZMod 2)).range = ⊥ :=
      (range_toGL_eq_bot_iff (K := ZMod 2) m).mpr (by omega)
    have hsub : Subsingleton ↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) (ZMod 2) →* GL (Fin m) (ZMod 2)).range := by
      rw [hbot]
      infer_instance
    have hsubB : Subsingleton ↥(spFlagLeviCoordBlock (K := K) hI t j) :=
      @Equiv.subsingleton _ _ eB.toEquiv hsub
    exact hBne (@Subgroup.eq_bot_of_subsingleton _ _ _ hsubB)
  have h3 : 3 ∣ Nat.card (↥(Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin m) (ZMod 2) →* GL (Fin m) (ZMod 2)).range ⧸
      center ↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) (ZMod 2) →* GL (Fin m) (ZMod 2)).range) :=
    three_dvd_card_quotient_center_range_toGL (K := ZMod 2) hm
  let eQ := QuotientGroup.congr
    (Subgroup.center ↥(spFlagLeviCoordBlock (K := K) hI t j))
    (Subgroup.center ↥(Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin m) (ZMod 2) →* GL (Fin m) (ZMod 2)).range)
    eB (CFSG.AGLEmbedding.LeviBlock.map_center_mulEquiv eB)
  have h3B : 3 ∣ Nat.card (↥(spFlagLeviCoordBlock (K := K) hI t j) ⧸
      center ↥(spFlagLeviCoordBlock (K := K) hI t j)) := by
    rw [Nat.card_congr eQ.toEquiv]
    exact h3
  let eQ2 := QuotientGroup.congr
    (Subgroup.center ↥(flagLevi (K := K) hI t j)) (Subgroup.center B) eS
    (CFSG.AGLEmbedding.LeviBlock.map_center_mulEquiv eS)
  rw [Nat.card_congr eQ2.toEquiv]
  exact h3B

omit [CharP K 2] in
private theorem blockFacts_flagLevi {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3)
    (hI1 : ∀ i ∈ I, 1 ≤ i) {t : ℕ} (htI : t ∈ I) (hK : Nat.card K = 2) :
    BlockFacts True False (flagLevi (K := K) hI t) :=
  ⟨fun j hq => three_dvd_card_quotient_center_flagLevi hI hI1 htI hK j hq,
    fun _ _ => trivial, Or.inl (card_nontrivial_flagLevi_le_two hI hI1 hK)⟩

private theorem exists_leviMap_data {S : Type} [Group S] [Finite S] {J : Subgroup S}
    (hK : Nat.card K = 2) (ρ : StatedSp 3 K ≃* ↥(⊤ : Subgroup S))
    (I : Set ℕ) (t : ℕ) (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ 3) (htI : t ∈ I)
    (hmax : ∀ c ∈ I, c ≤ t)
    (hcomap : (J.subgroupOf ⊤).comap ρ.toMonoidHom = flagStabilizer 3 K I) :
    ∃ (G : Fin 4 → Type) (_ : ∀ j, Group (G j)) (_ : ∀ j, Finite (G j))
      (S' : ∀ j, Subgroup (G j)) (β : ↥J →* ∀ j, G j),
      IsPGroup 2 β.ker ∧ Subgroup.pi Set.univ S' = ⊤ ∧ β.range = ⊤ ∧
      (∀ j, S' j = ⊥ ∨ IsLeviBlock ↥(S' j)) ∧ CensusAlt S' ∧
      BlockFacts True False S' := by
  let hI' : ∀ i ∈ I, i ≤ 3 := fun i hi => (hI i hi).2
  let QI := flagStabilizer 3 K I
  have hmapQ : QI.map ρ.toMonoidHom = J.subgroupOf ⊤ := by
    dsimp [QI]
    rw [← hcomap]
    change Subgroup.map ρ.toMonoidHom
      ((J.subgroupOf ⊤).comap ρ.toMonoidHom) = J.subgroupOf ⊤
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr ρ.surjective, top_inf_eq]
  let eJ : ↥QI ≃* ↥J :=
    (MulEquiv.subgroupMap ρ QI).trans
      ((MulEquiv.subgroupCongr hmapQ).trans
        (Subgroup.subgroupOfEquivOfLe (le_top : J ≤ ⊤)))
  obtain ⟨e₀⟩ := nonempty_quotient_pCore_flagStabilizer (K := K) hI htI hmax hK
  let G : Fin 4 → Type := fun j => ↥(flagBlock (K := K) hI' t j)
  let S' : ∀ j, Subgroup (G j) := flagLevi (K := K) hI' t
  have hcore : (CFSG.pCore 2 ↥J).map eJ.symm.toMonoidHom = CFSG.pCore 2 ↥QI :=
    CFSG.pCore_map_iso 2 eJ.symm
  let eQuot : ↥J ⧸ CFSG.pCore 2 ↥J ≃* ∀ j : Fin 4, G j :=
    (QuotientGroup.congr (CFSG.pCore 2 ↥J) (CFSG.pCore 2 ↥QI) eJ.symm hcore).trans e₀
  let β : ↥J →* ∀ j : Fin 4, G j :=
    eQuot.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥J))
  have hβker : β.ker = CFSG.pCore 2 ↥J := by
    dsimp [β]
    rw [MonoidHom.ker_comp_of_injective _ _ eQuot.injective, QuotientGroup.ker_mk']
  have hβrange : β.range = ⊤ :=
    MonoidHom.range_eq_top.mpr
      (eQuot.surjective.comp (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥J)))
  have hpi_top : Subgroup.pi Set.univ S' = ⊤ := by
    rw [show S' = fun _ => ⊤ from funext (flagLevi_eq_top (K := K) hI' t), Subgroup.pi_top]
  have hSblocks :=
    flagLevi_eq_bot_or_isLeviBlock (K := K) hI' (fun i hi => (hI i hi).1) htI hK
  have halt := censusAlt_flagLevi (K := K) hI' (fun i hi => (hI i hi).1) htI hK
  have hbf : BlockFacts True False S' :=
    blockFacts_flagLevi (K := K) hI' (fun i hi => (hI i hi).1) htI hK
  exact ⟨G, fun j => inferInstance, fun j => inferInstance, S', β,
    by rw [hβker]; exact CFSG.pCore_isPGroup, hpi_top, hβrange, hSblocks, halt, hbf⟩

private theorem hasLeviDataX_of_leviMap_data {S : Type} [Group S] [Finite S] {J : Subgroup S}
    (h : ∃ (G : Fin 4 → Type) (_ : ∀ j, Group (G j)) (_ : ∀ j, Finite (G j))
      (S' : ∀ j, Subgroup (G j)) (β : ↥J →* ∀ j, G j),
      IsPGroup 2 β.ker ∧ Subgroup.pi Set.univ S' = ⊤ ∧ β.range = ⊤ ∧
      (∀ j, S' j = ⊥ ∨ IsLeviBlock ↥(S' j)) ∧ CensusAlt S' ∧ BlockFacts True False S') :
    HasLeviDataX True False ↥J := by
  obtain ⟨G, hG, hGF, S', β, hβ, hpi, hβr, hS, halt, hbf⟩ := h
  refine ⟨↥J, inferInstance, inferInstance, MonoidHom.id ↥J, Fin 4, inferInstance,
    G, hG, hGF, S', β, ?_, ?_, ?_, hβ, ?_, ?_, ?_, hS, halt, hbf⟩
  · exact fun x => ⟨x, rfl⟩
  · rw [MonoidHom.ker_id]
    exact bot_le
  · rw [MonoidHom.ker_id, Subgroup.card_bot]
    exact odd_one
  · simp [hpi, hβr]
  · rw [hβr, hpi]
    exact Subgroup.le_normalizer
  · rw [hpi, hβr, Subgroup.relIndex_top_right, Subgroup.index_top]
    norm_num

theorem hasLeviDataX_of_psp_three_one {S : Type} [Group S] [Finite S]
    (h : CFSG.Blueprint.LieModel S .PSp 3 2 1) {J : Subgroup S}
    (hJ : S19.IsNontrivialParabolic S J) : HasLeviDataX True False ↥J := by
  classical
  obtain ⟨-, K, _, _, hKcard, ⟨eProj⟩⟩ :=
    h.statedClassicalModel (t := .PSp) (n := 3) (p := 2) (f := 1) (by decide)
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  have : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 1) (by simpa using hKcard)
  have hscal : (StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K) = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot
  let eS : S ≃* StatedSp 3 K :=
    eProj.trans ((QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot)
  let φ : ↥(⊤ : Subgroup S) ≃* StatedSp 3 K := Subgroup.topEquiv.trans eS
  obtain ⟨ρ, I, t, hI, htI, hmax, hcomap⟩ :=
    exists_flagStabilizer_of_isParabolicTwo
      (isParabolicTwo_top_of_isNontrivialParabolic hJ) hJ.2.1 φ
  exact hasLeviDataX_of_leviMap_data
    (exists_leviMap_data (K := K) hK2 ρ I t hI htI hmax hcomap)

theorem hasLeviData_of_psp_three_one {S : Type} [Group S] [Finite S]
    (h : CFSG.Blueprint.LieModel S .PSp 3 2 1) {J : Subgroup S}
    (hJ : S19.IsNontrivialParabolic S J) : HasLeviData ↥J :=
  (hasLeviDataX_of_psp_three_one h hJ).hasLeviData

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

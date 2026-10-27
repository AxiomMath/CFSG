module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFiveProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarConjShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3IndexNormal
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsNoO2Sixteen
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def K_U3IndexWreath : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K T H : Subgroup X) (n : ℕ),
    CFSG.Open.IsSubnormal K H → ¬ (K.subgroupOf H).Normal → ⁅K, K⁆ = K →
    CFSG.Open.IsQuasisimple (Bar2 K) → IsSU3 (Bar2 K) n →
    IsSylowIn 2 T H → K ⊔ T = H → InFSq n H

@[expose] def K_U3IndexF : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A) [L.Normal] (K : Subgroup A)
    (C : Subgroup A) [C.Normal] (n : ℕ),
    C = Subgroup.centralizer (L : Set A) → CFSG.Open.IsQuasisimple ↥L →
    IsU3 (↥L ⧸ Subgroup.center ↥L) n → IsPGroup 2 K → L ⊔ K = ⊤ →
    InFGroup n (A ⧸ C)

theorem k_U3Index_of_normal_and_wreath (hN : Inputs1719.K_U3IndexNormal)
    (hW : K_U3IndexWreath) : K_U3Index := by
  intro X _ _ K T H n hsub hperf hq hSU3 hTsyl hsup
  by_cases hKn : (K.subgroupOf H).Normal
  · exact hN X K T H n (CFSG.Open.IsSubnormal.le hsub) hKn hperf hq hSU3 hTsyl hsup
  · exact hW X K T H n hsub hKn hperf hq hSU3 hTsyl hsup

theorem isSU3_bar2_of_isSU3 {X : Type} [Group X] [Finite X] {K : Subgroup X} {n : ℕ}
    (hSU3 : IsSU3 ↥K n) (hodd : Odd (Nat.card (Subgroup.center ↥K))) :
    IsSU3 (UC22.Bar2 K) n := by
  have hpc : CFSG.pCore 2 ↥K ≤ Subgroup.center ↥K :=
    GL83.I243.pCore_le_center (p := 2) Nat.prime_two hSU3.1
  have hoddpc : Odd (Nat.card ↥(CFSG.pCore 2 ↥K)) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hpc)
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).exists_card_eq
  have hbot : CFSG.pCore 2 ↥K = ⊥ := by
    rw [hm] at hoddpc
    have hm0 : m = 0 := by
      rcases m with _ | k
      · rfl
      · exfalso
        have he : Even (2 ^ (k + 1)) := by
          rw [pow_succ]
          exact ⟨2 ^ k, by ring⟩
        exact (Nat.not_even_iff_odd.mpr hoddpc) he
    have hcard1 : Nat.card ↥(CFSG.pCore 2 ↥K) = 1 := by rw [hm, hm0, pow_zero]
    exact Subgroup.eq_bot_of_card_eq _ hcard1
  let e : UC22.Bar2 K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  refine ⟨hSU3.1.of_mulEquiv e, ?_⟩
  refine CFSG.Blueprint.LieModel.of_mulEquiv
    (QuotientGroup.congr (Subgroup.center (UC22.Bar2 K)) (Subgroup.center ↥K) e
      (Subgroup.map_center_eq e)).symm hSU3.2

@[expose] def HbBoundA (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (n : ℕ) (c : Ctx17_33 D V₀ V L n),
    barSub V₀ V c.hyp125.isElemAbelian L ≠ ⊥ →
    (∀ g ∈ D.M, ∃ t ∈ D.T,
      L.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj t).toMonoidHom) →
    fixV (barSub V₀ V c.hyp125.isElemAbelian (UC22.conjClosure D.M L)) = ⊥ →
    bBar (UC22.conjClosure D.M L) D.M V₀ V c.hyp125.isElemAbelian ≤ n

theorem hbBound_holds (hW4 : Inputs1719.W4Lem4_16b) (hKidx : K_U3Index)
    (D : Data G) (V₀ V : Subgroup G) : HbBoundA D V₀ V := by
  classical
  intro L n c hLb htr hfix
  have hV := c.hyp125
  have hLM : L ≤ D.M := c.mem_calC.1.le
  have hsubH : CFSG.Open.IsSubnormal L (L ⊔ D.T) := by
    have h := c.mem_calC.1.inf (L ⊔ D.T)
    rwa [inf_eq_left.2 le_sup_left, inf_eq_right.2 (sup_le hLM D.sylowM.le)] at h
  have hMS : D.M ≤ stabTil V₀ V :=
    le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀
  have hLS : L ≤ stabTil V₀ V := hLM.trans hMS
  have hTS : D.T ≤ stabTil V₀ V := D.sylowM.le.trans hMS
  have hSU3bar : IsSU3 ↥(barSub V₀ V hV.isElemAbelian L) n :=
    isSU3_barSub hV c.mem_calC hLb c.shape
  have hoddbar : Odd (Nat.card (Subgroup.center ↥(barSub V₀ V hV.isElemAbelian L))) :=
    odd_center_barSub hV c.mem_calC hLb
  have hbar2 : IsSU3 (UC22.Bar2 (barSub V₀ V hV.isElemAbelian L)) n :=
    isSU3_bar2_of_isSU3 hSU3bar hoddbar
  have hsubbar : CFSG.Open.IsSubnormal (barSub V₀ V hV.isElemAbelian L)
      (barSub V₀ V hV.isElemAbelian (L ⊔ D.T)) := by
    have h1 : CFSG.Open.IsSubnormal (L.subgroupOf (stabTil V₀ V))
        ((L ⊔ D.T).subgroupOf (stabTil V₀ V)) :=
      hsubH.comap (stabTil V₀ V).subtype
    exact h1.map (actTil V₀ V hV.isElemAbelian)
  have hsupbar : barSub V₀ V hV.isElemAbelian (L ⊔ D.T) =
      barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian D.T :=
    s16c7_barSub_sup V₀ V hV.isElemAbelian hLS hTS
  have hsyl : IsSylowIn 2 (barSub V₀ V hV.isElemAbelian D.T)
      (barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian D.T) := by
    have h := isSylowIn_barSub_T_sup hV hLM
    rwa [hsupbar] at h
  have hperfbar : ⁅barSub V₀ V hV.isElemAbelian L,
      barSub V₀ V hV.isElemAbelian L⁆ = barSub V₀ V hV.isElemAbelian L := by
    rw [← Subgroup.map_subtype_commutator, hSU3bar.1.1, Subgroup.map_top,
      Subgroup.range_subtype]
  have hIn' : InFSq n (barSub V₀ V hV.isElemAbelian (L ⊔ D.T)) :=
    hKidx (MulAut (Vtil V₀ V hV.isElemAbelian))
      (barSub V₀ V hV.isElemAbelian L) (barSub V₀ V hV.isElemAbelian D.T)
      (barSub V₀ V hV.isElemAbelian (L ⊔ D.T)) n hsubbar hperfbar hbar2.1 hbar2
      (hsupbar ▸ hsyl) hsupbar.symm
  have hInY : InFSq n (barSub V₀ V hV.isElemAbelian L ⊔
      barSub V₀ V hV.isElemAbelian D.T) := by
    rw [← hsupbar]
    exact hIn'
  have hcomp : IsComponentOf (barSub V₀ V hV.isElemAbelian L)
      (barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian D.T) := by
    refine CFSG.Quasithin.B15P4.isComponentOf_of_le
      (X := Mbar D.M V₀ V hV.isElemAbelian) ?_ le_sup_left ?_
    · simpa [compBar] using barSub_mem_compBar_of_ne_bot hV c.mem_calC hLb
    · exact sup_le (barSub_mono V₀ V hV.isElemAbelian hLM)
        (barSub_mono V₀ V hV.isElemAbelian D.sylowM.le)
  have hLX : barSub V₀ V hV.isElemAbelian L ≤
      barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L) :=
    barSub_mono V₀ V hV.isElemAbelian (TwelveTwentyThree.le_conjClosure D.M L)
  have hXne : barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L) ≠ ⊥ := by
    intro hbot
    exact hLb (le_bot_iff.1 (hLX.trans (le_of_eq hbot)))
  have hXle : barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L) ≤
      barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian D.T :=
    barSub_conjClosure_le_sup_T_of_transitive hV hLM htr
  have hsupX : barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L) ⊔
      barSub V₀ V hV.isElemAbelian D.T =
      barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian D.T :=
    le_antisymm (sup_le hXle le_sup_right) (sup_le_sup hLX le_rfl)
  have hfixT : fixV (barSub V₀ V hV.isElemAbelian D.T) ≠
      fixV (barSub V₀ V hV.isElemAbelian L ⊔
        barSub V₀ V hV.isElemAbelian D.T) := by
    have hne := fixV_ne_fixV_sup (W := Vtil V₀ V hV.isElemAbelian)
      (s15_Infra_vtil_sq_eq_one V₀ V hV.isElemAbelian) hXne hfix hsyl.isPGroup
    rwa [hsupX] at hne
  have hsum : fIndexSum ({(barSub V₀ V hV.isElemAbelian L ⊔
      barSub V₀ V hV.isElemAbelian D.T)} :
        Set (Subgroup (MulAut (Vtil V₀ V hV.isElemAbelian)))) ≤ (n : ℕ∞) := by
    rw [fIndexSum, finsum_mem_singleton]
    exact fIndex_le_iff.mpr hInY
  have hbound : bParam (barSub V₀ V hV.isElemAbelian L)
      (barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian D.T) ≤ n :=
    hW4 (Vtil V₀ V hV.isElemAbelian) (s15_Infra_vtil_sq_eq_one V₀ V hV.isElemAbelian)
      (barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian D.T)
      (barSub V₀ V hV.isElemAbelian L) (barSub V₀ V hV.isElemAbelian D.T)
      {(barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian D.T)} n
      le_sup_left le_sup_right rfl hcomp hsyl (Set.finite_singleton _)
      (by rintro H rfl; exact ⟨le_rfl, le_sup_right⟩) (by simp) hsum hfixT
  exact (bBar_conjClosure_le_bParam_sup_of_transitive hV hLM htr).trans hbound

theorem hbBound_of_hbBoundA {D : Data G} {V₀ V : Subgroup G} (h : HbBoundA D V₀ V)
    (hLb : ∀ (L : Subgroup G) (n : ℕ) (c : Ctx17_33 D V₀ V L n),
      barSub V₀ V c.hyp125.isElemAbelian L ≠ ⊥)
    (htr : ∀ (L : Subgroup G) (n : ℕ) (_c : Ctx17_33 D V₀ V L n), ∀ g ∈ D.M, ∃ t ∈ D.T,
      L.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj t).toMonoidHom)
    (hfix : ∀ (L : Subgroup G) (n : ℕ) (c : Ctx17_33 D V₀ V L n),
      fixV (barSub V₀ V c.hyp125.isElemAbelian (UC22.conjClosure D.M L)) = ⊥) :
    HbBound D V₀ V := by
  intro L n c
  exact h L n c (hLb L n c) (htr L n c) (hfix L n c)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end

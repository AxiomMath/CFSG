module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4R52c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c4_r52_root_group (D : Data G) (h22 : R1622 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (F : UFrame V₀ V hV L)
    (hr : ((mSub V₀ + 4 : ℕ) : ℕ∞) ≤ rMV D.M V) {g : G} (hAM : conjSubgroup V g ≤ D.M)
    (hAL : barSub V₀ V hV (conjSubgroup V g) ≤ lBar V₀ V hV L)
    (hAc : Nat.card (barSub V₀ V hV (conjSubgroup V g)) = 2 ^ 4) :
    ∃ B Z : Subgroup G, B ≤ conjSubgroup V g ∧ Z = V ⊓ centralizer (B : Set G) ∧
      conjSubgroup V g ⊓ centralizer (Z : Set G) = B ∧ E3.mQuot V Z = 2 ∧
      mSub B = 5 + mSub V₀ := by
  classical
  set A : Subgroup G := conjSubgroup V g with hA
  have hP := hS.setting.hyp16.hyp125.pairFacts
  have hAst : A ≤ stabTil V₀ V :=
    le_stabTil (hAM.trans hP.le_normalizer) (hAM.trans hP.le_normalizer₀)
  have hAel : IsElemAbelian 2 A := by
    rw [hA]
    exact E3.isElemAbelian_conjSubgroup hV g
  have hX2 : IsElemAbelian2 (barSub V₀ V hV A) := isElemAbelian2_barSub hV hAel
  obtain ⟨Bbar, hBbarA, hBbar_card, hfixBbar_card, hroot⟩ :=
    s16c4_r52_root_bar F hAL hX2 hAc
  set B : Subgroup G := preBarSub A V₀ V hV Bbar with hB
  set Z : Subgroup G := V ⊓ centralizer (B : Set G) with hZ
  have hBA : B ≤ A := by
    rw [hB]
    exact inf_le_left
  have hBst : B ≤ stabTil V₀ V := hBA.trans hAst
  have hmq : E3.mQuot A B = 3 := by
    have h1 : E3.mQuot (barSub V₀ V hV A) Bbar = E3.mQuot A B :=
      mQuot_barSub_preBarSub_gen hV hAst hBbarA
    rw [← h1, E3.mQuot]
    have hrel : Bbar.relIndex (barSub V₀ V hV A) = 8 := by
      have h := Subgroup.relIndex_mul_card (H := Bbar) (K := barSub V₀ V hV A)
      rw [inf_eq_left.2 hBbarA, hBbar_card, hAc] at h
      omega
    rw [hrel, show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  have hBΓ : B ∈ E3.gammaSet V 3 D.M :=
    ⟨hBA.trans hAM, g, by rw [← hA]; exact hBA, by rw [← hA]; exact hmq⟩
  have hi : ((3 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
    refine lt_of_lt_of_le ?_ hr
    rw [ENat.natCast_lt_natCast]
    omega
  have h23 := sixteen_twentyThree_one D h22 hS.setting.hyp16 hBΓ
    (by rw [← hA]; exact hBA) hi
  have hBbar_eq : barSub V₀ V hV B = Bbar := by
    rw [hB, barSub_preBarSub]
    exact inf_eq_left.2 hBbarA
  have hpB : preCTilde V₀ V B hV = Z := by
    rw [hZ]
    exact preCTilde_eq_inf_centralizer_of hV hBst h23.2.1
  have hp : preTil V₀ V hV (fixV Bbar) = Z := by
    rw [← hpB]
    unfold preCTilde
    rw [hBbar_eq]
  have hZi : E3.mQuot V Z = 2 := by
    rw [← hp, mQuot_preTil V₀ V hV (fixV Bbar)]
    unfold rkIdx
    have hci : Nat.card (fixV Bbar) * (fixV Bbar).index = Nat.card (Vtil V₀ V hV) :=
      Subgroup.card_mul_index (H := fixV Bbar)
    rw [hfixBbar_card, F.card_Vtil] at hci
    have hidx : (fixV Bbar).index = 2 ^ 2 := by
      norm_num at hci ⊢
      omega
    rw [hidx, padicValNat.prime_pow]
  have hd : A ⊓ centralizer (Z : Set G) = B := by
    apply le_antisymm
    · intro a ha
      rw [Subgroup.mem_inf] at ha
      obtain ⟨haA, hac⟩ := ha
      have haAst : a ∈ stabTil V₀ V := hAst haA
      have hmembar : actTil V₀ V hV ⟨a, haAst⟩ ∈ barSub V₀ V hV A :=
        actTil_mem_barSub V₀ V hV haA haAst
      have hfix : ∀ w ∈ fixV Bbar, actTil V₀ V hV ⟨a, haAst⟩ w = w := by
        intro w hw
        rw [← imgTil_preTil V₀ V hV (fixV Bbar)] at hw
        obtain ⟨x, hx, hxw⟩ :=
          (mem_imgTil V₀ V hV (preTil V₀ V hV (fixV Bbar)) w).1 hw
        rw [← hxw, actTil_mk]
        congr 1
        apply IntMod.val_injective
        rw [actStab_apply_val]
        have hxZ : x.val ∈ Z := by
          rw [← hp]
          exact hx
        have hcomm : a * x.val = x.val * a :=
          (Subgroup.mem_centralizer_iff.1 hac x.val hxZ).symm
        rw [hcomm]
        group
      have hrootmem : actTil V₀ V hV ⟨a, haAst⟩ ∈ Bbar :=
        hroot (actTil V₀ V hV ⟨a, haAst⟩) hmembar hfix
      rw [hB]
      exact (mem_preBarSub A V₀ V hV Bbar).2 ⟨haA, haAst, hrootmem⟩
    · intro b hb
      rw [Subgroup.mem_inf]
      refine ⟨hBA hb, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      simp only [hZ, Subgroup.mem_inf] at hz
      exact (Subgroup.mem_centralizer_iff.1 hz.2 b hb).symm
  have he : mSub B = 5 + mSub V₀ := by
    have hcard := s16c7_card_mul_card_preBarSub hV hAst hBbarA
    rw [hBbar_card, hAc] at hcard
    have hcardA : Nat.card A = 2 ^ (8 + mSub V₀) := by
      have h1 : Nat.card A = Nat.card V := by
        rw [hA, E3.card_conjSubgroup]
      rw [h1, card_eq_two_pow_mSub hV.isPGroup, F.mSub_V hS]
    rw [hcardA] at hcard
    have hB2 : IsPGroup 2 B := (E3.isPGroup_conjSubgroup hV.isPGroup g).to_le hBA
    have hcardB : Nat.card B = 2 ^ mSub B := card_eq_two_pow_mSub hB2
    rw [hcardB] at hcard
    have hEq : 2 ^ (mSub B + 4) = 2 ^ (8 + mSub V₀ + 1) := by
      calc 2 ^ (mSub B + 4) = 2 ^ mSub B * 2 ^ 4 := by rw [pow_add]
        _ = 2 ^ (8 + mSub V₀) * 2 := hcard.symm
        _ = 2 ^ (8 + mSub V₀ + 1) := by rw [pow_succ]
    have hm : mSub B + 4 = 8 + mSub V₀ + 1 :=
      Nat.pow_right_injective (by norm_num) hEq
    omega
  exact ⟨B, Z, hBA, hZ, hd, hZi, he⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

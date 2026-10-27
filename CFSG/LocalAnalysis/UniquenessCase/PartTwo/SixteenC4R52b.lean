module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4R52a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAk
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4R50c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace UFrame

variable {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G}
  (F : UFrame V₀ V hV L)

theorem card_fixV_eq {X : Subgroup (MulAut (Vtil V₀ V hV))} (hX : X ≤ lBar V₀ V hV L) :
    Nat.card (fixV X) = Nat.card (fixSp (F.suSub X)) := by
  have h : F.addSub (fixV X) = (fixSp (F.suSub X)).toAddSubgroup := by
    ext x
    change F.ofVec x ∈ fixV X ↔ x ∈ fixSp (F.suSub X)
    rw [F.mem_fixV_iff_fixSp hX, F.vec_ofVec]
  calc Nat.card (fixV X) = Nat.card (F.addSub (fixV X)) := (F.card_addSub (fixV X)).symm
    _ = Nat.card ((fixSp (F.suSub X)).toAddSubgroup) := by rw [h]
    _ = Nat.card (fixSp (F.suSub X)) := rfl

theorem exists_card_fixV_eq_pow_four (F : UFrame V₀ V hV L)
    {X : Subgroup (MulAut (Vtil V₀ V hV))}
    (hX : X ≤ lBar V₀ V hV L) : ∃ d : ℕ, Nat.card (fixV X) = 4 ^ d := by
  refine ⟨Module.finrank F.K ↥(fixSp (F.suSub X)), ?_⟩
  rw [F.card_fixV_eq hX, Module.natCard_eq_pow_finrank (K := F.K), F.card_K]

theorem card_commV_eq {X : Subgroup (MulAut (Vtil V₀ V hV))} (hX : X ≤ lBar V₀ V hV L) :
    Nat.card (commV X) = Nat.card (commSp (F.suSub X)) := by
  have h : F.addSub (commV X) = (commSp (F.suSub X)).toAddSubgroup := by
    ext x
    change F.ofVec x ∈ commV X ↔ x ∈ commSp (F.suSub X)
    rw [F.mem_commV_iff_commSp hX, F.vec_ofVec]
  calc Nat.card (commV X) = Nat.card (F.addSub (commV X)) := (F.card_addSub (commV X)).symm
    _ = Nat.card ((commSp (F.suSub X)).toAddSubgroup) := by rw [h]
    _ = Nat.card (commSp (F.suSub X)) := rfl

end UFrame

theorem s16c4_r52_mQuot_cent (D : Data G) (h22 : R1622 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (F : UFrame V₀ V hV L)
    (hr : ((mSub V₀ + 4 : ℕ) : ℕ∞) ≤ rMV D.M V) {g : G} (hAM : conjSubgroup V g ≤ D.M)
    (hAL : barSub V₀ V hV (conjSubgroup V g) ≤ lBar V₀ V hV L)
    (hfix : Nat.card (fixSp (F.suSub (barSub V₀ V hV (conjSubgroup V g)))) = 2 ^ 4) :
    E3.mQuot V (V ⊓ centralizer (conjSubgroup V g : Set G)) = 4 := by
  have hA : conjSubgroup V g ∈ E3.gammaSet V 0 D.M :=
    ⟨hAM, g, le_rfl, E3.mQuot_self _⟩
  have hi : ((0 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
    have h1 : mSub V₀ < mSub V₀ + 4 := Nat.lt_add_of_pos_right (by norm_num)
    exact lt_of_lt_of_le (by simpa using (ENat.natCast_lt_natCast.2 h1)) hr
  have h23 := sixteen_twentyThree_one D h22 hS.setting.hyp16 hA le_rfl hi
  have hpf := hS.setting.hyp16.hyp125.pairFacts
  have hAst : conjSubgroup V g ≤ stabTil V₀ V :=
    hAM.trans (le_stabTil hpf.le_normalizer hpf.le_normalizer₀)
  have hpre := preCTilde_eq_inf_centralizer_of (V₀ := V₀) (V := V)
    (D := conjSubgroup V g) hV hAst h23.2.1
  have hcardF : Nat.card (fixV (barSub V₀ V hV (conjSubgroup V g))) = 2 ^ 4 := by
    rw [F.card_fixV_eq hAL]
    exact hfix
  have hidx : (fixV (barSub V₀ V hV (conjSubgroup V g))).index = 2 ^ 4 := by
    have h := Subgroup.card_mul_index (fixV (barSub V₀ V hV (conjSubgroup V g)))
    rw [hcardF, F.card_Vtil] at h
    have h' : 2 ^ 4 * (fixV (barSub V₀ V hV (conjSubgroup V g))).index =
        2 ^ 4 * 2 ^ 4 := by rw [h]; norm_num
    exact Nat.mul_left_cancel (by norm_num) h'
  rw [← hpre]
  unfold preCTilde
  rw [mQuot_preTil, rkIdx, hidx, padicValNat.prime_pow]

theorem s16c4_r52_card_barSub (D : Data G) (h22 : R1622 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) {g : G} (hg : g ∉ D.M)
    (hAM : conjSubgroup V g ≤ D.M) (hVM : V ≤ conjSubgroup D.M g) :
    Nat.card (conjSubgroup V g) =
      Nat.card (conjSubgroup V g ⊓ centralizer (V : Set G) : Subgroup G) *
        Nat.card (barSub V₀ V hV (conjSubgroup V g)) := by
  have hpf := hS.setting.hyp16.hyp125.pairFacts
  have hAst : conjSubgroup V g ≤ stabTil V₀ V :=
    hAM.trans (le_stabTil hpf.le_normalizer hpf.le_normalizer₀)
  have hprebar : preBarSub (conjSubgroup V g) V₀ V hV ⊥ =
      conjSubgroup V g ⊓ centralizer (V : Set G) := by
    apply le_antisymm
    · intro a ha
      rw [mem_preBarSub] at ha
      obtain ⟨haA, h, hh⟩ := ha
      rw [Subgroup.mem_bot] at hh
      refine Subgroup.mem_inf.2 ⟨haA, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hV₀ : ⁅a, v⁆ ∈ V₀ := by
        have := (actTil_eq_one_iff V₀ V hV ⟨a, h⟩).1 hh v hv
        simpa only [commutatorElement_def] using this
      have hcomm := s16c4_r52_comm_mem_inf D hS hAM hVM haA hv
      have hmem : ⁅a, v⁆ ∈ V₀ ⊓ conjSubgroup V g := ⟨hV₀, hcomm.2⟩
      rw [s16c4_V0_inf_conj_eq_bot D h22 hS hg, Subgroup.mem_bot] at hmem
      exact (commutatorElement_eq_one_iff_mul_comm.1 hmem).symm
    · intro a ha
      rw [Subgroup.mem_inf] at ha
      obtain ⟨haA, hcent⟩ := ha
      rw [mem_preBarSub]
      refine ⟨haA, hAst haA, ?_⟩
      rw [Subgroup.mem_bot, actTil_eq_one_iff]
      intro v hv
      have hcomm : a * v = v * a :=
        (Subgroup.mem_centralizer_iff.1 hcent v hv).symm
      rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm.2 hcomm]
      exact V₀.one_mem
  have h1 := s16c7_card_mul_card_preBarSub (V₀ := V₀) (V := V)
    (E := conjSubgroup V g) hV hAst (Q := ⊥) bot_le
  rw [Subgroup.card_bot, mul_one, hprebar] at h1
  exact h1

theorem s16c4_r52_card_barSub_eq (D : Data G) (h22 : R1622 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) {g : G} (hg : g ∉ D.M)
    (hAM : conjSubgroup V g ≤ D.M) (hVM : V ≤ conjSubgroup D.M g)
    (hidx : E3.mQuot V (V ⊓ centralizer (conjSubgroup V g⁻¹ : Set G)) = 4) :
    Nat.card (barSub V₀ V hV (conjSubgroup V g)) = 2 ^ 4 := by
  have h6 := s16c4_r52_card_barSub D h22 hS hg hAM hVM
  have hA2 : IsPGroup 2 (conjSubgroup V g) :=
    CFSG.Open.IsElemAbelian.isPGroup (E3.isElemAbelian_conjSubgroup hV g)
  have h7 := E3.card_eq_two_pow_mul (V := conjSubgroup V g)
    (U := conjSubgroup V g ⊓ centralizer (V : Set G)) hA2 inf_le_left
  have hconj : E3.mQuot (conjSubgroup V g)
      (conjSubgroup V g ⊓ centralizer (V : Set G)) = 4 := by
    have h := E3.mQuot_conjSubgroup V (V ⊓ centralizer (conjSubgroup V g⁻¹ : Set G)) g
    have hU : conjSubgroup (V ⊓ centralizer (conjSubgroup V g⁻¹ : Set G)) g =
        conjSubgroup V g ⊓ centralizer (V : Set G) := by
      rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer, E3.conjSubgroup_inv_conj]
    rw [hU] at h
    rw [h]
    exact hidx
  rw [hconj] at h7
  have heq : 2 ^ 4 *
        Nat.card (conjSubgroup V g ⊓ centralizer (V : Set G) : Subgroup G) =
      Nat.card (barSub V₀ V hV (conjSubgroup V g)) *
        Nat.card (conjSubgroup V g ⊓ centralizer (V : Set G) : Subgroup G) :=
    calc 2 ^ 4 * Nat.card (conjSubgroup V g ⊓ centralizer (V : Set G) : Subgroup G)
        = Nat.card (conjSubgroup V g) := h7.symm
      _ = Nat.card (conjSubgroup V g ⊓ centralizer (V : Set G) : Subgroup G) *
            Nat.card (barSub V₀ V hV (conjSubgroup V g)) := h6
      _ = Nat.card (barSub V₀ V hV (conjSubgroup V g)) *
            Nat.card (conjSubgroup V g ⊓ centralizer (V : Set G) : Subgroup G) :=
          mul_comm _ _
  exact (Nat.mul_right_cancel Nat.card_pos heq).symm

theorem s16c4_r52_two (D : Data G) (h61 : UC6.R6_1 D) (h22 : R1622 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (h4 : Case167_4 D V₀ V hV L) (F : UFrame V₀ V hV L)
    (hr : ((mSub V₀ + 4 : ℕ) : ℕ∞) ≤ rMV D.M V)
    (h51 : ∀ A ∈ E3.gammaSet V 0 D.M, barSub V₀ V hV A ≠ ⊥ →
      barSub V₀ V hV A ∈ calABar 2 D.M V₀ V hV ∧ barSub V₀ V hV A ≤ lBar V₀ V hV L)
    {g : G} (hg : g ∉ D.M) (hAM : conjSubgroup V g ≤ D.M) (hVM : V ≤ conjSubgroup D.M g)
    (hne : ⁅V, conjSubgroup V g⁆ ≠ ⊥) :
    barSub V₀ V hV (conjSubgroup V g) ≤ lBar V₀ V hV L ∧
      Nat.card (barSub V₀ V hV (conjSubgroup V g)) = 2 ^ 4 ∧
      commSp (F.suSub (barSub V₀ V hV (conjSubgroup V g))) =
        fixSp (F.suSub (barSub V₀ V hV (conjSubgroup V g))) ∧
      Nat.card (fixSp (F.suSub (barSub V₀ V hV (conjSubgroup V g)))) = 2 ^ 4 ∧
      E3.mQuot V (V ⊓ centralizer (conjSubgroup V g : Set G)) = 4 := by
  obtain ⟨-, hAL, hcomm, hfix⟩ :=
    s16c4_r52_one D h61 h22 hS h4 F hr h51 hg hAM hVM hne
  obtain ⟨hg', hAM', hVM', hne'⟩ := s16c4_r52_symm D hg hAM hVM hne
  obtain ⟨-, hAL', -, hfix'⟩ :=
    s16c4_r52_one D h61 h22 hS h4 F hr h51 hg' hAM' hVM' hne'
  have hidx := s16c4_r52_mQuot_cent D h22 hS F hr hAM' hAL' hfix'
  exact ⟨hAL, s16c4_r52_card_barSub_eq D h22 hS hg hAM hVM hidx, hcomm, hfix,
    s16c4_r52_mQuot_cent D h22 hS F hr hAM hAL hfix⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

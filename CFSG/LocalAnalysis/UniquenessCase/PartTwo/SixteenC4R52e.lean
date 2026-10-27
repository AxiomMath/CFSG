module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4R52d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4R51

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c4_r52_parity (D : Data G) (h61 : UC6.R6_1 D) (h22 : R1622 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (h4 : Case167_4 D V₀ V hV L) (F : UFrame V₀ V hV L)
    (hr : ((mSub V₀ + 4 : ℕ) : ℕ∞) ≤ rMV D.M V)
    (h51 : ∀ A ∈ E3.gammaSet V 0 D.M, barSub V₀ V hV A ≠ ⊥ →
      barSub V₀ V hV A ∈ calABar 2 D.M V₀ V hV ∧ barSub V₀ V hV A ≤ lBar V₀ V hV L)
    {g : G} (hg : g ∉ D.M) (hAM : conjSubgroup V g ≤ D.M) (hVM : V ≤ conjSubgroup D.M g)
    (hne : ⁅V, conjSubgroup V g⁆ ≠ ⊥) {B Z : Subgroup G} (hZV : Z ≤ V)
    (hBZ : conjSubgroup V g ⊓ centralizer (Z : Set G) = B) (hZi : E3.mQuot V Z = 2)
    (hB : mSub B = 5 + mSub V₀) : False := by
  obtain ⟨hg', hAM', hVM', hne'⟩ := s16c4_r52_symm D hg hAM hVM hne
  obtain ⟨-, hAL', -, -⟩ :=
    s16c4_r52_one D h61 h22 hS h4 F hr h51 hg' hAM' hVM' hne'
  set Z' : Subgroup G := conjSubgroup Z g⁻¹ with hZ'def
  have hZ'A' : Z' ≤ conjSubgroup V g⁻¹ := E3.conjSubgroup_mono_left g⁻¹ hZV
  have hZ'M : Z' ≤ D.M := hZ'A'.trans hAM'
  have hmq : E3.mQuot (conjSubgroup V g⁻¹) Z' = 2 := by
    rw [hZ'def, E3.mQuot_conjSubgroup]
    exact hZi
  have hZ'Γ : Z' ∈ E3.gammaSet V 2 D.M := ⟨hZ'M, g⁻¹, hZ'A', hmq⟩
  have hi : ((2 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
    refine lt_of_lt_of_le ?_ hr
    rw [ENat.natCast_lt_natCast]
    omega
  have h23 := sixteen_twentyThree_one D h22 hS.setting.hyp16 hZ'Γ hZ'A' hi
  have hpf := hS.setting.hyp16.hyp125.pairFacts
  have hZ'st : Z' ≤ stabTil V₀ V :=
    le_stabTil (hZ'M.trans hpf.le_normalizer) (hZ'M.trans hpf.le_normalizer₀)
  have hpre : V ⊓ centralizer (Z' : Set G) = preCTilde V₀ V Z' hV :=
    (preCTilde_eq_inf_centralizer_of hV hZ'st h23.2.1).symm
  have hle : V₀ ≤ V := hpf.le
  have hZ'lbar : barSub V₀ V hV Z' ≤ lBar V₀ V hV L :=
    (barSub_mono V₀ V hV hZ'A').trans hAL'
  obtain ⟨d, hd⟩ := F.exists_card_fixV_eq_pow_four hZ'lbar
  have hrk : rk ↥(fixV (barSub V₀ V hV Z')) = 2 * d := by
    show padicValNat 2 (Nat.card ↥(fixV (barSub V₀ V hV Z'))) = 2 * d
    have h4 : (4 : ℕ) ^ d = 2 ^ (2 * d) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]
    rw [hd, h4, padicValNat.prime_pow]
  have hmV : mSub (V ⊓ centralizer (Z' : Set G)) =
      mSub V₀ + rk ↥(fixV (barSub V₀ V hV Z')) := by
    rw [hpre]
    show mSub (preTil V₀ V hV (fixV (barSub V₀ V hV Z'))) =
      mSub V₀ + rk ↥(fixV (barSub V₀ V hV Z'))
    rw [s16c4_mSub_preTil (S := fixV (barSub V₀ V hV Z')) hV hle]
  have hconjB : conjSubgroup B g⁻¹ = V ⊓ centralizer (Z' : Set G) := by
    rw [← hBZ, E3.conjSubgroup_inf, E3.conjSubgroup_centralizer, E3.conjSubgroup_conj_inv,
      hZ'def]
  have hBconj : mSub B = mSub (conjSubgroup B g⁻¹) := by
    show rk ↥B = rk ↥(conjSubgroup B g⁻¹)
    rw [E3.rk_conjSubgroup]
  have hB2 : mSub B = mSub V₀ + 2 * d := by
    rw [hBconj, hconjB, hmV, hrk]
  have h5 : 5 + mSub V₀ = mSub V₀ + 2 * d := hB.symm.trans hB2
  omega

theorem r16_52_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D) (hV1 : Case167_4_V1Eq D) :
    ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
      Case167_4 D V₀ V hV L →
        ∀ g : G, conjSubgroup V g ≤ D.M → V ≤ conjSubgroup D.M g → ⁅V, conjSubgroup V g⁆ = ⊥ := by
  intro V₀ V L hV hS h4 g hAM hVM
  by_cases hg : g ∈ D.M
  ·
    have h62 := hS.setting.hyp16.hyp125.hyp62
    have hgN : g ∈ normalizer (V : Set G) := h62.normalizer_eq ▸ hg
    rw [conjSubgroup_eq_iff_mem_normalizer.2 hgN]
    refine le_bot_iff.1 (Subgroup.commutator_le.2 ?_)
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact IsElemAbelian.comm hV ha hb
  · by_contra hne
    obtain ⟨F⟩ := exists_uFrame D h4 (hV1.v1Sub_eq hS h4)
    have hr := (r16_50_holds D h61 hV1 V₀ V L hV hS h4).1
    have h51 := r16_51_holds D hSg h1219 h21 h22 h61 hV1 V₀ V L hV hS h4
    obtain ⟨hAL, hAc, -, -, -⟩ :=
      s16c4_r52_two D h61 h22 hS h4 F hr h51 hg hAM hVM hne
    obtain ⟨B, Z, -, hZdef, hBZ, hZi, hB⟩ :=
      s16c4_r52_root_group D h22 hS F hr hAM hAL hAc
    exact s16c4_r52_parity D h61 h22 hS h4 F hr h51 hg hAM hVM hne
      (hZdef ▸ inf_le_left) hBZ hZi hB

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

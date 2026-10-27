module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11DimP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11TI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

@[expose] def S16C11DimD1 (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  ∀ E ∈ calABar 2 D.M V₀ V hV, E ≤ barSub V₀ V hV D.T → mBar D.M V₀ V hV ≤ rk ↥E →
    ¬ rkIdx (fixV E) ≤ CFSG.Open.pRank 2 (Mbar D.M V₀ V hV)

@[expose] def S16C11DimD2 (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  ∀ E ∈ calABar 3 D.M V₀ V hV, ¬ E ≤ barSub V₀ V hV D.T

theorem s16c11_barSub_conj_eq_bot_of_dimD1 (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V) {g : G} (hAT : conjSubgroup V g ≤ D.T)
    (hVg : V ≤ conjSubgroup D.M g)
    (hTI : V₀ ⊓ conjSubgroup V g = ⊥ ∧ V ⊓ conjSubgroup V₀ g = ⊥)
    (hm : MBarGT D.M V₀ V 1) (hr : ((1 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V)
    (hD1 : S16C11DimD1 D V₀ V hV) :
    barSub V₀ V hV (conjSubgroup V g) = ⊥ := by
  by_contra hA1
  have hP := h.pairFacts
  have hAM : conjSubgroup V g ≤ D.M := hAT.trans D.sylowM.le
  have hmem : barSub V₀ V hV (conjSubgroup V g) ∈ calABar 2 D.M V₀ V hV :=
    (s16c11_barSub_conj_eq_bot_or_mem_calABar_two D hV h hAM hm hr (Or.inl hTI.1)
      (Or.inl hTI)).resolve_left hA1
  exact hD1 _ hmem (barSub_mono V₀ V hV hAT)
    (s16c11_mBar_le_rk_barSub_of_ti hV hP.le hP.le_normalizer hP.le_normalizer₀ hAM hVg hTI hA1)
    (s16c11_rkIdx_fixV_barSub_le_pRank_of_ti hV hP.le_normalizer hP.le_normalizer₀ hAM hVg hTI)

theorem s16c11_barSub_conj_eq_bot_or_mem_calABar_three (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V) {g : G} (hAM : conjSubgroup V g ≤ D.M)
    (hVg : ¬ V ≤ conjSubgroup D.M g) (hTI : V₀ ⊓ conjSubgroup V g = ⊥)
    (hr : ((2 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V) (hβ : (2 : ℕ∞) < betaN 0 D.M V) :
    barSub V₀ V hV (conjSubgroup V g) = ⊥ ∨
      barSub V₀ V hV (conjSubgroup V g) ∈ calABar 3 D.M V₀ V hV := by
  by_cases hA1 : barSub V₀ V hV (conjSubgroup V g) = ⊥
  · exact Or.inl hA1
  refine Or.inr ?_
  have hP := h.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hVg' : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  refine s16c11_barSub_mem_calABar_of_forall hV hAM (hAM.trans hMst) hVg' hA1 ?_
  intro B hBA _ hB3 u hu huB a ha
  have hn : E3.mQuot (conjSubgroup V g) B ≤ 2 := by omega
  have hr' : ((E3.mQuot (conjSubgroup V g) B + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_le_of_lt (by exact_mod_cast Nat.add_le_add_right hn _) hr
  have hβ' : (E3.mQuot (conjSubgroup V g) B : ℕ∞) < betaN 0 D.M V :=
    lt_of_le_of_lt (by exact_mod_cast hn) hβ
  rw [s16c11_comm_eq_one_of_not_le D h hAM hVg hBA hr' hβ' (Or.inl hTI) hu huB a ha]
  exact V₀.one_mem

theorem s16c11_barSub_gammaSet_eq_bot_of_dimD (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V) (hTI : S16C11TI D V₀ V)
    (hm : MBarGT D.M V₀ V 1) (hr : ((2 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V)
    (hβ : (2 : ℕ∞) < betaN 0 D.M V) (hD1 : S16C11DimD1 D V₀ V hV)
    (hD2 : S16C11DimD2 D V₀ V hV) :
    ∀ A ∈ E3.gammaSet V 0 D.T, barSub V₀ V hV A = ⊥ := by
  intro A hA
  obtain ⟨hAT, g, hAg, hA0⟩ := hA
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hAeq : A = conjSubgroup V g := (E3.mQuot_eq_zero_iff hVg.isPGroup hAg).1 hA0
  subst hAeq
  by_cases hg : g ∈ D.M
  · have hgN : g ∈ normalizer (V : Set G) := h.normalizer_eq ▸ hg
    have hVV : conjSubgroup V g = V := by
      ext x
      rw [mem_conjSubgroup_iff]
      exact (Subgroup.mem_normalizer_iff.1 hgN x).symm
    rw [hVV]
    exact s16c11_barSub_self_eq_bot hV
  · have hAM : conjSubgroup V g ≤ D.M := hAT.trans D.sylowM.le
    have hTIg := hTI g hg
    have hr1 : ((1 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
      lt_of_le_of_lt (by exact_mod_cast Nat.add_le_add_right (by norm_num : 1 ≤ 2) _) hr
    by_cases hVMg : V ≤ conjSubgroup D.M g
    · exact s16c11_barSub_conj_eq_bot_of_dimD1 D hV h hAT hVMg hTIg hm hr1 hD1
    · rcases s16c11_barSub_conj_eq_bot_or_mem_calABar_three D hV h hAM hVMg hTIg.1 hr hβ with
        h0 | h3
      · exact h0
      · exact absurd (barSub_mono V₀ V hV hAT) (hD2 _ h3)

theorem s16c11_barSub_gammaSet_eq_bot_of_dimD' (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V) (hTI : S16C11TI D V₀ V)
    (hm : MBarGT D.M V₀ V 1)
    (hr : ((CFSG.Open.pRank 2 (Mbar D.M V₀ V hV) + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V)
    (hD1 : S16C11DimD1 D V₀ V hV) :
    ∀ A ∈ E3.gammaSet V 0 D.T, barSub V₀ V hV A = ⊥ := by
  intro A hA
  obtain ⟨hAT, g, hAg, hA0⟩ := hA
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hAeq : A = conjSubgroup V g := (E3.mQuot_eq_zero_iff hVg.isPGroup hAg).1 hA0
  subst hAeq
  by_cases hg : g ∈ D.M
  · have hgN : g ∈ normalizer (V : Set G) := h.normalizer_eq ▸ hg
    have hVV : conjSubgroup V g = V := by
      ext x
      rw [mem_conjSubgroup_iff]
      exact (Subgroup.mem_normalizer_iff.1 hgN x).symm
    rw [hVV]
    exact s16c11_barSub_self_eq_bot hV
  · by_contra hA1
    have hAM : conjSubgroup V g ≤ D.M := hAT.trans D.sylowM.le
    have hrk : rk ↥(barSub V₀ V hV (conjSubgroup V g)) ≤
        CFSG.Open.pRank 2 (Mbar D.M V₀ V hV) := s16c11_rk_barSub_le_pRank hV hAM hVg
    have hpos : 1 ≤ rk ↥(barSub V₀ V hV (conjSubgroup V g)) :=
      Nat.one_le_iff_ne_zero.2 fun h0 => hA1
        ((rk_eq_zero_iff_of_isPGroup
          (IsElemAbelian2.isPGroup (isElemAbelian2_barSub hV hVg))).1 h0)
    have hr1 : ((1 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
      lt_of_le_of_lt (by exact_mod_cast Nat.add_le_add_right (hpos.trans hrk) _) hr
    have hlt : ((rk ↥(barSub V₀ V hV (conjSubgroup V g)) + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
      lt_of_le_of_lt (by exact_mod_cast Nat.add_le_add_right hrk _) hr
    have hVMg : V ≤ conjSubgroup D.M g :=
      s16c11_le_conjSubgroup_of_rk_barSub_lt D hV h hAM hlt
    exact hA1 (s16c11_barSub_conj_eq_bot_of_dimD1 D hV h hAT hVMg (hTI g hg) hm hr1 hD1)

theorem s16c11_normalizer_le_of_dimD (D : Data G) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V) (hTI : S16C11TI D V₀ V)
    (hm : MBarGT D.M V₀ V 1) (hr : ((2 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V)
    (hβ : (2 : ℕ∞) < betaN 0 D.M V) (hD1 : S16C11DimD1 D V₀ V hV)
    (hD2 : S16C11DimD2 D V₀ V hV) {p : ℕ} (hp : p ∈ D.sig)
    {P : Subgroup (MulAut (Vtil V₀ V hV))} (hPM : P ≤ Mbar D.M V₀ V hV) (hPp : IsPGroup p ↥P)
    (hPc : ¬ IsCyclic ↥P) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
  s16c11_normalizer_le_of_forall_barSub_eq_bot D h61 hV h
    (s16c11_barSub_gammaSet_eq_bot_of_dimD D hV h hTI hm hr hβ hD1 hD2) hp hPM hPp hPc

theorem s16c11_normalizer_le_of_dimD' (D : Data G) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V) (hTI : S16C11TI D V₀ V)
    (hm : MBarGT D.M V₀ V 1)
    (hr : ((CFSG.Open.pRank 2 (Mbar D.M V₀ V hV) + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V)
    (hD1 : S16C11DimD1 D V₀ V hV) {p : ℕ} (hp : p ∈ D.sig)
    {P : Subgroup (MulAut (Vtil V₀ V hV))} (hPM : P ≤ Mbar D.M V₀ V hV) (hPp : IsPGroup p ↥P)
    (hPc : ¬ IsCyclic ↥P) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
  s16c11_normalizer_le_of_forall_barSub_eq_bot D h61 hV h
    (s16c11_barSub_gammaSet_eq_bot_of_dimD' D hV h hTI hm hr hD1) hp hPM hPp hPc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

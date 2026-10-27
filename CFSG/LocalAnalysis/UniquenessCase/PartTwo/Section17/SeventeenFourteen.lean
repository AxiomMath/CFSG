module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.L2Over17
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ComponentCalV1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenA
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.GH74.GLS.C3.Layer1.EvenSelBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace SeventeenFourteen

theorem i_le_three_of_R17_13 {D : Data G}
    {𝔉 : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Prop}
    {V₀ V L : Subgroup G} {r q : ℕ} {hC : Ctx17_6 D V₀ V L r q}
    (h : R17_13At D 𝔉 V₀ V L r q hC) : iL17_12 D 𝔉 r q L ≤ 3 := by
  rcases h with h1 | ⟨-, h2⟩ | ⟨-, h3⟩
  · simpa [h1] using (le_refl (1 : ℕ∞))
  · simpa [h2] using (show (2 : ℕ∞) ≤ 3 by norm_num)
  · simpa [h3] using (le_refl (3 : ℕ∞))

theorem b_le_two_of_R17_11 {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    {hC : Ctx17_6 D V₀ V L r q}
    (h : R17_11At D V₀ V L r q hC)
    (hL1 : barSub V₀ V hC.hyp125.isElemAbelian L ≠ ⊥) :
    bBar (conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian ≤ 2 := by
  rcases h hL1 with h1 | ⟨h2, -⟩ <;> omega

theorem barInf_equiv_bar2 {D : Data G} {L : Subgroup G} {q : ℕ}
    (hL : L ∈ calC D.M) (h : IsL2Over17 (Bar2 L) q) :
    Nonempty (BarInf L ≃* Bar2 L) := by
  obtain ⟨r, f, hr, hr2, hq, hf, hm⟩ := h
  have hsimple : IsSimpleGroup (Bar2 L) :=
    CFSG.GH74.GLS.EvenSelP.isSimpleGroup_of_lieModel' hr hr2 hm
  haveI : IsSimpleGroup (Bar2 L) := hsimple
  have hcenter : Subgroup.center (Bar2 L) = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21k_center_eq_bot hL.2.2
  obtain ⟨e1⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21k_barInf_equiv_of_calC hL
  obtain ⟨e2⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21k_quotCenter_equiv hcenter
  exact ⟨e1.trans e2⟩

theorem barInf_isL2Over17 {D : Data G} {L : Subgroup G} {q : ℕ}
    (hL : L ∈ calC D.M) (h : IsL2Over17 (Bar2 L) q) : IsL2Over17 (BarInf L) q := by
  obtain ⟨e⟩ := barInf_equiv_bar2 hL h
  exact isL2Over17_of_mulEquiv e h

theorem l2r_case {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q)
    (hL2r : IsL2Over17 (Bar2 L) r) (hq9 : q ≤ 9) :
    IsL2Over17 (Bar2 L) 7 := by
  have hL : L ∈ calC D.M := hC.memL
  have hBar : IsL2Over17 (BarInf L) r := barInf_isL2Over17 hL hL2r
  obtain ⟨hr, hr2, t, n, f, hadm, hq, hmodel⟩ := hC.lie
  have hf : 1 ≤ f := hadm.2.1
  have hrle : r ≤ 9 := by
    have hpow : r ^ 1 ≤ r ^ f := Nat.pow_le_pow_right (Nat.Prime.pos hr) hf
    rw [pow_one] at hpow
    omega
  have hr3 : r = 3 ∨ r = 5 ∨ r = 7 := by
    interval_cases r
    · exact absurd hr (by norm_num)
    · exact absurd hr (by norm_num)
    · exact absurd rfl hr2
    · exact Or.inl rfl
    · exact absurd hr (by norm_num)
    · exact Or.inr (Or.inl rfl)
    · exact absurd hr (by norm_num)
    · exact Or.inr (Or.inr rfl)
    · exact absurd hr (by norm_num)
    · exact absurd hr (by norm_num)
  rcases hr3 with rfl | rfl | rfl
  · exact (not_isL2Over17_three (BarInf L) hBar).elim
  · exact (hC.not_l2_five hBar).elim
  · obtain ⟨e⟩ := barInf_equiv_bar2 hL hL2r
    exact isL2Over17_of_mulEquiv e.symm hBar

theorem q_eq_25_of_isL2Over17_25 (hK : K_LieModelNotL2)
    {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q)
    (hL225 : IsL2Over17 (Bar2 L) 25) : q = 25 := by
  obtain ⟨hr, hr2, t, n, f, hadm, hq, hmodel⟩ := hC.lie
  obtain ⟨e⟩ := barInf_equiv_bar2 hC.memL hL225
  by_cases ht : t = .PSL
  · subst ht
    by_cases hn : n = 2
    · subst hn
      obtain ⟨r', f', hr', hr2', h25, hf', hmodel'⟩ := hL225
      have hmodel_bar2 : CFSG.Blueprint.LieModel (Bar2 L) .PSL 2 r f :=
        hmodel.of_mulEquiv e
      have hpow : r ^ f = r' ^ f' :=
        CFSG.GH74.GLS.EvenSelP.pow_eq_of_lieModel hr hr2 hr' hr2' hmodel_bar2 hmodel'
      rw [hq, hpow, ← h25]
    · exact (hK (Bar2 L) .PSL n r f 25 hr2 (Or.inr hn) hadm (hmodel.of_mulEquiv e) hL225).elim
  · exact (hK (Bar2 L) t n r f 25 hr2 (Or.inl ht) hadm (hmodel.of_mulEquiv e) hL225).elim

end SeventeenFourteen

theorem seventeen_fourteen (D : Data G)
    (𝔉 : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Prop)
    (V₀ V L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q)
    (h127 : R127 D) (h117 : C117 D V₀ V) (h17_7 : R17_7At D V₀ V L r q hC)
    (h17_10 : R17_10At D V₀ V L r q hC)
    (h17_11 : R17_11At D V₀ V L r q hC)
    (h17_13 : R17_13At D 𝔉 V₀ V L r q hC)
    (hK : K_LieModelNotL2) :
    R17_14At D 𝔉 V₀ V L r q hC := by
  have hL1 : barSub V₀ V hC.hyp125.isElemAbelian L ≠ ⊥ :=
    barSub_ne_bot_of_uniqueMax h127 hC.hyp125 h117 hC.memL h17_7.1
  let m := mBar D.M V₀ V hC.hyp125.isElemAbelian
  let i := iL17_12 D 𝔉 r q L
  let b := bBar (conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian
  have hk1 : 1 ≤ D.k := TwelveShort.one_le_k D
  have hk2 : D.k ≤ 2 := TwelveSeven.k_le_two D
  have hi3 : i ≤ 3 := SeventeenFourteen.i_le_three_of_R17_13 h17_13
  have hb2 : b ≤ 2 := SeventeenFourteen.b_le_two_of_R17_11 h17_11 hL1
  have hk' : (D.k : ℕ∞) ≤ 2 := by exact_mod_cast hk2
  have hb' : (b : ℕ∞) ≤ 2 := by exact_mod_cast hb2
  have hfirst7 (hm7 : MBarGT D.M V₀ V 7) :
      (m : ℕ∞) > (D.k : ℕ∞) + (i : ℕ∞) + (b : ℕ∞) := by
    have hle : (D.k : ℕ∞) + (i : ℕ∞) + (b : ℕ∞) ≤ (2 : ℕ∞) + 3 + 2 := by
      gcongr
    norm_num at hle ⊢
    exact lt_of_le_of_lt hle (by exact_mod_cast (hC.hyp125.mBarGT_iff_lt_mBar 7).1 hm7)
  have hfirst3 (hm3 : 3 < m) (hk1' : D.k = 1) (hi1 : i = 1) (hb1 : b = 1) :
      (m : ℕ∞) > (D.k : ℕ∞) + (i : ℕ∞) + (b : ℕ∞) := by
    have hk1'' : (D.k : ℕ∞) ≤ 1 := by exact_mod_cast hk1'.le
    have hi1' : i ≤ 1 := by rw [hi1]
    have hb1' : (b : ℕ∞) ≤ 1 := by exact_mod_cast hb1.le
    have hle : (D.k : ℕ∞) + (i : ℕ∞) + (b : ℕ∞) ≤ (1 : ℕ∞) + 1 + 1 := by
      gcongr
    norm_num at hle ⊢
    exact lt_of_le_of_lt hle (by exact_mod_cast hm3)
  rcases h17_10 hL1 with hm7 | ⟨hm3, hL2r | hL225⟩ | h7
  ·
    exact Or.inl (hfirst7 hm7)
  ·
    by_cases hk : D.k = 2
    · exact Or.inr (Or.inl ⟨hk, Or.inl hL2r⟩)
    · have hk1eq : D.k = 1 := by omega
      by_cases hL27 : IsL2Over17 (Bar2 L) 7
      · exact Or.inr (Or.inr hL27)
      · have hb1 : b = 1 := by
          rcases h17_11 hL1 with hb | ⟨hb, hq9⟩
          · exact hb
          · exact absurd (SeventeenFourteen.l2r_case hC hL2r hq9) hL27
        have hi1 : i = 1 := by
          rcases h17_13 with hi | ⟨hq9, hi⟩ | ⟨hq9, hi⟩
          · exact hi
          · exact absurd (SeventeenFourteen.l2r_case hC hL2r hq9) hL27
          · exact absurd (SeventeenFourteen.l2r_case hC hL2r (by omega)) hL27
        exact Or.inl (hfirst3 ((hC.hyp125.mBarGT_iff_lt_mBar 3).1 hm3) hk1eq hi1 hb1)
  ·
    by_cases hk : D.k = 2
    · exact Or.inr (Or.inl ⟨hk, Or.inr hL225⟩)
    · have hk1eq : D.k = 1 := by omega
      have hq25 : q = 25 := SeventeenFourteen.q_eq_25_of_isL2Over17_25 hK hC hL225
      have hqgt : 9 < q := by omega
      have hb1 : b = 1 := by
        rcases h17_11 hL1 with hb | ⟨hb, hq9⟩
        · exact hb
        · omega
      have hi1 : i = 1 := by
        rcases h17_13 with hi | ⟨hq9, hi⟩ | ⟨hq9, hi⟩
        · exact hi
        · omega
        · omega
      exact Or.inl (hfirst3 ((hC.hyp125.mBarGT_iff_lt_mBar 3).1 hm3) hk1eq hi1 hb1)
  ·
    exact Or.inr (Or.inr h7)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

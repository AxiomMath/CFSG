module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEightGraph
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEightGraphTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSixteenLevel
public import CFSG.LocalAnalysis.WeakClosure81.EightOneTrick
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.GapNEHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AltLocal17Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L33ParabolicPairHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L33GraphOuterHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.CGT.Timmesfeld75 (IsTI)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap17_8_graphOuterThree (D : Data G) (V₀ V : Subgroup G) : Prop :=
  Hyp125 D V₀ V → ∀ L : Subgroup G, L ∈ calC D.M → IsL3Odd (Bar2 L) 3 →
    D.T ≤ normalizer (L : Set G) → D.k = 1 →
    (∀ E : Subgroup G, E ≤ L → IsElemAbelian 3 E → Nat.card E = 9 → ¬ Permutes E D.T) →
    Nat.card V₀ = 8 →
    L ⊔ D.T ≤ normalizer (E3.wClos V₀ 0 (innerT17_8 D L) : Set G) →
    ¬ normalizer (E3.wClos V₀ 1 D.T : Set G) ≤ D.M →
    normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M →
    ∀ g : G, conjSubgroup V₀ g ≤ D.T → ¬ conjSubgroup V₀ g ≤ L ⊔ pCoreOf 2 (L ⊔ D.T) →
      Nat.card ↥(conjSubgroup V₀ g ⊓ pCoreOf 2 (L ⊔ D.T)) = 2 → False

theorem normalizer_wClos_le_of_outer_17_8 (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h66 : UC6.R6_6 D) (h88 : W3Thm88 G)
    (hKG : K_L33GraphOuter) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T) (h8 : 8 ≤ Nat.card V₀)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hL3 : IsL3Odd (Bar2 L) 3)
    (hTL : D.T ≤ normalizer (L : Set G)) (hk : D.k = 1) {g : G}
    (hgT : conjSubgroup V₀ g ≤ D.T) (hgout : ¬ conjSubgroup V₀ g ≤ L ⊔ pCoreOf 2 (L ⊔ D.T)) :
    ∃ e : ℕ, 1 ≤ e ∧ e ≤ 2 ∧
      Nat.card V₀ = 2 ^ e * Nat.card ↥(conjSubgroup V₀ g ⊓ pCoreOf 2 (L ⊔ D.T)) ∧
      normalizer (E3.wClos V₀ e D.T : Set G) ≤ D.M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup G := L ⊔ D.T with hHdef
  set Q : Subgroup G := pCoreOf 2 H with hQdef
  set A : Subgroup G := conjSubgroup V₀ g with hAdef
  have hne : V₀ ≠ ⊥ := by
    rintro rfl
    simp at h8
  have hW : InCalV D.M V₀ := hyp125_inCalV hV hne
  have hTI : IsTI V₀ := hyp125_isTI hV hne
  have hVab : IsElemAbelian 2 V₀ := hW.2.2.2
  have hNV : normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hW
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
    by_contra hns
    have h2 : D.k = 2 := (Data.k_eq_two_iff D).2 hns
    omega
  have hHM : H ≤ D.M := sup_le hL.1.le D.sylowM.le
  have hTH : D.T ≤ H := le_sup_right
  have hHQ : H ≤ normalizer (Q : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H)
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hQT : Q ≤ D.T := by
    have hsyl : IsSylowIn 2 D.T H := TwelveShort.isSylowIn_of_le D hTH
    exact CFSG.Quasithin.RonanD33.pCoreOf_le_of_sylow hTH hT2 hsyl.2.2
  have hInt : ∀ X : Subgroup G, X ≤ D.M → IsPGroup 3 X →
      ∀ x : G, x ∉ D.M → X ⊓ conjSubgroup D.M x = ⊥ := fun X hXM hXp x hx => by
    have hx' : x⁻¹ ∉ D.M := fun h => hx (by simpa using D.M.inv_mem h)
    simpa [conjSubgroup] using hsp.inf_map_conj_eq_bot Nat.prime_three hXM hXp x⁻¹ hx'
  have hV0Q : V₀ ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((uc22p22p_le_T_of_inCalV D hW).trans hTH) (hNV ▸ hHM) (CFSG.Open.IsElemAbelian.isPGroup hVab)
  have hgM : g ∉ D.M := by
    intro hg
    apply hgout
    rw [hAdef, conjSubgroup_eq_iff_mem_normalizer.2 (hNV ▸ hg)]
    exact hV0Q.trans le_sup_right
  have hout : ¬ D.T ≤ L ⊔ Q := fun h => hgout (hgT.trans h)
  obtain ⟨Y, hYL, hY3, hYc, hYT, hP⟩ := exists_three_17_8_graph hKG hL hL3 hTL hout
  have hYM : Y ≤ D.M := hYL.trans hL.1.le
  have hYne : Y ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hYc
    omega
  have h16 : Y ⊔ D.T ≤ normalizer (E3.wClos V₀ 0 D.T : Set G) :=
    (twelve_sixteen hTim hcat D h66 h88 hV h8 h93 (p := 3) (by norm_num) (by norm_num) hY3
      (fun x hx _ => hInt Y hYM hY3 x hx)
      (hsp.rankThreeGamma_one_le_of_le Nat.prime_three hY3 hYM) hYT).2
  have hAW : A ≤ E3.wClos V₀ 0 D.T := conjSubgroup_le_wClos_zero hgT
  have hW0T : E3.wClos V₀ 0 D.T ≤ D.T := wClos_zero_le V₀ D.T
  have hAab : IsElemAbelian 2 A := isElemAbelian_conjSubgroup' hVab g
  obtain ⟨hcard4, y, hyY, hnc⟩ := hP (E3.wClos V₀ 0 D.T) A hW0T h16 hAW hAab hgout
  set e : ℕ := E3.mQuot A (A ⊓ Q) with hedef
  have hA2 : IsPGroup 2 A := CFSG.Open.IsElemAbelian.isPGroup hAab
  have hcardA : Nat.card A = 2 ^ e * Nat.card ↥(A ⊓ Q) := E3.card_eq_two_pow_mul hA2 inf_le_left
  have hcardAV : Nat.card A = Nat.card V₀ := E3.card_conjSubgroup V₀ g
  have hpos : 0 < Nat.card ↥(A ⊓ Q) := Nat.card_pos
  have he2 : e ≤ 2 := by
    have h1 : 2 ^ e * Nat.card ↥(A ⊓ Q) ≤ 4 * Nat.card ↥(A ⊓ Q) := hcardA ▸ hcard4
    have h2 : 2 ^ e ≤ 4 := Nat.le_of_mul_le_mul_right h1 hpos
    by_contra h
    have : 2 ^ 3 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have he1 : 1 ≤ e := by
    by_contra h
    have h0 : e = 0 := by omega
    have hAQ : A ⊓ Q = A := (E3.mQuot_eq_zero_iff hA2 inf_le_left).1 h0
    exact hgout (hAQ ▸ inf_le_right |>.trans le_sup_right)
  have hB : A ⊓ Q ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot, mul_one] at hcardA
    have : 2 ^ e ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) he2
    omega
  have hBW : A ⊓ Q ∈ E3.gammaSet V₀ e Q := ⟨inf_le_right, g, inf_le_left, rfl⟩
  have hAQn : A ≤ normalizer (Q : Set G) := (hgT.trans hTH).trans hHQ
  have hyH : y ∈ H := (le_sup_left : L ≤ H) (hYL hyY)
  have hyQ : y ∈ normalizer (Q : Set G) := hHQ hyH
  have hyW : y ∈ normalizer (E3.wClos V₀ 0 D.T : Set G) := h16 ((le_sup_left : Y ≤ Y ⊔ D.T) hyY)
  have hPg : IsPGroup 2 ↥(A ⊔ conjSubgroup A y) := by
    refine hT2.to_le (sup_le (hAW.trans hW0T) ?_)
    have h1 : conjSubgroup A y ≤ conjSubgroup (E3.wClos V₀ 0 D.T) y :=
      E3.conjSubgroup_mono_left y hAW
    rw [conjSubgroup_eq_iff_mem_normalizer.2 hyW] at h1
    exact h1.trans hW0T
  have hAC : A ≤ centralizer (E3.cClos V₀ e Q : Set G) :=
    le_centralizer_cClos_of_not_commute hVab hTI ⟨g, rfl⟩ hAQn hyQ hB hBW hPg hnc
  have hnormC : ∀ C : Subgroup G, H ≤ normalizer (C : Set G) →
      H ≤ normalizer (H ⊓ centralizer (C : Set G) : Set G) := by
    intro C hC h hh
    have hHh : h ∈ normalizer (H : Set G) := Subgroup.le_normalizer hh
    have hCh : h ∈ normalizer ((centralizer (C : Set G) : Subgroup G) : Set G) :=
      CFSG.GroupTheory.FT63ChII.le_normalizer_centralizer hC hh
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := H) (K := centralizer (C : Set G))
      ⟨hHh, hCh⟩
  have hHcQ : H ≤ normalizer (E3.cClos V₀ e Q : Set G) :=
    hHQ.trans (E3.normalizer_le_normalizer_cClos (V := V₀) (i := e) Q)
  have hHwQ : H ≤ normalizer (E3.wClos V₀ e Q : Set G) :=
    hHQ.trans (E3.normalizer_le_normalizer_wClos (V := V₀) (i := e) Q)
  have hLC : L ≤ centralizer (E3.cClos V₀ e Q : Set G) := by
    rcases le_pCoreOf_or_le_of_normal_17_8 hL hL3 hTL
      (K := H ⊓ centralizer (E3.cClos V₀ e Q : Set G))
      inf_le_left (hnormC _ hHcQ) with h | h
    · exact absurd ((le_inf (hgT.trans hTH) hAC).trans h |>.trans le_sup_right) hgout
    · exact h.trans inf_le_right
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huW : u ∈ E3.wClos V₀ e Q := E3.le_wClos hBW hu
  have hCQ : H ⊓ centralizer (E3.wClos V₀ e Q : Set G) ≤ Q := by
    rcases le_pCoreOf_or_le_of_normal_17_8 hL hL3 hTL
      (K := H ⊓ centralizer (E3.wClos V₀ e Q : Set G))
      inf_le_left (hnormC _ hHwQ) with h | h
    · exact h
    · exfalso
      have hLA : L ≤ conjSubgroup D.M g := by
        rw [← hNV, E3.conjSubgroup_normalizer]
        intro l hl
        refine centralizer_le_normalizer_conj hTI g hu.1 hu1' ?_
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact (Subgroup.mem_centralizer_iff.mp (h hl).2) u huW
      apply hYne
      rw [← inf_eq_left.2 (hYL.trans hLA)]
      exact hInt Y hYM hY3 g hgM
  have hCT : E3.cClos V₀ e D.T ≤ E3.cClos V₀ e Q := by
    intro x hx
    have hxQ : x ∈ centralizer (E3.wClos V₀ e Q : Set G) :=
      Subgroup.centralizer_le (E3.wClos_mono (V := V₀) (i := e) hQT) hx.2
    exact ⟨hCQ ⟨hTH hx.1, hxQ⟩, hxQ⟩
  have hYC : Y ≤ centralizer (E3.cClos V₀ e D.T : Set G) :=
    (hYL.trans hLC).trans (Subgroup.centralizer_le hCT)
  have hrk : 2 < rk ↥V₀ := TwelveSeven.two_lt_rk_of_card hVab h8
  refine ⟨e, he1, he2, hcardAV ▸ hcardA, ?_⟩
  by_contra hN
  have hbot := inf_centralizer_cClos_eq_bot_of_lt D hW hTI (i := e) (by omega) (X := Y)
    (fun x hx _ => hInt Y hYM hY3 x hx) hN
  exact hYne (by rw [← inf_eq_left.2 hYC]; exact hbot)

theorem gap17_8_graphOuter_of_three (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h66 : UC6.R6_6 D) (h88 : W3Thm88 G)
    (h126 : R126 D) (h861 : W3Lem86_1 G) (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS)
    (hKG : K_L33GraphOuter) {V₀ V : Subgroup G}
    (h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T)
    (hThree : Gap17_8_graphOuterThree D V₀ V) : Gap17_8_graphOuter D V₀ V := by
  intro hV L hL hL3 hTL hk hE9 h8 hN h1
  have hne : V₀ ≠ ⊥ := by
    rintro rfl
    simp at h8
  have hW : InCalV D.M V₀ := hyp125_inCalV hV hne
  have hTI : IsTI V₀ := hyp125_isTI hV hne
  have hVab : IsElemAbelian 2 V₀ := hW.2.2.2
  rw [wClos_zero_eq_iSup hVab]
  refine iSup₂_le fun g hgT => ?_
  by_contra hgout
  obtain ⟨e, he1, he2, hcard, hNe⟩ :=
    normalizer_wClos_le_of_outer_17_8 hTim hcat D h66 h88 hKG hV h93 h8 hL hL3 hTL hk hgT hgout
  obtain rfl | rfl : e = 1 ∨ e = 2 := by omega
  · exact h1 hNe
  · by_cases h8eq : Nat.card V₀ = 8
    · have h2 : Nat.card ↥(conjSubgroup V₀ g ⊓ pCoreOf 2 (L ⊔ D.T)) = 2 := by
        rw [h8eq] at hcard
        omega
      exact hThree hV L hL hL3 hTL hk hE9 h8eq hN h1 hNe g hgT hgout h2
    · have hcardV : Nat.card V₀ = 2 ^ mSub V₀ :=
        card_eq_two_pow_mSub (CFSG.Open.IsElemAbelian.isPGroup hVab)
      have h16 : 16 ≤ Nat.card V₀ := by
        rw [hcardV] at h8 h8eq ⊢
        have h3 : 3 ≤ mSub V₀ := by
          by_contra h
          have : 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have h4 : 4 ≤ mSub V₀ := by
          by_contra h
          have : mSub V₀ = 3 := by omega
          rw [this] at h8eq
          exact h8eq rfl
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) h4
      have hm4 : 4 ≤ mSub V₀ := by
        by_contra h
        have : 2 ^ mSub V₀ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      obtain ⟨H₀, hmin⟩ := hV.exists_hyp124Min
      have h0 := isCalH0_of_min D hV hmin h5_11 h5_13 h66 h861 (by omega) hTim hcat
      have hV7 := TwelveSeven.hyp7_of_inCalV D hW hTI h8
      have hrk : D.k + 2 < rk ↥V₀ := by
        rw [hk]
        have : mSub V₀ = rk ↥V₀ := rfl
        omega
      exact normalizer_wClos_not_le_of_isCalH0 D h126 hmin hW hV7 h0 hrk hNe

section Certificates


theorem seventeen_eight_of_three
    {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h880 : F08.R880 D)
    (h17_1 : R17_1At D V₀ V hC.hyp125)
    (h17_7 : R17_7_1At D V₀ V L r q hC) (h127 : R127 D) (h117 : C117 D V₀ V)
    (hK8 : Inputs1719.K_U33AutE8)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (h86 : W3Lem86_1 G) (h88 : W3Thm88 G)
    (h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T)
    (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) (hThree : Gap17_8_graphOuterThree D V₀ V)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) (h77 : Inputs1719.W4Lem7_7)
    (hKL : Inputs1719.K_L33AutE8)
    (h411 : W4Lem4_11Prime) (h869 : F08.R869 D)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D) (h1114 : R1114 D)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h183 : W3Thm183 G) (h111 : W3Thm111 G) (h126 : R126 D) (h618 : W3_6_18 G)
    (h416 : Inputs1719.W4Lem4_16) :
    R17_8At D V₀ V L r q hC :=
  seventeen_eight_of_outer hC h880 h17_1 h17_7 h127 h117 Inputs1719.k_U33Local_holds
    Inputs1719.k_L33Local_holds Inputs1719.k_U33SThreePair_holds hK8 hTim hcat h86 h88
    Inputs1719.k_L33ParabolicPair_holds
    (gap17_8_graphOuter_of_three hTim hcat D h66 h88 h126 h86 h5_11 h5_13
      Inputs1719.k_L33GraphOuter_holds h93 hThree)
    h1669 h77 hKL h411 h869 hx h61 h66 h1114 h162 hTor h1482 h183 h111 h126 h618 h93 h416

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

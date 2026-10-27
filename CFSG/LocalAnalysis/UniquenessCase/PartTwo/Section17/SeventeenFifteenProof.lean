module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFourteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.VZeroSmall17
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenNotCartan
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosure
public import CFSG.LocalAnalysis.WeakClosure81.InFSqPrimeTwoGroup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenPair
public import CFSG.CGT.T75H.L2Case
public import CFSG.Quasithin.H13.A5W1618f
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenB
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase (fundPred)
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isL3_one_of_isL2Over17_seven {X : Type} [Group X] (h : IsL2Over17 X 7) : IsL3 X 1 := by
  have hodd : IsL2Odd X 7 := isL2Odd_seven_of_isL2Over17_seven h
  have hsc : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 7 1 :=
    LieModel.statedClassicalModel_of_ne_zero (by norm_num) hodd
  have h32 : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 1 :=
    CFSG.CGT.T75H.statedClassicalModel_psl_three_two_of_psl_two_seven hsc
  exact Or.inl ⟨by decide, h32⟩

theorem k_eq_one_of_three_conj (D : Data G) (h82 : F08.R82 D) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hL7 : IsL2Over17 (Bar2 L) 7) {x y : G} (hx : x ∈ D.M) (hy : y ∈ D.M)
    (hxL : L.map (MulAut.conj x).toMonoidHom ≠ L)
    (hyL : L.map (MulAut.conj y).toMonoidHom ≠ L)
    (hyx : L.map (MulAut.conj y).toMonoidHom ≠ L.map (MulAut.conj x).toMonoidHom) :
    D.k = 1 := by
  have hL3 : IsL3 (Bar2 L) 1 := isL3_one_of_isL2Over17_seven hL7
  have hMx : D.M.map (MulAut.conj x).toMonoidHom = D.M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hx)
  have hMy : D.M.map (MulAut.conj y).toMonoidHom = D.M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hy)
  have hLx : L.map (MulAut.conj x).toMonoidHom ∈ calC D.M :=
    UC6S846.calC_map D.M _ hMx hL
  have hLy : L.map (MulAut.conj y).toMonoidHom ∈ calC D.M :=
    UC6S846.calC_map D.M _ hMy hL
  have hLx3 : IsL3 (Bar2 (L.map (MulAut.conj x).toMonoidHom)) 1 :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.isL3_bar2_map_conj (MulAut.conj x) hL3
  have hLy3 : IsL3 (Bar2 (L.map (MulAut.conj y).toMonoidHom)) 1 :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.isL3_bar2_map_conj (MulAut.conj y) hL3
  exact s16c1614_k_eq_one_of_sp D
    (h82 _ (hyp81_of_three hL hLx hLy hxL.symm hyL.symm hyx.symm hL3 hLx3 hLy3))

@[expose] def Gap17_15_P (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  IsL2Over17 (Bar2 L) 7 → D.k = 1 →
    ∀ x ∈ D.M, ∀ y ∈ D.M, L.map (MulAut.conj x).toMonoidHom ≠ L →
      L.map (MulAut.conj y).toMonoidHom ≠ L →
      L.map (MulAut.conj y).toMonoidHom ≠ L.map (MulAut.conj x).toMonoidHom →
    (∃ X : Subgroup G, F11.InP11 D X) ∨
      CFSG.Quasithin.F6.IsPGL2 7 (Bar2 (L ⊔ NTL17 D L))

@[expose] def Gap17_15_paraTwo (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  IsL2Over17 (Bar2 L) 7 → Nat.card V₀ ≤ 4

@[expose] def Gap17_15_paraSix (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  IsL2Over17 (Bar2 L) 7 → V₀ = ⊥ → D.k = 2 →
    mBar D.M V₀ V hC.hyp125.isElemAbelian = 4 → False

@[expose] def Gap17_15_pair (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  IsL2Over17 (Bar2 L) 7 →
    ∃ H₁ H₂ : Subgroup G,
      D.T ≤ H₁ ∧ H₁ ≤ D.M ∧ D.T ≤ H₂ ∧ H₂ ≤ D.M ∧ L ≤ H₁ ⊔ H₂ ⊔ D.T ∧
        CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₁ ∧
        CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₂ ∧
        (∀ g : G, g ∉ D.M → ¬ twoResidual H₁ ≤ conjSubgroup D.M g) ∧
        (∀ g : G, g ∉ D.M → ¬ twoResidual H₂ ≤ conjSubgroup D.M g) ∧
        UniqueMax D.M (H₁ ⊔ H₂ ⊔ D.T)

@[expose] def Gap17_15_pairOuter (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  IsL2Over17 (Bar2 L) 7 → ¬ IsL2Over17 (Bar2 (L ⊔ D.T)) 7 →
    ∃ H₁ H₂ : Subgroup G,
      D.T ≤ H₁ ∧ H₁ ≤ D.M ∧ D.T ≤ H₂ ∧ H₂ ≤ D.M ∧ L ≤ H₁ ⊔ H₂ ⊔ D.T ∧
        CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₁ ∧
        CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₂ ∧
        (∀ g : G, g ∉ D.M → ¬ twoResidual H₁ ≤ conjSubgroup D.M g) ∧
        (∀ g : G, g ∉ D.M → ¬ twoResidual H₂ ≤ conjSubgroup D.M g) ∧
        UniqueMax D.M (H₁ ⊔ H₂ ⊔ D.T)

@[expose] def Gap17_15_paraTwoOuter (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  IsL2Over17 (Bar2 L) 7 → ¬ IsL2Over17 (Bar2 (L ⊔ D.T)) 7 → Nat.card V₀ ≤ 4

theorem gap17_15_pair_inner (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) (h17_7 : R17_7At D V₀ V L r q hC)
    (hKL0 : K_L27Local) (h7 : IsL2Over17 (Bar2 L) 7)
    (hYs : IsL2Over17 (Bar2 (L ⊔ D.T)) 7) :
      ∃ H₁ H₂ : Subgroup G,
        D.T ≤ H₁ ∧ H₁ ≤ D.M ∧ D.T ≤ H₂ ∧ H₂ ≤ D.M ∧ L ≤ H₁ ⊔ H₂ ⊔ D.T ∧
          CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₁ ∧
          CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₂ ∧
          (∀ g : G, g ∉ D.M → ¬ twoResidual H₁ ≤ conjSubgroup D.M g) ∧
          (∀ g : G, g ∉ D.M → ¬ twoResidual H₂ ≤ conjSubgroup D.M g) ∧
          UniqueMax D.M (H₁ ⊔ H₂ ⊔ D.T) := by
  obtain ⟨X₁, X₂, hX₁L, hX₂L, hX₁c, hX₂c, hperm₁, hperm₂, hLgen⟩ :=
    exists_pair_of_bar2_l2 D hC.memL h7 hYs hKL0
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hC.memL.1
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hX₁p : IsPGroup 3 X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁c]; norm_num)
  have hX₂p : IsPGroup 3 X₂ := IsPGroup.of_card (n := 1) (by rw [hX₂c]; norm_num)
  have hInf : ∀ g : G, g ∉ D.M → ¬ twoResidual (X₁ ⊔ D.T) ≤ conjSubgroup D.M g := by
    intro g hg hle
    have hXle : X₁ ≤ twoResidual (X₁ ⊔ D.T) :=
      le_twoResidual_of_odd_prime_card le_sup_left Nat.prime_three (by norm_num) hX₁c
    have hXg : X₁ ≤ conjSubgroup D.M g := hXle.trans hle
    have h3dvd : 3 ∣ Nat.card ↥(L ⊓ conjSubgroup D.M g) := by
      have hXleLinf : X₁ ≤ L ⊓ conjSubgroup D.M g := le_inf hX₁L hXg
      have hcard : Nat.card X₁ ∣ Nat.card ↥(L ⊓ conjSubgroup D.M g) :=
        Subgroup.card_dvd_of_le hXleLinf
      rwa [hX₁c] at hcard
    have hg' : g⁻¹ ∉ D.M := fun h => hg (by simpa using D.M.inv_mem h)
    refine h17_7.2 h7 g⁻¹ hg' ⟨Nat.prime_three, ?_⟩
    simpa [conjSubgroup] using h3dvd
  have hInf₂ : ∀ g : G, g ∉ D.M → ¬ twoResidual (X₂ ⊔ D.T) ≤ conjSubgroup D.M g := by
    intro g hg hle
    have hXle : X₂ ≤ twoResidual (X₂ ⊔ D.T) :=
      le_twoResidual_of_odd_prime_card le_sup_left Nat.prime_three (by norm_num) hX₂c
    have hXg : X₂ ≤ conjSubgroup D.M g := hXle.trans hle
    have h3dvd : 3 ∣ Nat.card ↥(L ⊓ conjSubgroup D.M g) := by
      have hXleLinf : X₂ ≤ L ⊓ conjSubgroup D.M g := le_inf hX₂L hXg
      have hcard : Nat.card X₂ ∣ Nat.card ↥(L ⊓ conjSubgroup D.M g) :=
        Subgroup.card_dvd_of_le hXleLinf
      rwa [hX₂c] at hcard
    have hg' : g⁻¹ ∉ D.M := fun h => hg (by simpa using D.M.inv_mem h)
    refine h17_7.2 h7 g⁻¹ hg' ⟨Nat.prime_three, ?_⟩
    simpa [conjSubgroup] using h3dvd
  have hH₁M : X₁ ⊔ D.T ≤ D.M := sup_le (hX₁L.trans hLM) hTM
  have hH₂M : X₂ ⊔ D.T ≤ D.M := sup_le (hX₂L.trans hLM) hTM
  have hgen : L ≤ (X₁ ⊔ D.T) ⊔ (X₂ ⊔ D.T) ⊔ D.T := by
    have hEq : (X₁ ⊔ D.T) ⊔ (X₂ ⊔ D.T) ⊔ D.T = X₁ ⊔ X₂ ⊔ D.T := by ac_rfl
    rw [hEq]
    exact hLgen
  have hU : UniqueMax D.M ((X₁ ⊔ D.T) ⊔ (X₂ ⊔ D.T) ⊔ D.T) :=
    uc22p22u_uniqueMax_mono D hgen (sup_le (sup_le hH₁M hH₂M) hTM) h17_7.1
  exact ⟨X₁ ⊔ D.T, X₂ ⊔ D.T, le_sup_right, hH₁M, le_sup_right, hH₂M, hgen,
    CFSG.LocalAnalysis.WeakClosure81.inFSq_one_of_prime_mul_two_group X₁ D.T 3
      Nat.prime_three (by norm_num) hX₁c hT2 hperm₁,
    CFSG.LocalAnalysis.WeakClosure81.inFSq_one_of_prime_mul_two_group X₂ D.T 3
      Nat.prime_three (by norm_num) hX₂c hT2 hperm₂,
    hInf, hInf₂, hU⟩

theorem gap17_15_pair_of_inputs (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) (h17_7 : R17_7At D V₀ V L r q hC)
    (hKL0 : K_L27Local) (hOuter : Gap17_15_pairOuter D V₀ V L r q hC) :
    Gap17_15_pair D V₀ V L r q hC := by
  intro h7
  by_cases hYs : IsL2Over17 (Bar2 (L ⊔ D.T)) 7
  · exact gap17_15_pair_inner D V₀ V L r q hC h17_7 hKL0 h7 hYs
  · exact hOuter h7 hYs

theorem barInf_isL2Over17_at_q (hK : K_LieModelNotL2) {D : Data G} {V₀ V L : Subgroup G}
    {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q)
    (hL2 : IsL2Over17 (Bar2 L) r ∨ IsL2Over17 (Bar2 L) 25)
    (hnot7 : ¬ IsL2Over17 (Bar2 L) 7) : IsL2Over17 (BarInf L) q ∧ 9 < q := by
  rcases hL2 with hL2r | hL25
  · obtain ⟨hr, hr2, t, n, f, hadm, hq, hmodel⟩ := hC.lie
    have hif : IsL2Over17 (BarInf L) r := SeventeenFourteen.barInf_isL2Over17 hC.memL hL2r
    have htn : t = .PSL ∧ n = 2 := by
      by_contra hne
      rw [not_and_or] at hne
      exact hK (BarInf L) t n r f r hr2 hne hadm hmodel hif
    obtain ⟨ht, hn⟩ := htn
    rw [ht, hn] at hmodel
    have hif0 := hif
    obtain ⟨r', f', hr', hr2', hrq, hf', hmodel'⟩ := hif
    have hpow : r ^ f = r' ^ f' :=
      CFSG.GH74.GLS.EvenSelP.pow_eq_of_lieModel hr hr2 hr' hr2' hmodel hmodel'
    have hrlf : r ^ f = r := by rw [← hrq] at hpow; exact hpow
    have hf1 : f = 1 := by
      rcases Nat.eq_zero_or_pos f with h0 | h0
      · exfalso
        rw [h0, pow_zero] at hrlf
        have hr1 : 1 < r := hr.one_lt
        omega
      · by_contra hf1
        have h2 : 2 ≤ f := by omega
        have hlt : r ^ 1 < r ^ f := Nat.pow_lt_pow_right hr.one_lt h2
        rw [hrlf] at hlt
        rw [pow_one] at hlt
        exact lt_irrefl r hlt
    have hqr : q = r := by rw [hq, hf1, pow_one]
    refine ⟨hqr.symm ▸ hif0, ?_⟩
    rw [hqr]
    have h3 : r ≠ 3 := by
      rintro rfl
      exact not_isL2Over17_three (BarInf L) hif0
    have h5 : r ≠ 5 := fun h5 => hC.not_l2_five (h5 ▸ hif0)
    have h7 : r ≠ 7 := by
      rintro rfl
      obtain ⟨e⟩ := SeventeenFourteen.barInf_equiv_bar2 hC.memL hL2r
      exact hnot7 (isL2Over17_of_mulEquiv e.symm hif0)
    by_contra hle
    have hrle : r ≤ 9 := by omega
    interval_cases r
    · exact absurd hr (by norm_num)
    · exact absurd hr (by norm_num)
    · exact hr2 rfl
    · exact h3 rfl
    · exact absurd hr (by norm_num)
    · exact h5 rfl
    · exact absurd hr (by norm_num)
    · exact h7 rfl
    · exact absurd hr (by norm_num)
    · exact absurd hr (by norm_num)
  · have hq25 : q = 25 := SeventeenFourteen.q_eq_25_of_isL2Over17_25 hK hC hL25
    have hif : IsL2Over17 (BarInf L) 25 := SeventeenFourteen.barInf_isL2Over17 hC.memL hL25
    exact ⟨hq25.symm ▸ hif, by omega⟩


theorem card_vzero_le_four_of_w3Lem915 (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h66 : UC6.R6_6 D)
    (h86 : W3Lem86_1 G) (h88 : W3Thm88 G) (h126 : R126 D) (h915 : W3Lem915 G)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) {N L L₁ L₂ : Subgroup G}
    (hTN : D.T ≤ N) (hNV : N ≤ normalizer (V₀ : Set G)) (hNL : N = D.T ⊔ L)
    (hLperf : L = CFSG.Quasithin.perfectCore (L ⊔ CFSG.Open.pCoreOf 2 N))
    (hψ : ∃ (Z : Type) (_ : Group Z) (ψ : ↥N →* Z), Function.Surjective ψ ∧
      (∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 N) ∧
      CFSG.IsComponent ((L.subgroupOf N).map ψ) ∧ IsL3 ↥((L.subgroupOf N).map ψ) 1)
    (hL₁ : L₁ = L) (hL₂ : ∃ t ∈ D.T, L₂ = conjSubgroup L t) (hne : L₁ ≠ L₂)
    (hall : ∀ t ∈ D.T, conjSubgroup L t = L₁ ∨ conjSubgroup L t = L₂)
    (hX : ∃ X : Subgroup G, IsSylowIn 3 X N ∧
      X ⊓ L₁ ∈ CFSG.LocalAnalysis.WeakClosure81.calP V₀ ∧
      X ⊓ L₂ ∈ CFSG.LocalAnalysis.WeakClosure81.calP V₀)
    (hU : UniqueMax D.M N) : Nat.card V₀ ≤ 4 := by
  by_contra h4
  have hV₀p : IsPGroup 2 V₀ := CFSG.Open.IsElemAbelian.isPGroup h.pairFacts.elemAbelian₀
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hV₀p
  rw [hm] at h4
  have h8 : 8 ≤ Nat.card V₀ := by
    rw [hm]
    have hm3 : 3 ≤ m := by
      by_contra h
      apply h4
      have hm2 : m ≤ 2 := by omega
      calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
        _ = 4 := by norm_num
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
  have hne0 : V₀ ≠ ⊥ := by
    rintro rfl
    simp at h8
  have hW : InCalV D.M V₀ := hyp125_inCalV h hne0
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V₀ := hyp125_isTI h hne0
  have h9 : CFSG.LocalAnalysis.WeakClosure81.Hyp9 V₀ D.T :=
    hyp9_of_hyp125 hTim hcat D h h8
  have hN : normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hW
  have h1 : ¬ normalizer (E3.wClos V₀ 1 D.T : Set G) ≤ D.M :=
    twelve_seven_three_one hTim hcat D h66 h88 h.2 hW hTI h8
      (fun z hz hzc hz1 => hyp125_centralizer_le h hne0 hz hzc hz1)
  obtain ⟨X, hX1, hXP1, hXP2⟩ := hX
  rcases h915 V₀ D.T N L h9 hTN hNV hNL hLperf hψ L₁ L₂ hL₁ hL₂ hne hall
    X hX1 hXP1 hXP2 with h2 | h2
  · exact h1 (hN ▸ h2)
  · have hNM : N ≤ D.M := by rw [← hN]; exact hNV
    exact twelve_seven_one hTim hcat D h86 h126 h.2 hW hTI h8
      (uc22p22u_uniqueMax_mono D (le_inf hNM h2) inf_le_left hU)

section NotSeven


theorem seventeen_fifteen_of_not_seven (D : Data G)
    (V₀ V L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q)
    (h17_7 : R17_7At D V₀ V L r q hC)
    (h17_10 : R17_10At D V₀ V L r q hC)
    (h17_11 : R17_11At D V₀ V L r q hC)
    (h17_13 : R17_13At D (fundPred q) V₀ V L r q hC)
    (h17_14 : R17_14At D (fundPred q) V₀ V L r q hC)
    (h127 : R127 D) (h117 : C117 D V₀ V) (h111 : W3Thm111 G)
    (hK : K_LieModelNotL2)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D) (h1114 : R1114 D)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) (h183 : W3Thm183 G)
    (h126 : R126 D)
    (hnot7 : ¬ IsL2Over17 (Bar2 L) 7)
    (hnot : ¬ ((mBar D.M V₀ V hC.hyp125.isElemAbelian : ℕ∞) >
      (D.k : ℕ∞) + iL17_12 D (fundPred q) r q L +
        (bBar (UC22.conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian : ℕ∞))) : False := by
  let m : ℕ := mBar D.M V₀ V hC.hyp125.isElemAbelian
  let i : ℕ∞ := iL17_12 D (fundPred q) r q L
  let b : ℕ := bBar (UC22.conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian
  have hnot' : ¬ (m : ℕ∞) > (D.k : ℕ∞) + i + (b : ℕ∞) := hnot
  have hL1 : barSub V₀ V hC.hyp125.isElemAbelian L ≠ ⊥ :=
    barSub_ne_bot_of_uniqueMax h127 hC.hyp125 h117 hC.memL h17_7.1
  have hk2 : D.k = 2 := by
    rcases h17_14 with hgt | ⟨hk, -⟩ | h7
    · exact absurd hgt hnot'
    · exact hk
    · exact absurd h7 hnot7
  have hL2 : IsL2Over17 (Bar2 L) r ∨ IsL2Over17 (Bar2 L) 25 := by
    rcases h17_14 with hgt | ⟨-, h2⟩ | h7
    · exact absurd hgt hnot'
    · exact h2
    · exact absurd h7 hnot7
  have hq : IsL2Over17 (BarInf L) q ∧ 9 < q :=
    barInf_isL2Over17_at_q hK hC hL2 hnot7
  have hb1 : b = 1 := by
    rcases h17_11 hL1 with h1 | ⟨h2, hq9⟩
    · exact h1
    · omega
  have hi1 : i = 1 := by
    rcases h17_13 with h1 | ⟨hq9, h2⟩ | ⟨hq9, h3⟩
    · exact h1
    · omega
    · omega
  have hm3 : 3 < m := by
    rcases h17_10 hL1 with h7 | ⟨h3, -⟩ | h7
    · have h : 7 < m := by
        rw [show m = mBar D.M V₀ V hC.hyp125.isElemAbelian from rfl]
        exact (hC.hyp125.mBarGT_iff_lt_mBar 7).1 h7
      omega
    · have h : 3 < m := by
        rw [show m = mBar D.M V₀ V hC.hyp125.isElemAbelian from rfl]
        exact (hC.hyp125.mBarGT_iff_lt_mBar 3).1 h3
      omega
    · exact absurd h7 hnot7
  have hm4 : m = 4 := by
    have h1 : (m : ℕ∞) ≤ (D.k : ℕ∞) + i + (b : ℕ∞) := not_lt.mp hnot'
    have h2 : (m : ℕ∞) ≤ (D.k : ℕ∞) + 1 + (b : ℕ∞) := by simpa only [hi1] using h1
    have h3 : m ≤ D.k + 1 + b := by
      refine ENat.coe_le_coe.mp ?_
      simpa only [Nat.cast_add, Nat.cast_one] using h2
    omega
  have hP : P17_12_1 r q L := Or.inl hq.1
  have hmemΔ : D.T ⊔ L ∈ Delta17_12 D (fundPred q) r q L := by
    unfold Delta17_12
    rw [dif_pos hP]
    refine ⟨1, D.M.one_mem, ?_⟩
    congr 1
    ext x
    simp [MulAut.conj_apply]
  have hUc : UniqueMax D.M (UC22.conjClosure D.M L) :=
    uc22p22u_uniqueMax_mono D (TwelveTwentyThree.le_conjClosure D.M L)
      (TwelveTwentyThree.conjClosure_le hC.memL.1.le) h17_7.1
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hC.memL.1
  by_cases hV0 : V₀ = ⊥
  ·
    have h1 := twelve_twentyThree_one D hx h61 h126 h111 hC.hyp125 hV0
      hC.memL.1 hC.memL.2.2 hL1 hUc
    have h2 : m ≤ b + D.k := h1
    omega
  ·
    let Δ : Finset (Subgroup G) := {D.T ⊔ L}
    have hΔ : ∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M := by
      intro H hH
      simp only [Δ, Finset.mem_singleton] at hH
      subst hH
      exact ⟨le_sup_left, sup_le D.sylowM.le hLM⟩
    have hΔU : UniqueMax D.M (⨆ H ∈ Δ, H) := by
      rw [← Finset.sup_eq_iSup]
      have hsup : Δ.sup (fun H => H) = D.T ⊔ L := by simp [Δ]
      rw [hsup]
      exact uc22p22u_uniqueMax_mono D le_sup_right (sup_le D.sylowM.le hLM) h17_7.1
    have hι : ∀ H ∈ Δ, CFSG.LocalAnalysis.WeakClosure81.InFSq (1 : ℕ) H := by
      intro H hH
      simp only [Δ, Finset.mem_singleton] at hH
      subst hH
      have hfm : fIndexMax (Delta17_12 D (fundPred q) r q L) ≤ (1 : ℕ∞) :=
        le_of_eq (show iL17_12 D (fundPred q) r q L = (1 : ℕ∞) from hi1)
      exact (fIndexMax_le_iff.mp hfm) (D.T ⊔ L) hmemΔ
    have hO2 : ∀ H ∈ Δ, ∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g := by
      intro H hH g hg
      simp only [Δ, Finset.mem_singleton] at hH
      subst hH
      exact twoResidual_not_le_conjSubgroup_of_uniqueMax D.maxLocal h17_7.1
        (CFSG.Quasithin.H13.A5.le_twoResidual_of_perfect hC.memL.2.1 le_sup_right) hg
    have hmax : Δ.sup (fun _ => 1) = 1 := by simp [Δ]
    have hmk : D.k + 1 < m := by omega
    have hbound := twelve_twentyThree_three_two D hx h61 h66 h127 h1114 h162 hTor h1482
      h183 hC.hyp125 hV0 hC.memL.1 hC.memL.2.2 hL1 hΔ hΔU (fun _ => 1) hι hO2 hmax hmk
    have h2 : m ≤ b + 1 := hbound
    omega

end NotSeven

theorem seventeen_fifteen_of_seven (D : Data G)
    (V₀ V L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h17_7 : R17_7At D V₀ V L r q hC)
    (h17_11 : R17_11At D V₀ V L r q hC)
    (h127 : R127 D) (h117 : C117 D V₀ V) (h111 : W3Thm111 G)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D) (h1114 : R1114 D)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) (h183 : W3Thm183 G)
    (h126 : R126 D)
    (hparaTwo : Gap17_15_paraTwo D V₀ V L r q hC)
    (hpair : Gap17_15_pair D V₀ V L r q hC)
    (hparaSix : Gap17_15_paraSix D V₀ V L r q hC)
    (h7 : IsL2Over17 (Bar2 L) 7) : False := by
  classical
  have hL1 : barSub V₀ V hC.hyp125.isElemAbelian L ≠ ⊥ :=
    barSub_ne_bot_of_uniqueMax h127 hC.hyp125 h117 hC.memL h17_7.1
  have hV4 : Nat.card V₀ ≤ 4 := hparaTwo h7
  have hm3 : 3 < mBar D.M V₀ V hC.hyp125.isElemAbelian :=
    (hC.hyp125.mBarGT_iff_lt_mBar 3).1 (h1669 hV4)
  have hb2 : bBar (UC22.conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian ≤ 2 :=
    SeventeenFourteen.b_le_two_of_R17_11 h17_11 hL1
  obtain ⟨H₁, H₂, hT1, hH1M, hT2, hH2M, hLle, hIF1, hIF2, hO2₁, hO2₂, hU⟩ := hpair h7
  have hk : D.k = 1 ∨ D.k = 2 := by
    have h1 := TwelveShort.one_le_k D
    have h2 := TwelveSeven.k_le_two D
    omega
  have hUc : UniqueMax D.M (UC22.conjClosure D.M L) :=
    uc22p22u_uniqueMax_mono D (TwelveTwentyThree.le_conjClosure D.M L)
      (TwelveTwentyThree.conjClosure_le hC.memL.1.le) h17_7.1
  have hU' : UniqueMax D.M (H₁ ⊔ H₂) := by
    have hTeq : H₁ ⊔ H₂ ⊔ D.T = H₁ ⊔ H₂ := by
      rw [sup_eq_left.mpr (hT1.trans le_sup_left)]
    rwa [hTeq] at hU
  by_cases hV0 : V₀ = ⊥
  ·
    have hm := twelve_twentyThree_one D hx h61 h126 h111 hC.hyp125 hV0
      hC.memL.1 hC.memL.2.2 hL1 hUc
    rcases hk with hk1 | hk2
    · omega
    · have hmle : mBar D.M V₀ V hC.hyp125.isElemAbelian ≤
          bBar (UC22.conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian + D.k := hm
      have hm4 : mBar D.M V₀ V hC.hyp125.isElemAbelian = 4 := by omega
      have hbge2 : 2 ≤ bBar (UC22.conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian := by
        omega
      have hb2' : bBar (UC22.conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian = 2 :=
        le_antisymm hb2 hbge2
      exact hparaSix h7 hV0 hk2 hm4
  ·
    let Δ : Finset (Subgroup G) := {H₁, H₂}
    have hΔ : ∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M := by
      intro H hH
      simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hH
      rcases hH with rfl | rfl
      · exact ⟨hT1, hH1M⟩
      · exact ⟨hT2, hH2M⟩
    have hΔU : UniqueMax D.M (⨆ H ∈ Δ, H) := by
      rw [← Finset.sup_eq_iSup]
      have hsup : Δ.sup (fun H => H) = H₁ ⊔ H₂ := by simp [Δ]
      rw [hsup]
      exact hU'
    have hι : ∀ H ∈ Δ, CFSG.LocalAnalysis.WeakClosure81.InFSq (1 : ℕ) H := by
      intro H hH
      simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hH
      rcases hH with rfl | rfl
      · exact hIF1
      · exact hIF2
    have hO2 : ∀ H ∈ Δ, ∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g := by
      intro H hH g hg
      simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hH
      rcases hH with rfl | rfl
      · exact hO2₁ g hg
      · exact hO2₂ g hg
    have hmax : Δ.sup (fun _ => 1) = 1 := by simp [Δ]
    have hmk : D.k + 1 < mBar D.M V₀ V hC.hyp125.isElemAbelian := by omega
    have hbound := twelve_twentyThree_three_two D hx h61 h66 h127 h1114 h162 hTor h1482 h183
      hC.hyp125 hV0 hC.memL.1 hC.memL.2.2 hL1 hΔ hΔU (fun _ => 1) hι hO2 hmax hmk
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end

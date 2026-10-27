module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoApply
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoStab
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoBar2
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7FiftyEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenL3WrA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSixtyOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24R
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24Beta

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr CFSG.Quasithin.H13 CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Finite

variable {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}

theorem Case167_7F.tensor_realizes (h : Case167_7F D V₀ V hV) :
    (tensorPairModel SL32 SL32).RealizesMod (fstarBar D.M V₀ V hV) := by
  obtain ⟨K, _, hfin, hK, hmodel⟩ := h.2.1
  have hK2 : Nat.card K = 2 := by simpa using hK
  exact tensorNat_realizes_zmod_two hK2 hmodel

theorem Case167_7F.mBarGT_two (hH : Hyp125 D V₀ V) (h : Case167_7F D V₀ V hV) :
    MBarGT D.M V₀ V 2 := by
  have h3 : 3 ≤ E3.mParam (Mbar D.M V₀ V hV) :=
    H44_L3Wreath_mParam h.tensor_realizes (mbar_le_normalizer_fstarBar D.M V₀ V hV)
  exact (hH.pairFacts.mBarGT_iff_lt_mBar 2).2 h3

theorem Case167_7F.aBar_eq_two (h : Case167_7F D V₀ V hV) : aBar D.M V₀ V hV = 2 :=
  L3Wreath_aParam_eq_two h.tensor_realizes (fstarBar_le_mbar D.M V₀ V hV)
    (mbar_le_normalizer_fstarBar D.M V₀ V hV)

theorem Case167_7F.le_rMV (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} (hH : Hyp16 D V₀ V)
    (h : Case167_7F D V₀ V hV) : ((mSub V₀ + 3 : ℕ) : ℕ∞) ≤ rMV D.M V := by
  have hP := hH.hyp125.pairFacts
  have hsig : D.sig = {7} := h.2.2
  have h7s : 7 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 7
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hT : (tensorPairModel SL32 SL32).RealizesMod
      (barSub V₀ V hV (fstarBarPre D.M V₀ V hV)) := by
    rw [barSub_fstarBarPre]
    exact h.tensor_realizes
  have hnorm : Mbar D.M V₀ V hV ≤
      normalizer (barSub V₀ V hV (fstarBarPre D.M V₀ V hV) : Set (MulAut (Vtil V₀ V hV))) := by
    rw [barSub_fstarBarPre]
    exact mbar_le_normalizer_fstarBar D.M V₀ V hV
  obtain ⟨B, hBM, hBp, hBc, hB3⟩ :=
    exists_noncyclic_seven_fix hV hMs (hx.three_le 7 h7s) hT hnorm
  have hBst : B ≤ stabTil V₀ V := hBM.trans hMs
  have hBV₀ : B ≤ centralizer (V₀ : Set G) :=
    le_centralizer_of_mSub_le_two (by norm_num) (by norm_num) hP.elemAbelian₀
      hH.small hBp (hBst.trans (stabTil_le_normalizer₀ V₀ V))
  have hV₀B : V₀ ≤ centralizer (B : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.1 (hBV₀ hb) v hv).symm
  have h1 := rk_add_rk_fixV_barSub_le hV hP.le (by norm_num : Nat.Prime 7) (by norm_num) hBp
    hBst hV₀B
  have h2 := rk_inf_centralizer_le_rMV D h61 h7s hBM hBp hBc hV
  have h3 : mSub V₀ + 3 ≤ rk ↥(V ⊓ centralizer (B : Set G)) := by
    have h4 : mSub V₀ = rk ↥V₀ := rfl
    omega
  exact le_trans (by exact_mod_cast h3) h2

theorem Case167_7F.sixteen_fiftyEight (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} (hH : Hyp16 D V₀ V)
    (h : Case167_7F D V₀ V hV) :
    ((mSub V₀ + 3 : ℕ) : ℕ∞) ≤ rMV D.M V ∧ (3 : ℕ∞) ≤ deltaInf D.M V :=
  ⟨h.le_rMV D hx h61 hH, succ_le_deltaInf_of_mBarGT D hH.hyp125 (h.mBarGT_two hH.hyp125)⟩

theorem Case167_7F.sixteen_fiftyNine (D : Data G) (hx : DataExt D) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h21 : R1621 D) (h22 : R1622 D) (h129 : R129_1 D)
    (h61 : UC6.R6_1 D) {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} (hH : Hyp16 D V₀ V)
    (h7 : Case167_7F D V₀ V hV) :
    ⁅E3.wClos V 0 D.T, V⁆ = ⊥ ∧ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  obtain ⟨hr, hδ⟩ := h7.sixteen_fiftyEight D hx h61 hH
  have hP := hH.hyp125.pairFacts
  have h3le : ∀ p ∈ D.sig, 3 ≤ CFSG.pRank p ↥D.M := fun p hp => by
    rw [UC6.groupPRank_eq_pRank]
    exact hSg.three_le p hp
  have hW : E3.wClos V 0 D.T ≤ centralizer (V : Set G) := by
    refine E3.wClos_le_of_forall fun A hA => ?_
    have hAM : A ∈ E3.gammaSet V 0 D.M := E3.gammaSet_mono D.sylowM.le hA
    obtain ⟨hAT, g, hAg, -⟩ := hA
    have hAMle : A ≤ D.M := hAT.trans D.sylowM.le
    have hr3 : ((3 + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V :=
      le_trans (by exact_mod_cast (by omega : 3 + mSub V₀ ≤ mSub V₀ + 3)) hr
    by_cases hbar : barSub V₀ V hV A = ⊥
    · have hi0 : ((0 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
        lt_of_lt_of_le (by exact_mod_cast (by omega : 0 + mSub V₀ < 3 + mSub V₀)) hr3
      obtain ⟨-, hc, -⟩ := sixteen_twentyThree_one D h22 hH hAM hAg hi0
      have hCt := (WeakClosure81.barSub_eq_bot_iff hV hP.le_normalizer hP.le_normalizer₀
        hAMle).1 hbar
      have hVc : V ≤ centralizer (A : Set G) := fun v hv => hc v hv fun a ha => by
        have hcm := WeakClosure81.centralizesMod_of_mem_cTilde hV hP.le_normalizer
          hP.le_normalizer₀ (hCt ha) v hv
        have e : ⁅v, a⁆ = (a * v * a⁻¹ * v⁻¹)⁻¹ := by group
        rw [e]
        exact V₀.inv_mem hcm
      exact Subgroup.le_centralizer_iff.1 hVc
    · have hmem := barSub_mem_calABar_of_gammaSet_zero D hSg h1219 h21 h22 hH hr3
        (by exact_mod_cast hδ) hAM hbar
      have h3 : 3 ≤ aBar D.M V₀ V hV := E3.le_aParam_of_mem_aSet (by norm_num) hmem
      have h2 := h7.aBar_eq_two
      omega
  exact ⟨Subgroup.commutator_eq_bot_iff_le_centralizer.2 hW,
    fifteen_thirteen_a D h129 h61 hSg.nonempty h3le hH.hyp125 hW⟩

theorem Case167_7F.sixteen_sixty (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h66 : UC6.R6_6 D) (h127 : R127 D) (h1114 : R1114 D) (h183 : W3Thm183 G)
    {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} (hH : Hyp16 D V₀ V)
    (h7 : Case167_7F D V₀ V hV) (hN : normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M) :
    V₀ = ⊥ := by
  by_contra hne
  exact twelve_ten_one_zero D hx h61 h66 h127 h1114 h183 hH.hyp125 hne
    (h7.mBarGT_two hH.hyp125) hN

theorem Case167_7F.trichotomy (D : Data G) (h126 : R126 D) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (hx : DataExt D) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G}
    {hV : IsElemAbelian 2 V} (hH : Hyp16 D V₀ V) (h7 : Case167_7F D V₀ V hV) :
    ¬ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M ∨
      ¬ centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M ∨ (calO2 D.k D.M V₀ V).Nonempty :=
  trichotomy_of_lt D h126 hH.hyp125
    (Sixteen24.k_lt_rParam_of_hyp125 D hSg h1219 hx h61 hH.hyp125)
    (lt_of_le_of_lt (by exact_mod_cast TwelveSeven.k_le_two D)
      (Sixteen24.lt_betaN_zero_of_mBarGT D hH.hyp125 (h7.mBarGT_two hH.hyp125)))

theorem Case167_7F.sixteen_sixtyOne (D : Data G) {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hH : Hyp16 D V₀ V) (h7 : Case167_7F D V₀ V hV)
    (h24 : ¬ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M ∨
      ¬ centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M ∨ (calO2 D.k D.M V₀ V).Nonempty)
    (hN : normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M) (h0 : V₀ = ⊥) :
    calO2 2 D.M V₀ V = ∅ ∧ ¬ centralizer (E3.cClos V 2 D.T : Set G) ≤ D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst h0
  have hm2 : MBarGT D.M ⊥ V 2 := h7.mBarGT_two hH.hyp125
  have hk : D.k ≤ 2 := TwelveSeven.k_le_two D
  have hrk : 2 < rk ↥V := by
    have h8 := hH.hyp125.eight_le_card_of_bot
    have hcard := card_eq_two_pow_mSub hV.isPGroup
    by_contra hle
    have h2 : 2 ^ mSub V ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hle)
    omega
  refine ⟨calO2_eq_empty_of_mBarGT D hH.hyp125 le_rfl hm2, fun hcen => ?_⟩
  have hcc : E3.cClos V 2 D.T ≤ E3.cClos V D.k D.T :=
    inf_le_inf_left _ (Subgroup.centralizer_le
      (SetLike.coe_subset_coe.2 (wClos_le_wClos_of_le hV hk hrk D.T)))
  rcases h24 with h | h | h
  · exact h hN
  · exact h ((Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hcc)).trans hcen)
  · rw [calO2_eq_empty_of_mBarGT D hH.hyp125 hk hm2] at h
    exact Set.not_nonempty_empty h

theorem Case167_7F.sixteen_sixtyTwo (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h119 : R119W D) (h145 : Thm145 D) {V₀ V : Subgroup G}
    {hV : IsElemAbelian 2 V} (hH : Hyp16 D V₀ V) (h7 : Case167_7F D V₀ V hV) (h0 : V₀ = ⊥) :
    ∃ z : G, V ⊓ centralizer (D.T : Set G) = Subgroup.zpowers z ∧ orderOf z = 2 ∧
      centralizer ({z} : Set G) ≤ D.M := by
  subst h0
  obtain ⟨X₀, _, hX₀, ⟨φ⟩⟩ := h7.1
  haveI : Finite X₀ := s16c7_finite_of_psi φ
  have hT := h7.tensor_realizes
  have hsig : D.sig = {7} := h7.2.2
  have h7s : (7 : ℕ) ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 7
  have hP := hH.hyp125.pairFacts
  have hMV : D.M ≤ normalizer (V : Set G) := hP.le_normalizer
  have hMs : D.M ≤ stabTil ⊥ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hH11 := Hyp125.hyp11 h127 hH.hyp125
  have hnorm := mbar_le_normalizer_fstarBar D.M ⊥ V hV
  have hAM := fstarBar_le_mbar D.M ⊥ V hV
  obtain ⟨K₁, K₂, hK₁, hK₂, hne, hbarA, hMN, hL₁, hL₂, hn₁, hn₂⟩ :=
    s16c7_lift_factors D h119 hV hMV hH11 hAM hnorm hX₀ φ
  have hK₁M : K₁ ≤ D.M := uc22p22a_le_of_isSubnormal hK₁.1
  have hK₂M : K₂ ≤ D.M := uc22p22a_le_of_isSubnormal hK₂.1
  obtain ⟨hsh₁, -⟩ := s16c7_bar2_of_calC hV hMs hK₁M hK₁.2.2 hL₁
  obtain ⟨hsh₂, -⟩ := s16c7_bar2_of_calC hV hMs hK₂M hK₂.2.2 hL₂
  obtain ⟨a, ha⟩ := s16c7_card_of_bar2 hsh₁
  obtain ⟨b, hb⟩ := s16c7_card_of_bar2 hsh₂
  have hA : Nat.card (barSub ⊥ V hV (K₁ ⊔ K₂)) = 168 * 168 := by
    rw [hbarA]
    have h1 : Nat.card ↥(fstarBar D.M ⊥ V hV) = Nat.card (X₀ × X₀) := Nat.card_congr φ.toEquiv
    rw [h1, Nat.card_prod, card_eq_of_isL3 hX₀]
  have hreal : (tensorPairModel SL32 SL32).RealizesMod (barSub ⊥ V hV (K₁ ⊔ K₂)) := by
    rw [hbarA]
    exact hT
  have hMA : Mbar D.M ⊥ V hV ≤
      normalizer (barSub ⊥ V hV (K₁ ⊔ K₂) : Set (MulAut (Vtil ⊥ V hV))) := by
    rw [hbarA]
    exact hnorm
  obtain ⟨z, X, hzV, hz1, hz2, hCT, hCX, hXsyl, hperm⟩ :=
    s16c7_exists_X_z D V hV hMs hK₁M hK₂M hn₁ hMN hA ha hb hreal hMA
  have hC : CFSG.Open.pRank 7 (F11.CTilde D.M ⊥ V) ≤ 1 :=
    uc22p22q_pRank_ctilde_le_one D h61 hH11 (by rw [Subgroup.card_bot]; norm_num) h7s
  have hM7 : CFSG.Open.pRank 7 D.M ≤ 3 := s16c7_pRank_seven_le_three hV hMs hT hnorm hC
  have hrank : CFSG.Open.evenRank G = 3 := s16c7_evenRank_eq_three D hx hsig hM7
  have hH141 : Hyp141 D K₁ K₂ X :=
    ⟨hsig, hrank, hK₁, hK₂, hne, hsh₁, hsh₂, hXsyl, hperm⟩
  have h7dvd := s16c7_seven_dvd_card_centralizer_inf D hx hsig hV hMs hT hnorm hzV
  exact ⟨z, hCT, orderOf_eq_prime hz2 hz1,
    s16c7_centralizer_le_of_thm145 D h145 hH141 hMV hzV hz1 hz2 hCT hCX h7dvd⟩

end Finite

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

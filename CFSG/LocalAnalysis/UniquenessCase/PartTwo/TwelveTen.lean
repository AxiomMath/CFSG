module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEighteenSetting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSixLocal
import CFSG.LocalAnalysis.WeakClosure81.FourteenTwo
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

namespace TwelveTen

theorem not_normalizer_wClos_le (D : Data G) (h66 : UC6.R6_6 D) (h183 : W3Thm183 G)
    (h124 : ∃ H₀ ∈ RankThreeUC.hSet D.T D.M, RankThreeUC.Hyp124 D.M H₀) {V₀ V : Subgroup G}
    (hs : WeakClosureSetting D V₀ V) (hV₀ : V₀ ≠ ⊥) {i : ℕ} (hi : i ≤ 1)
    (hm : MBarGT D.M V₀ V (max 2 (D.k + i))) :
    ¬ normalizer (E3.wClos V i D.T : Set G) ≤ D.M := by
  intro hN
  obtain ⟨H₀, hH₀, h124'⟩ := h124
  obtain ⟨h1, h2⟩ := h183 D V₀ V hs hV₀ H₀ (TwelveSix.w3Hyp171 D h66 hH₀) i hi hN hH₀.2.1
  by_cases hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M
  · have h3 := h1 (TwelveSix.w3Hyp181 D h66 hH₀ hsp)
      (TwelveShort.mBarGT_mono hm (le_max_left _ _))
    rw [TwelveSix.hasCompFactor_calL1_iff] at h3
    exact h124'.1 h3
  · have hk : D.k = 2 := by
      unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
      rw [if_neg hsp]
    have h3 := h2 (TwelveSix.w3Hyp182 D h66 hH₀)
      (TwelveShort.mBarGT_mono hm (le_trans (by omega) (le_max_right _ _)))
    rw [TwelveSix.hasCompFactor_calL0_iff] at h3
    exact h124'.2 hsp h3

theorem le_centralizer_of_card_lt_four {V W E : Subgroup G} (hV : IsPGroup 2 V) (hWV : W ≤ V)
    (hEW : E ≤ normalizer (W : Set G)) (hW4 : Nat.card W < 4) :
    W ≤ centralizer (E : Set G) := by
  obtain ⟨k, hk⟩ := (hV.to_le hWV).exists_card_eq
  have hk1 : k ≤ 1 := by
    by_contra hc
    have h22 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk1 with rfl | rfl
  · rw [pow_zero, Subgroup.card_eq_one] at hk
    rw [hk]
    exact bot_le
  · rw [pow_one] at hk
    rw [Subgroup.le_centralizer_iff]
    exact hEW.trans (CFSG.Semidihedral.Local.normalizer_le_centralizer_of_card_eq_two hk)

theorem exists_card_centralizer_ge_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {V E : Subgroup G}
    (hV : IsPGroup 2 V) (hV4 : 4 ≤ Nat.card V) (hE : IsElemAbelian p E)
    (hEcard : p ^ 3 ≤ Nat.card E) (hEV : E ≤ normalizer (V : Set G)) :
    ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = p ^ 2 ∧
      4 ≤ Nat.card ↥(V ⊓ centralizer (B : Set G)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := by
    intro x
    exact ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨n, hn⟩ := hEp.exists_card_eq
  have hn3 : 3 ≤ n := by
    by_contra hc
    have : p ^ n < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega
  have hcop : Nat.Coprime p (Nat.card V) := by
    obtain ⟨a, ha⟩ := hV.exists_card_eq
    rw [ha]
    exact Nat.Coprime.pow_right a ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes hp hE
    (by rw [hn]; exact Nat.le_self_pow (by omega) p) hEV hcop
  have hEF : ∀ F : Subgroup G, F ≤ E → E ≤ normalizer (F : Set G) := fun F hFE =>
    (le_centralizer_iff_isMulCommutative.2 hE.1).trans
      ((Subgroup.centralizer_le hFE).trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨F, hF, hF4⟩ : ∃ F ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes p E,
      4 ≤ Nat.card ↥(V ⊓ centralizer (F : Set G)) := by
    by_contra hcon
    push Not at hcon
    have hVE : V ≤ centralizer (E : Set G) := by
      rw [← hgen]
      refine iSup₂_le fun F hF => ?_
      exact le_centralizer_of_card_lt_four hV inf_le_left
        (A1a.le_normalizer_inf hEV (A1a.le_normalizer_centralizer (hEF F hF.1))) (hcon F hF)
    obtain ⟨F₀, hF₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) p (n := n - 1)
      (by rw [hn]; exact pow_dvd_pow p (by omega))
    have hF₀mem : F₀.map E.subtype ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes p E := by
      refine ⟨Subgroup.map_subtype_le F₀, ?_⟩
      rw [Subgroup.card_map_of_injective E.subtype_injective, hF₀, hn, ← pow_succ']
      congr 1
      omega
    have hle : V ≤ V ⊓ centralizer ((F₀.map E.subtype : Subgroup G) : Set G) :=
      le_inf le_rfl (hVE.trans (Subgroup.centralizer_le (Subgroup.map_subtype_le F₀)))
    have h1 := hcon _ hF₀mem
    have h2 : Nat.card V ≤ Nat.card ↥(V ⊓ centralizer
        ((F₀.map E.subtype : Subgroup G) : Set G)) := Subgroup.card_le_of_le hle
    omega
  obtain ⟨hFE, hFcard⟩ := hF
  have hFcard' : Nat.card F = p ^ (n - 1) := by
    rw [hn] at hFcard
    have h1 : p ^ n = p * p ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h1] at hFcard
    exact (Nat.eq_of_mul_eq_mul_left hp.pos hFcard).symm
  obtain ⟨B₀, hB₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := F) p (n := 2)
    (by rw [hFcard']; exact pow_dvd_pow p (by omega))
  refine ⟨B₀.map F.subtype, (Subgroup.map_subtype_le B₀).trans hFE, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective F.subtype_injective, hB₀]
  · refine hF4.trans (Subgroup.card_le_of_le (inf_le_inf_left _ ?_))
    exact Subgroup.centralizer_le (Subgroup.map_subtype_le B₀)

theorem one_lt_rMV (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) {V : Subgroup G}
    (hV : InCalV D.M V) (h4 : 4 ≤ Nat.card V) : 1 < rMV D.M V := by
  rw [FourteenTwo.rMV_gt_one_iff]
  intro U hUV hU1
  have hV2 : IsPGroup 2 V := CFSG.Open.IsElemAbelian.isPGroup hV.2.2.2
  obtain ⟨p, hpσ⟩ := hx.sig_nonempty
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  haveI : Fact p.Prime := ⟨hp⟩
  have h3 : 3 ≤ CFSG.Open.pRank p D.M := hx.three_le p hpσ
  obtain ⟨E, hEM, hEel, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp D.M
  obtain ⟨B, hBE, hBcard, hB4⟩ := exists_card_centralizer_ge_four hp hp2 hV2 h4 hEel
    (by rw [hEcard]; exact Nat.pow_le_pow_right hp.pos h3) (hEM.trans hV.2.2.1)
  have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    hEel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩ |> congrArg Subtype.val
  have hBel : IsElemAbelian p B :=
    ⟨⟨⟨fun a b => Subtype.ext (hEab a (hBE a.2) b (hBE b.2))⟩⟩, fun x hx => hEel.2 x (hBE hx)⟩
  have hBnc : ¬ IsCyclic B := uc22p22n_not_isCyclic_of_card hp hBel hBcard.ge
  have hBp : IsPGroup p B := IsPGroup.of_card hBcard
  have hBU : UniqueMax D.M B := h61 p hpσ B (hBE.trans hEM) hBp hBnc
  set W : Subgroup G := U ⊓ centralizer (B : Set G) with hW
  have hWV : W ≤ V := inf_le_left.trans hUV
  have hWne : W ≠ ⊥ := by
    intro hbot
    have hidx := Subgroup.relIndex_mul_card (H := U) (K := V ⊓ centralizer (B : Set G))
    have hinf : U ⊓ (V ⊓ centralizer (B : Set G)) = W := by
      rw [hW, ← inf_assoc, inf_eq_left.2 hUV]
    rw [hinf, hbot, Subgroup.card_bot, mul_one] at hidx
    have hle : U.relIndex (V ⊓ centralizer (B : Set G)) ≤ U.relIndex V :=
      Subgroup.relIndex_le_of_le_right inf_le_left (by
        rw [E3.relIndex_eq_two_pow hV2]; positivity)
    have h2 : U.relIndex V ≤ 2 := by
      rw [E3.relIndex_eq_two_pow hV2]
      calc 2 ^ E3.mQuot V U ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hU1
        _ = 2 := by norm_num
    omega
  have hW2 : IsPGroup 2 W := hV2.to_le hWV
  have hBW : B ≤ normalizer (W : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.le_centralizer_iff]
    exact inf_le_right
  have hNW : normalizer (W : Set G) ≤ D.M := normalizer_le_of_uniqueMax hBU hWne hW2 hBW
  exact (Subgroup.centralizer_le inf_le_left).trans
    ((Subgroup.centralizer_le_normalizer _).trans hNW)

end TwelveTen

open TwelveShort

theorem twelve_ten_one (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D)
    (h127 : R127 D) (h1114 : R1114 D) (h183 : W3Thm183 G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hV₀ : V₀ ≠ ⊥) (hm : MBarGT D.M V₀ V (D.k + 1)) :
    ¬ normalizer (E3.wClos V 1 D.T : Set G) ≤ D.M := by
  have hk : 2 ≤ D.k + 1 := by have := one_le_k D; omega
  exact TwelveTen.not_normalizer_wClos_le D h66 h183 h.2
    (weakClosureSetting_of_hyp125 D hx h61 h127 h1114 h hV₀) hV₀ le_rfl
    (by rwa [max_eq_right hk])

theorem twelve_ten_one_zero (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h66 : UC6.R6_6 D) (h127 : R127 D) (h1114 : R1114 D) (h183 : W3Thm183 G)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (hV₀ : V₀ ≠ ⊥) (hm : MBarGT D.M V₀ V 2) :
    ¬ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hk : D.k + 0 ≤ 2 := by
    unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
    split_ifs <;> norm_num
  exact TwelveTen.not_normalizer_wClos_le D h66 h183 h.2
    (weakClosureSetting_of_hyp125 D hx h61 h127 h1114 h hV₀) hV₀ (Nat.zero_le 1)
    (by rwa [max_eq_left hk])

theorem twelve_ten_two (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D)
    (h111 : W3Thm111 G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (hV₀ : V₀ = ⊥) {i : ℕ}
    (hm : MBarGT D.M V₀ V (D.k + i)) :
    ¬ normalizer (E3.wClos V i D.T : Set G) ≤ D.M ∨
      ¬ centralizer (E3.cClos V (D.k + i) D.T : Set G) ≤ D.M := by
  subst hV₀
  rw [← not_and_or]
  rintro ⟨hN, hC⟩
  rcases h.1 with ⟨hW, -⟩ | ⟨h0, -, -⟩
  · have hV1 : InCalV1 D.M D.T V := hW.1.1
    have hVV : InCalV D.M V := hV1.1
    have hV' : IsElemAbelian 2 V := hVV.2.2.2
    obtain ⟨H₀, hmin⟩ := h.exists_hyp124Min
    have hS : IsSylowIn 2 D.T H₀ := isSylowIn_of_le D hmin.1.1
    have hE : E1.InE D.k H₀ := h126 H₀ hmin
    have hlt : D.k + i < E3.sParam hV' := by
      by_cases hm2 : MBarGT D.M ⊥ V 2
      · exact lt_sParam_of_mBarGT D h111 hV1 hm2 hm
      · have hki : D.k + i = 1 := by
          have h1 := one_le_k D
          by_contra hc
          exact hm2 (mBarGT_mono hm (by omega))
        have hr : ((D.k + i : ℕ) : ℕ∞) < E3.rParam V := by
          have h1 := TwelveTen.one_lt_rMV D hx h61 hVV (by have := hW.1.2.1; omega)
          rw [rMV_eq_rParam_of_inCalV D hVV] at h1
          rw [hki]
          exact_mod_cast h1
        exact E3.lt_sParam_of_lt hV' hr ((mBarGT_bot_iff_lt_mParam_autI D hVV _).1 hm)
    have h611 := six_eleven_three hV' hS hE (i := i) (j := D.k) (by omega)
    rw [Nat.add_comm i D.k] at h611
    apply hmin.1.2.1
    rw [← h611]
    exact sup_le (inf_le_right.trans hC) (inf_le_right.trans hN)
  · exact absurd rfl h0.1.1

theorem twelve_ten (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D)
    (h126 : R126 D) (h127 : R127 D) (h1114 : R1114 D) (h111 : W3Thm111 G) (h183 : W3Thm183 G)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) :
    (V₀ ≠ ⊥ → MBarGT D.M V₀ V (D.k + 1) → ¬ normalizer (E3.wClos V 1 D.T : Set G) ≤ D.M) ∧
      (V₀ = ⊥ → ∀ i : ℕ, MBarGT D.M V₀ V (D.k + i) →
        ¬ normalizer (E3.wClos V i D.T : Set G) ≤ D.M ∨
          ¬ centralizer (E3.cClos V (D.k + i) D.T : Set G) ≤ D.M) :=
  ⟨fun hV₀ hm => twelve_ten_one D hx h61 h66 h127 h1114 h183 h hV₀ hm,
    fun hV₀ _ hm => twelve_ten_two D hx h61 h126 h111 h hV₀ hm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

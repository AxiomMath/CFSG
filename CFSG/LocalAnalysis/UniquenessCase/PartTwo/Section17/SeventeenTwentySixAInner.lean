module

public import CFSG.GroupTheory.AlternatingFive.HomPermFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentySixAProof

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.CGT.Timmesfeld75 (IsTI)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_H17_25_one_inf_normalizer {D : Data G} {V₀ V L : Subgroup G}
    (c : Ctx17_17 D V₀ V L) (hm : 4 < mSub V₀) (hsp : IsStronglyPEmbedded 5 D.M)
    (hU : ∀ X : Subgroup G, X ≤ H17_25_one D V₀ V L c.hyp125.isElemAbelian →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≠ 5 ∧ Nat.card X = p) → UC6.InU D.M X)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T)
    (hAO : ¬ A ≤ pCoreOf 2 (H17_25_one D V₀ V L c.hyp125.isElemAbelian)) :
    IsPGroup 2 ↥(H17_25_one D V₀ V L c.hyp125.isElemAbelian ⊓ normalizer (A : Set G)) := by
  classical
  set H₁ : Subgroup G := H17_25_one D V₀ V L c.hyp125.isElemAbelian with hH₁def
  set Q : Subgroup G := pCoreOf 2 H₁ with hQdef
  have hMn : normalizer (D.M : Set G) = D.M := UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal
  have hH₁M : H₁ ≤ D.M := H17_25_one_le_M c.hyp125 c.mem_calC.1.le
  obtain ⟨-, g, hAgle, hquot⟩ := hA
  have hV0p : IsPGroup 2 V₀ :=
    CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian c.hyp125.pairFacts.elemAbelian₀
  have hAg : A = conjSubgroup V₀ g :=
    (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup hV0p g) hAgle).mp hquot
  have hV0cal : InCalV D.M V₀ := by
    have hV0ne : V₀ ≠ ⊥ := by
      intro hbot
      rw [hbot, mSub, CFSG.Quasithin.rk_bot] at hm
      omega
    rcases c.hyp125.1 with ⟨-, hbot⟩ | ⟨h0, -, -⟩
    · exact absurd hbot hV0ne
    · exact h0.1
  have hNA : normalizer (A : Set G) = conjSubgroup D.M g := by
    rw [hAg]
    change normalizer (V₀.map (MulAut.conj g⁻¹).toMonoidHom) =
      D.M.map (MulAut.conj g⁻¹).toMonoidHom
    rw [← Subgroup.map_normalizer_eq_of_bijective (H := V₀)
      (f := (MulAut.conj g⁻¹).toMonoidHom) (hf := (MulAut.conj g⁻¹).bijective),
      normalizer_eq_of_inCalV D hV0cal]
  have hgM : g ∉ D.M := by
    intro hg
    have hAV0 : A = V₀ := by
      rw [hAg]
      exact CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr
        (c.hyp125.pairFacts.le_normalizer₀ hg)
    refine hAO ?_
    rw [hAV0]
    have hVT : V ≤ D.T :=
      IsSylowIn.le_of_normal (TwelveShort.isSylowIn_of_le D D.sylowM.le) c.hyp125.inCalV.2.1
        ((Subgroup.normal_subgroupOf_iff_le_normalizer c.hyp125.inCalV.2.1).2
          c.hyp125.inCalV.2.2.1)
        (CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian c.hyp125.isElemAbelian)
    refine CFSG.ClassicalGroups.PCoreSection.le_pCoreOf
      ((c.hyp125.pairFacts.le.trans hVT).trans (T_le_H17_25_one c.hyp125)) ?_ hV0p
    intro x hx y hy
    exact (c.hyp125.pairFacts.le_normalizer₀
      (H17_25_one_le_M c.hyp125 c.mem_calC.1.le hx) y).mp hy
  rw [isPGroup_iff_primeFactors_card_subset (p := 2) (by norm_num)]
  intro q hq
  obtain ⟨hqprime, hqdvd, -⟩ := Nat.mem_primeFactors.mp hq
  have hq2 : q = 2 := by
    by_contra hqne
    have hfact : Fact q.Prime := ⟨hqprime⟩
    obtain ⟨z, hzord⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥(H₁ ⊓ normalizer (A : Set G))) q hqdvd
    have hzH : (z : G) ∈ H₁ := (Subgroup.mem_inf.mp z.2).1
    have hzordG : orderOf (z : G) = q := by rw [Subgroup.orderOf_coe, hzord]
    let Y : Subgroup G := Subgroup.zpowers (z : G)
    have hYH : Y ≤ H₁ := Subgroup.zpowers_le.mpr hzH
    have hYcard : Nat.card Y = q := by rw [Nat.card_zpowers, hzordG]
    have hYle : Y ≤ conjSubgroup D.M g := by
      refine Subgroup.zpowers_le.mpr ?_
      rw [← hNA]
      exact (Subgroup.mem_inf.mp z.2).2
    by_cases hq5 : q = 5
    · have h5dvd : 5 ∣ Nat.card ↥(D.M ⊓ D.M.map (MulAut.conj g⁻¹).toMonoidHom) := by
        rw [← hq5, ← hYcard]
        exact Subgroup.card_dvd_of_le (le_inf (hYH.trans hH₁M) hYle)
      exact hsp.2.2 g⁻¹ (fun h => hgM (by simpa using D.M.inv_mem h)) h5dvd
    · have hYU : UC6.InU D.M Y := hU Y hYH ⟨q, hqprime, hqne, hq5, hYcard⟩
      exact ((UC6.inU_iff_not_le hMn).mp hYU).2 g hgM hYle
  subst hq2
  exact Nat.mem_primeFactors.mpr ⟨by norm_num, dvd_rfl, by norm_num⟩

theorem inf_conjSubgroup_eq_bot_of_inU {D : Data G} {X : Subgroup G} (hX : UC6.InU D.M X)
    (hXp : (Nat.card X).Prime) :
    ∀ g : G, g ∉ D.M → X ⊓ conjSubgroup D.M g = ⊥ := by
  have hMn : normalizer (D.M : Set G) = D.M := UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal
  intro g hg
  have hnotle : ¬ X ≤ conjSubgroup D.M g :=
    ((UC6.inU_iff_not_le hMn).mp hX).2 g hg
  by_contra hne
  have hdvd : Nat.card ↥(X ⊓ conjSubgroup D.M g) ∣ Nat.card ↥X :=
    Subgroup.card_dvd_of_le inf_le_left
  have hne1 : Nat.card ↥(X ⊓ conjSubgroup D.M g) ≠ 1 := by
    intro h1
    exact hne (Subgroup.card_eq_one.mp h1)
  rcases (Nat.dvd_prime hXp).mp hdvd with h1 | hcard
  · exact hne1 h1
  · have hYX : X ⊓ conjSubgroup D.M g = X :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq hcard.symm)
    exact hnotle (hYX ▸ inf_le_right)

theorem rankThreeGamma_le_of_inU {D : Data G} {X : Subgroup G} (hX : UC6.InU D.M X)
    (hX3 : Nat.card X = 3) : rankThreeGamma 1 3 X ≤ D.M := by
  have hMn : normalizer (D.M : Set G) = D.M := UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal
  rw [rankThreeGamma]
  refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall ?_
  intro Q hQX hQ3
  have hQne : Q ≠ ⊥ := by
    intro hbot
    obtain ⟨E, hEQ, -, hEcard⟩ := CFSG.SectionRank.exists_pRank (show 1 < 3 by norm_num) Q
    rw [hbot] at hEQ
    have hEbot : E = ⊥ := le_bot_iff.mp hEQ
    have hk : 3 ^ 1 ≤ 3 ^ CFSG.Open.pRank 3 Q :=
      Nat.pow_le_pow_right (by norm_num) hQ3
    rw [← hEcard, hEbot, Subgroup.card_bot] at hk
    norm_num at hk
  have hcardQ : Nat.card ↥Q = 3 := by
    have hdvd : Nat.card ↥Q ∣ 3 := by
      rw [← hX3]
      exact Subgroup.card_dvd_of_le hQX
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (Subgroup.card_eq_one.mp h1) hQne
    · exact h3
  have hQX' : Q = X :=
    Subgroup.eq_of_le_of_card_ge hQX (by rw [hcardQ, hX3])
  rw [hQX']
  exact hX.normalizer_le hMn

theorem map_gammaZero_le_alternatingGroup (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) {D : Data G} {V₀ V L : Subgroup G}
    (c : Ctx17_17 D V₀ V L) (h66 : UC6.R6_6 D) (h88 : W3Thm88 G) (h93 : Thm93 V₀ D.T)
    (hm : 4 < mSub V₀)
    (hU3 : ∀ X : Subgroup G, X ≤ H17_25_one D V₀ V L c.hyp125.isElemAbelian →
      Nat.card X = 3 → UC6.InU D.M X)
    (ψ : ↥(H17_25_one D V₀ V L c.hyp125.isElemAbelian) →* Equiv.Perm (Fin 5))
    (hker : ψ.ker = (pCoreOf 2 (H17_25_one D V₀ V L c.hyp125.isElemAbelian)).subgroupOf
      (H17_25_one D V₀ V L c.hyp125.isElemAbelian))
    (hrange : ψ.range = alternatingGroup (Fin 5) ∨ ψ.range = ⊤)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T) :
    (A.subgroupOf (H17_25_one D V₀ V L c.hyp125.isElemAbelian)).map ψ ≤
      alternatingGroup (Fin 5) := by
  classical
  let H₁ : Subgroup G := H17_25_one D V₀ V L c.hyp125.isElemAbelian
  let Q : Subgroup G := pCoreOf 2 H₁
  have hH₁M : H₁ ≤ D.M := H17_25_one_le_M c.hyp125 c.mem_calC.1.le
  have hTH : D.T ≤ H₁ := T_le_H17_25_one c.hyp125
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hQleT : Q ≤ D.T := pCoreOf_H17_25_one_le_T c
  have hQ2 : IsPGroup 2 Q := CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 H₁
  have hker' : ψ.ker = Q.subgroupOf H₁ := hker
  have hker2 : IsPGroup 2 ψ.ker := by
    rw [hker']
    exact hQ2.comap_subtype
  have h8 : 8 ≤ Nat.card ↥V₀ := by
    have hcardV0 : Nat.card ↥V₀ = 2 ^ mSub V₀ :=
      card_eq_two_pow_mSub c.hyp125.pairFacts.elemAbelian₀.isPGroup
    rw [hcardV0]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hAcopy := hA
  obtain ⟨hAT, gA, hAgle, -⟩ := hAcopy
  rcases hrange with hrange | hrange
  · rw [← hrange]
    exact Subgroup.map_le_range ψ (A.subgroupOf H₁)
  · have hsurj : Function.Surjective ψ := MonoidHom.range_eq_top.mp hrange
    let P : Subgroup (Equiv.Perm (Fin 5)) := (D.T.subgroupOf H₁).map ψ
    have hP2 : IsPGroup 2 P := IsPGroup.map hT2.comap_subtype ψ
    obtain ⟨p, hp⟩ := hP2.nonempty_fixed_point_of_prime_not_dvd_card (Fin 5) (by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      decide)
    obtain ⟨c₀, hc₀3, hc₀1, hc₀p, hc₀prop⟩ :=
      CFSG.GroupTheory.AlternatingFive.exists_three_cycle_moving_swaps p
    have hc₀ord : orderOf c₀ = 3 := by
      have hdvd : orderOf c₀ ∣ 3 := orderOf_dvd_of_pow_eq_one hc₀3
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hc₀1
      · exact h3
    obtain ⟨y, hy⟩ := hsurj c₀
    have hy3ker : y ^ 3 ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_pow, hy, hc₀3]
    obtain ⟨k, hk⟩ := hker2.exists_orderOf_eq_pow ⟨y ^ 3, hy3ker⟩
    rw [← Subgroup.orderOf_coe] at hk
    have hdvdy : orderOf y ∣ 3 * 2 ^ k := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_mul, ← hk]
      exact pow_orderOf_eq_one (y ^ 3)
    have h3y : 3 ∣ orderOf y := by
      have h := orderOf_map_dvd ψ y
      rwa [hy, hc₀ord] at h
    let d : ℕ := orderOf y / 3
    have hordy : orderOf y = 3 * d := by
      change orderOf y = 3 * (orderOf y / 3)
      exact (Nat.mul_div_cancel' h3y).symm
    have hdvd2k : d ∣ 2 ^ k := by
      rw [hordy] at hdvdy
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvdy
    obtain ⟨e, -, hde⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2k
    let z : ↥H₁ := y ^ d
    have hzord : orderOf z = 3 := by
      change orderOf (y ^ (orderOf y / 3)) = 3
      exact orderOf_pow_orderOf_div (x := y) (n := 3) (orderOf_pos y).ne' h3y
    have hzψ : ψ z = c₀ ^ d := by
      change ψ (y ^ d) = c₀ ^ d
      rw [map_pow, hy]
    have hd2eq : d ^ 2 = 4 ^ e := by
      rw [hde, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
    have h4pow : ∀ e : ℕ, (4 : ℕ) ^ e ≡ 1 [MOD 3] := by
      intro e
      induction e with
      | zero => decide
      | succ e ih =>
          rw [pow_succ]
          simpa using ih.mul (by decide : (4 : ℕ) ≡ 1 [MOD 3])
    have hdvd3 : 3 ∣ d ^ 2 - 1 := by
      rw [hd2eq]
      exact (Nat.modEq_iff_dvd' (Nat.one_le_pow e 4 (by norm_num))).mp (h4pow e).symm
    obtain ⟨m, hm⟩ := hdvd3
    have hdpos : 1 ≤ d ^ 2 := by
      rw [hde]
      exact Nat.one_le_pow 2 (2 ^ e) (by positivity)
    have hd2 : d ^ 2 = 3 * m + 1 := by omega
    have hc₀d2 : c₀ ^ (d ^ 2) = c₀ := by
      rw [hd2, pow_add, pow_mul, hc₀3, one_pow, one_mul, pow_one]
    let x : ↥H₁ := z ^ d
    have hxψ : ψ x = c₀ := by
      calc ψ x = (ψ z) ^ d := by
            change ψ (z ^ d) = (ψ z) ^ d
            rw [map_pow]
        _ = (c₀ ^ d) ^ d := by rw [hzψ]
        _ = c₀ ^ (d * d) := by rw [pow_mul]
        _ = c₀ ^ (d ^ 2) := by rw [pow_two]
        _ = c₀ := hc₀d2
    let X : Subgroup G := Subgroup.zpowers (z : G)
    have hXH : X ≤ H₁ := Subgroup.zpowers_le.mpr z.2
    have hXcard : Nat.card X = 3 := by
      change Nat.card (Subgroup.zpowers (z : G)) = 3
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hzord]
    have hXprime : (Nat.card X).Prime := by
      rw [hXcard]
      norm_num
    have hInU : UC6.InU D.M X := hU3 X hXH hXcard
    have hXM : ∀ g : G, g ∉ D.M → V₀ ≤ conjSubgroup D.M g → X ⊓ conjSubgroup D.M g = ⊥ :=
      fun g hg _ => inf_conjSubgroup_eq_bot_of_inU hInU hXprime g hg
    have hΓ : rankThreeGamma 1 3 X ≤ D.M := rankThreeGamma_le_of_inU hInU hXcard
    have hxX : (x : G) ∈ X := by
      change (z : G) ^ d ∈ Subgroup.zpowers (z : G)
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers (z : G)) d
    have hXinfT : X ⊓ D.T = ⊥ := by
      refine Subgroup.inf_eq_bot_of_coprime ?_
      rw [hXcard]
      obtain ⟨n, hn⟩ := hT2.exists_card_eq
      rw [hn]
      exact Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)
    let S : Subgroup G :=
      ((MulAction.stabilizer (Equiv.Perm (Fin 5)) p).comap ψ).map H₁.subtype
    have hTS : D.T ≤ S := by
      intro t ht
      change t ∈ ((MulAction.stabilizer (Equiv.Perm (Fin 5)) p).comap ψ).map H₁.subtype
      refine Subgroup.mem_map_of_mem H₁.subtype (x := ⟨t, hTH ht⟩) ?_
      rw [Subgroup.mem_comap]
      refine (MulAction.mem_stabilizer_iff).mpr ?_
      have hmem : ψ ⟨t, hTH ht⟩ ∈ P := Subgroup.mem_map_of_mem ψ ht
      have hfix := (MulAction.mem_fixedPoints.mp hp) ⟨ψ ⟨t, hTH ht⟩, hmem⟩
      simpa using hfix
    have hXS : X ≤ S := by
      refine Subgroup.zpowers_le.mpr ?_
      change (z : G) ∈ ((MulAction.stabilizer (Equiv.Perm (Fin 5)) p).comap ψ).map H₁.subtype
      refine Subgroup.mem_map_of_mem H₁.subtype (x := z) ?_
      rw [Subgroup.mem_comap, hzψ]
      exact Subgroup.pow_mem _ ((MulAction.mem_stabilizer_iff).mpr hc₀p) d
    have hcardcomap : 5 * Nat.card ↥((MulAction.stabilizer (Equiv.Perm (Fin 5)) p).comap ψ) =
        Nat.card ↥H₁ := by
      have hSindex : ((MulAction.stabilizer (Equiv.Perm (Fin 5)) p).comap ψ).index = 5 := by
        rw [Subgroup.index_comap_of_surjective
          (H := MulAction.stabilizer (Equiv.Perm (Fin 5)) p) (f := ψ) hsurj]
        exact CFSG.Quasithin.SteinbergBS.index_stabilizer_perm_five p
      have h := Subgroup.index_mul_card
        (H := (MulAction.stabilizer (Equiv.Perm (Fin 5)) p).comap ψ)
      rw [hSindex] at h
      exact h
    have hkerK : ψ.ker ≤ D.T.subgroupOf H₁ := by
      rw [hker']
      exact Subgroup.subgroupOf_mono H₁ hQleT
    have hkercard : Nat.card ↥ψ.ker = Nat.card ↥Q := by
      rw [hker']
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (CFSG.openPCoreOf_le 2 H₁)).toEquiv
    have hKcard : Nat.card ↥(D.T.subgroupOf H₁) = Nat.card ↥D.T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
    have hrel := Subgroup.relIndex_mul_card ψ.ker (D.T.subgroupOf H₁)
    rw [Subgroup.relIndex_ker, inf_eq_left.mpr hkerK] at hrel
    have hoddT : Odd (D.T.relIndex H₁) :=
      Nat.not_even_iff_odd.mp (by
        rw [even_iff_two_dvd]
        exact (TwelveShort.isSylowIn_of_le D hTH).not_dvd_relIndex)
    have hcardKmap : Nat.card ↥((D.T.subgroupOf H₁).map ψ) = 8 := by
      obtain ⟨i, hi⟩ := (IsPGroup.map hT2.comap_subtype ψ).exists_card_eq
      have hidx : ((D.T.subgroupOf H₁).map ψ).index = D.T.relIndex H₁ := by
        rw [Subgroup.index_map_eq (H := D.T.subgroupOf H₁) (f := ψ) hsurj hkerK]
        rfl
      have hmul := Subgroup.index_mul_card (H := (D.T.subgroupOf H₁).map ψ)
      rw [Nat.card_perm, Nat.card_fin] at hmul
      have hPcard : Nat.card ↥((D.T.subgroupOf H₁).map ψ) = 2 ^ i := hi
      rw [hidx, hPcard] at hmul
      norm_num at hmul
      obtain ⟨j, hj⟩ := hoddT
      rw [hj] at hmul
      have hi6 : i ≤ 6 := by
        have hdvd : 2 ^ i ∣ 120 := ⟨2 * j + 1, by rw [mul_comm]; exact hmul.symm⟩
        have hle : 2 ^ i ≤ 120 := Nat.le_of_dvd (by norm_num) hdvd
        by_contra h
        have h7 : 7 ≤ i := by omega
        have hpow : 2 ^ 7 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h7
        norm_num at hpow
        omega
      have hi3 : i = 3 := by
        interval_cases i <;> norm_num at hmul <;> omega
      rw [hPcard, hi3]
      norm_num
    have hcardT : Nat.card ↥D.T = 8 * Nat.card ↥Q := by
      rw [hcardKmap, hkercard, hKcard] at hrel
      exact hrel.symm
    have hcardH1 : Nat.card ↥H₁ = 120 * Nat.card ↥Q := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (ψ.ker)
      rw [hkercard] at h
      have hquot : Nat.card (↥H₁ ⧸ ψ.ker) = 120 := by
        have hq := Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
        rw [hrange, Subgroup.card_top, Nat.card_perm, Nat.card_fin] at hq
        norm_num at hq
        exact hq
      rw [hquot] at h
      exact h
    have hcardS : Nat.card ↥S = 3 * Nat.card ↥D.T := by
      have hcardS' : Nat.card ↥S =
          Nat.card ↥((MulAction.stabilizer (Equiv.Perm (Fin 5)) p).comap ψ) :=
        Subgroup.card_map_of_injective
          (K := (MulAction.stabilizer (Equiv.Perm (Fin 5)) p).comap ψ) H₁.subtype_injective
      omega
    have hcsup : Nat.card ↥(X ⊔ D.T) ≤ Nat.card ↥X * Nat.card ↥D.T := by
      have h := Subgroup.card_le_of_le (sup_le hXS hTS)
      rw [hcardS] at h
      rw [hXcard]
      exact h
    have hXT : (X : Set G) * (D.T : Set G) = (D.T : Set G) * (X : Set G) :=
      CFSG.Quasithin.H.L3Wr.permute_of_card hXinfT hcsup
    have h16 := twelve_sixteen hTim hcat D h66 h88 c.hyp125 h8 h93 (p := 3) (by norm_num)
      (by norm_num) (IsPGroup.of_card (hXcard.trans (pow_one 3).symm)) hXM hΓ hXT
    intro τ hτ
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hτ
    by_contra hτA
    have haA : (a : G) ∈ A := ha
    have haT : (a : G) ∈ D.T := hAT haA
    have hAea : IsElemAbelian 2 A :=
      (E3.isElemAbelian_conjSubgroup c.hyp125.pairFacts.elemAbelian₀ gA).mono hAgle
    have ha2 : (a : G) ^ 2 = 1 := hAea.2 (a : G) haA
    have hτ2 : (ψ a) ^ 2 = 1 := by
      calc (ψ a) ^ 2 = ψ (a ^ 2) := (map_pow ψ a 2).symm
        _ = 1 := by rw [show a ^ 2 = 1 from Subtype.ext (by simpa using ha2), map_one]
    have hmemP : ψ a ∈ P :=
      Subgroup.mem_map_of_mem ψ (show a ∈ D.T.subgroupOf H₁ from haT)
    have hτp : ψ a • p = p := by
      have hfix := (MulAction.mem_fixedPoints.mp hp) ⟨ψ a, hmemP⟩
      simpa using hfix
    have hxN : (x : G) ∈ normalizer (E3.wClos V₀ 0 D.T : Set G) :=
      h16.2 (Subgroup.mem_sup_left hxX)
    have haW : (a : G) ∈ E3.wClos V₀ 0 D.T := E3.le_wClos hA haA
    have hconjW : (x : G)⁻¹ * (a : G) * (x : G) ∈ E3.wClos V₀ 0 D.T := by
      have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) (a : G)).mp haW
      simpa using h
    have hprodW : ((a * x⁻¹ * a * x : ↥H₁) : G) ∈ E3.wClos V₀ 0 D.T := by
      have h := (E3.wClos V₀ 0 D.T).mul_mem haW hconjW
      simpa [mul_assoc] using h
    have hmemMap : ψ (a * x⁻¹ * a * x) ∈ (((E3.wClos V₀ 0 D.T).subgroupOf H₁).map ψ) :=
      Subgroup.mem_map_of_mem ψ
        (show a * x⁻¹ * a * x ∈ (E3.wClos V₀ 0 D.T).subgroupOf H₁ from hprodW)
    have hW0T : E3.wClos V₀ 0 D.T ≤ D.T := E3.wClos_le 0 D.T
    have hW2 : IsPGroup 2 (((E3.wClos V₀ 0 D.T).subgroupOf H₁).map ψ) :=
      IsPGroup.map (hT2.to_le hW0T).comap_subtype ψ
    have hvalue : ψ (a * x⁻¹ * a * x) = ψ a * (c₀⁻¹ * ψ a * c₀) := by
      simp only [map_mul, map_inv, hxψ]
      group
    have hA2 := hc₀prop (ψ a) hτ2 (by simpa using hτp) hτA
    have hodd : Odd (orderOf (ψ (a * x⁻¹ * a * x))) := by
      rw [hvalue]
      have hdvd : orderOf (ψ a * (c₀⁻¹ * ψ a * c₀)) ∣ 3 :=
        orderOf_dvd_of_pow_eq_one hA2.1
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hA2.2
      · rw [h3]
        norm_num
    have hone : ψ (a * x⁻¹ * a * x) = 1 := by
      by_contra hne
      have hne' : (⟨ψ (a * x⁻¹ * a * x), hmemMap⟩ : ↥(((E3.wClos V₀ 0 D.T).subgroupOf H₁).map ψ))
          ≠ 1 := fun h => hne (congrArg Subtype.val h)
      have hnot2 : ¬ 2 ∣ orderOf
          (⟨ψ (a * x⁻¹ * a * x), hmemMap⟩ : ↥(((E3.wClos V₀ 0 D.T).subgroupOf H₁).map ψ)) := by
        rw [← Subgroup.orderOf_coe]
        exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
      exact hnot2 (hW2.dvd_orderOf hne')
    exact hA2.2 (hvalue ▸ hone)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end

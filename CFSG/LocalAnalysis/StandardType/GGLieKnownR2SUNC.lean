module

import all CFSG.LieType.Universal.Unitary.Roots
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2FixedPointOdd
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSU
public import CFSG.Timmesfeld.Transvection.ModelSUCore
public import CFSG.Timmesfeld.Transvection.ModelSUTheta
public import CFSG.Timmesfeld.Transvection.ModelSUPerp
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Timmesfeld.RankOne

public section

namespace CFSG.StandardType.LieKnownR2.PSU

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Unitary
open CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg
open CFSG.LieType.BorelTits (unitaryInvolution)
open Matrix CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.Transvection
open CFSG.Timmesfeld.Transvection.ModelRank

private theorem l10su4_toStd_weylAction_long {n : ℕ}
    (w : (coxeterMatrix (isFiniteType_cartan n)).Group)
    {γ : Fin (n / 2) → ℤ} {i : Fin n} (hi : i ≠ Fin.rev i) (h : toStd n γ = 2 • weight n i) :
    ∃ j : Fin n, j ≠ Fin.rev j ∧
      toStd n (weylAction (isFiniteType_cartan n) w γ) = 2 • weight n j := by
  induction w using (coxeterMatrix (isFiniteType_cartan n)).toCoxeterSystem.simple_induction_left
    with
  | one =>
    rw [map_one, Module.End.one_apply]
    exact ⟨i, hi, h⟩
  | mul_simple_left w k ih =>
    obtain ⟨j, hj, hj'⟩ := ih
    refine ⟨levelPerm k j, levelPerm_ne_rev k hj, ?_⟩
    rw [weylAction_mul_apply, weylAction_simple, toStd_reflection, hj', stdRefl_nsmul,
      weight_levelPerm]

private theorem l10su4_exists_highest {n : ℕ} (hn : 2 ≤ n) :
    ∃ θ : Fin (n / 2) → ℤ,
      toStd n θ = 2 • weight n (lowIdx (⟨0, by omega⟩ : Fin (n / 2))) := by
  have hm : 0 < n / 2 := by omega
  by_cases he : Even n
  · refine ⟨fun a => if a.val + 1 = n / 2 then 1 else 2, ?_⟩
    funext a
    rw [toStd_apply_of_even he, Pi.smul_apply, weight_lowIdx]
    simp only [Pi.single_apply, nsmul_eq_mul]
    by_cases h0 : a.val = 0
    · have : a = ⟨0, hm⟩ := Fin.ext h0
      subst this
      simp
      split_ifs <;> simp_all <;> omega
    · have h1 : 0 < a.val := Nat.pos_of_ne_zero h0
      have hne : ¬ (a = ⟨0, hm⟩) := fun e => h0 (by rw [e])
      simp [h1, hne]
      split_ifs <;> simp_all <;> omega
  · refine ⟨fun _ => 2, ?_⟩
    funext a
    simp only [toStd, he, ite_false, Pi.smul_apply, weight_lowIdx, Pi.single_apply, nsmul_eq_mul]
    by_cases h0 : a.val = 0
    · have : a = ⟨0, hm⟩ := Fin.ext h0
      subst this
      simp
    · have h1 : 0 < a.val := Nat.pos_of_ne_zero h0
      have hne : ¬ (a = ⟨0, hm⟩) := fun e => h0 (by rw [e])
      simp [h1, hne]

private theorem l10su4_exists_weight_of_ggLongRoot {F : Type} [Field F] [Finite F] {f : ℕ}
    [CharP F 2] (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ}
    {β : Fin (rootDatum hc n).rank → ℤ} (hβ : β ∈ (rootDatum hc n).roots)
    (hl : GGLongRoot (rootDatum hc n) β) :
    ∃ i : Fin n, i ≠ Fin.rev i ∧ toStd n β = 2 • weight n i := by
  have hn : 2 ≤ n := by
    have hβ' : β ∈ roots (isFiniteType_cartan n) (divisible n) := hβ
    rcases hβ' with ⟨_, l, _⟩ | ⟨_, l, _, _⟩ <;> have := l.isLt <;> omega
  obtain ⟨w, γ₀, hγ₀, hmax, rfl⟩ := hl
  have hγ' : γ₀ ∈ roots (isFiniteType_cartan n) (divisible n) := hγ₀
  have hm : 0 < n / 2 := by omega
  obtain ⟨θ, hθ⟩ := l10su4_exists_highest hn
  have hθr : θ ∈ roots (isFiniteType_cartan n) (divisible n) := by
    rw [roots_eq]
    exact Or.inr (Or.inl ⟨lowIdx ⟨0, hm⟩, lowIdx_ne_rev _ _, hθ⟩)
  have hle : ht (ι := Fin (n / 2)) θ ≤ ht (ι := Fin (n / 2)) γ₀ := hmax θ hθr
  have hθ2 : ht (ι := Fin (n / 2)) θ = (n : ℤ) - 1 := by
    have h := two_mul_ht θ
    have h0 : (lowIdx (⟨0, hm⟩ : Fin (n / 2))).val = 0 := rfl
    rw [hθ, map_nsmul, lv_weight, h0] at h
    simp only [nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_zero, mul_zero, sub_zero] at h
    omega
  have h2 := two_mul_ht γ₀
  have hγ'' := hγ'
  rw [roots_eq] at hγ''
  rcases hγ'' with ⟨i, j, hij, hi, hj, hji, h⟩ | ⟨i, hi, h⟩ | ⟨he, i, hi, h⟩
  · exfalso
    rw [h, map_sub, lv_weight, lv_weight] at h2
    have hi' := i.isLt
    have hj' := j.isLt
    exact hji (Fin.ext (by rw [Fin.val_rev]; omega))
  · exact l10su4_toStd_weylAction_long w hi h
  · exfalso
    rw [h, lv_weight] at h2
    have hi' := i.isLt
    omega

private theorem l10su4_prod_single {n : ℕ} {F : Type} [Field F] {a : Fin n} {c : F} :
    ∏ j, (if j = a then c else 1) = c := by
  rw [Finset.prod_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

private theorem l10su4_diagonal_mul_antidiag {n : ℕ} {F : Type} [Field F]
    {a b : Fin n → F} (h : ∀ s, a s * b (Fin.rev s) = 1) :
    diagonal a * antidiag n * diagonal b = antidiag n := by
  ext s t
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases ht : t = Fin.rev s
  · subst ht
    simp [antidiag, h s]
  · simp [antidiag, ht]

private theorem l10su4_diagonal_mem_SU {n : ℕ} {F : Type} [Field F] {σ : F ≃+* F}
    {d : Fin n → F} (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) (hdet : ∏ s, d s = 1) :
    ∃ h : SU σ n, suMat σ n h = diagonal d := by
  have hdet' : (diagonal d : Matrix (Fin n) (Fin n) F).det ≠ 0 := by
    rw [Matrix.det_diagonal, hdet]
    exact one_ne_zero
  let hGL : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal d) hdet'
  have hmem : hGL ∈ SU σ n := by
    rw [mem_SU]
    constructor
    · change (diagonal d : Matrix (Fin n) (Fin n) F).det = 1
      rw [Matrix.det_diagonal, hdet]
    · change conjTr σ (diagonal d) * antidiag n * diagonal d = antidiag n
      have hc : conjTr σ (diagonal d) = diagonal (fun s => σ (d s)) := by
        rw [conjTr, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]
      rw [hc]
      exact l10su4_diagonal_mul_antidiag hd
  exact ⟨⟨hGL, hmem⟩, rfl⟩

private theorem l10su4_exists_lam_mu_large {F : Type} [Field F] [Finite F]
    {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (hf : f ≠ 1)
    {σ : F ≃+* F} (hσapply : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ lam mu : F, lam ≠ 0 ∧ mu ≠ 0 ∧ lam * (σ lam)⁻¹ * mu ^ 2 = 1 ∧
      σ mu * mu = 1 ∧ mu ≠ (σ lam)⁻¹ ∧ (σ lam)⁻¹ ≠ 1 := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hgoal : orderOf g = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  have hf0 : f ≠ 0 := by
    intro h0
    have h1 : Nat.card F = 1 := by rw [hF, h0]; norm_num
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hf2 : 2 ≤ f := by omega
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hpow : (g : F) ^ (Nat.card F - 1) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one (g : F) (Units.ne_zero g)
  have hlamσ : σ ((g : F) ^ (2 ^ f + 1)) = (g : F) ^ (2 ^ f + 1) := by
    rw [hσapply, ← pow_mul]
    have hexp : (2 ^ f + 1) * 2 ^ f = (2 ^ f + 1) + (Nat.card F - 1) := by
      rw [hF]
      have h1 : 0 < (2 ^ f) ^ 2 := by positivity
      calc (2 ^ f + 1) * 2 ^ f = (2 ^ f) ^ 2 + 2 ^ f := by ring
        _ = (2 ^ f + 1) + ((2 ^ f) ^ 2 - 1) := by omega
    rw [hexp, pow_add, hpow, mul_one]
  have hlam1 : (g : F) ^ (2 ^ f + 1) ≠ 1 := by
    intro h
    have hdvd : orderOf g ∣ 2 ^ f + 1 :=
      orderOf_dvd_iff_pow_eq_one.mpr (Units.ext h)
    rw [hgoal] at hdvd
    have hpos : 0 < 2 ^ f + 1 := by positivity
    have hle := Nat.le_of_dvd hpos hdvd
    have hbig : 2 ^ f + 1 < Nat.card F - 1 := by
      rw [hF]
      have h1 : (2 ^ f + 1) + 1 < (2 ^ f) ^ 2 := by
        rw [pow_two]
        nlinarith [hq4]
      omega
    omega
  refine ⟨(g : F) ^ (2 ^ f + 1), 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pow_ne_zero _ (Units.ne_zero g)
  · exact one_ne_zero
  · rw [hlamσ, mul_inv_cancel₀]
    · simp
    · exact pow_ne_zero _ (Units.ne_zero g)
  · simp
  · intro h
    have h' : σ ((g : F) ^ (2 ^ f + 1)) = 1 := inv_eq_one.mp h.symm
    exact hlam1 (by rwa [hlamσ] at h')
  · intro h
    rw [hlamσ] at h
    exact hlam1 (inv_eq_one.mp h)

private theorem l10su4_exists_lam_mu_two {F : Type} [Field F] [Finite F]
    {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (hf : f = 1)
    {σ : F ≃+* F} (hσapply : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ lam mu : F, lam ≠ 0 ∧ mu ≠ 0 ∧ lam * (σ lam)⁻¹ * mu ^ 2 = 1 ∧
      σ mu * mu = 1 ∧ mu ≠ (σ lam)⁻¹ ∧ (σ lam)⁻¹ ≠ 1 := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hcard : Nat.card F = 4 := by
    rw [hF, hf]
    norm_num
  have hgoal : orderOf g = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hcard]
  have hg3 : (g : F) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one g
    rw [hgoal] at h
    exact congrArg (fun x : Fˣ => (x : F)) h
  have hlam1 : (g : F) ≠ 1 := by
    intro h
    have h' : g = 1 := Units.ext h
    rw [h', orderOf_one] at hgoal
    omega
  have hσlam : σ (g : F) = (g : F) ^ 2 := by
    rw [hσapply, hf]
    norm_num
  refine ⟨(g : F), (g : F) ^ 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Units.ne_zero g
  · exact pow_ne_zero _ (Units.ne_zero g)
  · rw [hσlam]
    have hg0 : (g : F) ≠ 0 := Units.ne_zero g
    have h1 : (g : F) * ((g : F) ^ 2)⁻¹ * ((g : F) ^ 2) ^ 2 = (g : F) ^ 3 := by
      field_simp
    rw [h1, hg3]
  · rw [map_pow, hσlam]
    have h6 : ((g : F) ^ 2) ^ 2 * (g : F) ^ 2 = (g : F) ^ 6 := by
      rw [← pow_mul, ← pow_add]
    rw [h6, show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, hg3, one_pow]
  · rw [hσlam]
    intro h
    have hh : (g : F) ^ 2 * (g : F) ^ 2 = 1 := by
      nth_rewrite 1 [h]
      rw [inv_mul_cancel₀ (pow_ne_zero 2 (Units.ne_zero g))]
    have h4 : (g : F) ^ 4 = 1 := by
      rwa [← pow_add, show (2 + 2 : ℕ) = 4 by norm_num] at hh
    have hdvd : orderOf g ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr (Units.ext h4)
    rw [hgoal] at hdvd
    omega
  · rw [hσlam]
    intro h
    have h2 : (g : F) ^ 2 = 1 := inv_eq_one.mp h
    have hdvd : orderOf g ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (Units.ext h2)
    rw [hgoal] at hdvd
    omega

private theorem l10su4_exists_lam_mu_three {F : Type} [Field F] [Finite F]
    {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (hf : f ≠ 1)
    {σ : F ≃+* F} (hσapply : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ lam mu : F, lam ≠ 0 ∧ mu ≠ 0 ∧ lam * (σ lam)⁻¹ * mu = 1 ∧
      σ mu * mu = 1 ∧ mu ≠ (σ lam)⁻¹ ∧ (σ lam)⁻¹ ≠ 1 := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hgoal : orderOf g = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  have hf0 : f ≠ 0 := by
    intro h0
    have h1 : Nat.card F = 1 := by rw [hF, h0]; norm_num
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hf2 : 2 ≤ f := by omega
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hpow : (g : F) ^ (Nat.card F - 1) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one (g : F) (Units.ne_zero g)
  have hσg : σ (g : F) = (g : F) ^ 2 ^ f := hσapply _
  have hlam0 : (g : F) ≠ 0 := Units.ne_zero g
  have hmu0 : (g : F) ^ (2 ^ f - 1) ≠ 0 := pow_ne_zero _ hlam0
  refine ⟨(g : F), (g : F) ^ (2 ^ f - 1), hlam0, hmu0, ?_, ?_, ?_, ?_⟩
  · rw [hσg]
    have h1 : (g : F) * ((g : F) ^ 2 ^ f)⁻¹ * (g : F) ^ (2 ^ f - 1) = 1 := by
      field_simp
      nth_rewrite 1 [← pow_one (g : F)]
      rw [← pow_add, show 1 + (2 ^ f - 1) = 2 ^ f by omega]
    exact h1
  · rw [map_pow, hσg]
    have h1 : ((g : F) ^ 2 ^ f) ^ (2 ^ f - 1) * (g : F) ^ (2 ^ f - 1) = 1 := by
      rw [← pow_mul, ← pow_add]
      rw [show 2 ^ f * (2 ^ f - 1) + (2 ^ f - 1) = Nat.card F - 1 by
        rw [hF]
        have hq1 : 1 ≤ 2 ^ f := by omega
        have h1 : 2 ^ f * (2 ^ f - 1) + (2 ^ f - 1) + 1 = (2 ^ f) ^ 2 := by
          have ht : 2 ^ f - 1 + 1 = 2 ^ f := Nat.sub_add_cancel hq1
          nlinarith [ht]
        omega]
      exact hpow
    exact h1
  · rw [hσg]
    intro h
    have h2 : (g : F) ^ (2 ^ f - 1) * (g : F) ^ 2 ^ f = 1 := by
      rw [h, inv_mul_cancel₀ (pow_ne_zero _ hlam0)]
    have h3 : (g : F) ^ (2 * 2 ^ f - 1) = 1 := by
      have h2' : (g : F) ^ ((2 ^ f - 1) + 2 ^ f) = 1 := by
        rw [pow_add]; exact h2
      rwa [show (2 ^ f - 1) + 2 ^ f = 2 * 2 ^ f - 1 by omega] at h2'
    have hdvd : orderOf g ∣ 2 * 2 ^ f - 1 :=
      orderOf_dvd_iff_pow_eq_one.mpr (Units.ext h3)
    rw [hgoal] at hdvd
    have hle := Nat.le_of_dvd (by omega) hdvd
    have hlt : 2 * 2 ^ f - 1 < Nat.card F - 1 := by
      rw [hF]
      have h1 : 2 * 2 ^ f < (2 ^ f) ^ 2 := by
        rw [pow_two]; nlinarith [hq4]
      omega
    omega
  · rw [hσg]
    intro h
    have h2 : (g : F) ^ 2 ^ f = 1 := inv_eq_one.mp h
    have hdvd : orderOf g ∣ 2 ^ f := orderOf_dvd_iff_pow_eq_one.mpr (Units.ext h2)
    rw [hgoal] at hdvd
    have hle := Nat.le_of_dvd (by positivity) hdvd
    have hlt : 2 ^ f < Nat.card F - 1 := by
      rw [hF]
      have h1 : 2 ^ f + 1 < (2 ^ f) ^ 2 := by
        rw [pow_two]; nlinarith [hq4]
      omega
    omega

private theorem l10su4_exists_j₀ {n : ℕ} (hn : 4 ≤ n) {i : Fin n} :
    ∃ j₀ : Fin n, j₀ ≠ i ∧ j₀ ≠ Fin.rev i ∧ j₀ ≠ Fin.rev j₀ := by
  classical
  let z : Fin n := ⟨0, by omega⟩
  let o : Fin n := ⟨1, by omega⟩
  let l : Fin n := ⟨n - 1, by omega⟩
  let j₀ : Fin n := if i = z ∨ i = l then o else z
  have hz : Fin.rev z = l := by ext; simp [z, l, Fin.val_rev]
  have hl : Fin.rev l = z := by ext; simp [z, l, Fin.val_rev]; omega
  have ho : Fin.rev o = ⟨n - 2, by omega⟩ := by ext; simp [o, Fin.val_rev]
  have hoz : o ≠ z := by intro h; have := congrArg Fin.val h; simp [o, z] at this
  have hol : o ≠ l := by
    intro h; have := congrArg Fin.val h; simp [o, l] at this; omega
  have hzl : z ≠ l := by
    intro h; have := congrArg Fin.val h; simp [z, l] at this; omega
  have hozrev : o ≠ Fin.rev o := by
    rw [ho]; intro h; have := congrArg Fin.val h; simp [o] at this; omega
  have hzrev : z ≠ Fin.rev z := by rw [hz]; exact hzl
  refine ⟨j₀, ?_, ?_, ?_⟩
  · intro h
    by_cases hc : i = z ∨ i = l
    · simp only [j₀, if_pos hc] at h
      rcases hc with hc | hc
      · exact hoz (hc ▸ h)
      · exact hol (hc ▸ h)
    · simp only [j₀, if_neg hc] at h
      exact hc (Or.inl h.symm)
  · intro h
    by_cases hc : i = z ∨ i = l
    · simp only [j₀, if_pos hc] at h
      rcases hc with hc | hc
      · rw [hc, hz] at h
        exact hol h
      · rw [hc, hl] at h
        exact hoz h
    · simp only [j₀, if_neg hc] at h
      have hli : i ≠ l := fun hh => hc (Or.inr hh)
      have hzi : Fin.rev i ≠ z := by
        intro hh
        exact hli (by rw [← Fin.rev_rev i, hh, hz])
      exact hzi h.symm
  · intro h
    by_cases hc : i = z ∨ i = l
    · simp only [j₀, if_pos hc] at h
      exact hozrev h
    · simp only [j₀, if_neg hc] at h
      exact hzrev h

private theorem l10su4_diag_data {n : ℕ} {F : Type} [Field F] {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) {i : Fin n} (hi : i ≠ Fin.rev i) {j₀ : Fin n}
    (hj₀i : j₀ ≠ i) (hj₀ri : j₀ ≠ Fin.rev i) (hj₀ : j₀ ≠ Fin.rev j₀) {lam mu : F}
    (hlam0 : lam ≠ 0) (hmu0 : mu ≠ 0) (hlammu : lam * (σ lam)⁻¹ * mu ^ 2 = 1)
    (hmu : σ mu * mu = 1) (hmune : mu ≠ (σ lam)⁻¹) (hlamne : (σ lam)⁻¹ ≠ 1) :
    ∃ d : Fin n → F,
      d i = lam ∧ d (Fin.rev i) = (σ lam)⁻¹ ∧ d j₀ = mu ∧ d (Fin.rev j₀) = mu ∧
      (∀ j, d j ≠ 0) ∧ (∀ j, σ (d j) * d (Fin.rev j) = 1) ∧
      (∏ j, d j = 1) ∧ (∀ j, j ≠ i → j ≠ Fin.rev i → d j ≠ (σ lam)⁻¹) := by
  let d : Fin n → F := fun j =>
    (if j = i then lam else 1) * (if j = Fin.rev i then (σ lam)⁻¹ else 1) *
      (if j = j₀ then mu else if j = Fin.rev j₀ then mu else 1)
  have hdi : d i = lam := by
    have h1 : i ≠ Fin.rev i := hi
    have h2 : i ≠ j₀ := fun h => hj₀i h.symm
    have h3 : i ≠ Fin.rev j₀ := fun h => hj₀ri (by rw [h, Fin.rev_rev])
    simp [d, h1, h2, h3]
  have hdri : d (Fin.rev i) = (σ lam)⁻¹ := by
    have h1 : Fin.rev i ≠ i := fun h => hi h.symm
    have h2 : Fin.rev i ≠ j₀ := fun h => hj₀ri h.symm
    have h3 : Fin.rev i ≠ Fin.rev j₀ := fun h => hj₀i (Fin.rev_injective h.symm)
    simp [d, h1, h2, h3]
  have hdj₀ : d j₀ = mu := by
    simp [d, hj₀i, hj₀ri, hj₀]
  have hdrj₀ : d (Fin.rev j₀) = mu := by
    have h1 : Fin.rev j₀ ≠ i := fun h => hj₀ri (by rw [← h, Fin.rev_rev])
    have h2 : Fin.rev j₀ ≠ Fin.rev i := by simpa [Fin.rev_inj] using hj₀i
    simp [d, h1, h2, hj₀]
  have hd0 : ∀ j, d j ≠ 0 := by
    intro j
    by_cases h1 : j = i
    · rw [h1, hdi]; exact hlam0
    · by_cases h2 : j = Fin.rev i
      · rw [h2, hdri]; exact inv_ne_zero ((map_ne_zero σ).2 hlam0)
      · by_cases h3 : j = j₀
        · rw [h3, hdj₀]; exact hmu0
        · by_cases h4 : j = Fin.rev j₀
          · rw [h4, hdrj₀]; exact hmu0
          · simp [d, h1, h2, h3, h4]
  have hSU : ∀ j, σ (d j) * d (Fin.rev j) = 1 := by
    intro j
    by_cases h1 : j = i
    · subst h1
      rw [hdi, hdri]
      exact mul_inv_cancel₀ ((map_ne_zero σ).2 hlam0)
    · by_cases h2 : j = Fin.rev i
      · subst h2
        rw [hdri, Fin.rev_rev, hdi, map_inv₀, hσ]
        exact inv_mul_cancel₀ hlam0
      · by_cases h3 : j = j₀
        · subst h3
          rw [hdj₀, hdrj₀]
          exact hmu
        · by_cases h4 : j = Fin.rev j₀
          · subst h4
            rw [hdrj₀, Fin.rev_rev, hdj₀]
            exact hmu
          · have h5 : Fin.rev j ≠ j₀ := fun h => h4 (by rw [← h, Fin.rev_rev])
            have h6 : Fin.rev j ≠ i := fun h => h2 (by rw [← h, Fin.rev_rev])
            simp [d, h1, h2, h3, h4, h5, h6]
  have hprod : ∏ j, d j = 1 := by
    have hsplit : ∏ j, d j = (∏ j, (if j = i then lam else 1)) *
        (∏ j, (if j = Fin.rev i then (σ lam)⁻¹ else 1)) *
        (∏ j, (if j = j₀ then mu else if j = Fin.rev j₀ then mu else 1)) := by
      simp only [d]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have h3 : (∏ j, (if j = j₀ then mu else if j = Fin.rev j₀ then mu else 1)) = mu ^ 2 := by
      have hfun : (fun j => if j = j₀ then mu else if j = Fin.rev j₀ then mu else 1) =
          fun j => (if j = j₀ then mu else 1) * (if j = Fin.rev j₀ then mu else 1) := by
        funext j
        by_cases h1 : j = j₀
        · subst h1; simp [hj₀]
        · by_cases h2 : j = Fin.rev j₀
          · subst h2; simp [h1]
          · simp [h1, h2]
      rw [hfun, Finset.prod_mul_distrib, l10su4_prod_single, l10su4_prod_single, pow_two]
    rw [hsplit, l10su4_prod_single, l10su4_prod_single, h3, hlammu]
  refine ⟨d, hdi, hdri, hdj₀, hdrj₀, hd0, hSU, hprod, ?_⟩
  intro j hji hjri
  by_cases h3 : j = j₀
  · rw [h3, hdj₀]; exact hmune
  · by_cases h4 : j = Fin.rev j₀
    · rw [h4, hdrj₀]; exact hmune
    · have hdj1 : d j = 1 := by simp [d, hji, hjri, h3, h4]
      rw [hdj1]
      exact fun h => hlamne h.symm

private theorem l10su4_diag_data_three {F : Type} [Field F] {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) {i : Fin 3} (hi : i ≠ Fin.rev i) {m : Fin 3}
    (hm : m = Fin.rev m) (hmi : m ≠ i) (hmri : m ≠ Fin.rev i) {lam mu : F}
    (hlam0 : lam ≠ 0) (hmu0 : mu ≠ 0) (hlammu : lam * (σ lam)⁻¹ * mu = 1)
    (hmu : σ mu * mu = 1) (hmune : mu ≠ (σ lam)⁻¹) :
    ∃ d : Fin 3 → F, d i = lam ∧ d (Fin.rev i) = (σ lam)⁻¹ ∧ d m = mu ∧
      (∀ j, d j ≠ 0) ∧ (∀ j, σ (d j) * d (Fin.rev j) = 1) ∧
      (∏ j, d j = 1) ∧ (∀ j, j ≠ i → j ≠ Fin.rev i → d j ≠ (σ lam)⁻¹) := by
  have hm1 : m = 1 := by
    fin_cases m <;> simp_all [Fin.rev]
  subst hm1
  fin_cases i
  · let d : Fin 3 → F := ![lam, mu, (σ lam)⁻¹]
    refine ⟨d, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · rfl
    · intro j; fin_cases j <;> simp [d, hlam0, hmu0]
    · intro j
      fin_cases j <;> simp [d, hσ, hmu, mul_inv_cancel₀ ((map_ne_zero σ).2 hlam0),
        inv_mul_cancel₀ hlam0]
    · simp [d, Fin.prod_univ_three]; linear_combination hlammu
    · intro j h0 h2
      fin_cases j
      · simp_all [d]
      · exact hmune
      · simp_all [d]
  · exact absurd rfl hi
  · let d : Fin 3 → F := ![(σ lam)⁻¹, mu, lam]
    refine ⟨d, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · rfl
    · intro j; fin_cases j <;> simp [d, hlam0, hmu0]
    · intro j
      fin_cases j <;> simp [d, hσ, hmu, mul_inv_cancel₀ ((map_ne_zero σ).2 hlam0),
        inv_mul_cancel₀ hlam0]
    · simp [d, Fin.prod_univ_three]; linear_combination hlammu
    · intro j h0 h2
      fin_cases j
      · simp_all [d]
      · exact hmune
      · simp_all [d]

private theorem l10su4_perpPair_iff {n : ℕ} {F : Type} [Field F] {σ : F ≃+* F}
    {i : Fin n} {r : Fin n → F} :
    r ∈ perpPair σ (Pi.single i (1 : F)) (Pi.single (Fin.rev i) (1 : F)) ↔
      r (Fin.rev i) = 0 ∧ r i = 0 := by
  rw [mem_perpPair, uForm_single_left, uForm_single_left, Fin.rev_rev]

private theorem l10su4_diagonal_mulVec_perpPair {n : ℕ} {F : Type} [Field F]
    {σ : F ≃+* F} {d : Fin n → F} {i : Fin n} {r : Fin n → F}
    (hr : r ∈ perpPair σ (Pi.single i 1) (Pi.single (Fin.rev i) 1)) :
    diagonal d *ᵥ r ∈ perpPair σ (Pi.single i 1) (Pi.single (Fin.rev i) 1) := by
  rw [l10su4_perpPair_iff] at hr ⊢
  constructor
  · rw [Matrix.mulVec_diagonal]; simp [hr.1]
  · rw [Matrix.mulVec_diagonal]; simp [hr.2]

private theorem l10su4_levAct_diagonal {n : ℕ} {F : Type} [Field F] {σ : F ≃+* F}
    {d : Fin n → F} {i : Fin n} {h : SU σ n} (hh : suMat σ n h = diagonal d)
    {r : Fin n → F}
    (hr : r ∈ perpPair σ (Pi.single i 1) (Pi.single (Fin.rev i) 1)) :
    levAct σ (Pi.single i 1) (Pi.single (Fin.rev i) 1) h r = diagonal d *ᵥ r := by
  rw [levAct, hh, projPair_of_mem (l10su4_diagonal_mulVec_perpPair hr)]

private theorem l10su4_radVec_zero {n : ℕ} {F : Type} [Field F] {σ : F ≃+* F}
    {d : Fin n → F} {i : Fin n} {h : SU σ n} {lam : F}
    (hh : suMat σ n h = diagonal d)
    (hd : ∀ j, j ≠ i → j ≠ Fin.rev i → d j ≠ (σ lam)⁻¹)
    {r : Fin n → F}
    (hr : r ∈ perpPair σ (Pi.single i 1) (Pi.single (Fin.rev i) 1))
    (heq : r = σ lam • levAct σ (Pi.single i 1) (Pi.single (Fin.rev i) 1) h r) :
    r = 0 := by
  rw [l10su4_levAct_diagonal hh hr] at heq
  funext j
  by_cases hji : j = i
  · rw [hji]
    exact (l10su4_perpPair_iff.mp hr).2
  · by_cases hjri : j = Fin.rev i
    · rw [hjri]
      exact (l10su4_perpPair_iff.mp hr).1
    · have hdj := hd j hji hjri
      have h1 : r j = σ lam * (d j * r j) := by
        have := congrFun heq j
        simpa [Pi.smul_apply, Matrix.mulVec_diagonal, mul_assoc] using this
      have h2 : (1 - σ lam * d j) * r j = 0 := by
        linear_combination h1
      have h3 : (1 - σ lam * d j) ≠ 0 := by
        intro h0
        apply hdj
        have h1' : σ lam * d j = 1 := by linear_combination -h0
        exact eq_inv_of_mul_eq_one_left (by rwa [mul_comm] at h1')
      exact (mul_eq_zero.mp h2).resolve_left h3

private theorem l10su4_mem_roots {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ}
    {β : Fin (Unitary.rootDatum hF n).rank → ℤ}
    (hl : GGLongRoot (Unitary.rootDatum hF n) β) :
    β ∈ (Unitary.rootDatum hF n).roots := by
  obtain ⟨w, γ₀, hγ₀, -, rfl⟩ := hl
  exact CFSG.LieType.CurtisTits.weylAction_mem_roots hγ₀ w

private theorem l10su4_pCore_le_uRad_three {F : Type} [Field F] [CharP F 2]
    {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {i m : Fin 3} (hi : i ≠ Fin.rev i)
    (hm : m = Fin.rev m) (hmi : m ≠ i) (hmri : m ≠ Fin.rev i)
    {T : Subgroup (SU σ 3)} (hT : IsUTransGroup σ (Pi.single i 1) T)
    (Θ : SUThetaFacts σ (Pi.single i 1) (Pi.single (Fin.rev i) 1) T) :
    pCoreOf 2 (Subgroup.normalizer (T : Set (SU σ 3))) ≤ uRad σ (Pi.single i 1) := by
  have hm1 : m = 1 := by
    fin_cases m <;> simp_all [Fin.rev]
  have h1i : (1 : Fin 3) ≠ i := by rw [← hm1]; exact hmi
  have h1ri : (1 : Fin 3) ≠ Fin.rev i := by rw [← hm1]; exact hmri
  have ha : (Pi.single i (1 : F) : Fin 3 → F) ≠ 0 := by
    intro h; have := congrFun h i; simp at this
  intro x hx
  have hxline : x ∈ uLine σ (Pi.single i 1) := by
    rw [← normalizer_eq_uLine hσ ha hT]
    exact CFSG.StandardType.GGRootNorm.pCoreOf_le _ hx
  obtain ⟨k, hk⟩ := (CFSG.StandardType.GGRootNorm.isPGroup_pCoreOf _) ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hxa : suMat σ 3 x *ᵥ Pi.single i 1 = Pi.single i 1 :=
    suMat_mulVec_eq_of_pow_two_pow ha hxline hk'
  let e : Fin 3 → F := Pi.single (1 : Fin 3) 1
  have heperp : e ∈ perpPair σ (Pi.single i 1) (Pi.single (Fin.rev i) 1) := by
    rw [l10su4_perpPair_iff]
    constructor
    · simp [e, h1ri]
    · simp [e, h1i]
  have he0 : e ≠ 0 := by
    intro h; have := congrFun h 1; simp [e] at this
  have hspan : ∀ r ∈ perpPair σ (Pi.single i 1) (Pi.single (Fin.rev i) 1),
      r = r 1 • e := by
    intro r hr
    have hr' := l10su4_perpPair_iff.mp hr
    funext j
    fin_cases i <;> fin_cases j <;> simp_all [e, Pi.smul_apply]
  have hlevx : levAct σ (Pi.single i 1) (Pi.single (Fin.rev i) 1) x e =
      (levAct σ (Pi.single i 1) (Pi.single (Fin.rev i) 1) x e 1) • e :=
    hspan _ (Θ.levAct_mem hxline heperp)
  set c : F := levAct σ (Pi.single i 1) (Pi.single (Fin.rev i) 1) x e 1 with hc
  have hlevpow : ∀ n : ℕ, levAct σ (Pi.single i 1) (Pi.single (Fin.rev i) 1) (x ^ n) e =
      c ^ n • e := by
    intro n
    induction n with
    | zero => rw [pow_zero, Θ.levAct_one heperp, pow_zero, one_smul]
    | succ n ih =>
      rw [pow_succ, Θ.levAct_mul (pow_mem hxline n) hxline heperp, hlevx,
        Θ.levAct_smul, ih, smul_smul, pow_succ, mul_comm]
  have hc1 : c = 1 := by
    have h0 : levAct σ (Pi.single i 1) (Pi.single (Fin.rev i) 1) (x ^ 2 ^ k) e = e := by
      rw [hk', Θ.levAct_one heperp]
    rw [hlevpow] at h0
    have h1 : c ^ 2 ^ k = 1 := by
      have := congrFun h0 1
      simpa [e, Pi.smul_apply] using this
    have h4 : (c - 1) ^ 2 ^ k = 0 := by
      rw [sub_pow_char_pow, h1, one_pow, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).mp h4)
  have hlev : ∀ r ∈ perpPair σ (Pi.single i 1) (Pi.single (Fin.rev i) 1),
      levAct σ (Pi.single i 1) (Pi.single (Fin.rev i) 1) x r = r := by
    intro r hr
    rw [hspan r hr, Θ.levAct_smul, hlevx, hc1, one_smul, ← hspan r hr]
  exact Θ.mem_uRad hxa hlev

private theorem l10su4_fpf_three {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : f ≠ 1)
    {β : Fin (Unitary.rootDatum hF 3).rank → ℤ}
    (hβ : β ∈ (Unitary.rootDatum hF 3).roots)
    (hl : GGLongRoot (Unitary.rootDatum hF 3) β) :
    ∃ h ∈ Subgroup.normalizer
        (((Unitary.rootDatum hF 3).rootGroup β :
          Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) 3)) :
          Set ↥(Unitary.SU (unitaryInvolution F 2 f) 3)),
      Odd (orderOf h) ∧ ∀ y ∈ pCoreOf 2 (Subgroup.normalizer
        (((Unitary.rootDatum hF 3).rootGroup β :
          Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) 3)) :
          Set ↥(Unitary.SU (unitaryInvolution F 2 f) 3))),
        h * y = y * h → y ∈ (Unitary.rootDatum hF 3).rootGroup β := by
  haveI : Fintype F := Fintype.ofFinite F
  have hσ := CFSG.LieType.BorelTits.unitaryInvolution_involutive hF
  have hσapply : ∀ c, unitaryInvolution F 2 f c = c ^ 2 ^ f :=
    fun c => CFSG.LieType.BorelTits.unitaryInvolution_apply F 2 f c
  have htr : ∀ x, unitaryInvolution F 2 f x = x →
      ∃ c, c + unitaryInvolution F 2 f c = x :=
    fun _ hx => CFSG.LieType.BorelTits.exists_add_unitaryInvolution_eq hF hx
  obtain ⟨i, hi, hβi⟩ := l10su4_exists_weight_of_ggLongRoot hF hβ hl
  let v : Fin 3 → F := Pi.single i 1
  let w : Fin 3 → F := Pi.single (Fin.rev i) 1
  have hT : IsUTransGroup (unitaryInvolution F 2 f) v
      ((Unitary.rootDatum hF 3).rootGroup β) := by
    change IsUTransGroup (unitaryInvolution F 2 f) (Pi.single i 1)
      (Unitary.rootGroup (unitaryInvolution F 2 f)
        (CFSG.LieType.BorelTits.unitaryInvolution_involutive hF) 3 β)
    exact isUTransGroup_rootGroup_long' hσ hi hβi
  have haa : uForm (unitaryInvolution F 2 f) v v = 0 :=
    uForm_single_self (σ := unitaryInvolution F 2 f) hi
  have hdd : uForm (unitaryInvolution F 2 f) w w = 0 := by
    change uForm (unitaryInvolution F 2 f) (Pi.single (Fin.rev i) 1)
      (Pi.single (Fin.rev i) 1) = 0
    exact uForm_single_self (σ := unitaryInvolution F 2 f)
      (fun h => hi (by rw [Fin.rev_rev] at h; exact h.symm))
  have had : uForm (unitaryInvolution F 2 f) v w = 1 := by
    change uForm (unitaryInvolution F 2 f) (Pi.single i 1) (Pi.single (Fin.rev i) 1) = 1
    rw [uForm_single_right, Fin.rev_rev, Pi.single_eq_same, map_one]
  have ha : v ≠ 0 := by
    intro h
    have := congrFun h i
    simp [v] at this
  let Θ := suThetaFacts_holds hσ htr haa hdd had hT
  have hm : (1 : Fin 3) = Fin.rev 1 := by decide
  have hmi : (1 : Fin 3) ≠ i := by
    fin_cases i <;> simp_all
  have hmri : (1 : Fin 3) ≠ Fin.rev i := by
    fin_cases i <;> simp_all
  obtain ⟨lam, mu, hlam0, hmu0, hlammu, hmu, hmune, hlamne⟩ :=
    l10su4_exists_lam_mu_three hF hf hσapply
  obtain ⟨d, hdi, hdri, hdm, hd0, hSU, hprod, hdfix⟩ :=
    l10su4_diag_data_three hσ hi hm hmi hmri hlam0 hmu0 hlammu hmu hmune
  obtain ⟨h, hh⟩ := l10su4_diagonal_mem_SU hSU hprod
  have hlamv : suMat (unitaryInvolution F 2 f) 3 h *ᵥ v = lam • v := by
    rw [hh]
    funext j
    rw [Matrix.mulVec_diagonal]
    by_cases hj : j = i
    · subst hj
      rw [hdi]
      simp [v]
    · simp [v, hj]
  have hN : h ∈ Subgroup.normalizer
      (((Unitary.rootDatum hF 3).rootGroup β :
        Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) 3)) :
        Set ↥(Unitary.SU (unitaryInvolution F 2 f) 3)) := by
    rw [normalizer_eq_uLine hσ ha hT]
    exact ⟨lam, hlam0, hlamv⟩
  have hpow : h ^ (Nat.card F - 1) = 1 := by
    apply suMat_injective (σ := unitaryInvolution F 2 f)
    rw [map_pow, hh, map_one, Matrix.diagonal_pow]
    have hdN : (d ^ (Nat.card F - 1)) = fun _ => (1 : F) := by
      funext j
      rw [Pi.pow_apply, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one (d j) (hd0 j)
    rw [hdN, Matrix.diagonal_one]
  have hf0 : f ≠ 0 := by
    intro h0
    have h1 : Nat.card F = 1 := by rw [hF, h0]; norm_num
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hodd : Odd (orderOf h) := by
    have hdvd : orderOf h ∣ Nat.card F - 1 :=
      orderOf_dvd_iff_pow_eq_one.mpr hpow
    have heven : Even (Nat.card F) := by
      rw [hF, ← pow_mul]
      exact Even.pow_of_ne_zero even_two (Nat.mul_ne_zero hf0 (by norm_num))
    have hpos : 0 < Nat.card F := by
      rw [hF]
      positivity
    exact Odd.of_dvd_nat (Nat.Even.sub_odd hpos heven odd_one) hdvd
  refine ⟨h, hN, hodd, ?_⟩
  intro y hy hcomm
  have hpCore := l10su4_pCore_le_uRad_three hσ hi hm hmi hmri hT Θ
  have hyu : y ∈ uRad (unitaryInvolution F 2 f) v := hpCore hy
  have hcomm' : h * y * h⁻¹ = y := by
    rw [hcomm, mul_inv_cancel_right]
  have hrad := Θ.conj (g := h) (x := y) (μ := lam) hlamv hyu
  rw [hcomm'] at hrad
  have hzero : radVec (unitaryInvolution F 2 f) v w y = 0 :=
    l10su4_radVec_zero hh hdfix (Θ.mem_perp y) hrad
  exact (Θ.eq_zero_iff hyu).mp hzero
private theorem l10su4_fpf {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n) (hnf : ¬ (n = 3 ∧ f = 1))
    {β : Fin (Unitary.rootDatum hF n).rank → ℤ} (hl : GGLongRoot (Unitary.rootDatum hF n) β) :
    ∃ h ∈ Subgroup.normalizer
        (((Unitary.rootDatum hF n).rootGroup β :
          Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) n)) :
          Set ↥(Unitary.SU (unitaryInvolution F 2 f) n)),
      Odd (orderOf h) ∧ ∀ y ∈ pCoreOf 2 (Subgroup.normalizer
        (((Unitary.rootDatum hF n).rootGroup β :
          Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) n)) :
          Set ↥(Unitary.SU (unitaryInvolution F 2 f) n))),
        h * y = y * h → y ∈ (Unitary.rootDatum hF n).rootGroup β := by
  by_cases hn3 : n = 3
  · subst hn3
    exact l10su4_fpf_three hF (fun hf1 => hnf ⟨rfl, hf1⟩)
      (l10su4_mem_roots hF hl) hl
  · haveI : Fintype F := Fintype.ofFinite F
    have hβ := l10su4_mem_roots hF hl
    have hn4 : 4 ≤ n := by omega
    have hσ := CFSG.LieType.BorelTits.unitaryInvolution_involutive hF
    have hσapply : ∀ c, unitaryInvolution F 2 f c = c ^ 2 ^ f :=
      fun c => CFSG.LieType.BorelTits.unitaryInvolution_apply F 2 f c
    have htr : ∀ x, unitaryInvolution F 2 f x = x →
        ∃ c, c + unitaryInvolution F 2 f c = x :=
      fun _ hx => CFSG.LieType.BorelTits.exists_add_unitaryInvolution_eq hF hx
    have hnorm : ∀ x, unitaryInvolution F 2 f x = x →
        ∃ a, unitaryInvolution F 2 f a * a = x :=
      fun _ hx => exists_norm_eq hF hx
    obtain ⟨i, hi, hβi⟩ := l10su4_exists_weight_of_ggLongRoot hF hβ hl
    let v : Fin n → F := Pi.single i 1
    let w : Fin n → F := Pi.single (Fin.rev i) 1
    have hT : IsUTransGroup (unitaryInvolution F 2 f) v
        ((Unitary.rootDatum hF n).rootGroup β) := by
      change IsUTransGroup (unitaryInvolution F 2 f) (Pi.single i 1)
        (Unitary.rootGroup (unitaryInvolution F 2 f)
          (CFSG.LieType.BorelTits.unitaryInvolution_involutive hF) n β)
      exact isUTransGroup_rootGroup_long' hσ hi hβi
    have haa : uForm (unitaryInvolution F 2 f) v v = 0 :=
      uForm_single_self (σ := unitaryInvolution F 2 f) hi
    have hdd : uForm (unitaryInvolution F 2 f) w w = 0 := by
      change uForm (unitaryInvolution F 2 f) (Pi.single (Fin.rev i) 1)
        (Pi.single (Fin.rev i) 1) = 0
      exact uForm_single_self (σ := unitaryInvolution F 2 f)
        (fun h => hi (by rw [Fin.rev_rev] at h; exact h.symm))
    have had : uForm (unitaryInvolution F 2 f) v w = 1 := by
      change uForm (unitaryInvolution F 2 f) (Pi.single i 1) (Pi.single (Fin.rev i) 1) = 1
      rw [uForm_single_right, Fin.rev_rev, Pi.single_eq_same, map_one]
    have ha : v ≠ 0 := by
      intro h
      have := congrFun h i
      simp [v] at this
    let Θ := suThetaFacts_holds hσ htr haa hdd had hT
    have hG : SUGeomFacts (unitaryInvolution F 2 f) v w :=
      suGeomFacts_holds hσ htr hnorm hn4 haa hdd had
    have hpCore : pCoreOf 2 (Subgroup.normalizer
        (((Unitary.rootDatum hF n).rootGroup β :
          Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) n)) :
          Set ↥(Unitary.SU (unitaryInvolution F 2 f) n))) =
        uRad (unitaryInvolution F 2 f) v :=
      pCoreOf_normalizer_eq_uRad hσ ha hT Θ hG
    obtain ⟨j₀, hj₀i, hj₀ri, hj₀⟩ := l10su4_exists_j₀ hn4
    have hdata : ∃ lam mu : F, lam ≠ 0 ∧ mu ≠ 0 ∧
        lam * (unitaryInvolution F 2 f lam)⁻¹ * mu ^ 2 = 1 ∧
        unitaryInvolution F 2 f mu * mu = 1 ∧
        mu ≠ (unitaryInvolution F 2 f lam)⁻¹ ∧
        (unitaryInvolution F 2 f lam)⁻¹ ≠ 1 := by
      by_cases hf1 : f = 1
      · exact l10su4_exists_lam_mu_two hF hf1 hσapply
      · exact l10su4_exists_lam_mu_large hF hf1 hσapply
    obtain ⟨lam, mu, hlam0, hmu0, hlammu, hmu, hmune, hlamne⟩ := hdata
    obtain ⟨d, hdi, hdri, hdj, hdrj, hd0, hSU, hprod, hdfix⟩ :=
      l10su4_diag_data hσ hi hj₀i hj₀ri hj₀ hlam0 hmu0 hlammu hmu hmune hlamne
    obtain ⟨h, hh⟩ := l10su4_diagonal_mem_SU hSU hprod
    have hlamv : suMat (unitaryInvolution F 2 f) n h *ᵥ v = lam • v := by
      rw [hh]
      funext j
      rw [Matrix.mulVec_diagonal]
      by_cases hj : j = i
      · subst hj
        rw [hdi]
        simp [v]
      · simp [v, hj]
    have hN : h ∈ Subgroup.normalizer
        (((Unitary.rootDatum hF n).rootGroup β :
          Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) n)) :
          Set ↥(Unitary.SU (unitaryInvolution F 2 f) n)) := by
      rw [normalizer_eq_uLine hσ ha hT]
      exact ⟨lam, hlam0, hlamv⟩
    have hpow : h ^ (Nat.card F - 1) = 1 := by
      apply suMat_injective (σ := unitaryInvolution F 2 f)
      rw [map_pow, hh, map_one, Matrix.diagonal_pow]
      have hdN : (d ^ (Nat.card F - 1)) = fun _ => (1 : F) := by
        funext j
        rw [Pi.pow_apply, Nat.card_eq_fintype_card]
        exact FiniteField.pow_card_sub_one_eq_one (d j) (hd0 j)
      rw [hdN, Matrix.diagonal_one]
    have hf0 : f ≠ 0 := by
      intro h0
      have h1 : Nat.card F = 1 := by rw [hF, h0]; norm_num
      have h2 : 1 < Nat.card F := Finite.one_lt_card
      omega
    have hodd : Odd (orderOf h) := by
      have hdvd : orderOf h ∣ Nat.card F - 1 :=
        orderOf_dvd_iff_pow_eq_one.mpr hpow
      have heven : Even (Nat.card F) := by
        rw [hF, ← pow_mul]
        exact Even.pow_of_ne_zero even_two (Nat.mul_ne_zero hf0 (by norm_num))
      have hpos : 0 < Nat.card F := by
        rw [hF]
        positivity
      exact Odd.of_dvd_nat (Nat.Even.sub_odd hpos heven odd_one) hdvd
    refine ⟨h, hN, hodd, ?_⟩
    intro y hy hcomm
    rw [hpCore] at hy
    have hcomm' : h * y * h⁻¹ = y := by
      rw [hcomm, mul_inv_cancel_right]
    have hrad := Θ.conj (g := h) (x := y) (μ := lam) hlamv hy
    rw [hcomm'] at hrad
    have hzero : radVec (unitaryInvolution F 2 f) v w y = 0 :=
      l10su4_radVec_zero hh hdfix (Θ.mem_perp y) hrad
    exact (Θ.eq_zero_iff hy).mp hzero
private theorem l10su4_fpf_map {K : Type*} [Group K] (e : K ≃* K) {X : Subgroup K} {h : K}
    (hhN : h ∈ Subgroup.normalizer (X : Set K))
    (hfix : ∀ y ∈ pCoreOf 2 (Subgroup.normalizer (X : Set K)), h * y = y * h → y ∈ X) :
    e h ∈ Subgroup.normalizer ((X.map e.toMonoidHom : Subgroup K) : Set K) ∧
      ∀ y ∈ pCoreOf 2 (Subgroup.normalizer ((X.map e.toMonoidHom : Subgroup K) : Set K)),
        e h * y = y * e h → y ∈ X.map e.toMonoidHom := by
  constructor
  · rw [GGRootNorm.normalizer_map_mulEquiv e X]
    exact ⟨h, hhN, rfl⟩
  · intro y hy hcomm
    rw [GGRootNorm.normalizer_map_mulEquiv e X,
      GGRootNorm.pCoreOf_map_mulEquiv e (Subgroup.normalizer (X : Set K))] at hy
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map.mpr ⟨y', hfix y' hy' (by
      apply e.injective
      rw [map_mul, map_mul]
      exact hcomm), rfl⟩

theorem ggRootNoCentral_su_long {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n) (hnf : ¬ (n = 3 ∧ f = 1))
    {β : Fin (Unitary.rootDatum hF n).rank → ℤ} (hl : GGLongRoot (Unitary.rootDatum hF n) β)
    (u : ↥(Unitary.SU (unitaryInvolution F 2 f) n)) :
    GGRootNoCentralAt (⊤ : Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) n))
      (((Unitary.rootDatum hF n).rootGroup β).map (MulAut.conj u).toMonoidHom) := by
  obtain ⟨h, hhN, hodd, hfix⟩ := l10su4_fpf hF hn hnf hl
  obtain ⟨hhN', hfix'⟩ := l10su4_fpf_map (MulAut.conj u) hhN hfix
  refine noCentral_of_fixedPoint_odd (K := ⊤)
    (R := ((Unitary.rootDatum hF n).rootGroup β).map (MulAut.conj u).toMonoidHom)
    ?_ ⟨Subgroup.mem_top _, hhN'⟩ ?_
  · rw [MulEquiv.orderOf_eq]
    exact hodd
  · intro y hy hcomm
    rw [top_inf_eq] at hy
    exact hfix' y hy hcomm

end CFSG.StandardType.LieKnownR2.PSU

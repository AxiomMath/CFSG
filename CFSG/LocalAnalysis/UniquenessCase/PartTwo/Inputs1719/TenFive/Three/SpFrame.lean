module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.SpPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Map

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open Matrix
open CFSG.Open (StatedProj StatedSp)
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (formJ)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
  (unipSp spForm spN spT spT_mul_spT spForm_swap spN_mul_self isSp_spN isSp_neg
    neg_mul_self_neg)

variable {r : ℕ} {K : Type} [Field K]

@[expose] def IsSpFrame (e f : Fin 4 → Fin r ⊕ Fin r → K) : Prop :=
  ∀ i j, spForm (e i) (e j) = 0 ∧ spForm (f i) (f j) = 0 ∧
    spForm (e i) (f j) = if i = j then 1 else 0

@[expose] def frameN (e f : Fin 4 → Fin r ⊕ Fin r → K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  spN (e 0) (f 3) - spN (e 2) (f 1)

theorem isSp_frameN (e f : Fin 4 → Fin r ⊕ Fin r → K) :
    (frameN e f)ᵀ * formJ r K + formJ r K * frameN e f = 0 := by
  have h1 := isSp_spN (e 0) (f 3)
  have h2 := isSp_spN (e 2) (f 1)
  rw [frameN, transpose_sub, Matrix.sub_mul, Matrix.mul_sub]
  calc (spN (e 0) (f 3))ᵀ * formJ r K - (spN (e 2) (f 1))ᵀ * formJ r K +
        (formJ r K * spN (e 0) (f 3) - formJ r K * spN (e 2) (f 1)) =
      ((spN (e 0) (f 3))ᵀ * formJ r K + formJ r K * spN (e 0) (f 3)) -
        ((spN (e 2) (f 1))ᵀ * formJ r K + formJ r K * spN (e 2) (f 1)) := by abel
    _ = 0 := by rw [h1, h2, sub_zero]

private lemma spForm_frame_f_e {e f : Fin 4 → Fin r ⊕ Fin r → K} (hef : IsSpFrame e f)
    (i j : Fin 4) : spForm (f i) (e j) = -(if i = j then 1 else 0) := by
  rw [spForm_swap, (hef j i).2.2]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun h' => h h'.symm]

private lemma spN_mul_spN (a c a' c' : Fin r ⊕ Fin r → K) :
    spN a c * spN a' c' = spForm a' c • spT c' a + spForm c' c • spT a' a +
      spForm a' a • spT c' c + spForm c' a • spT a' c := by
  simp only [spN, Matrix.add_mul, Matrix.mul_add, spT_mul_spT]
  abel

private lemma frame_spN_mul {e f : Fin 4 → Fin r ⊕ Fin r → K} (hef : IsSpFrame e f)
    (i j k l : Fin 4) : spN (e i) (f j) * spN (e k) (f l) =
      (if j = k then 1 else 0) • spT (f l) (e i) - (if i = l then 1 else 0) • spT (e k) (f j) := by
  rw [spN_mul_spN, (hef k j).2.2, (hef l j).2.1, (hef k i).1, spForm_frame_f_e hef l i]
  have h : (if k = j then (1 : K) else 0) = if j = k then 1 else 0 := by
    by_cases hjk : j = k
    · rw [if_pos hjk.symm, if_pos hjk]
    · rw [if_neg fun h => hjk h.symm, if_neg hjk]
  have h' : (if l = i then (1 : K) else 0) = if i = l then 1 else 0 := by
    by_cases hil : i = l
    · rw [if_pos hil.symm, if_pos hil]
    · rw [if_neg fun h => hil h.symm, if_neg hil]
  rw [h, h', neg_smul, sub_eq_add_neg]
  simp

private lemma spN_mul_spT (a c c' a' : Fin r ⊕ Fin r → K) :
    spN a c * spT c' a' = spForm a' c • spT c' a + spForm a' a • spT c' c := by
  rw [spN, Matrix.add_mul, spT_mul_spT, spT_mul_spT]

private lemma spT_mul_spN (c a a' c' : Fin r ⊕ Fin r → K) :
    spT c a * spN a' c' = spForm a' c • spT c' a + spForm c' c • spT a' a := by
  rw [spN, Matrix.mul_add, spT_mul_spT, spT_mul_spT]

private lemma frame_spN_mul_zero {e f : Fin 4 → Fin r ⊕ Fin r → K} (hef : IsSpFrame e f)
    {i j k l : Fin 4} (hjk : j ≠ k) (hil : i ≠ l) :
    spN (e i) (f j) * spN (e k) (f l) = 0 := by
  rw [frame_spN_mul hef, if_neg hjk, if_neg hil, zero_smul, zero_smul, sub_zero]

private lemma frame_spN_mul_te {e f : Fin 4 → Fin r ⊕ Fin r → K} (hef : IsSpFrame e f)
    {i j l : Fin 4} (hil : i ≠ l) :
    spN (e i) (f j) * spN (e j) (f l) = spT (f l) (e i) := by
  rw [frame_spN_mul hef, if_pos rfl, if_neg hil, one_smul, zero_smul, sub_zero]

private lemma frame_spN_mul_tn {e f : Fin 4 → Fin r ⊕ Fin r → K} (hef : IsSpFrame e f)
    {i j k : Fin 4} (hjk : j ≠ k) :
    spN (e i) (f j) * spN (e k) (f i) = -spT (e k) (f j) := by
  rw [frame_spN_mul hef, if_neg hjk, if_pos rfl, zero_smul, one_smul, zero_sub]

private lemma frame_T_fe_mul_N {e f : Fin 4 → Fin r ⊕ Fin r → K} (hef : IsSpFrame e f)
    (i j k l : Fin 4) :
    spT (f i) (e j) * spN (e k) (f l) = (if k = i then 1 else 0) • spT (f l) (e j) := by
  rw [spT_mul_spN, (hef k i).2.2, (hef l i).2.1]
  simp

private lemma frame_T_ef_mul_N {e f : Fin 4 → Fin r ⊕ Fin r → K} (hef : IsSpFrame e f)
    (i j k l : Fin 4) :
    spT (e i) (f j) * spN (e k) (f l) = -(if l = i then 1 else 0) • spT (e k) (f j) := by
  rw [spT_mul_spN, (hef k i).1, spForm_frame_f_e hef l i]
  simp

private lemma frame_N_mul_T_fe {e f : Fin 4 → Fin r ⊕ Fin r → K} (hef : IsSpFrame e f)
    (i j k l : Fin 4) :
    spN (e i) (f j) * spT (f k) (e l) = (if l = j then 1 else 0) • spT (f k) (e i) := by
  rw [spN_mul_spT, (hef l j).2.2, (hef l i).1]
  simp

private lemma frame_N_mul_T_ef {e f : Fin 4 → Fin r ⊕ Fin r → K} (hef : IsSpFrame e f)
    (i j k l : Fin 4) :
    spN (e i) (f j) * spT (e k) (f l) = -(if l = i then 1 else 0) • spT (e k) (f j) := by
  rw [spN_mul_spT, (hef l j).2.1, spForm_frame_f_e hef l i]
  simp

private lemma frame_e_ne_zero {e f : Fin 4 → Fin r ⊕ Fin r → K} (hef : IsSpFrame e f)
    (i : Fin 4) : e i ≠ 0 := by
  intro h
  have h1 := (hef i i).2.2
  rw [h, if_pos rfl] at h1
  simp [spForm] at h1

private lemma frame_f_ne_zero {e f : Fin 4 → Fin r ⊕ Fin r → K} (hef : IsSpFrame e f)
    (i : Fin 4) : f i ≠ 0 := by
  intro h
  have h1 := (hef i i).2.2
  rw [h, if_pos rfl] at h1
  simp [spForm] at h1

private lemma frame_T10_ne_zero {e f : Fin 4 → Fin r ⊕ Fin r → K} (hef : IsSpFrame e f) :
    spT (f 1) (e 0) ≠ 0 := by
  intro h
  have h2 := congrArg (fun M => M *ᵥ e 1) h
  simp only [Matrix.zero_mulVec] at h2
  rw [spT_mulVec, (hef 1 1).2.2, if_pos rfl, one_smul] at h2
  exact frame_e_ne_zero hef 0 h2

private lemma frame_T01_ne_zero {e f : Fin 4 → Fin r ⊕ Fin r → K} (hef : IsSpFrame e f) :
    spT (e 0) (f 1) ≠ 0 := by
  intro h
  have h2 := congrArg (fun M => M *ᵥ f 0) h
  simp only [Matrix.zero_mulVec] at h2
  rw [spT_mulVec, spForm_frame_f_e hef 0 0, if_pos rfl, neg_one_smul] at h2
  exact frame_f_ne_zero hef 1 (neg_eq_zero.mp h2)

private lemma frame_N01_ne_zero {e f : Fin 4 → Fin r ⊕ Fin r → K} (hef : IsSpFrame e f) :
    spN (e 0) (f 1) ≠ 0 := by
  intro h
  have h2 : spN (e 0) (f 1) *ᵥ f 0 = - f 1 := by
    rw [spN, Matrix.add_mulVec, spT_mulVec, spT_mulVec, (hef 0 1).2.1,
      spForm_frame_f_e hef 0 0, if_pos rfl, zero_smul, zero_add, neg_one_smul]
  rw [h, Matrix.zero_mulVec] at h2
  exact frame_f_ne_zero hef 1 (neg_eq_zero.mp h2.symm)

theorem frameN_mul_self {e f : Fin 4 → Fin r ⊕ Fin r → K} (hef : IsSpFrame e f) :
    frameN e f * frameN e f = 0 := by
  have h03 : spN (e 0) (f 3) * spN (e 0) (f 3) = 0 := by
    rw [frame_spN_mul hef]; simp
  have h03' : spN (e 0) (f 3) * spN (e 2) (f 1) = 0 := by
    rw [frame_spN_mul hef]; simp
  have h21 : spN (e 2) (f 1) * spN (e 0) (f 3) = 0 := by
    rw [frame_spN_mul hef]; simp
  have h21' : spN (e 2) (f 1) * spN (e 2) (f 1) = 0 := by
    rw [frame_spN_mul hef]; simp
  rw [frameN, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, h03, h03', h21, h21']
  abel

theorem good_unipSp_frameN_three [Finite K] (hK : Nat.card K = 3) (hr : 1 ≤ r)
    {e f : Fin 4 → Fin r ⊕ Fin r → K} (hef : IsSpFrame e f) :
    orderOf (proj r K (unipSp (frameN e f) (isSp_frameN e f) (frameN_mul_self hef))) = 3 ∧
      IsExtraGood (proj r K (unipSp (frameN e f) (isSp_frameN e f) (frameN_mul_self hef))) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hk' : Fintype.card K = 3 := by rwa [Fintype.card_eq_nat_card]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 := charP_of_card_eq_prime hk'
  have hb03 : spForm (e 0) (f 3) = 0 := by rw [(hef 0 3).2.2]; simp
  have hb31 : spForm (e 3) (f 1) = 0 := by rw [(hef 3 1).2.2]; simp
  have hb21 : spForm (e 2) (f 1) = 0 := by rw [(hef 2 1).2.2]; simp
  have hb02 : spForm (e 0) (f 2) = 0 := by rw [(hef 0 2).2.2]; simp
  have hs₁ : (spN (e 0) (f 3))ᵀ * formJ r K + formJ r K * spN (e 0) (f 3) = 0 :=
    isSp_spN _ _
  have hs₂ : (spN (e 3) (f 1))ᵀ * formJ r K + formJ r K * spN (e 3) (f 1) = 0 :=
    isSp_spN _ _
  have hs₃ : (-spN (e 2) (f 1))ᵀ * formJ r K + formJ r K * (-spN (e 2) (f 1)) = 0 :=
    isSp_neg (isSp_spN _ _)
  have hs₄ : (spN (e 0) (f 2))ᵀ * formJ r K + formJ r K * spN (e 0) (f 2) = 0 :=
    isSp_spN _ _
  have h₁ : spN (e 0) (f 3) * spN (e 0) (f 3) = 0 := spN_mul_self hb03
  have h₂ : spN (e 3) (f 1) * spN (e 3) (f 1) = 0 := spN_mul_self hb31
  have h₃ : (-spN (e 2) (f 1)) * (-spN (e 2) (f 1)) = 0 :=
    neg_mul_self_neg (spN_mul_self hb21)
  have h₄ : spN (e 0) (f 2) * spN (e 0) (f 2) = 0 := spN_mul_self hb02
  have hA12 : spN (e 0) (f 3) * spN (e 3) (f 1) = spT (f 1) (e 0) :=
    frame_spN_mul_te hef (i := 0) (j := 3) (l := 1) (by decide)
  have hA21 : spN (e 3) (f 1) * spN (e 0) (f 3) = -spT (e 0) (f 1) :=
    frame_spN_mul_tn hef (i := 3) (j := 1) (k := 0) (by decide)
  have hA34 : -spN (e 2) (f 1) * spN (e 0) (f 2) = spT (e 0) (f 1) := by
    rw [Matrix.neg_mul, frame_spN_mul_tn hef (i := 2) (j := 1) (k := 0) (by decide), neg_neg]
  have hA43 : spN (e 0) (f 2) * -spN (e 2) (f 1) = -spT (f 1) (e 0) := by
    rw [Matrix.mul_neg, frame_spN_mul_te hef (i := 0) (j := 2) (l := 1) (by decide)]
  have h₁₂₁ : spN (e 0) (f 3) * spN (e 3) (f 1) * spN (e 0) (f 3) = 0 := by
    rw [hA12, frame_T_fe_mul_N hef 1 0 0 3]
    simp
  have h₂₁₂ : spN (e 3) (f 1) * spN (e 0) (f 3) * spN (e 3) (f 1) = 0 := by
    rw [hA21, Matrix.neg_mul, frame_T_ef_mul_N hef 0 1 3 1]
    simp
  have h₃₄₃ : -spN (e 2) (f 1) * spN (e 0) (f 2) * -spN (e 2) (f 1) = 0 := by
    rw [Matrix.mul_assoc, hA43, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
      frame_N_mul_T_fe hef 2 1 1 0]
    simp
  have h₄₃₄ : spN (e 0) (f 2) * -spN (e 2) (f 1) * spN (e 0) (f 2) = 0 := by
    rw [Matrix.mul_assoc, hA34, frame_N_mul_T_ef hef 0 2 0 1]
    simp
  have h₁₂ : spN (e 0) (f 3) * spN (e 3) (f 1) ≠ 0 := by
    rw [hA12]; exact frame_T10_ne_zero hef
  have h₃₄ : -spN (e 2) (f 1) * spN (e 0) (f 2) ≠ 0 := by
    rw [hA34]; exact frame_T01_ne_zero hef
  have hPQ : spN (e 0) (f 3) * spN (e 3) (f 1) ≠ spN (e 3) (f 1) * spN (e 0) (f 3) := by
    rw [hA12, hA21]
    intro h
    exact frame_N01_ne_zero hef (by rw [spN, h]; abel)
  have hPQ' : -spN (e 2) (f 1) * spN (e 0) (f 2) ≠ spN (e 0) (f 2) * -spN (e 2) (f 1) := by
    rw [hA34, hA43]
    intro h
    exact frame_N01_ne_zero hef (by rw [spN, add_comm, h]; abel)
  have h₁₃ : spN (e 0) (f 3) * -spN (e 2) (f 1) = 0 := by
    rw [Matrix.mul_neg, frame_spN_mul_zero hef (i := 0) (j := 3) (k := 2) (l := 1)
      (by decide) (by decide), neg_zero]
  have h₁₄ : spN (e 0) (f 3) * spN (e 0) (f 2) = 0 :=
    frame_spN_mul_zero hef (i := 0) (j := 3) (k := 0) (l := 2) (by decide) (by decide)
  have h₂₃ : spN (e 3) (f 1) * -spN (e 2) (f 1) = 0 := by
    rw [Matrix.mul_neg, frame_spN_mul_zero hef (i := 3) (j := 1) (k := 2) (l := 1)
      (by decide) (by decide), neg_zero]
  have h₂₄ : spN (e 3) (f 1) * spN (e 0) (f 2) = 0 :=
    frame_spN_mul_zero hef (i := 3) (j := 1) (k := 0) (l := 2) (by decide) (by decide)
  have h₃₁ : -spN (e 2) (f 1) * spN (e 0) (f 3) = 0 := by
    rw [Matrix.neg_mul, frame_spN_mul_zero hef (i := 2) (j := 1) (k := 0) (l := 3)
      (by decide) (by decide), neg_zero]
  have h₃₂ : -spN (e 2) (f 1) * spN (e 3) (f 1) = 0 := by
    rw [Matrix.neg_mul, frame_spN_mul_zero hef (i := 2) (j := 1) (k := 3) (l := 1)
      (by decide) (by decide), neg_zero]
  have h₄₁ : spN (e 0) (f 2) * spN (e 0) (f 3) = 0 :=
    frame_spN_mul_zero hef (i := 0) (j := 2) (k := 0) (l := 3) (by decide) (by decide)
  have h₄₂ : spN (e 0) (f 2) * spN (e 3) (f 1) = 0 :=
    frame_spN_mul_zero hef (i := 0) (j := 2) (k := 3) (l := 1) (by decide) (by decide)
  have hcen : spN (e 0) (f 3) * spN (e 3) (f 1) -
      spN (e 3) (f 1) * spN (e 0) (f 3) =
      -spN (e 2) (f 1) * spN (e 0) (f 2) - spN (e 0) (f 2) * -spN (e 2) (f 1) := by
    rw [hA12, hA21, hA34, hA43]
    abel
  obtain ⟨ι₁, ι₂, hι₁, hι₂, hcomm, hcenι, hι₁1, hι₂1, -⟩ :=
    exists_heis_pair_projectiveSp hr (N₁ := spN (e 0) (f 3)) (N₂ := spN (e 3) (f 1))
      (N₃ := -spN (e 2) (f 1)) (N₄ := spN (e 0) (f 2))
      hs₁ hs₂ hs₃ hs₄ h₁ h₂ h₃ h₄ h₁₂₁ h₂₁₂ h₃₄₃ h₄₃₄ h₁₂ hPQ h₃₄ hPQ'
      h₁₃ h₁₄ h₂₃ h₂₄ h₃₁ h₃₂ h₄₁ h₄₂ hcen
  have hunip : unipSp (frameN e f) (isSp_frameN e f) (frameN_mul_self hef) =
      unipSp (spN (e 0) (f 3)) hs₁ h₁ * unipSp (-spN (e 2) (f 1)) hs₃ h₃ := by
    apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
    rw [Subgroup.coe_mul, Units.val_mul, coe_unipSp, coe_unipSp, coe_unipSp]
    rw [frameN, sub_eq_add_neg, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul,
      Matrix.one_mul, h₁₃]
    abel
  have hx : proj r K (unipSp (frameN e f) (isSp_frameN e f) (frameN_mul_self hef)) =
      ι₁ ⟨1, 0, 0⟩ * ι₂ ⟨1, 0, 0⟩ := by
    rw [hunip, map_mul, hι₁1, hι₂1]
  have hmem : proj r K (unipSp (frameN e f) (isSp_frameN e f) (frameN_mul_self hef)) ∈
      ι₁.range ⊔ ι₂.range := by
    rw [hx]
    exact Subgroup.mul_mem_sup (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
      (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hx3 : (proj r K (unipSp (frameN e f) (isSp_frameN e f) (frameN_mul_self hef))) ^ 3 = 1 := by
    have hu3 : ((⟨1, 0, 0⟩ : Heis K) ^ 3) = 1 :=
      Heis.pow_prime_eq_one Nat.prime_three (by norm_num) ⟨1, 0, 0⟩
    calc (proj r K (unipSp (frameN e f) (isSp_frameN e f) (frameN_mul_self hef))) ^ 3
        = (ι₁ ⟨1, 0, 0⟩ * ι₂ ⟨1, 0, 0⟩) ^ 3 := by rw [hx]
      _ = (ι₁ ⟨1, 0, 0⟩) ^ 3 * (ι₂ ⟨1, 0, 0⟩) ^ 3 :=
            (hcomm ⟨1, 0, 0⟩ ⟨1, 0, 0⟩).mul_pow 3
      _ = ι₁ ((⟨1, 0, 0⟩ : Heis K) ^ 3) * ι₂ ((⟨1, 0, 0⟩ : Heis K) ^ 3) := by
            rw [map_pow, map_pow]
      _ = 1 := by rw [hu3, map_one, map_one, mul_one]
  have hne : proj r K (unipSp (frameN e f) (isSp_frameN e f) (frameN_mul_self hef)) ≠ 1 := by
    intro h1
    have hscal : unipSp (frameN e f) (isSp_frameN e f) (frameN_mul_self hef) ∈
        CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars r K := by
      rw [← CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj]
      exact h1
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars, Subgroup.mem_subgroupOf,
      CFSG.Open.StatedScalars, MonoidHom.mem_range] at hscal
    obtain ⟨d, hd⟩ := hscal
    have hdN : (1 + frameN e f : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        (d : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
      have h := congrArg (fun g : GL (Fin r ⊕ Fin r) K =>
        (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hd
      rw [coe_unipSp] at h
      rw [← h, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal]
    have hNscal : frameN e f =
        ((d : K) - 1) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
      calc frameN e f = (1 + frameN e f) - 1 := by abel
        _ = (d : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) - 1 := by rw [hdN]
        _ = ((d : K) - 1) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
            rw [sub_smul, one_smul]
    have hsq : (((d : K) - 1) ^ 2) •
        (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 0 := by
      have h := frameN_mul_self hef
      rw [hNscal, Matrix.smul_mul, Matrix.one_mul, smul_smul] at h
      simpa [pow_two] using h
    have hcz : ((d : K) - 1) ^ 2 = 0 := by
      have hr0 : 0 < r := by omega
      have h00 := congrFun (congrFun hsq (Sum.inl ⟨0, hr0⟩)) (Sum.inl ⟨0, hr0⟩)
      simpa using h00
    have hN0 : frameN e f = 0 := by
      rw [hNscal, eq_zero_of_pow_eq_zero hcz, zero_smul]
    have hval : frameN e f *ᵥ f 0 = - f 3 := by
      have hA : spN (e 0) (f 3) *ᵥ f 0 = - f 3 := by
        rw [spN, Matrix.add_mulVec, spT_mulVec, spT_mulVec, (hef 0 3).2.1,
          spForm_frame_f_e hef 0 0, if_pos rfl, zero_smul, zero_add, neg_one_smul]
      have hM : spN (e 2) (f 1) *ᵥ f 0 = 0 := by
        rw [spN, Matrix.add_mulVec, spT_mulVec, spT_mulVec, (hef 0 1).2.1,
          spForm_frame_f_e hef 0 2, if_neg (by decide), neg_zero, zero_smul, zero_smul,
          add_zero]
      rw [frameN, Matrix.sub_mulVec, hA, hM, sub_zero]
    rw [hN0, Matrix.zero_mulVec] at hval
    exact frame_f_ne_zero hef 3 (neg_eq_zero.mp hval.symm)
  exact ⟨orderOf_eq_prime hx3 hne,
    isExtraGood_of_mem_sup_heis_pair hK hι₁ hι₂ hcomm hcenι hmem⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

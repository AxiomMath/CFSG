module

public import CFSG.RankThree.PartOne.K159.KleinWeights

public section

namespace CFSG.RankThree.PartOne.K159.Klein

open Matrix CFSG.LocalAnalysis Finset

variable {K : Type} [Field K]

theorem coords_apply_kleinIndexPair (M : Matrix (Fin 4) (Fin 4) K) (s : Fin 3 ⊕ Fin 3) :
    coords M s = M (kleinIndexPair s).1 (kleinIndexPair s).2 := by
  rcases s with c | c <;> fin_cases c <;> rfl

theorem alt_single_eq [CharP K 2] (s : Fin 3 ⊕ Fin 3) :
    alt (Pi.single s (1 : K)) = single (kleinIndexPair s).1 (kleinIndexPair s).2 1 +
      single (kleinIndexPair s).2 (kleinIndexPair s).1 1 := by
  rcases s with c | c <;> fin_cases c <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [alt, antiMat, kleinIndexPair, single_apply, CharTwo.neg_eq]

theorem mul_single_one_mul_transpose_apply (g : Matrix (Fin 4) (Fin 4) K) (a b i j : Fin 4) :
    (g * (single a b 1 : Matrix (Fin 4) (Fin 4) K) * gᵀ) i j = g i a * g j b := by
  simp only [mul_apply, single_apply, transpose_apply, mul_ite, mul_one, mul_zero, ite_and,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, ite_mul, zero_mul]

theorem cong_single_apply [CharP K 2] (g : Matrix (Fin 4) (Fin 4) K) (s s' : Fin 3 ⊕ Fin 3) :
    cong g (Pi.single s 1) s' =
      g (kleinIndexPair s').1 (kleinIndexPair s).1 * g (kleinIndexPair s').2 (kleinIndexPair s).2 +
        g (kleinIndexPair s').1 (kleinIndexPair s).2 *
          g (kleinIndexPair s').2 (kleinIndexPair s).1 := by
  rw [cong_apply, coords_apply_kleinIndexPair, alt_single_eq, Matrix.mul_add, Matrix.add_mul,
    Matrix.add_apply, mul_single_one_mul_transpose_apply, mul_single_one_mul_transpose_apply]

@[expose] def RootEntry (p q u v : Fin 4) : Prop := u = v ∨ (u = p ∧ v = q)

instance (p q u v : Fin 4) : Decidable (RootEntry p q u v) := by
  unfold RootEntry
  infer_instance

theorem coe_transvection_one_apply {p q : Fin 4} (hpq : p ≠ q) (u v : Fin 4) :
    (Matrix.SpecialLinearGroup.transvection hpq (1 : K) : Matrix (Fin 4) (Fin 4) K) u v =
      if RootEntry p q u v then 1 else 0 := by
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, one_apply, single_apply]
  unfold RootEntry
  by_cases huv : u = v
  · subst huv
    have h : ¬(p = u ∧ q = u) := fun h => hpq (h.1.trans h.2.symm)
    simp [h]
  · by_cases h : u = p ∧ v = q
    · obtain ⟨rfl, rfl⟩ := h
      simp [huv]
    · have h' : ¬(p = u ∧ q = v) := fun h'' => h ⟨h''.1.symm, h''.2.symm⟩
      simp [huv, h, h']

@[expose] def rootSuppN (p q m : Fin 4) : Finset (Fin 4) := univ.filter fun k => RootEntry p q k m

@[expose] def rootSuppW (p q : Fin 4) (s : Fin 3 ⊕ Fin 3) : Finset (Fin 3 ⊕ Fin 3) :=
  univ.filter fun s' =>
    ¬((RootEntry p q (kleinIndexPair s').1 (kleinIndexPair s).1 ∧
        RootEntry p q (kleinIndexPair s').2 (kleinIndexPair s).2) ↔
      (RootEntry p q (kleinIndexPair s').1 (kleinIndexPair s).2 ∧
        RootEntry p q (kleinIndexPair s').2 (kleinIndexPair s).1))

theorem transvection_smul_single_eq_sum {p q : Fin 4} (hpq : p ≠ q) (m : Fin 4) :
    Matrix.SpecialLinearGroup.transvection hpq (1 : K) • (Pi.single m 1 : Fin 4 → K) =
      ∑ k ∈ rootSuppN p q m, Pi.single k 1 := by
  ext k
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, mulVec_single_one, col_apply,
    coe_transvection_one_apply hpq, Finset.sum_apply]
  simp only [Pi.single_apply, Finset.sum_ite_eq, rootSuppN, Finset.mem_filter, Finset.mem_univ,
    true_and]

theorem rho_transvection_single_eq_sum [CharP K 2] {p q : Fin 4} (hpq : p ≠ q)
    (s : Fin 3 ⊕ Fin 3) :
    rho (Matrix.SpecialLinearGroup.transvection hpq (1 : K)) (Pi.single s 1) =
      ∑ s' ∈ rootSuppW p q s, Pi.single s' 1 := by
  have key : ∀ (P₁ P₂ P₃ P₄ : Prop) [Decidable P₁] [Decidable P₂] [Decidable P₃] [Decidable P₄],
      (if P₁ then (1 : K) else 0) * (if P₂ then 1 else 0) +
          (if P₃ then 1 else 0) * (if P₄ then 1 else 0) =
        if ¬((P₁ ∧ P₂) ↔ (P₃ ∧ P₄)) then 1 else 0 := by
    intro P₁ P₂ P₃ P₄ _ _ _ _
    by_cases h₁ : P₁ <;> by_cases h₂ : P₂ <;> by_cases h₃ : P₃ <;> by_cases h₄ : P₄ <;>
      simp [h₁, h₂, h₃, h₄, CharTwo.add_self_eq_zero]
  funext s'
  rw [rho_apply, cong_single_apply, coe_transvection_one_apply hpq, coe_transvection_one_apply hpq,
    coe_transvection_one_apply hpq, coe_transvection_one_apply hpq, key, Finset.sum_apply]
  simp only [Pi.single_apply, Finset.sum_ite_eq, rootSuppW, Finset.mem_filter, Finset.mem_univ,
    true_and]

abbrev NoInvIdx := Fin 4 × (Fin 3 ⊕ Fin 3) × Fin 4 × (Fin 3 ⊕ Fin 3)

@[expose] def noInvCoeff (β : (Fin 4 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 4 → K) →ₗ[K]
    (Fin 3 ⊕ Fin 3 → K) →ₗ[K] K) (τ : NoInvIdx) : K :=
  β (Pi.single τ.1 1) (Pi.single τ.2.1 1) (Pi.single τ.2.2.1 1) (Pi.single τ.2.2.2 1)

@[expose] def rootSupp (p q : Fin 4) (τ : NoInvIdx) : Finset NoInvIdx :=
  rootSuppN p q τ.1 ×ˢ rootSuppW p q τ.2.1 ×ˢ rootSuppN p q τ.2.2.1 ×ˢ rootSuppW p q τ.2.2.2

theorem noInvCoeff_root [CharP K 2] (σ : K →+* K)
    {β : (Fin 4 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 4 → K) →ₗ[K]
      (Fin 3 ⊕ Fin 3 → K) →ₗ[K] K}
    (hβ : ∀ (A : Matrix.SpecialLinearGroup (Fin 4) K) (v v' : Fin 4 → K)
        (w w' : Fin 3 ⊕ Fin 3 → K),
      β (Matrix.SpecialLinearGroup.map σ A • v) (rho A w)
          (Matrix.SpecialLinearGroup.map σ A • v') (rho A w') = β v w v' w')
    {p q : Fin 4} (hpq : p ≠ q) (τ : NoInvIdx) :
    ∑ τ' ∈ rootSupp p q τ, noInvCoeff β τ' = noInvCoeff β τ := by
  have hmap : Matrix.SpecialLinearGroup.map σ (Matrix.SpecialLinearGroup.transvection hpq (1 : K)) =
      Matrix.SpecialLinearGroup.transvection hpq 1 := by
    ext u v
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, map_apply,
      coe_transvection_one_apply hpq]
    split_ifs <;> simp
  have h := hβ (Matrix.SpecialLinearGroup.transvection hpq 1) (Pi.single τ.1 1)
    (Pi.single τ.2.2.1 1) (Pi.single τ.2.1 1) (Pi.single τ.2.2.2 1)
  rw [hmap, transvection_smul_single_eq_sum hpq, transvection_smul_single_eq_sum hpq,
    rho_transvection_single_eq_sum hpq, rho_transvection_single_eq_sum hpq] at h
  simp only [map_sum, LinearMap.sum_apply] at h
  rw [noInvCoeff, ← h]
  simp only [rootSupp, Finset.sum_product_right, noInvCoeff]

@[expose] def kleinCnt (s : Fin 3 ⊕ Fin 3) : Fin 4 → ℤ :=
  Pi.single (kleinIndexPair s).1 1 + Pi.single (kleinIndexPair s).2 1

@[expose] def NoInvTorusKilled (τ : NoInvIdx) : Prop :=
  HasGap (kleinCnt τ.2.1 + kleinCnt τ.2.2.2) ((univ.erase τ.1).erase τ.2.2.1)

instance (τ : NoInvIdx) : Decidable (NoInvTorusKilled τ) := by
  unfold NoInvTorusKilled
  infer_instance

theorem twoPtEntry_mul_twoPtEntry (t : TwoPt K) (s : Fin 3 ⊕ Fin 3) :
    twoPtEntry t (kleinIndexPair s).1 * twoPtEntry t (kleinIndexPair s).2 =
      twoPtWt (kleinCnt s) t := by
  rw [kleinCnt, twoPtWt_add, twoPtEntry_eq_twoPtWt, twoPtEntry_eq_twoPtWt]

theorem noInvCoeff_eq_zero_of_torusKilled [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (σ : K →+* K)
    {β : (Fin 4 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 4 → K) →ₗ[K]
      (Fin 3 ⊕ Fin 3 → K) →ₗ[K] K}
    (hβ : ∀ (A : Matrix.SpecialLinearGroup (Fin 4) K) (v v' : Fin 4 → K)
        (w w' : Fin 3 ⊕ Fin 3 → K),
      β (Matrix.SpecialLinearGroup.map σ A • v) (rho A w)
          (Matrix.SpecialLinearGroup.map σ A • v') (rho A w') = β v w v' w')
    {τ : NoInvIdx} (hτ : NoInvTorusKilled τ) : noInvCoeff β τ = 0 := by
  obtain ⟨i, s, j, s'⟩ := τ
  obtain ⟨t, ht1, htw⟩ := exists_twoPtWt_ne hK (μ := 0) (by rw [sub_zero]; exact hτ)
  have hi : twoPtEntry t i = 1 := ht1 i (by simp)
  have hj : twoPtEntry t j = 1 := ht1 j (by simp)
  have h := hβ (twoPtSL t) (Pi.single i 1) (Pi.single j 1) (Pi.single s 1) (Pi.single s' 1)
  rw [map_twoPtSL_smul_single, map_twoPtSL_smul_single, hi, hj, map_one, one_smul, one_smul,
    rho_twoPtSL_single, rho_twoPtSL_single, twoPtEntry_mul_twoPtEntry,
    twoPtEntry_mul_twoPtEntry] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  have h0 : twoPtWt (0 : Fin 4 → ℤ) t = 1 := by simp [twoPtWt]
  have hne : twoPtWt (kleinCnt s + kleinCnt s') t - 1 ≠ 0 := sub_ne_zero.mpr (h0 ▸ htw)
  have h2 : (twoPtWt (kleinCnt s + kleinCnt s') t - 1) * noInvCoeff β (i, s, j, s') = 0 := by
    rw [twoPtWt_add, noInvCoeff]
    linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left hne

@[expose] def NoInvKilled (done : List NoInvIdx) (τ : NoInvIdx) : Prop :=
  NoInvTorusKilled τ ∨ τ ∈ done

instance (done : List NoInvIdx) (τ : NoInvIdx) : Decidable (NoInvKilled done τ) := by
  unfold NoInvKilled
  infer_instance

@[expose] def NoInvRestKilled (done : List NoInvIdx) (t c : NoInvIdx) (p q : Fin 4) : Prop :=
  ∀ τ ∈ rootSupp p q c, τ = c ∨ τ = t ∨ NoInvKilled done τ

instance (done : List NoInvIdx) (t c : NoInvIdx) (p q : Fin 4) :
    Decidable (NoInvRestKilled done t c p q) := by
  unfold NoInvRestKilled
  infer_instance

@[expose] def noInvStepOK (done : List NoInvIdx) (t c : NoInvIdx) (p q : Fin 4) : Bool :=
  decide (p ≠ q) && decide (c ∈ rootSupp p q c) && decide (t ∈ rootSupp p q c) &&
    decide (t ≠ c) && decide (NoInvRestKilled done t c p q)

@[expose] def noInvStepsCheck :
    List NoInvIdx → List (NoInvIdx × NoInvIdx × Fin 4 × Fin 4) → Bool
  | _, [] => true
  | done, (t, c, p, q) :: rest => noInvStepOK done t c p q && noInvStepsCheck (t :: done) rest

theorem eq_zero_of_noInvStepsCheck {C : NoInvIdx → K} (hT : ∀ τ, NoInvTorusKilled τ → C τ = 0)
    (hR : ∀ p q : Fin 4, p ≠ q → ∀ τ, ∑ τ' ∈ rootSupp p q τ, C τ' = C τ) :
    ∀ (steps : List (NoInvIdx × NoInvIdx × Fin 4 × Fin 4)) (done : List NoInvIdx),
      (∀ τ ∈ done, C τ = 0) → noInvStepsCheck done steps = true →
        ∀ τ ∈ steps.map Prod.fst, C τ = 0
  | [], _, _, _ => by simp
  | (t, c, p, q) :: rest, done, hdone, hcheck => by
    rw [noInvStepsCheck, Bool.and_eq_true, noInvStepOK] at hcheck
    obtain ⟨hstep, hrest⟩ := hcheck
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hstep
    obtain ⟨⟨⟨⟨hpq, hc⟩, ht⟩, htc⟩, hkill⟩ := hstep
    have h1 := hR p q hpq c
    rw [← Finset.add_sum_erase _ _ hc, add_eq_left] at h1
    rw [Finset.sum_eq_single_of_mem t (Finset.mem_erase.mpr ⟨htc, ht⟩) fun τ hτ hτt => ?_] at h1
    · have hdone' : ∀ τ ∈ t :: done, C τ = 0 := by
        intro τ hτ
        rcases List.mem_cons.mp hτ with rfl | hτ
        · exact h1
        · exact hdone τ hτ
      intro τ hτ
      rcases List.mem_cons.mp hτ with rfl | hτ
      · exact h1
      · exact eq_zero_of_noInvStepsCheck hT hR rest (t :: done) hdone' hrest τ hτ
    · obtain ⟨hτc, hτS⟩ := Finset.mem_erase.mp hτ
      rcases hkill τ hτS with h | h | h | h
      · exact absurd h hτc
      · exact absurd h hτt
      · exact hT τ h
      · exact hdone τ h

@[expose] def noInvSteps : List (NoInvIdx × NoInvIdx × Fin 4 × Fin 4) := [
    ((2, .inr 2, 1, .inr 2), (0, .inl 0, 1, .inl 0), 2, 0),
    ((0, .inl 1, 2, .inl 1), (0, .inl 0, 1, .inl 0), 2, 1),
    ((3, .inr 1, 1, .inr 1), (0, .inl 0, 1, .inl 0), 3, 0),
    ((0, .inl 2, 3, .inl 2), (0, .inl 0, 1, .inl 0), 3, 1),
    ((0, .inl 0, 1, .inl 0), (0, .inl 0, 1, .inl 1), 1, 2),
    ((0, .inl 0, 0, .inr 0), (0, .inl 0, 1, .inr 0), 0, 1),
    ((1, .inl 0, 1, .inr 0), (0, .inl 0, 1, .inr 0), 1, 0),
    ((2, .inl 0, 1, .inr 0), (0, .inl 0, 1, .inr 0), 2, 0),
    ((0, .inl 0, 2, .inr 0), (0, .inl 0, 1, .inr 0), 2, 1),
    ((3, .inl 0, 1, .inr 0), (0, .inl 0, 1, .inr 0), 3, 0),
    ((0, .inl 0, 3, .inr 0), (0, .inl 0, 1, .inr 0), 3, 1),
    ((1, .inl 0, 2, .inr 1), (0, .inl 0, 2, .inl 2), 1, 0),
    ((3, .inr 1, 2, .inl 2), (0, .inl 0, 2, .inl 2), 3, 0),
    ((0, .inl 2, 2, .inr 2), (0, .inl 0, 2, .inr 2), 3, 1),
    ((0, .inl 0, 2, .inl 2), (0, .inl 0, 2, .inr 1), 0, 1),
    ((0, .inl 1, 2, .inr 1), (0, .inl 0, 2, .inr 1), 2, 1),
    ((0, .inr 1, 2, .inr 1), (0, .inl 0, 2, .inr 1), 3, 0),
    ((1, .inl 0, 2, .inr 0), (0, .inl 0, 2, .inr 0), 1, 0),
    ((0, .inl 0, 1, .inr 0), (0, .inl 0, 2, .inr 0), 1, 2),
    ((3, .inl 0, 2, .inr 0), (0, .inl 0, 2, .inr 0), 3, 0),
    ((1, .inl 0, 3, .inr 2), (0, .inl 0, 3, .inl 1), 1, 0),
    ((2, .inr 2, 3, .inl 1), (0, .inl 0, 3, .inl 1), 2, 0),
    ((0, .inl 0, 3, .inl 1), (0, .inl 0, 3, .inl 2), 2, 3),
    ((0, .inr 2, 3, .inr 2), (0, .inl 0, 3, .inr 2), 2, 0),
    ((0, .inl 2, 3, .inr 2), (0, .inl 0, 3, .inr 2), 3, 1),
    ((0, .inl 1, 3, .inr 1), (0, .inl 0, 3, .inr 1), 2, 1),
    ((1, .inl 0, 3, .inr 0), (0, .inl 0, 3, .inr 0), 1, 0),
    ((2, .inl 0, 3, .inr 0), (0, .inl 0, 3, .inr 0), 2, 0),
    ((2, .inl 1, 0, .inl 1), (0, .inl 1, 0, .inl 1), 2, 0),
    ((0, .inl 1, 0, .inr 1), (0, .inl 1, 0, .inr 0), 1, 2),
    ((2, .inl 1, 1, .inr 0), (0, .inl 1, 1, .inl 2), 2, 0),
    ((3, .inr 0, 1, .inl 2), (0, .inl 1, 1, .inl 2), 3, 0),
    ((0, .inl 1, 1, .inl 2), (0, .inl 1, 1, .inr 1), 0, 1),
    ((2, .inl 1, 1, .inr 1), (0, .inl 1, 1, .inr 1), 2, 0),
    ((3, .inl 1, 1, .inr 1), (0, .inl 1, 1, .inr 1), 3, 0),
    ((0, .inl 1, 1, .inr 1), (0, .inl 1, 1, .inr 0), 1, 2),
    ((0, .inr 0, 1, .inr 0), (0, .inl 1, 1, .inr 0), 3, 0),
    ((1, .inr 2, 2, .inr 2), (0, .inl 1, 2, .inl 1), 1, 0),
    ((3, .inr 0, 2, .inr 0), (0, .inl 1, 2, .inl 1), 3, 0),
    ((1, .inl 1, 2, .inr 1), (0, .inl 1, 2, .inr 1), 1, 0),
    ((2, .inl 1, 2, .inr 1), (0, .inl 1, 2, .inr 1), 2, 0),
    ((3, .inl 1, 2, .inr 1), (0, .inl 1, 2, .inr 1), 3, 0),
    ((1, .inr 2, 3, .inl 0), (0, .inl 1, 3, .inl 0), 1, 0),
    ((2, .inl 1, 3, .inr 2), (0, .inl 1, 3, .inl 0), 2, 0),
    ((1, .inl 1, 3, .inl 1), (0, .inl 1, 3, .inl 1), 1, 0),
    ((0, .inl 1, 3, .inl 0), (0, .inl 1, 3, .inl 1), 1, 2),
    ((1, .inl 1, 3, .inr 1), (0, .inl 1, 3, .inr 1), 1, 0),
    ((2, .inl 1, 3, .inr 1), (0, .inl 1, 3, .inr 1), 2, 0),
    ((3, .inl 2, 0, .inl 2), (0, .inl 2, 0, .inl 2), 3, 0),
    ((0, .inl 2, 0, .inr 2), (0, .inl 2, 0, .inr 1), 2, 3),
    ((2, .inr 0, 1, .inl 1), (0, .inl 2, 1, .inl 1), 2, 0),
    ((3, .inl 2, 1, .inr 0), (0, .inl 2, 1, .inl 1), 3, 0),
    ((2, .inl 2, 1, .inl 2), (0, .inl 2, 1, .inl 2), 2, 0),
    ((0, .inl 2, 1, .inl 1), (0, .inl 2, 1, .inl 2), 2, 3),
    ((2, .inl 2, 1, .inr 2), (0, .inl 2, 1, .inr 2), 2, 0),
    ((3, .inl 2, 1, .inr 2), (0, .inl 2, 1, .inr 2), 3, 0),
    ((0, .inl 2, 1, .inr 2), (0, .inl 2, 1, .inr 1), 2, 3),
    ((1, .inr 1, 2, .inl 0), (0, .inl 2, 2, .inl 0), 1, 0),
    ((3, .inl 2, 2, .inr 1), (0, .inl 2, 2, .inl 0), 3, 0),
    ((0, .inl 2, 2, .inl 0), (0, .inl 2, 2, .inl 1), 1, 2),
    ((1, .inl 2, 2, .inl 2), (0, .inl 2, 2, .inl 2), 1, 0),
    ((1, .inl 2, 2, .inr 2), (0, .inl 2, 2, .inr 2), 1, 0),
    ((3, .inl 2, 2, .inr 2), (0, .inl 2, 2, .inr 2), 3, 0),
    ((1, .inr 1, 3, .inr 1), (0, .inl 2, 3, .inl 2), 1, 0),
    ((2, .inr 0, 3, .inr 0), (0, .inl 2, 3, .inl 2), 2, 0),
    ((1, .inl 2, 3, .inr 2), (0, .inl 2, 3, .inr 2), 1, 0),
    ((2, .inl 2, 3, .inr 2), (0, .inl 2, 3, .inr 2), 2, 0),
    ((3, .inl 2, 3, .inr 2), (0, .inl 2, 3, .inr 2), 3, 0),
    ((3, .inr 2, 0, .inr 2), (0, .inr 2, 0, .inr 2), 3, 0),
    ((0, .inr 2, 0, .inl 2), (0, .inr 2, 0, .inr 1), 0, 1),
    ((2, .inr 2, 1, .inl 2), (0, .inr 2, 1, .inl 2), 2, 0),
    ((0, .inr 2, 2, .inl 2), (0, .inr 2, 1, .inl 2), 2, 1),
    ((3, .inr 2, 1, .inl 2), (0, .inr 2, 1, .inl 2), 3, 0),
    ((0, .inr 2, 3, .inl 2), (0, .inr 2, 1, .inl 2), 3, 1),
    ((0, .inr 2, 1, .inl 2), (0, .inr 2, 1, .inr 1), 0, 1),
    ((0, .inr 2, 2, .inr 0), (0, .inr 2, 1, .inr 1), 2, 1),
    ((0, .inr 0, 3, .inr 1), (0, .inr 2, 1, .inr 1), 3, 1),
    ((0, .inr 2, 1, .inr 1), (0, .inr 2, 1, .inr 0), 1, 2),
    ((0, .inr 0, 2, .inl 0), (0, .inr 2, 2, .inl 0), 3, 1),
    ((3, .inr 2, 2, .inl 1), (0, .inr 2, 2, .inl 1), 3, 0),
    ((1, .inr 2, 2, .inl 2), (0, .inr 2, 2, .inl 2), 1, 0),
    ((2, .inr 2, 2, .inl 2), (0, .inr 2, 2, .inl 2), 2, 0),
    ((3, .inr 2, 2, .inl 2), (0, .inr 2, 2, .inl 2), 3, 0),
    ((0, .inr 0, 2, .inr 2), (0, .inr 2, 2, .inr 2), 3, 1),
    ((0, .inr 1, 3, .inr 0), (0, .inr 2, 2, .inr 0), 3, 2),
    ((0, .inr 0, 3, .inl 0), (0, .inr 2, 3, .inl 0), 3, 1),
    ((0, .inr 1, 3, .inl 1), (0, .inr 2, 3, .inl 1), 3, 2),
    ((1, .inr 2, 3, .inl 2), (0, .inr 2, 3, .inl 2), 1, 0),
    ((2, .inr 2, 3, .inl 2), (0, .inr 2, 3, .inl 2), 2, 0),
    ((3, .inr 2, 3, .inl 2), (0, .inr 2, 3, .inl 2), 3, 0),
    ((0, .inr 1, 0, .inl 1), (0, .inr 1, 0, .inl 2), 2, 3),
    ((2, .inr 1, 0, .inr 1), (0, .inr 1, 0, .inr 1), 2, 0),
    ((3, .inr 1, 0, .inr 0), (0, .inr 1, 0, .inr 0), 3, 0),
    ((2, .inr 1, 1, .inl 1), (0, .inr 1, 1, .inl 1), 2, 0),
    ((0, .inr 1, 2, .inl 1), (0, .inr 1, 1, .inl 1), 2, 1),
    ((3, .inr 1, 1, .inl 1), (0, .inr 1, 1, .inl 1), 3, 0),
    ((0, .inr 1, 1, .inl 1), (0, .inr 1, 1, .inl 2), 2, 3),
    ((0, .inr 1, 1, .inr 2), (0, .inr 1, 1, .inr 1), 2, 3),
    ((1, .inr 1, 2, .inl 1), (0, .inr 1, 2, .inl 1), 1, 0),
    ((2, .inr 1, 2, .inl 1), (0, .inr 1, 2, .inl 1), 2, 0),
    ((3, .inr 1, 2, .inl 1), (0, .inr 1, 2, .inl 1), 3, 0),
    ((1, .inr 1, 3, .inl 1), (0, .inr 1, 3, .inl 1), 1, 0),
    ((2, .inr 1, 3, .inl 1), (0, .inr 1, 3, .inl 1), 2, 0),
    ((3, .inr 1, 3, .inl 1), (0, .inr 1, 3, .inl 1), 3, 0),
    ((2, .inr 1, 3, .inl 2), (0, .inr 1, 3, .inl 2), 2, 0),
    ((0, .inr 0, 0, .inl 0), (0, .inr 0, 0, .inl 1), 1, 2),
    ((2, .inr 0, 0, .inr 2), (0, .inr 0, 0, .inr 2), 2, 0),
    ((3, .inr 0, 0, .inr 1), (0, .inr 0, 0, .inr 1), 3, 0),
    ((1, .inr 0, 0, .inr 0), (0, .inr 0, 0, .inr 0), 1, 0),
    ((1, .inr 0, 1, .inl 0), (0, .inr 0, 1, .inl 0), 1, 0),
    ((2, .inr 0, 1, .inl 0), (0, .inr 0, 1, .inl 0), 2, 0),
    ((3, .inr 0, 1, .inl 0), (0, .inr 0, 1, .inl 0), 3, 0),
    ((0, .inr 0, 1, .inl 0), (0, .inr 0, 1, .inl 1), 1, 2),
    ((1, .inr 0, 2, .inl 0), (0, .inr 0, 2, .inl 0), 1, 0),
    ((2, .inr 0, 2, .inl 0), (0, .inr 0, 2, .inl 0), 2, 0),
    ((3, .inr 0, 2, .inl 0), (0, .inr 0, 2, .inl 0), 3, 0),
    ((1, .inr 0, 2, .inl 1), (0, .inr 0, 2, .inl 1), 1, 0),
    ((1, .inr 0, 3, .inl 0), (0, .inr 0, 3, .inl 0), 1, 0),
    ((2, .inr 0, 3, .inl 0), (0, .inr 0, 3, .inl 0), 2, 0),
    ((3, .inr 0, 3, .inl 0), (0, .inr 0, 3, .inl 0), 3, 0),
    ((1, .inr 0, 3, .inl 2), (0, .inr 0, 3, .inl 2), 1, 0),
    ((1, .inl 0, 0, .inl 0), (1, .inl 0, 0, .inl 1), 1, 2),
    ((1, .inr 1, 0, .inr 2), (1, .inl 0, 0, .inr 2), 3, 0),
    ((1, .inr 2, 0, .inr 1), (1, .inl 0, 0, .inr 1), 2, 0),
    ((2, .inl 0, 0, .inr 0), (1, .inl 0, 0, .inr 0), 2, 1),
    ((3, .inl 0, 0, .inr 0), (1, .inl 0, 0, .inr 0), 3, 1),
    ((1, .inr 1, 1, .inl 1), (1, .inl 0, 1, .inl 1), 3, 0),
    ((1, .inr 2, 1, .inl 2), (1, .inl 0, 1, .inl 2), 2, 0),
    ((1, .inl 0, 0, .inr 0), (1, .inl 0, 1, .inr 0), 0, 1),
    ((3, .inl 0, 2, .inl 0), (1, .inl 0, 2, .inl 0), 3, 1),
    ((2, .inl 0, 3, .inl 0), (1, .inl 0, 3, .inl 0), 2, 1),
    ((1, .inl 1, 2, .inr 0), (1, .inl 1, 0, .inl 2), 2, 0),
    ((1, .inl 1, 0, .inl 2), (1, .inl 1, 0, .inr 1), 0, 1),
    ((1, .inl 1, 1, .inr 1), (1, .inl 1, 0, .inr 1), 1, 0),
    ((2, .inl 1, 0, .inr 1), (1, .inl 1, 0, .inr 1), 2, 1),
    ((3, .inl 1, 0, .inr 1), (1, .inl 1, 0, .inr 1), 3, 1),
    ((1, .inl 1, 0, .inr 1), (1, .inl 1, 0, .inr 0), 1, 2),
    ((3, .inl 1, 1, .inl 1), (1, .inl 1, 1, .inl 1), 3, 1),
    ((1, .inl 2, 1, .inr 2), (1, .inl 1, 1, .inr 2), 3, 2),
    ((3, .inl 1, 3, .inr 1), (1, .inl 1, 1, .inr 1), 3, 1),
    ((3, .inl 1, 2, .inr 2), (1, .inl 1, 2, .inr 2), 3, 1),
    ((1, .inl 2, 3, .inr 0), (1, .inl 1, 2, .inr 0), 3, 2),
    ((1, .inl 2, 0, .inl 1), (1, .inl 2, 0, .inl 2), 2, 3),
    ((2, .inl 2, 0, .inr 2), (1, .inl 2, 0, .inr 2), 2, 1),
    ((3, .inl 2, 0, .inr 2), (1, .inl 2, 0, .inr 2), 3, 1),
    ((1, .inl 2, 0, .inr 2), (1, .inl 2, 0, .inr 1), 2, 3),
    ((2, .inl 2, 2, .inr 2), (1, .inl 2, 1, .inr 2), 2, 1),
    ((2, .inl 2, 3, .inr 1), (1, .inl 2, 3, .inr 1), 2, 1),
    ((2, .inr 2, 0, .inl 2), (1, .inr 2, 0, .inl 2), 2, 1),
    ((3, .inr 2, 0, .inl 2), (1, .inr 2, 0, .inl 2), 3, 1),
    ((1, .inr 2, 0, .inl 2), (1, .inr 2, 0, .inr 1), 0, 1),
    ((2, .inr 2, 0, .inr 0), (1, .inr 2, 0, .inr 1), 2, 1),
    ((3, .inr 2, 1, .inl 0), (1, .inr 2, 1, .inl 0), 3, 1),
    ((2, .inr 1, 0, .inl 1), (1, .inr 1, 0, .inl 1), 2, 1),
    ((3, .inr 1, 0, .inl 1), (1, .inr 1, 0, .inl 1), 3, 1),
    ((1, .inr 1, 0, .inl 1), (1, .inr 1, 0, .inl 2), 2, 3),
    ((2, .inr 1, 1, .inl 0), (1, .inr 1, 1, .inl 0), 2, 1),
    ((2, .inr 0, 0, .inl 0), (1, .inr 0, 0, .inl 0), 2, 1),
    ((3, .inr 0, 0, .inl 0), (1, .inr 0, 0, .inl 0), 3, 1),
    ((1, .inr 0, 0, .inl 0), (1, .inr 0, 0, .inl 1), 1, 2),
    ((2, .inl 0, 1, .inr 1), (2, .inl 0, 0, .inl 2), 1, 0),
    ((2, .inl 0, 2, .inr 0), (2, .inl 0, 0, .inl 2), 2, 0),
    ((2, .inl 0, 0, .inl 2), (2, .inl 0, 0, .inr 1), 0, 1),
    ((3, .inl 0, 1, .inr 2), (2, .inl 0, 1, .inr 2), 3, 2),
    ((3, .inl 0, 3, .inr 0), (2, .inl 0, 2, .inr 0), 3, 2),
    ((2, .inl 2, 0, .inl 0), (2, .inl 2, 0, .inl 1), 1, 2),
    ((3, .inl 0, 0, .inl 1), (3, .inl 0, 0, .inl 2), 2, 3),
    ((3, .inl 1, 0, .inl 0), (3, .inl 1, 0, .inl 1), 1, 2)
  ]

theorem noInvSteps_check : noInvStepsCheck [] noInvSteps = true := by decide +kernel

theorem noInvSteps_cover (τ : NoInvIdx) : NoInvKilled (noInvSteps.map Prod.fst) τ := by
  revert τ
  decide +kernel

theorem noInvForm_eq_zero [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) (σ : K →+* K)
    (β : (Fin 4 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 4 → K) →ₗ[K]
      (Fin 3 ⊕ Fin 3 → K) →ₗ[K] K)
    (hβ : ∀ (A : Matrix.SpecialLinearGroup (Fin 4) K) (v v' : Fin 4 → K)
        (w w' : Fin 3 ⊕ Fin 3 → K),
      β (Matrix.SpecialLinearGroup.map σ A • v) (rho A w)
          (Matrix.SpecialLinearGroup.map σ A • v') (rho A w') = β v w v' w') :
    β = 0 := by
  have hC : ∀ τ, noInvCoeff β τ = 0 := by
    have hT := fun τ (h : NoInvTorusKilled τ) => noInvCoeff_eq_zero_of_torusKilled hK σ hβ h
    have hS := eq_zero_of_noInvStepsCheck hT (fun p q hpq τ => noInvCoeff_root σ hβ hpq τ)
      noInvSteps [] (by simp) noInvSteps_check
    intro τ
    rcases noInvSteps_cover τ with h | h
    · exact hT τ h
    · exact hS τ h
  refine (Pi.basisFun K (Fin 4)).ext fun i => (Pi.basisFun K (Fin 3 ⊕ Fin 3)).ext fun s =>
    (Pi.basisFun K (Fin 4)).ext fun j => (Pi.basisFun K (Fin 3 ⊕ Fin 3)).ext fun s' => ?_
  simp only [Pi.basisFun_apply, LinearMap.zero_apply]
  exact hC (i, s, j, s')

end CFSG.RankThree.PartOne.K159.Klein

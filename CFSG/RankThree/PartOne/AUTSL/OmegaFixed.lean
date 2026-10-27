module

public import CFSG.RankThree.PartOne.AUTSL.QuadCount
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataSemilinear
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailCharTwoSign

public section

namespace CFSG.RankThree.PartOne.AUTSL

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.LieType.Universal.Spin CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal Matrix

section Count

variable {K : Type} [Field K] [Fintype K]

noncomputable def thetaEquiv (n : ℕ) (hn : 1 ≤ n) :
    (Fin (2 * n) → K) ≃ (Fin (n - 1) → K × K) × (Fin 2 → K) where
  toFun v := (fun i => (v (minusIndexEquiv n hn (.inl i)),
      v (minusIndexEquiv n hn (.inr (.inl i)))),
    fun j => v (minusIndexEquiv n hn (.inr (.inr j))))
  invFun p := fun k =>
    match (minusIndexEquiv n hn).symm k with
    | .inl i => (p.1 i).1
    | .inr (.inl i) => (p.1 i).2
    | .inr (.inr j) => p.2 j
  left_inv v := by
    funext k
    rcases h : (minusIndexEquiv n hn).symm k with i | i | j
    · simp only [h]
      have := (minusIndexEquiv n hn).apply_symm_apply k
      rw [h] at this
      rw [this]
    · simp only [h]
      have := (minusIndexEquiv n hn).apply_symm_apply k
      rw [h] at this
      rw [this]
    · simp only [h]
      have := (minusIndexEquiv n hn).apply_symm_apply k
      rw [h] at this
      rw [this]
  right_inv p := by
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · simp
    · simp


omit [Fintype K] in
theorem coordinateQuadMinus_eq (n : ℕ) (hn : 1 ≤ n) (b c : K) (v : Fin (2 * n) → K) :
    coordinateQuadMinus n K hn b c v = hypForm (n - 1) (thetaEquiv n hn v).1 +
      ((thetaEquiv n hn v).2 0 ^ 2 + b * (thetaEquiv n hn v).2 0 * (thetaEquiv n hn v).2 1 +
        c * (thetaEquiv n hn v).2 1 ^ 2) := by
  rw [coordinateQuadMinus_apply]
  simp [hypForm, thetaEquiv, add_assoc]

omit [Fintype K] in
theorem tail_eq_zero_iff (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (u : Fin 2 → K) :
    u 0 ^ 2 + b * u 0 * u 1 + c * u 1 ^ 2 = 0 ↔ u = 0 := by
  constructor
  · intro h
    by_cases h1 : u 1 = 0
    · have h0 : u 0 = 0 := by
        rw [h1] at h
        have : u 0 ^ 2 = 0 := by linear_combination h
        exact pow_eq_zero_iff two_ne_zero |>.1 this
      funext j
      fin_cases j
      · exact h0
      · exact h1
    · exfalso
      apply hirr (u 0 / u 1)
      field_simp
      linear_combination h
  · rintro rfl
    simp

theorem cntQ_tail_zero (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    cntQ (fun u : Fin 2 → K => u 0 ^ 2 + b * u 0 * u 1 + c * u 1 ^ 2) 0 = 1 := by
  simp only [cntQ]
  rw [Finset.card_eq_one]
  refine ⟨0, ?_⟩
  ext u
  simp [tail_eq_zero_iff b c hirr]

theorem cntQ_coordinate_zero (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    cntQ (coordinateQuadMinus 4 K (by norm_num) b c) 0 + Fintype.card K ^ 4 =
      Fintype.card K ^ 7 + Fintype.card K ^ 3 := by
  have h1 := cntQ_hypForm_zero (K := K) (Y := Fin 2 → K)
    (fun u => u 0 ^ 2 + b * u 0 * u 1 + c * u 1 ^ 2) (cntQ_tail_zero b c hirr)
    (by simp) (4 - 1)
  have h2 : cntQ (coordinateQuadMinus 4 K (by norm_num) b c) 0 =
      cntQ (fun r : (Fin (4 - 1) → K × K) × (Fin 2 → K) => hypForm (4 - 1) r.1 +
        (r.2 0 ^ 2 + b * r.2 0 * r.2 1 + c * r.2 1 ^ 2)) 0 := by
    rw [← cntQ_comp_equiv (thetaEquiv 4 (by norm_num))]
    congr 1
    funext v
    exact coordinateQuadMinus_eq 4 (by norm_num) b c v
  rw [h2]
  simpa using h1


omit [Field K] [Fintype K] in
theorem cntQ_eq_of_ne_zero {V : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype V]
    (Q : QuadraticForm K V) (hsq : ∀ a : K, ∃ c : K, c * c = a) {a : K} (ha : a ≠ 0) :
    cntQ Q a = cntQ Q 1 := by
  obtain ⟨c, hc⟩ := hsq a
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact ha (by simpa using hc.symm)
  simp only [cntQ]
  refine Finset.card_bij (fun v _ => c⁻¹ • v) ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    rw [QuadraticMap.map_smul, hv, smul_eq_mul, ← hc]
    field_simp
  · intro v _ w _ h
    simpa [hc0] using h
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    refine ⟨c • w, ?_, by simp [hc0]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [QuadraticMap.map_smul, hw, smul_eq_mul, mul_one, hc]

theorem cntQ_coordinate_one [CharP K 2] (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    cntQ (coordinateQuadMinus 4 K (by norm_num) b c) 1 =
      Fintype.card K ^ 7 + Fintype.card K ^ 3 := by
  classical
  have hsq : ∀ a : K, ∃ c : K, c * c = a := fun a => by
    obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) a
    exact ⟨c, hc.symm⟩
  set Qc := coordinateQuadMinus 4 K (by norm_num : 1 ≤ 4) b c with hQc
  have hsum := sum_cntQ Qc
  have hcard : Fintype.card (Fin (2 * 4) → K) = Fintype.card K ^ 8 := by
    simp
  rw [hcard, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K))] at hsum
  have h1 : ∑ a ∈ Finset.univ.erase (0 : K), cntQ Qc a =
      (Fintype.card K - 1) * cntQ Qc 1 := by
    rw [Finset.sum_congr rfl fun a ha => cntQ_eq_of_ne_zero Qc hsq (Finset.ne_of_mem_erase ha),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      smul_eq_mul]
  rw [h1] at hsum
  have h0 := cntQ_coordinate_zero b c hirr
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card K = r + 1 :=
    ⟨Fintype.card K - 1, by have := Fintype.card_pos (α := K); omega⟩
  rw [hr] at hsum h0 ⊢
  have hr0 : 0 < r := by
    have : 1 < Fintype.card K := Fintype.one_lt_card
    omega
  simp only [Nat.add_sub_cancel] at hsum
  refine Nat.eq_of_mul_eq_mul_left hr0 ?_
  nlinarith [hsum, h0]


theorem not_dvd_norm_one_count {p q : ℕ} (hp5 : 5 ≤ p) (hq : 1 ≤ q)
    (hpq : p ∣ q - 1 ∨ p ∣ q + 1) : ¬ p ∣ q ^ 7 + q ^ 3 := by
  intro hdvd
  have h2 : p ∣ 2 := by
    rcases hpq with h | h
    · have h1 : p ∣ q ^ 7 - 1 := h.trans (Nat.sub_one_dvd_pow_sub_one q 7)
      have h3 : p ∣ q ^ 3 - 1 := h.trans (Nat.sub_one_dvd_pow_sub_one q 3)
      have h4 : q ^ 7 + q ^ 3 = (q ^ 7 - 1) + (q ^ 3 - 1) + 2 := by
        have : 1 ≤ q ^ 7 := Nat.one_le_pow _ _ hq
        have : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq
        omega
      rw [h4] at hdvd
      exact (Nat.dvd_add_right (dvd_add h1 h3)).1 hdvd
    · have h1 : p ∣ q ^ 7 + 1 := h.trans (by
        simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 7))
      have h3 : p ∣ q ^ 3 + 1 := h.trans (by
        simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3))
      have h4 : (q ^ 7 + 1) + (q ^ 3 + 1) = (q ^ 7 + q ^ 3) + 2 := by ring
      have h5 := dvd_add h1 h3
      rw [h4] at h5
      exact (Nat.dvd_add_right hdvd).1 h5
  have := Nat.le_of_dvd (by norm_num) h2
  omega


omit [Fintype K] in
theorem exists_fixed_norm_one [Fintype K] [CharP K 2] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hpq : p ∣ Fintype.card K - 1 ∨ p ∣ Fintype.card K + 1)
    (A : Subgroup (GL (Fin (2 * 4)) K)) (hA : IsPGroup p A)
    (hAQ : ∀ g ∈ A, ∀ v : Fin (2 * 4) → K,
      coordinateQuadMinus 4 K (by norm_num) b c ((g : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v) =
        coordinateQuadMinus 4 K (by norm_num) b c v) :
    ∃ w : Fin (2 * 4) → K, coordinateQuadMinus 4 K (by norm_num) b c w = 1 ∧
      ∀ g ∈ A, (g : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w = w := by
  classical
  let S : Type := {v : Fin (2 * 4) → K // coordinateQuadMinus 4 K (by norm_num) b c v = 1}
  let _ : MulAction A S :=
    { smul := fun g v => ⟨((g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v.1,
        by rw [hAQ g g.2, v.2]⟩
      one_smul := fun v => Subtype.ext (by
        change (((1 : A) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v.1 = v.1
        simp)
      mul_smul := fun g h v => Subtype.ext (by
        change (((g * h : A) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v.1 =
          ((g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
            (((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v.1)
        simp [Matrix.mulVec_mulVec]) }
  have hfin : Finite S := inferInstance
  have hmod := hA.card_modEq_card_fixedPoints S
  have hcardS : Nat.card S = Fintype.card K ^ 7 + Fintype.card K ^ 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact cntQ_coordinate_one b c hirr
  have hnd := not_dvd_norm_one_count (p := p) hp5 Fintype.card_pos hpq
  have hne : Nat.card (MulAction.fixedPoints A S) ≠ 0 := by
    intro h0
    rw [h0, hcardS] at hmod
    exact hnd ((Nat.modEq_zero_iff_dvd).1 hmod)
  obtain ⟨⟨⟨w, hwQ⟩, hwfix⟩⟩ : Nonempty (MulAction.fixedPoints A S) := by
    have : 0 < Nat.card (MulAction.fixedPoints A S) := Nat.pos_of_ne_zero hne
    exact (Nat.card_pos_iff.1 this).1
  refine ⟨w, hwQ, fun g hg => ?_⟩
  have := hwfix ⟨g, hg⟩
  exact congrArg Subtype.val this

end Count

end CFSG.RankThree.PartOne.AUTSL

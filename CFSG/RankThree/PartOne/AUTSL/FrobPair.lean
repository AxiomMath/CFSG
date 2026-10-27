module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
public import CFSG.RankThree.PartOne.AUTSL.TraceAS
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataSemilinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataConjugation

public noncomputable section

namespace CFSG.RankThree.PartOne.AUTSL

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData Matrix

section Tail

variable {K : Type} [Field K] (n : ℕ) (hn : 1 ≤ n)

@[expose] def tailZero : Fin (2 * n) := minusIndexEquiv n hn (.inr (.inr 0))

@[expose] def tailOne : Fin (2 * n) := minusIndexEquiv n hn (.inr (.inr 1))

theorem tailZero_ne_tailOne : tailZero n hn ≠ tailOne n hn := by
  intro h
  have := (minusIndexEquiv n hn).injective h
  simp at this

theorem tailOne_ne_tailZero : tailOne n hn ≠ tailZero n hn := (tailZero_ne_tailOne n hn).symm

theorem tailZero_ne_inl (i : Fin (n - 1)) : minusIndexEquiv n hn (.inl i) ≠ tailZero n hn :=
  fun h => by simpa using (minusIndexEquiv n hn).injective h

theorem tailOne_ne_inl (i : Fin (n - 1)) : minusIndexEquiv n hn (.inl i) ≠ tailOne n hn :=
  fun h => by simpa using (minusIndexEquiv n hn).injective h

theorem tailZero_ne_inr (i : Fin (n - 1)) : minusIndexEquiv n hn (.inr (.inl i)) ≠ tailZero n hn :=
  fun h => by simpa using (minusIndexEquiv n hn).injective h

theorem tailOne_ne_inr (i : Fin (n - 1)) : minusIndexEquiv n hn (.inr (.inl i)) ≠ tailOne n hn :=
  fun h => by simpa using (minusIndexEquiv n hn).injective h

variable (b c : K)

@[expose] def tailLin : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K) where
  toFun v := fun k => if k = tailZero n hn then v k + c * v (tailOne n hn)
    else if k = tailOne n hn then b * v k else v k
  map_add' v w := by
    funext k
    simp only [Pi.add_apply]
    split_ifs <;> first | rfl | ring
  map_smul' a v := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> first | rfl | ring

theorem tailLin_apply (v : Fin (2 * n) → K) (k : Fin (2 * n)) :
    tailLin n hn b c v k = if k = tailZero n hn then v k + c * v (tailOne n hn)
      else if k = tailOne n hn then b * v k else v k := rfl

theorem tailLin_zero (v : Fin (2 * n) → K) :
    tailLin n hn b c v (tailZero n hn) = v (tailZero n hn) + c * v (tailOne n hn) := by
  simp [tailLin_apply]

theorem tailLin_one (v : Fin (2 * n) → K) :
    tailLin n hn b c v (tailOne n hn) = b * v (tailOne n hn) := by
  simp [tailLin_apply, tailOne_ne_tailZero n hn]

theorem tailLin_other (v : Fin (2 * n) → K) {k : Fin (2 * n)} (h0 : k ≠ tailZero n hn)
    (h1 : k ≠ tailOne n hn) : tailLin n hn b c v k = v k := by
  simp [tailLin_apply, h0, h1]

@[expose] def tailLinInv : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K) where
  toFun v := fun k => if k = tailZero n hn then v k - c * b⁻¹ * v (tailOne n hn)
    else if k = tailOne n hn then b⁻¹ * v k else v k
  map_add' v w := by
    funext k
    simp only [Pi.add_apply]
    split_ifs <;> first | rfl | ring
  map_smul' a v := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> first | rfl | ring

theorem tailLinInv_apply (v : Fin (2 * n) → K) (k : Fin (2 * n)) :
    tailLinInv n hn b c v k = if k = tailZero n hn then v k - c * b⁻¹ * v (tailOne n hn)
      else if k = tailOne n hn then b⁻¹ * v k else v k := rfl

theorem tailLinInv_zero (v : Fin (2 * n) → K) :
    tailLinInv n hn b c v (tailZero n hn) = v (tailZero n hn) - c * b⁻¹ * v (tailOne n hn) := by
  simp [tailLinInv_apply]

theorem tailLinInv_one (v : Fin (2 * n) → K) :
    tailLinInv n hn b c v (tailOne n hn) = b⁻¹ * v (tailOne n hn) := by
  simp [tailLinInv_apply, tailOne_ne_tailZero n hn]

theorem tailLinInv_other (v : Fin (2 * n) → K) {k : Fin (2 * n)} (h0 : k ≠ tailZero n hn)
    (h1 : k ≠ tailOne n hn) : tailLinInv n hn b c v k = v k := by
  simp [tailLinInv_apply, h0, h1]

theorem tailLin_tailLinInv (hb : b ≠ 0) (v : Fin (2 * n) → K) :
    tailLin n hn b c (tailLinInv n hn b c v) = v := by
  funext k
  by_cases h0 : k = tailZero n hn
  · subst h0
    rw [tailLin_zero, tailLinInv_zero, tailLinInv_one]
    ring
  · by_cases h1 : k = tailOne n hn
    · subst h1
      rw [tailLin_one, tailLinInv_one]
      field_simp
    · rw [tailLin_other n hn b c _ h0 h1, tailLinInv_other n hn b c _ h0 h1]

theorem tailLinInv_tailLin (hb : b ≠ 0) (v : Fin (2 * n) → K) :
    tailLinInv n hn b c (tailLin n hn b c v) = v := by
  funext k
  by_cases h0 : k = tailZero n hn
  · subst h0
    rw [tailLinInv_zero, tailLin_zero, tailLin_one]
    field_simp
    ring
  · by_cases h1 : k = tailOne n hn
    · subst h1
      rw [tailLinInv_one, tailLin_one]
      field_simp
    · rw [tailLinInv_other n hn b c _ h0 h1, tailLin_other n hn b c _ h0 h1]

@[expose] def tailEquiv (hb : b ≠ 0) : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K) :=
  LinearEquiv.ofLinearMap (tailLin n hn b c) (tailLinInv n hn b c)
    (LinearMap.ext fun v => tailLin_tailLinInv n hn b c hb v)
    (LinearMap.ext fun v => tailLinInv_tailLin n hn b c hb v)

theorem tailEquiv_apply (hb : b ≠ 0) (v : Fin (2 * n) → K) :
    tailEquiv n hn b c hb v = tailLin n hn b c v := rfl

omit [Field K] in
theorem coordQuadMinus_apply' {K : Type} [Field K] (b c : K) (v : Fin (2 * n) → K) :
    coordinateQuadMinus n K hn b c v =
      ∑ i, v (minusIndexEquiv n hn (.inl i)) * v (minusIndexEquiv n hn (.inr (.inl i))) +
        v (tailZero n hn) ^ 2 + b * v (tailZero n hn) * v (tailOne n hn) +
        c * v (tailOne n hn) ^ 2 :=
  coordinateQuadMinus_apply n K hn b c v

theorem form_tailLin_sq [CharP K 2] (v : Fin (2 * n) → K) :
    coordinateQuadMinus n K hn b c (tailLin n hn b c (fun i => v i ^ 2)) =
      (coordinateQuadMinus n K hn b c v) ^ 2 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [coordQuadMinus_apply', coordQuadMinus_apply']
  have hsum : ∑ i : Fin (n - 1), tailLin n hn b c (fun i => v i ^ 2)
        (minusIndexEquiv n hn (.inl i)) *
      tailLin n hn b c (fun i => v i ^ 2) (minusIndexEquiv n hn (.inr (.inl i))) =
      ∑ i : Fin (n - 1), (v (minusIndexEquiv n hn (.inl i)) *
        v (minusIndexEquiv n hn (.inr (.inl i)))) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tailLin_other n hn b c _ (tailZero_ne_inl n hn i) (tailOne_ne_inl n hn i),
      tailLin_other n hn b c _ (tailZero_ne_inr n hn i) (tailOne_ne_inr n hn i)]
    ring
  have key : ∀ S a e : K, (S + a ^ 2 + b * a * e + c * e ^ 2) ^ 2 =
      S ^ 2 + (a ^ 2) ^ 2 + (b * a * e) ^ 2 + (c * e ^ 2) ^ 2 := by
    intro S a e
    rw [CharTwo.add_sq, CharTwo.add_sq, CharTwo.add_sq]
  rw [hsum, tailLin_zero, tailLin_one, key, CharTwo.sum_sq,
    CharTwo.add_sq (v (tailZero n hn) ^ 2) (c * v (tailOne n hn) ^ 2)]
  linear_combination (b ^ 2 * c * (v (tailOne n hn)) ^ 4) * h2

end Tail

section Pair

variable {K : Type} [Field K] (n : ℕ) (hn : 1 ≤ n) (b c : K) (hb : b ≠ 0)

theorem ne_zero_of_irreducible_tail [Finite K] [CharP K 2] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    b ≠ 0 := by
  intro hb0
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
  apply hirr s
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [hb0, hs]
  linear_combination (s * s) * h2

@[expose] def frobMat : GL (Fin (2 * n)) K := matrixLinearIso.symm (tailEquiv n hn b c hb)

theorem frobMat_mulVec (w : Fin (2 * n) → K) :
    (frobMat n hn b c hb).val *ᵥ w = tailLin n hn b c w := by
  have h : matrixLinearEquiv (frobMat n hn b c hb) w = (tailEquiv n hn b c hb) w := by
    change matrixLinearIso (frobMat n hn b c hb) w = _
    rw [frobMat, MulEquiv.apply_symm_apply]
  exact h

section FrobPair

variable [Finite K] [CharP K 2]

@[expose] def frobElt : coordinateSemilinearGroup (2 * n) K :=
  ⟨frobMat n hn b c hb, frobeniusEquiv K 2⟩

theorem frobElt_apply (v : Fin (2 * n) → K) :
    coordinateSemilinearMap (frobElt n hn b c hb) v = tailLin n hn b c (fun i => v i ^ 2) := by
  rw [coordinateSemilinearMap_apply]
  have e : (fun i => (frobElt n hn b c hb).right (v i)) = fun i => v i ^ 2 := rfl
  rw [e]
  exact frobMat_mulVec n hn b c hb _

theorem frobElt_mem :
    frobElt n hn b c hb ∈ similarityPairs (coordinateQuadMinus n K hn b c) := by
  refine ⟨1, fun v => ?_⟩
  rw [frobElt_apply, form_tailLin_sq, Units.val_one, one_mul]
  rfl

@[expose] def frobPair : similarityPairs (coordinateQuadMinus n K hn b c) :=
  ⟨frobElt n hn b c hb, frobElt_mem n hn b c hb⟩

theorem frobPair_right : (frobPair n hn b c hb).val.right = frobeniusEquiv K 2 := rfl

end FrobPair

@[expose] def tailSeq (b c : K) : ℕ → K × K
  | 0 => (0, 1)
  | j + 1 => ((tailSeq b c j).1 ^ 2 + c * (tailSeq b c j).2 ^ 2, b * (tailSeq b c j).2 ^ 2)

variable [Finite K] [CharP K 2]

theorem frobPair_pow_apply (j : ℕ) (v : Fin (2 * n) → K) :
    ∀ k : Fin (2 * n), coordinateSemilinearMap ((frobPair n hn b c hb) ^ j).val v k =
      if k = tailZero n hn then v k ^ 2 ^ j + (tailSeq b c j).1 * v (tailOne n hn) ^ 2 ^ j
      else if k = tailOne n hn then (tailSeq b c j).2 * v k ^ 2 ^ j else v k ^ 2 ^ j := by
  induction j with
  | zero =>
    intro k
    have e : (((frobPair n hn b c hb) ^ 0 : similarityPairs _).val) = 1 := rfl
    rw [e, coordinateSemilinearMap_one]
    by_cases h0 : k = tailZero n hn
    · subst h0
      simp [tailSeq]
    · by_cases h1 : k = tailOne n hn
      · subst h1
        simp [tailSeq, h0]
      · simp [h0, h1]
  | succ j ih =>
    intro k
    have e1 : ((frobPair n hn b c hb ^ (j + 1) : similarityPairs _).val) =
        (frobElt n hn b c hb) * (frobPair n hn b c hb ^ j).val := by
      rw [pow_succ']
      rfl
    rw [e1, coordinateSemilinearMap_mul, frobElt_apply]
    by_cases h0 : k = tailZero n hn
    · subst h0
      rw [tailLin_zero, ih (tailZero n hn), ih (tailOne n hn)]
      simp only [ite_true, tailOne_ne_tailZero n hn, ite_false, tailSeq]
      rw [CharTwo.add_sq]
      ring
    · by_cases h1 : k = tailOne n hn
      · subst h1
        rw [tailLin_one, ih (tailOne n hn)]
        simp only [tailOne_ne_tailZero n hn, ite_true, ite_false, tailSeq]
        ring
      · rw [tailLin_other n hn b c _ h0 h1, ih k]
        simp only [h0, h1, ite_false]
        ring

omit [Finite K] [CharP K 2] in
theorem tailSeq_snd_mul (j : ℕ) : (tailSeq b c j).2 * b = b ^ 2 ^ j := by
  induction j with
  | zero => simp [tailSeq]
  | succ j ih =>
    simp only [tailSeq]
    calc b * (tailSeq b c j).2 ^ 2 * b = ((tailSeq b c j).2 * b) ^ 2 := by ring
      _ = b ^ 2 ^ (j + 1) := by rw [ih]; ring

omit [Finite K] in
include hb in
theorem tailSeq_fst (j : ℕ) :
    (tailSeq b c j).1 = b ^ 2 ^ j * ∑ i ∈ Finset.range j, (c / b ^ 2) ^ 2 ^ i := by
  induction j with
  | zero => simp [tailSeq]
  | succ j ih =>
    simp only [tailSeq]
    rw [ih, mul_pow, CharTwo.sum_sq, Finset.sum_range_succ' _ j]
    have h1 : c * (tailSeq b c j).2 ^ 2 = (c / b ^ 2) * b ^ 2 ^ (j + 1) := by
      have := tailSeq_snd_mul b c j
      calc c * (tailSeq b c j).2 ^ 2 = (c / b ^ 2) * ((tailSeq b c j).2 * b) ^ 2 := by
            field_simp
        _ = (c / b ^ 2) * b ^ 2 ^ (j + 1) := by rw [this]; ring
    rw [h1]
    have h2 : ∀ i : ℕ, ((c / b ^ 2) ^ 2 ^ i) ^ 2 = (c / b ^ 2) ^ 2 ^ (i + 1) := fun i => by ring
    simp only [h2, pow_zero, pow_one]
    ring

theorem frobeniusEquiv_pow_apply (j : ℕ) (x : K) :
    ((frobeniusEquiv K 2) ^ j) x = x ^ 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ']
    change (frobeniusEquiv K 2) (((frobeniusEquiv K 2) ^ j) x) = _
    rw [ih, frobeniusEquiv_def]
    ring

theorem frobPair_pow_f {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ p : K, p ≠ 0 ∧ ((frobPair n hn b c hb) ^ f).val.right = 1 ∧
      ∀ (v : Fin (2 * n) → K) (k : Fin (2 * n)),
        coordinateSemilinearMap ((frobPair n hn b c hb) ^ f).val v k =
          v k + if k = tailZero n hn then p * v (tailOne n hn) else 0 := by
  have : Fintype K := Fintype.ofFinite K
  have hf' : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hf
  have hpow : ∀ x : K, x ^ 2 ^ f = x := fun x => by
    rw [← hf']
    exact FiniteField.pow_card x
  have hs : (tailSeq b c f).2 = 1 := by
    have h := tailSeq_snd_mul b c f
    rw [hpow b] at h
    have : (tailSeq b c f).2 * b = 1 * b := by rw [h, one_mul]
    exact mul_right_cancel₀ hb this
  have hp : (tailSeq b c f).1 ≠ 0 := by
    rw [tailSeq_fst b c hb, hpow b]
    refine mul_ne_zero hb fun htr => ?_
    obtain ⟨y, hy⟩ := exists_sq_add_eq_of_trace_zero hf' (c / b ^ 2) htr
    apply hirr (b * y)
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hc : c = (c / b ^ 2) * b ^ 2 := by field_simp
    rw [hc, ← hy]
    linear_combination (b ^ 2 * y * y + b ^ 2 * y) * h2
  refine ⟨(tailSeq b c f).1, hp, ?_, fun v k => ?_⟩
  · have e : ((frobPair n hn b c hb) ^ f).val.right = (frobeniusEquiv K 2) ^ f := by
      change ((frobPair n hn b c hb).val ^ f).right = _
      exact map_pow SemidirectProduct.rightHom _ f
    rw [e]
    exact RingEquiv.ext fun x => by rw [frobeniusEquiv_pow_apply, hpow x]; rfl
  · rw [frobPair_pow_apply, hs]
    by_cases h0 : k = tailZero n hn
    · subst h0
      simp only [ite_true, hpow]
    · by_cases h1 : k = tailOne n hn
      · subst h1
        simp only [tailOne_ne_tailZero n hn, ite_true, ite_false, hpow, one_mul, add_zero]
      · simp only [h0, h1, ite_false, hpow, add_zero]

end Pair

end CFSG.RankThree.PartOne.AUTSL

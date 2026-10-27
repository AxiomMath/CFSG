module

public import CFSG.Quasithin.Background.F918W3

public section

namespace CFSG.Quasithin.D35ValChk

open Matrix

private theorem transK_eq (a f : Nat) :
    transK a f = Nat.xor 1 (fmul (kent a 0) (kent f 0)) + fmul (kent a 0) (kent f 2) * 2 ^ 2 +
      fmul (kent a 0) (kent f 4) * 2 ^ 4 + fmul (kent a 2) (kent f 0) * 2 ^ 6 +
      Nat.xor 1 (fmul (kent a 2) (kent f 2)) * 2 ^ 8 + fmul (kent a 2) (kent f 4) * 2 ^ 10 +
      fmul (kent a 4) (kent f 0) * 2 ^ 12 + fmul (kent a 4) (kent f 2) * 2 ^ 14 +
      Nat.xor 1 (fmul (kent a 4) (kent f 4)) * 2 ^ 16 := by
  have e : ∀ x y : Nat, fmul (kent a x) (kent f y) < 4 := fun x y => by
    unfold fmul
    exact smul_lt4 _ (kent_lt4 _ _) _ (kent_lt4 _ _)
  have ex : ∀ x y : Nat, Nat.xor 1 (fmul (kent a x) (kent f y)) < 4 := fun x y =>
    Nat.xor_lt_two_pow (n := 2) (by norm_num) (e x y)
  have h0 := ex 0 0
  have h1 := e 0 2
  have h2 := e 0 4
  have h3 := e 2 0
  have h4 := ex 2 2
  have h5 := e 2 4
  have h6 := e 4 0
  have h7 := e 4 2
  have h8 := ex 4 4
  unfold transK
  rw [lor_shl 2 h0, lor_shl 4 (by omega), lor_shl 6 (by omega), lor_shl 8 (by omega), lor_shl 10 (by omega),
    lor_shl 12 (by omega), lor_shl 14 (by omega), lor_shl 16 (by omega)]

private theorem kent_transK (a f i j : Nat) (hi : i < 3) (hj : j < 3) :
    kent (transK a f) (6 * i + 2 * j) =
      if i = j then Nat.xor 1 (fmul (kent a (2 * i)) (kent f (2 * j))) else
        fmul (kent a (2 * i)) (kent f (2 * j)) := by
  have e : ∀ x y : Nat, fmul (kent a x) (kent f y) < 4 := fun x y => by
    unfold fmul
    exact smul_lt4 _ (kent_lt4 _ _) _ (kent_lt4 _ _)
  have ex : ∀ x y : Nat, Nat.xor 1 (fmul (kent a x) (kent f y)) < 4 := fun x y =>
    Nat.xor_lt_two_pow (n := 2) (by norm_num) (e x y)
  have h0 := ex 0 0
  have h1 := e 0 2
  have h2 := e 0 4
  have h3 := e 2 0
  have h4 := ex 2 2
  have h5 := e 2 4
  have h6 := e 4 0
  have h7 := e 4 2
  have h8 := ex 4 4
  rw [transK_eq, kent_eq_div_mod]
  interval_cases i <;> interval_cases j <;>
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reducePow, Nat.reduceEqDiff, ↓reduceIte] <;> omega

private theorem transK_lt (a f : Nat) : transK a f < 2 ^ 18 := by
  have e : ∀ x y : Nat, fmul (kent a x) (kent f y) < 4 := fun x y => by
    unfold fmul
    exact smul_lt4 _ (kent_lt4 _ _) _ (kent_lt4 _ _)
  have ex : ∀ x y : Nat, Nat.xor 1 (fmul (kent a x) (kent f y)) < 4 := fun x y =>
    Nat.xor_lt_two_pow (n := 2) (by norm_num) (e x y)
  have h0 := ex 0 0
  have h1 := e 0 2
  have h2 := e 0 4
  have h3 := e 2 0
  have h4 := ex 2 2
  have h5 := e 2 4
  have h6 := e 4 0
  have h7 := e 4 2
  have h8 := ex 4 4
  rw [transK_eq]
  omega

private theorem mc_one_add_vecMulVec {K : Type} [Field K] (C : KCoding K) (a f : Fin 3 → K) :
    C.mc (1 + Matrix.vecMulVec a f) = transK (C.vc a) (C.vc f) := by
  refine eq_of_kent_eq_fin (C.mc_lt _) (transK_lt _ _) ?_
  intro i j
  rw [C.kent_mc, kent_transK _ _ i.val j.val i.2 j.2, C.kent_vc, C.kent_vc]
  unfold fmul
  by_cases hij : i = j
  · subst hij
    have h1 : (1 + Matrix.vecMulVec a f) i i = 1 + a i * f i := by simp [Matrix.vecMulVec_apply]
    rw [h1, C.enc_add, C.enc_one, C.enc_mul]
    simp
  · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have h1 : (1 + Matrix.vecMulVec a f) i j = a i * f j := by
      simp [Matrix.vecMulVec_apply, hij]
    rw [h1, C.enc_mul]
    simp [hv]

theorem exists_vecMulVec_of_sq_zero {K : Type} [Field K] {N : Matrix (Fin 3) (Fin 3) K}
    (hN : N * N = 0) (h0 : N ≠ 0) :
    ∃ a c : Fin 3 → K, a ≠ 0 ∧ c ≠ 0 ∧ N = Matrix.vecMulVec a c ∧ c ⬝ᵥ a = 0 := by
  classical
  set f : (Fin 3 → K) →ₗ[K] (Fin 3 → K) := Matrix.toLin' N with hf
  have hff : f ∘ₗ f = 0 := by
    rw [hf, ← Matrix.toLin'_mul, hN, map_zero]
  have hle : LinearMap.range f ≤ LinearMap.ker f := by
    rw [LinearMap.range_le_ker_iff]
    exact hff
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  have hdim : Module.finrank K (Fin 3 → K) = 3 := by simp
  have hmono : Module.finrank K (LinearMap.range f) ≤ Module.finrank K (LinearMap.ker f) :=
    Submodule.finrank_mono hle
  have hf0 : f ≠ 0 := by
    intro h
    apply h0
    apply Matrix.toLin'.injective
    rw [map_zero]
    exact h
  have hpos : Module.finrank K (LinearMap.range f) ≠ 0 := by
    intro h
    apply hf0
    rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
    exact h
  have hfr : Module.finrank K (LinearMap.range f) = 1 := by omega
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hfr
  have hcol : ∀ s : Fin 3, ∃ c : K, ∀ r, N r s = c * (v : Fin 3 → K) r := by
    intro s
    have hmem : f (Pi.single s 1) ∈ LinearMap.range f := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ := hv ⟨f (Pi.single s 1), hmem⟩
    refine ⟨c, fun r => ?_⟩
    have := congrArg (fun w : LinearMap.range f => (w : Fin 3 → K) r) hc
    simpa [hf, Matrix.toLin'_apply] using this.symm
  choose c hc using hcol
  have hvne : (v : Fin 3 → K) ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hNeq : N = Matrix.vecMulVec (v : Fin 3 → K) c := by
    ext r s
    rw [Matrix.vecMulVec_apply, hc s r, mul_comm]
  have hcne : c ≠ 0 := by
    intro h
    apply h0
    rw [hNeq, h]
    ext r s
    simp
  refine ⟨v, c, hvne, hcne, hNeq, ?_⟩
  obtain ⟨r, hr⟩ : ∃ r, (v : Fin 3 → K) r ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hvne (funext hcon)
  obtain ⟨t, ht⟩ : ∃ t, c t ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hcne (funext hcon)
  have h1 := congrFun (congrFun hN r) t
  rw [hNeq] at h1
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Fin.sum_univ_three, Matrix.zero_apply] at h1
  have h2 : (v : Fin 3 → K) r * c t * (c ⬝ᵥ (v : Fin 3 → K)) = 0 := by
    simp only [dotProduct, Fin.sum_univ_three]
    linear_combination h1
  exact (mul_eq_zero.mp h2).resolve_left (mul_ne_zero hr ht)

private theorem exists_normalized {K : Type} [Field K] {a : Fin 3 → K} (ha : a ≠ 0) :
    ∃ u : K, u ≠ 0 ∧ ((u⁻¹ • a) 0 = 1 ∨ ((u⁻¹ • a) 0 = 0 ∧ (u⁻¹ • a) 1 = 1) ∨
      ((u⁻¹ • a) 0 = 0 ∧ (u⁻¹ • a) 1 = 0 ∧ (u⁻¹ • a) 2 = 1)) := by
  by_cases h0 : a 0 = 0
  · by_cases h1 : a 1 = 0
    · have h2 : a 2 ≠ 0 := by
        intro h2
        apply ha
        funext i
        fin_cases i <;> simp [h0, h1, h2]
      refine ⟨a 2, h2, Or.inr (Or.inr ?_)⟩
      simp [h0, h1, h2]
    · refine ⟨a 1, h1, Or.inr (Or.inl ?_)⟩
      simp [h0, h1]
  · exact ⟨a 0, h0, Or.inl (by simp [h0])⟩

private theorem mc_trans_mem_tList {K : Type} [Field K] (C : KCoding K) {a f : Fin 3 → K}
    (ha : a 0 = 1 ∨ (a 0 = 0 ∧ a 1 = 1) ∨ (a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 1)) (hf : f ≠ 0) (hdot : f ⬝ᵥ a = 0) :
    C.mc (1 + Matrix.vecMulVec a f) ∈ tList := by
  have e0 : kent (C.vc a) 0 = C.enc (a 0) := by simpa using C.kent_vc a 0
  have e1 : kent (C.vc a) 2 = C.enc (a 1) := by simpa using C.kent_vc a 1
  have e2 : kent (C.vc a) 4 = C.enc (a 2) := by simpa using C.kent_vc a 2
  have f0 : kent (C.vc f) 0 = C.enc (f 0) := by simpa using C.kent_vc f 0
  have f1 : kent (C.vc f) 2 = C.enc (f 1) := by simpa using C.kent_vc f 1
  have f2 : kent (C.vc f) 4 = C.enc (f 2) := by simpa using C.kent_vc f 2
  rw [mc_one_add_vecMulVec]
  unfold tList
  rw [List.mem_flatMap]
  refine ⟨C.vc a, ?_, ?_⟩
  · rw [List.mem_filter, List.mem_range]
    refine ⟨C.vc_lt a, ?_⟩
    unfold isNormVec
    rw [e0, e1, e2]
    rcases ha with h | ⟨h0, h1⟩ | ⟨h0, h1, h2⟩
    · simp [h, C.enc_one]
    · simp [h0, h1, C.enc_zero, C.enc_one]
    · simp [h0, h1, h2, C.enc_zero, C.enc_one]
  · rw [List.mem_map]
    refine ⟨C.vc f, ?_, rfl⟩
    rw [List.mem_filter, List.mem_range]
    refine ⟨C.vc_lt f, ?_⟩
    have hne : C.vc f ≠ 0 := by
      intro h
      apply hf
      apply C.vc_inj
      rw [h]
      simp [KCoding.vc, C.enc_zero]
    have hd : dotK (C.vc a) (C.vc f) = C.enc (f ⬝ᵥ a) := by
      unfold dotK fmul
      rw [e0, e1, e2, f0, f1, f2, ← C.enc_mul, ← C.enc_mul, ← C.enc_mul, ← C.enc_add, ← C.enc_add]
      simp only [dotProduct, Fin.sum_univ_three]
      congr 1
      ring
    show (!Nat.beq (C.vc f) 0 && Nat.beq (dotK (C.vc a) (C.vc f)) 0) = true
    rw [hd, hdot, C.enc_zero]
    have hb : Nat.beq (C.vc f) 0 = false := by
      cases h : Nat.beq (C.vc f) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hne
    rw [hb]
    rfl

theorem mc_mem_tList {K : Type} [Field K] [CharP K 2] (C : KCoding K) {X : Matrix (Fin 3) (Fin 3) K}
    (h2 : X * X = 1) (h1 : X ≠ 1) : C.mc X ∈ tList := by
  have h2K : (2 : K) = 0 := by
    have := CharP.cast_eq_zero K 2
    simpa using this
  have hXX : ∀ M : Matrix (Fin 3) (Fin 3) K, M + M = 0 := fun M => by
    rw [← two_smul K M, h2K, zero_smul]
  have hN : (X + 1) * (X + 1) = 0 := by
    have : (X + 1) * (X + 1) = X * X + X + X + 1 := by noncomm_ring
    rw [this, h2]
    calc (1 : Matrix (Fin 3) (Fin 3) K) + X + X + 1 = (X + X) + (1 + 1) := by abel
      _ = 0 := by rw [hXX X, hXX 1, add_zero]
  have hN0 : X + 1 ≠ 0 := by
    intro h
    apply h1
    have : X = (X + 1) + 1 := by rw [add_assoc, hXX 1, add_zero]
    rw [this, h, zero_add]
  obtain ⟨a, c, ha, hc, hNeq, hdot⟩ := exists_vecMulVec_of_sq_zero hN hN0
  obtain ⟨u, hu, hnorm⟩ := exists_normalized ha
  have hX : X = 1 + Matrix.vecMulVec (u⁻¹ • a) (u • c) := by
    have h3 : Matrix.vecMulVec (u⁻¹ • a) (u • c) = Matrix.vecMulVec a c := by
      ext i j
      simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    have : X = (X + 1) + 1 := by rw [add_assoc, hXX 1, add_zero]
    rw [h3, ← hNeq, add_comm 1 (X + 1)]
    exact this
  rw [hX]
  refine mc_trans_mem_tList C hnorm (smul_ne_zero hu hc) ?_
  rw [smul_dotProduct, dotProduct_smul, hdot]
  simp

end CFSG.Quasithin.D35ValChk

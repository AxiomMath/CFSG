module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat
public import CFSG.LieType.BorelTits.Flag

public section

namespace CFSG.Quasithin.H13.Ch4.Sp4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

section Blocks

variable {F : Type} [Field F]

theorem two_eq_zero_of_card_eq_four [Fintype F] (hF : Fintype.card F = 4) : (2 : F) = 0 := by
  have h : ((4 : ℕ) : F) = 0 := hF ▸ FiniteField.cast_card_eq_zero F
  have h4 : (2 : F) ^ 2 = 0 := by
    rw [show (2 : F) ^ 2 = ((4 : ℕ) : F) by norm_num]
    exact h
  exact pow_eq_zero_iff (by norm_num) |>.mp h4

theorem mul_eq_fromBlocks (M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    M * N = fromBlocks (M.toBlocks₁₁ * N.toBlocks₁₁ + M.toBlocks₁₂ * N.toBlocks₂₁)
      (M.toBlocks₁₁ * N.toBlocks₁₂ + M.toBlocks₁₂ * N.toBlocks₂₂)
      (M.toBlocks₂₁ * N.toBlocks₁₁ + M.toBlocks₂₂ * N.toBlocks₂₁)
      (M.toBlocks₂₁ * N.toBlocks₁₂ + M.toBlocks₂₂ * N.toBlocks₂₂) := by
  conv_lhs => rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N]
  rw [fromBlocks_multiply]

theorem blocks_of_symplectic {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hM : Mᵀ * fromBlocks 0 1 (-1) 0 * M = fromBlocks 0 1 (-1) 0) (h21 : M.toBlocks₂₁ = 0) :
    M.toBlocks₁₁ᵀ * M.toBlocks₂₂ = 1 ∧
      M.toBlocks₁₂ᵀ * M.toBlocks₂₂ = M.toBlocks₂₂ᵀ * M.toBlocks₁₂ := by
  rw [← fromBlocks_toBlocks M, h21, fromBlocks_transpose, fromBlocks_multiply,
    fromBlocks_multiply, fromBlocks_inj] at hM
  obtain ⟨-, h2, -, h4⟩ := hM
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.mul_neg, Matrix.neg_mul, transpose_zero, neg_zero] at h2 h4
  exact ⟨h2, (neg_add_eq_zero.mp h4).symm⟩

@[expose] def blockHom {Λ : Type} [Group Λ] (f : Λ →* GL (Fin 2 ⊕ Fin 2) F)
    (hf : ∀ x, (f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0) :
    Λ →* Matrix (Fin 2) (Fin 2) F where
  toFun x := (f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁
  map_one' := by
    rw [map_one, Units.val_one, ← fromBlocks_one, toBlocks_fromBlocks₁₁]
  map_mul' x y := by
    rw [map_mul, Units.val_mul, mul_eq_fromBlocks, toBlocks_fromBlocks₁₁, hf y,
      Matrix.mul_zero, add_zero]

theorem blockHom_apply {Λ : Type} [Group Λ] (f : Λ →* GL (Fin 2 ⊕ Fin 2) F)
    (hf : ∀ x, (f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0) (x : Λ) :
    blockHom f hf x = (f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ := rfl

end Blocks

section Levi

variable {F : Type} [Field F] {Λ : Type} [Group Λ] (f : Λ →* GL (Fin 2 ⊕ Fin 2) F)
  (h21 : ∀ x, (f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0)

theorem det_blockHom_eq_one (hperf : commutator Λ = ⊤) (x : Λ) : (blockHom f h21 x).det = 1 := by
  set φ : Λ →* F := Matrix.detMonoidHom.comp (blockHom f h21) with hφ
  have h := Abelianization.commutator_subset_ker φ.toHomUnits
  rw [hperf] at h
  have hx : φ.toHomUnits x = 1 := h (Subgroup.mem_top x)
  have := congrArg Units.val hx
  simpa [φ] using this

@[expose] def slHom (hperf : commutator Λ = ⊤) : Λ →* SpecialLinearGroup (Fin 2) F where
  toFun x := ⟨blockHom f h21 x, det_blockHom_eq_one f h21 hperf x⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x y)

theorem coe_slHom (hperf : commutator Λ = ⊤) (x : Λ) :
    ((slHom f h21 hperf x : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ := rfl

variable (hS : ∀ x, f x ∈ StatedSp 2 F)
include h21 hS

theorem toBlocks₁₁_transpose_mul (x : Λ) :
    (f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ᵀ *
      (f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₂ = 1 :=
  (blocks_of_symplectic (SymplecticTorusWeyl.mem_statedSp_iff.mp (hS x)) (h21 x)).1

theorem isPGroup_ker_slHom (h2 : (2 : F) = 0) (hperf : commutator Λ = ⊤)
    (hker : IsPGroup 2 f.ker) : IsPGroup 2 (slHom f h21 hperf).ker := by
  rintro ⟨x, hx⟩
  have hA : (f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ = 1 := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F))
      (MonoidHom.mem_ker.mp hx)
    simpa [coe_slHom] using this
  have hD : (f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₂ = 1 := by
    have h1 := toBlocks₁₁_transpose_mul f h21 hS x
    rwa [hA, transpose_one, Matrix.one_mul] at h1
  have hsq : f (x ^ 2) = 1 := by
    apply Units.ext
    rw [map_pow, Units.val_pow_eq_pow_val, pow_two, Units.val_one, mul_eq_fromBlocks, hA, hD,
      h21 x, ← fromBlocks_one]
    congr 1
    · simp
    · rw [Matrix.one_mul, Matrix.mul_one, ← two_smul F, h2, zero_smul]
    · simp
    · simp
  obtain ⟨k, hk⟩ := hker ⟨x ^ 2, hsq⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  have := congrArg Subtype.val hk
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this ⊢
  rw [pow_succ', pow_mul]
  exact this

theorem slHom_surjective [Fintype F] (hF : Fintype.card F = 4) [Finite Λ]
    (hperf : commutator Λ = ⊤) (hker : IsPGroup 2 f.ker)
    (h60 : Nat.card (Λ ⧸ CFSG.pCore 2 Λ) = 60) : Function.Surjective (slHom f h21 hperf) := by
  have h2 : (2 : F) = 0 := two_eq_zero_of_card_eq_four hF
  set ρ := slHom f h21 hperf with hρ
  have hK : ρ.ker ≤ CFSG.pCore 2 Λ :=
    le_sSup ⟨inferInstance, isPGroup_ker_slHom f h21 hS h2 hperf hker⟩
  have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv] at e1
  have e2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 Λ)
  rw [h60] at e2
  have hle := Subgroup.card_le_of_le hK
  have hpos : 0 < Nat.card (CFSG.pCore 2 Λ) := Nat.card_pos
  have hcardSL : Nat.card (SpecialLinearGroup (Fin 2) F) = 60 := by
    rw [card_SL_field 2, Fin.prod_univ_two, hF]
    norm_num
  have hrange : 60 ≤ Nat.card ρ.range := by
    by_contra h
    push Not at h
    have h3 : Nat.card ρ.range * Nat.card ρ.ker < 60 * Nat.card (CFSG.pCore 2 Λ) :=
      calc Nat.card ρ.range * Nat.card ρ.ker ≤ Nat.card ρ.range * Nat.card (CFSG.pCore 2 Λ) :=
            Nat.mul_le_mul_left _ hle
        _ < 60 * Nat.card (CFSG.pCore 2 Λ) := Nat.mul_lt_mul_of_pos_right h hpos
    omega
  have htop : ρ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have := Subgroup.card_le_card_group ρ.range
    omega
  exact MonoidHom.range_eq_top.mp htop

end Levi

section Two

variable {F : Type} [Field F]

theorem exists_sl2_mulVec_single (a : Fin 2 → F) (ha : a ≠ 0) :
    ∃ M : SpecialLinearGroup (Fin 2) F, (M : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] = a := by
  by_cases h0 : a 0 = 0
  · have h1 : a 1 ≠ 0 := by
      intro h1
      apply ha
      funext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨⟨!![0, -(a 1)⁻¹; a 1, 0], by simp [det_fin_two_of, h1]⟩, ?_⟩
    funext i
    fin_cases i <;> simp [h0]
  · refine ⟨⟨!![a 0, 0; a 1, (a 0)⁻¹], by simp [det_fin_two_of, h0]⟩, ?_⟩
    funext i
    fin_cases i <;> simp

theorem exists_sl2_mulVec (a b : Fin 2 → F) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ M : SpecialLinearGroup (Fin 2) F, (M : Matrix (Fin 2) (Fin 2) F) *ᵥ a = b := by
  obtain ⟨A, hA⟩ := exists_sl2_mulVec_single a ha
  obtain ⟨B, hB⟩ := exists_sl2_mulVec_single b hb
  have hmul : ∀ (M N : SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F),
      ((M * N : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v =
        (M : Matrix (Fin 2) (Fin 2) F) *ᵥ ((N : Matrix (Fin 2) (Fin 2) F) *ᵥ v) := by
    intro M N v
    rw [Matrix.mulVec_mulVec]
    rfl
  refine ⟨B * A⁻¹, ?_⟩
  rw [hmul, ← hA, ← hmul A⁻¹ A, inv_mul_cancel]
  change (B : Matrix (Fin 2) (Fin 2) F) *ᵥ ((1 : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0]) = b
  rw [one_mulVec, hB]

variable (h2 : (2 : F) = 0)
include h2

theorem conj_upper (a b c : F) :
    !![1, 1; 0, 1] * !![a, b; b, c] * (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F)ᵀ =
      !![a + c, b + c; b + c, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination b * h2

theorem conj_lower (a b : F) :
    !![1, 0; 1, 1] * !![a, b; b, 0] * (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F)ᵀ =
      !![a, a + b; a + b, a] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination b * h2

omit h2 in
theorem conj_torus {l : F} (hl : l ≠ 0) (a b c : F) :
    !![l, 0; 0, l⁻¹] * !![a, b; b, c] * (!![l, 0; 0, l⁻¹] : Matrix (Fin 2) (Fin 2) F)ᵀ =
      !![l * l * a, b; b, l⁻¹ * l⁻¹ * c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem conj_alt (A : Matrix (Fin 2) (Fin 2) F) (hA : A.det = 1) (e : F) :
    A * !![0, e; e, 0] * Aᵀ = !![0, e; e, 0] := by
  rw [Matrix.eta_fin_two A, det_fin_two_of] at hA
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (A 0 0 * A 0 1 * e) * h2
  · linear_combination e * hA + (A 0 1 * A 1 0 * e) * h2
  · linear_combination e * hA + (A 0 1 * A 1 0 * e) * h2
  · linear_combination (A 1 0 * A 1 1 * e) * h2

theorem exists_alt_of_closed {l : F} (hl0 : l ≠ 0) (hl1 : l ≠ 1) (hl3 : l ^ 3 = 1)
    (𝒳 : Set (Matrix (Fin 2) (Fin 2) F)) (hadd : ∀ S ∈ 𝒳, ∀ S' ∈ 𝒳, S + S' ∈ 𝒳)
    (hconj : ∀ A : Matrix (Fin 2) (Fin 2) F, A.det = 1 → ∀ S ∈ 𝒳, A * S * Aᵀ ∈ 𝒳)
    (S : Matrix (Fin 2) (Fin 2) F) (hS : S ∈ 𝒳) (hSsym : Sᵀ = S) (hS0 : S ≠ 0) :
    ∃ e : F, e ≠ 0 ∧ !![0, e; e, 0] ∈ 𝒳 := by
  have hU : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by simp [det_fin_two_of]
  have hL : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by simp [det_fin_two_of]
  have hT : ∀ m : F, m ≠ 0 → (!![m, 0; 0, m⁻¹] : Matrix (Fin 2) (Fin 2) F).det = 1 :=
    fun m hm => by simp [det_fin_two_of, hm]
  have hl2 : l * l ≠ 0 := mul_ne_zero hl0 hl0
  have hsum : 1 + l * l + l * l * (l * l) = 0 := by
    have h3 : (l - 1) * (l * l + l + 1) = 0 := by linear_combination hl3
    have h4 : l * l + l + 1 = 0 := (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hl1)
    linear_combination h4 + l * hl3
  have key : ∀ a b c : F, c ≠ 0 → !![a, b; b, c] ∈ 𝒳 → ∃ e : F, e ≠ 0 ∧ !![0, e; e, 0] ∈ 𝒳 := by
    intro a b c hc h
    have h1 := hadd _ (hconj _ hU _ h) _ h
    rw [conj_upper h2] at h1
    have e1 : !![a + c, b + c; b + c, c] + !![a, b; b, c] = (!![c, c; c, 0] : Matrix _ _ F) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · linear_combination a * h2
      · linear_combination b * h2
      · linear_combination b * h2
      · linear_combination c * h2
    rw [e1] at h1
    have h3 := hconj _ (hT l hl0) _ h1
    have h4 := hconj _ (hT (l * l) hl2) _ h1
    rw [conj_torus hl0] at h3
    rw [conj_torus hl2] at h4
    refine ⟨c, hc, ?_⟩
    have h5 := hadd _ (hadd _ h1 _ h3) _ h4
    convert h5 using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination (-c) * hsum
    · linear_combination c * h2
    · linear_combination c * h2
  rw [Matrix.eta_fin_two S] at hS hS0
  have hb : S 1 0 = S 0 1 := by
    have := congrFun (congrFun hSsym 0) 1
    simpa using this
  rw [hb] at hS hS0
  by_cases hc : S 1 1 = 0
  · by_cases ha : S 0 0 = 0
    · rw [ha, hc] at hS hS0
      refine ⟨S 0 1, fun h => hS0 ?_, hS⟩
      rw [h]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · rw [hc] at hS
      have h1 := hadd _ (hconj _ hL _ hS) _ hS
      rw [conj_lower h2] at h1
      have e1 : !![S 0 0, S 0 0 + S 0 1; S 0 0 + S 0 1, S 0 0] + !![S 0 0, S 0 1; S 0 1, 0] =
          (!![0, S 0 0; S 0 0, S 0 0] : Matrix _ _ F) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp
        · linear_combination S 0 0 * h2
        · linear_combination S 0 1 * h2
        · linear_combination S 0 1 * h2
      rw [e1] at h1
      exact key 0 (S 0 0) (S 0 0) ha h1
  · exact key _ _ _ hc hS

end Two

section Std

variable {F : Type} [Field F] {Λ : Type} [Group Λ] (f : Λ →* GL (Fin 2 ⊕ Fin 2) F)
  (h21 : ∀ x, (f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0)
  (hS : ∀ x, f x ∈ StatedSp 2 F)
include h21 hS

theorem exists_toBlocks₂₂_mulVec (hperf : commutator Λ = ⊤)
    (hsurj : Function.Surjective (slHom f h21 hperf)) (a b : Fin 2 → F) (ha : a ≠ 0)
    (hb : b ≠ 0) :
    ∃ x, (f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₂ *ᵥ a = b := by
  obtain ⟨D, hD⟩ := exists_sl2_mulVec a b ha hb
  let A : SpecialLinearGroup (Fin 2) F := ⟨(adjugate (D : Matrix (Fin 2) (Fin 2) F))ᵀ, by
    rw [det_transpose, det_adjugate, D.2, one_pow]⟩
  obtain ⟨x, hx⟩ := hsurj A
  refine ⟨x, ?_⟩
  have h1 := toBlocks₁₁_transpose_mul f h21 hS x
  have hAx : (f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ =
      (adjugate (D : Matrix (Fin 2) (Fin 2) F))ᵀ := by
    rw [← coe_slHom f h21 hperf x, hx]
  rw [hAx, transpose_transpose] at h1
  have h3 : (D : Matrix (Fin 2) (Fin 2) F) * adjugate (D : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [mul_adjugate, D.2, one_smul]
  have hDx : (f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₂ = D :=
    calc (f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₂ =
          ((D : Matrix (Fin 2) (Fin 2) F) * adjugate (D : Matrix (Fin 2) (Fin 2) F)) *
            (f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₂ := by
          rw [h3, Matrix.one_mul]
      _ = D * (adjugate (D : Matrix (Fin 2) (Fin 2) F) *
            (f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₂) := by
          rw [Matrix.mul_assoc]
      _ = D := by rw [h1, Matrix.mul_one]
  rw [hDx, hD]

theorem false_of_radical_std [Fintype F] (hF : Fintype.card F = 4) (hperf : commutator Λ = ⊤)
    (hsurj : Function.Surjective (slHom f h21 hperf))
    (X : Subgroup (GL (Fin 2 ⊕ Fin 2) F)) (hXS : X ≤ StatedSp 2 F)
    (hX : ∀ x ∈ X, (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ = 1 ∧
      (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0 ∧
      (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₂ = 1)
    (hXN : ∀ y, f y ∈ Subgroup.normalizer (X : Set (GL (Fin 2 ⊕ Fin 2) F))) (hX1 : X ≠ ⊥)
    (hXC : ∀ x ∈ X, (∀ y, f y * x = x * f y) → x = 1) : False := by
  have h2 : (2 : F) = 0 := two_eq_zero_of_card_eq_four hF
  set σ : GL (Fin 2 ⊕ Fin 2) F → Matrix (Fin 2) (Fin 2) F :=
    fun x => (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₂ with hσ
  have hform : ∀ x ∈ X,
      (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = fromBlocks 1 (σ x) 0 1 := by
    intro x hx
    obtain ⟨h1, h3, h4⟩ := hX x hx
    conv_lhs => rw [← fromBlocks_toBlocks (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)]
    rw [h1, h3, h4]
  have hinj : ∀ x ∈ X, ∀ x' ∈ X, σ x = σ x' → x = x' := by
    intro x hx x' hx' h
    apply Units.ext
    rw [hform x hx, hform x' hx', h]
  have hmul : ∀ x ∈ X, ∀ x' ∈ X, σ (x * x') = σ x + σ x' := by
    intro x hx x' hx'
    show ((x * x' : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₂ =
      σ x + σ x'
    rw [Units.val_mul, hform x hx, hform x' hx', fromBlocks_multiply, toBlocks_fromBlocks₁₂,
      Matrix.one_mul, Matrix.mul_one, add_comm]
  have hσ1 : σ 1 = 0 := by
    simp only [hσ, Units.val_one]
    rw [← fromBlocks_one, toBlocks_fromBlocks₁₂]
  have hsym : ∀ x ∈ X, (σ x)ᵀ = σ x := by
    intro x hx
    obtain ⟨-, h3, h4⟩ := hX x hx
    have h5 := (blocks_of_symplectic (SymplecticTorusWeyl.mem_statedSp_iff.mp (hXS hx)) h3).2
    rw [h4, Matrix.mul_one, transpose_one, Matrix.one_mul] at h5
    exact h5
  have hconj : ∀ y, ∀ x ∈ X, σ (f y * x * (f y)⁻¹) =
      (f y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ * σ x *
        (f y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ᵀ := by
    intro y x hx
    obtain ⟨z, hzX, hzdef⟩ : ∃ z ∈ X, z = f y * x * (f y)⁻¹ :=
      ⟨_, (Subgroup.mem_normalizer_iff.mp (hXN y) x).mp hx, rfl⟩
    rw [← hzdef]
    have heq : z * f y = f y * x := by rw [hzdef]; group
    have h12 := congrArg
      (fun M : GL (Fin 2 ⊕ Fin 2) F => (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₂)
      heq
    simp only [Units.val_mul] at h12
    rw [mul_eq_fromBlocks, mul_eq_fromBlocks, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₁₂,
      (hX z hzX).1, (hX x hx).2.2, Matrix.one_mul, Matrix.mul_one] at h12
    have h3 : σ z * (f y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₂ =
        (f y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ * σ x :=
      add_left_cancel (h12.trans (add_comm _ _))
    have hDA : (f y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₂ *
        (f y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ᵀ = 1 :=
      mul_eq_one_comm.mp (toBlocks₁₁_transpose_mul f h21 hS y)
    calc σ z = σ z * ((f y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₂ *
          (f y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ᵀ) := by
          rw [hDA, Matrix.mul_one]
      _ = σ z * (f y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₂ *
          (f y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ᵀ := by
          rw [Matrix.mul_assoc]
      _ = _ := by rw [h3]
  set 𝒳 : Set (Matrix (Fin 2) (Fin 2) F) := {S | ∃ x ∈ X, σ x = S} with h𝒳
  have hadd : ∀ S ∈ 𝒳, ∀ S' ∈ 𝒳, S + S' ∈ 𝒳 := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    exact ⟨x * x', X.mul_mem hx hx', hmul x hx x' hx'⟩
  have hconj' : ∀ A : Matrix (Fin 2) (Fin 2) F, A.det = 1 → ∀ S ∈ 𝒳, A * S * Aᵀ ∈ 𝒳 := by
    rintro A hA _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := hsurj ⟨A, hA⟩
    have hAy : (f y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ = A := by
      rw [← coe_slHom f h21 hperf y, hy]
    refine ⟨f y * x * (f y)⁻¹, (Subgroup.mem_normalizer_iff.mp (hXN y) x).mp hx, ?_⟩
    rw [hconj y x hx, hAy]
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX1
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hσx : σ x ≠ 0 := fun h => hx1' (hinj x hx 1 X.one_mem (h.trans hσ1.symm))
  obtain ⟨l, hl0, hl1⟩ : ∃ l : F, l ≠ 0 ∧ l ≠ 1 := by
    classical
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset F) ⊆ ({0, 1} : Finset F) := fun l _ => by
      by_cases hl : l = 0
      · simp [hl]
      · simp [h l hl]
    have h5 := Finset.card_le_card hsub
    rw [Finset.card_univ, hF] at h5
    have h6 := Finset.card_insert_le (0 : F) ({1} : Finset F)
    rw [Finset.card_singleton] at h6
    omega
  have hl3 : l ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one l hl0
    rwa [hF] at this
  obtain ⟨e, he, z, hz, hze⟩ :=
    exists_alt_of_closed h2 hl0 hl1 hl3 𝒳 hadd hconj' (σ x) ⟨x, hx, rfl⟩ (hsym x hx) hσx
  have hzc : ∀ y, f y * z = z * f y := by
    intro y
    have h3 := hconj y z hz
    have hdet : ((f y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁).det = 1 :=
      det_blockHom_eq_one f h21 hperf y
    rw [hze, conj_alt h2 _ hdet e, ← hze] at h3
    have h4 := hinj _ ((Subgroup.mem_normalizer_iff.mp (hXN y) z).mp hz) z hz h3
    calc f y * z = (f y * z * (f y)⁻¹) * f y := by group
      _ = z * f y := by rw [h4]
  have hz1 := hXC z hz hzc
  rw [hz1, hσ1] at hze
  apply he
  have := congrFun (congrFun hze 0) 1
  simpa using this.symm

end Std

section Lagrangian

variable {F : Type} [Field F]

@[expose] def stdPlane (F : Type) [Field F] : Submodule F (Fin 2 ⊕ Fin 2 → F) :=
  SymplecticFlag.isoFlag 2 F 2

theorem mem_stdPlane {v : Fin 2 ⊕ Fin 2 → F} : v ∈ stdPlane F ↔ ∀ j, v (Sum.inr j) = 0 := by
  rw [stdPlane, SymplecticFlag.mem_isoFlag]
  exact ⟨fun h => h.1, fun h => ⟨h, fun j hj => absurd hj (not_le.mpr j.isLt)⟩⟩

theorem finrank_stdPlane : Module.finrank F (stdPlane F) = 2 :=
  SymplecticHigher.finrank_isoFlag le_rfl

theorem isTotallyIsotropic_stdPlane :
    SymplecticFlag.IsTotallyIsotropic (pairedSympForm F 2) (stdPlane F) := by
  intro x hx y hy
  rw [pairedSympForm_apply]
  have hx' : x ∘ Sum.inr = 0 := funext fun j => mem_stdPlane.mp hx j
  have hy' : y ∘ Sum.inr = 0 := funext fun j => mem_stdPlane.mp hy j
  rw [hx', hy', dotProduct_zero, zero_dotProduct, sub_zero]

theorem mulVec_inr (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (v : Fin 2 ⊕ Fin 2 → F)
    (j : Fin 2) : (M *ᵥ v) (Sum.inr j) =
      (M.toBlocks₂₁ *ᵥ (v ∘ Sum.inl)) j + (M.toBlocks₂₂ *ᵥ (v ∘ Sum.inr)) j := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  rw [fromBlocks_mulVec]
  rfl

theorem toBlocks₂₁_eq_zero_of_mulVec_mem {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hM : ∀ w ∈ stdPlane F, M *ᵥ w ∈ stdPlane F) : M.toBlocks₂₁ = 0 := by
  ext i j
  have h := mem_stdPlane.mp (hM (Pi.single (Sum.inl j) 1) (mem_stdPlane.mpr fun k => by simp)) i
  simpa [toBlocks₂₁, mulVec, dotProduct, Pi.single_apply] using h

theorem blocks_of_mem_radical {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (h1 : ∀ w ∈ stdPlane F, M *ᵥ w = w) (h2 : ∀ v, M *ᵥ v - v ∈ stdPlane F) :
    M.toBlocks₁₁ = 1 ∧ M.toBlocks₂₁ = 0 ∧ M.toBlocks₂₂ = 1 := by
  have hs : ∀ j, (Pi.single (Sum.inl j) 1 : Fin 2 ⊕ Fin 2 → F) ∈ stdPlane F :=
    fun j => mem_stdPlane.mpr fun k => by simp
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have h := congrFun (h1 _ (hs j)) (Sum.inl i)
    simpa [toBlocks₁₁, mulVec, dotProduct, Pi.single_apply, one_apply, eq_comm] using h
  · ext i j
    have h := congrFun (h1 _ (hs j)) (Sum.inr i)
    simpa [toBlocks₂₁, mulVec, dotProduct, Pi.single_apply] using h
  · ext i j
    have h := mem_stdPlane.mp (h2 (Pi.single (Sum.inr j) 1)) i
    simp [Pi.single_apply, sub_eq_zero] at h
    simp [toBlocks₂₂, one_apply, h]

@[expose] def conjHom (g : GL (Fin 2 ⊕ Fin 2) F) {Λ : Type} [Group Λ]
    (f : Λ →* GL (Fin 2 ⊕ Fin 2) F) : Λ →* GL (Fin 2 ⊕ Fin 2) F :=
  (MulAut.conj g⁻¹).toMonoidHom.comp f

theorem conjHom_apply (g : GL (Fin 2 ⊕ Fin 2) F) {Λ : Type} [Group Λ]
    (f : Λ →* GL (Fin 2 ⊕ Fin 2) F) (x : Λ) : conjHom g f x = g⁻¹ * f x * g := by
  simp [conjHom]

theorem mem_iff_of_map_eq {W : Submodule F (Fin 2 ⊕ Fin 2 → F)} {g : GL (Fin 2 ⊕ Fin 2) F}
    (hg : (stdPlane F).map (mulVecLin (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) = W)
    (v : Fin 2 ⊕ Fin 2 → F) :
    v ∈ W ↔ ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v ∈
      stdPlane F := by
  rw [← hg, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mulVecLin_apply, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_mulVec]
    exact hw
  · intro h
    refine ⟨_, h, ?_⟩
    rw [mulVecLin_apply, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mulVec]

structure LeviData (F : Type) [Field F] [Fintype F] (W : Submodule F (Fin 2 ⊕ Fin 2 → F))
    {Λ : Type} [Group Λ] [Finite Λ] (f : Λ →* GL (Fin 2 ⊕ Fin 2) F) : Prop where
  card : Fintype.card F = 4
  finrank : Module.finrank F W = 2
  iso : SymplecticFlag.IsTotallyIsotropic (pairedSympForm F 2) W
  mem : ∀ x, f x ∈ StatedSp 2 F
  stab : ∀ x, ∀ w ∈ W, (f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈ W
  perf : commutator Λ = ⊤
  ker : IsPGroup 2 f.ker
  card60 : Nat.card (Λ ⧸ CFSG.pCore 2 Λ) = 60

variable [Fintype F] {W : Submodule F (Fin 2 ⊕ Fin 2 → F)} {Λ : Type} [Group Λ] [Finite Λ]
  {f : Λ →* GL (Fin 2 ⊕ Fin 2) F}

theorem LeviData.exists_std (d : LeviData F W f) :
    ∃ g : GL (Fin 2 ⊕ Fin 2) F, g ∈ StatedSp 2 F ∧
      (∀ v, v ∈ W ↔ ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v ∈ stdPlane F) ∧
      (∀ x, conjHom g f x ∈ StatedSp 2 F) ∧
      ∃ h21 : ∀ x, (conjHom g f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0,
        Function.Surjective (slHom (conjHom g f) h21 d.perf) := by
  obtain ⟨g, hg⟩ := SymplecticFlag.exists_statedSp_map_eq isTotallyIsotropic_stdPlane d.iso
    (finrank_stdPlane.trans d.finrank.symm)
  have hmem := mem_iff_of_map_eq hg
  have hS₀ : ∀ x, conjHom (g : GL (Fin 2 ⊕ Fin 2) F) f x ∈ StatedSp 2 F := fun x => by
    rw [conjHom_apply]
    exact (StatedSp 2 F).mul_mem ((StatedSp 2 F).mul_mem ((StatedSp 2 F).inv_mem g.2) (d.mem x))
      g.2
  have hstab₀ : ∀ x, ∀ w ∈ stdPlane F,
      (conjHom (g : GL (Fin 2 ⊕ Fin 2) F) f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈
        stdPlane F := by
    intro x w hw
    have hgw :
        ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈ W := by
      rw [hmem, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
      exact hw
    have h3 := (hmem _).mp (d.stab x _ hgw)
    rw [conjHom_apply, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
    exact h3
  have h21 : ∀ x, (conjHom (g : GL (Fin 2 ⊕ Fin 2) F) f x :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0 :=
    fun x => toBlocks₂₁_eq_zero_of_mulVec_mem (hstab₀ x)
  have hker₀ : IsPGroup 2 (conjHom (g : GL (Fin 2 ⊕ Fin 2) F) f).ker := by
    have : (conjHom (g : GL (Fin 2 ⊕ Fin 2) F) f).ker = f.ker := by
      ext x
      simp only [MonoidHom.mem_ker, conjHom_apply]
      constructor
      · intro h
        have h' : f x = g * 1 * (g : GL (Fin 2 ⊕ Fin 2) F)⁻¹ := by rw [← h]; group
        rw [h']
        group
      · intro h
        rw [h]
        group
    rw [this]
    exact d.ker
  exact ⟨g, g.2, hmem, hS₀, h21, slHom_surjective _ h21 hS₀ d.card d.perf hker₀ d.card60⟩

theorem LeviData.exists_mulVec_sub_mem (d : LeviData F W f) (v v' : Fin 2 ⊕ Fin 2 → F)
    (hv : v ∉ W) (hv' : v' ∉ W) :
    ∃ x, (f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v - v' ∈ W := by
  obtain ⟨g, -, hmem, hS₀, h21, hsurj⟩ := d.exists_std
  set gi : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hgi
  have hu : (gi *ᵥ v) ∘ Sum.inr ≠ 0 := fun h =>
    hv ((hmem v).mpr (mem_stdPlane.mpr fun j => congrFun h j))
  have hu' : (gi *ᵥ v') ∘ Sum.inr ≠ 0 := fun h =>
    hv' ((hmem v').mpr (mem_stdPlane.mpr fun j => congrFun h j))
  obtain ⟨x, hx⟩ := exists_toBlocks₂₂_mulVec (conjHom g f) h21 hS₀ d.perf hsurj _ _ hu hu'
  refine ⟨x, (hmem _).mpr (mem_stdPlane.mpr fun j => ?_)⟩
  have hgg : ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
      (gi *ᵥ v) = v := by
    rw [hgi, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have e : gi *ᵥ ((f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v - v') =
      (conjHom g f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ (gi *ᵥ v) - gi *ᵥ v' := by
    rw [mulVec_sub, conjHom_apply, Units.val_mul, Units.val_mul, ← mulVec_mulVec,
      ← mulVec_mulVec, hgg]
  rw [e, Pi.sub_apply, mulVec_inr, h21 x, zero_mulVec, Pi.zero_apply, zero_add, hx]
  simp

theorem LeviData.false_of_radical (d : LeviData F W f) (X : Subgroup (GL (Fin 2 ⊕ Fin 2) F))
    (hXS : X ≤ StatedSp 2 F)
    (hX1 : ∀ x ∈ X, ∀ w ∈ W, (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w = w)
    (hX2 : ∀ x ∈ X, ∀ v, (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v - v ∈ W)
    (hXN : ∀ y, f y ∈ Subgroup.normalizer (X : Set (GL (Fin 2 ⊕ Fin 2) F))) (hXne : X ≠ ⊥)
    (hXC : ∀ x ∈ X, (∀ y, f y * x = x * f y) → x = 1) : False := by
  obtain ⟨g, hgS, hmem, hS₀, h21, hsurj⟩ := d.exists_std
  set X₀ := X.map (MulAut.conj g⁻¹).toMonoidHom with hX₀
  have hX₀mem : ∀ z ∈ X₀, ∃ x ∈ X, z = g⁻¹ * x * g := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp⟩
  have hgg : ∀ v : Fin 2 ⊕ Fin 2 → F,
      ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
        (((g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v) = v := by
    intro v
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hgg' : ∀ v : Fin 2 ⊕ Fin 2 → F,
      ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
        (((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v) = v := by
    intro v
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hconjv : ∀ x : GL (Fin 2 ⊕ Fin 2) F, ∀ v,
      ((g⁻¹ * x * g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v =
        ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
          ((x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
            (((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v)) := by
    intro x v
    rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
  refine false_of_radical_std (conjHom g f) h21 hS₀ d.card d.perf hsurj X₀ ?_ ?_ ?_ ?_ ?_
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := hX₀mem z hz
    exact (StatedSp 2 F).mul_mem ((StatedSp 2 F).mul_mem ((StatedSp 2 F).inv_mem hgS) (hXS hx))
      hgS
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := hX₀mem z hz
    apply blocks_of_mem_radical
    · intro w hw
      have hgw : ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈
          W := by
        rw [hmem, hgg']
        exact hw
      rw [hconjv, hX1 x hx _ hgw, hgg']
    · intro v
      have h3 := hX2 x hx (((g : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v)
      rw [hmem, mulVec_sub, hgg'] at h3
      rw [hconjv]
      exact h3
  · intro y
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      obtain ⟨x, hx, rfl⟩ := hX₀mem z hz
      refine ⟨f y * x * (f y)⁻¹, (Subgroup.mem_normalizer_iff.mp (hXN y) x).mp hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conjHom_apply]
      group
    · intro hz
      obtain ⟨x, hx, hxe⟩ := hX₀mem _ hz
      have hxe' : z = g⁻¹ * ((f y)⁻¹ * x * f y) * g := by
        rw [conjHom_apply] at hxe
        calc z = (g⁻¹ * f y * g)⁻¹ * (g⁻¹ * x * g) * (g⁻¹ * f y * g) := by rw [← hxe]; group
          _ = g⁻¹ * ((f y)⁻¹ * x * f y) * g := by group
      rw [hxe']
      refine ⟨(f y)⁻¹ * x * f y, ?_, by simp⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hXN y)) x).mp hx
      simpa using this
  · intro hbot
    apply hXne
    rw [eq_bot_iff]
    intro x hx
    have h3 : (MulAut.conj g⁻¹).toMonoidHom x ∈ X₀ := ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h3
    have h4 : g⁻¹ * x * g = 1 := by simpa [MulAut.conj_apply] using h3
    rw [Subgroup.mem_bot]
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h4]; group
  · intro z hz hzc
    obtain ⟨x, hx, rfl⟩ := hX₀mem z hz
    have hxc : ∀ y, f y * x = x * f y := by
      intro y
      have h3 := hzc y
      rw [conjHom_apply] at h3
      have h4 : g * (g⁻¹ * f y * g * (g⁻¹ * x * g)) * g⁻¹ =
          g * (g⁻¹ * x * g * (g⁻¹ * f y * g)) * g⁻¹ := by rw [h3]
      simpa [mul_assoc] using h4
    rw [hXC x hx hxc]
    group

end Lagrangian

section Sylow

variable {F : Type} [Field F]

theorem isTotallyIsotropic_of_mem_orthogonal {W : Submodule F (Fin 2 ⊕ Fin 2 → F)}
    (hW : Module.finrank F W = 2) {a : Fin 2 ⊕ Fin 2 → F} (haW : a ∈ W)
    (ha : a ∈ (pairedSympForm F 2).orthogonal W) (ha0 : a ≠ 0) :
    SymplecticFlag.IsTotallyIsotropic (pairedSympForm F 2) W := by
  set B := pairedSympForm F 2 with hB
  set b := Module.finBasisOfFinrankEq F W hW
  have hskew : ∀ u v, B u v = -B v u := by
    intro u v
    rw [hB, pairedSympForm_apply, pairedSympForm_apply, dotProduct_comm (u ∘ Sum.inl),
      dotProduct_comm (u ∘ Sum.inr)]
    ring
  have hself : ∀ u, B u u = 0 := pairedSympForm_self
  have hb01 : B (b 0) (b 1) = 0 := by
    have hsum := b.sum_repr ⟨a, haW⟩
    rw [Fin.sum_univ_two] at hsum
    have hsum' : (b.repr ⟨a, haW⟩ 0) • ((b 0 : W) : Fin 2 ⊕ Fin 2 → F) +
        (b.repr ⟨a, haW⟩ 1) • ((b 1 : W) : Fin 2 ⊕ Fin 2 → F) = a := by
      have := congrArg Subtype.val hsum
      simpa using this
    have h0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp ha) _ (b 0).2
    have h1 := (LinearMap.BilinForm.mem_orthogonal_iff.mp ha) _ (b 1).2
    rw [← hsum'] at h0 h1
    simp only [map_add, map_smul, smul_eq_mul, hself, mul_zero, zero_add, add_zero] at h0 h1
    rw [hskew ((b 1 : W) : Fin 2 ⊕ Fin 2 → F)] at h1
    by_contra hne
    have hc1 : b.repr ⟨a, haW⟩ 1 = 0 := (mul_eq_zero.mp h0).resolve_right hne
    have hc0 : b.repr ⟨a, haW⟩ 0 = 0 := (mul_eq_zero.mp h1).resolve_right (neg_ne_zero.mpr hne)
    apply ha0
    rw [← hsum', hc0, hc1, zero_smul, zero_smul, add_zero]
  have hzero : B.restrict W = 0 := by
    refine LinearMap.BilinForm.ext_basis b fun i j => ?_
    simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      LinearMap.zero_apply]
    fin_cases i <;> fin_cases j
    · exact hself _
    · exact hb01
    · simp only [Fin.mk_one, Fin.zero_eta]
      rw [hskew, hb01, neg_zero]
    · exact hself _
  intro x hx y hy
  have := congrArg (fun B' : LinearMap.BilinForm F W => B' ⟨x, hx⟩ ⟨y, hy⟩) hzero
  simpa using this

theorem inv_upper : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F)⁻¹ = !![1, -1; 0, 1] :=
  Matrix.inv_eq_left_inv (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])

@[expose] noncomputable def regUnip (F : Type) [Field F] : StatedSp 2 F :=
  SymplecticFlag.blockElt (A := !![1, 1; 0, 1]) (by simp [det_fin_two_of])
    (C := !![0, 0; 0, 1]) (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp)

theorem coe_regUnip :
    (((regUnip F : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      fromBlocks !![1, 1; 0, 1] !![0, 1; 0, 1] 0 !![1, 0; -1, 1] := by
  rw [regUnip, SymplecticFlag.coe_blockElt, SymplecticFlag.blockMat, inv_upper]
  congr 1
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem eq_smul_of_regUnip_mulVec_eq {v : Fin 2 ⊕ Fin 2 → F}
    (hv : (((regUnip F : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v = v) :
    v = v (Sum.inl 0) • Pi.single (Sum.inl 0) 1 := by
  rw [coe_regUnip] at hv
  have h1 := congrFun hv (Sum.inl 0)
  have h2 := congrFun hv (Sum.inl 1)
  have h4 := congrFun hv (Sum.inr 1)
  simp [mulVec, dotProduct, Fin.sum_univ_two] at h1 h2 h4
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [h2, h4]
  linear_combination h1 - h2

theorem regUnip_pow_four (h2 : (2 : F) = 0) : regUnip F ^ 4 = 1 := by
  set M := (((regUnip F : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hM
  have hM2 : M * M = fromBlocks 1 !![1, 1; 1, 0] 0 1 := by
    rw [hM, coe_regUnip, fromBlocks_multiply]
    congr 1
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
      linear_combination h2
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
      · linear_combination (-1 : F) * h2
      · linear_combination h2
      · linear_combination (-1 : F) * h2
      · linear_combination h2
    · simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
      linear_combination (-1 : F) * h2
  apply Subtype.ext
  apply Units.ext
  rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one,
    ← hM, show M ^ 4 = (M * M) * (M * M) by noncomm_ring, hM2, fromBlocks_multiply,
    ← fromBlocks_one]
  congr 1
  · simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination h2
    · linear_combination h2
    · linear_combination h2
  · simp
  · simp

theorem isTotallyIsotropic_of_isPGroup [Fintype F] (hF : Fintype.card F = 4)
    (P : Subgroup (StatedSp 2 F)) (hP : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.index)
    {W : Submodule F (Fin 2 ⊕ Fin 2 → F)} (hW : Module.finrank F W = 2)
    (hPW : ∀ p ∈ P, ∀ w ∈ W, ((p : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈ W) :
    SymplecticFlag.IsTotallyIsotropic (pairedSympForm F 2) W := by
  classical
  have h2 : (2 : F) = 0 := two_eq_zero_of_card_eq_four hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by rw [hF]; norm_num)
  have hU : IsPGroup 2 (Subgroup.zpowers (regUnip F)) := by
    rintro ⟨_, k, rfl⟩
    refine ⟨2, Subtype.ext ?_⟩
    change (regUnip F ^ k) ^ (2 ^ 2) = 1
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      show ((2 ^ 2 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, regUnip_pow_four h2,
      _root_.one_zpow]
  obtain ⟨Q, hQ⟩ := hU.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedSp 2 F) Q (hP.toSylow hPi)
  have hgu : g * regUnip F * g⁻¹ ∈ P := by
    have h1 : regUnip F ∈ (Q : Subgroup (StatedSp 2 F)) := hQ (Subgroup.mem_zpowers _)
    have h3 := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ h1
    rw [← Sylow.coe_subgroup_smul, hg] at h3
    simpa [MulAut.smul_def, MulAut.conj_apply] using h3
  have hfix : ∀ U : Submodule F (Fin 2 ⊕ Fin 2 → F), U ≠ ⊥ →
      (∀ p ∈ P, ∀ u ∈ U, ((p : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ u ∈ U) →
      ∃ u ∈ U, u ≠ 0 ∧ ∀ p ∈ P, ((p : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ u = u := by
    intro U hU hPU
    let ρ : P →* Module.End F U :=
      { toFun := fun p => (mulVecLin (((p : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)).restrict (fun u hu => hPU p p.2 u hu)
        map_one' := by
          apply LinearMap.ext
          intro u
          apply Subtype.ext
          simp
        map_mul' := by
          intro p q
          apply LinearMap.ext
          intro u
          apply Subtype.ext
          change ((((p * q : P) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ (u : Fin 2 ⊕ Fin 2 → F) =
            (((p : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
              ((((q : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
                Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ (u : Fin 2 ⊕ Fin 2 → F))
          rw [mulVec_mulVec]
          rfl }
    have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hU
    obtain ⟨u, hu0, hu⟩ := CFSG.LieType.BorelTits.exists_fixed_ne_zero ρ 2 ⊤ (hP.to_subgroup ⊤)
    refine ⟨u, u.2, fun h => hu0 (Subtype.ext h), fun p hp => ?_⟩
    have := hu ⟨p, hp⟩ (Subgroup.mem_top _)
    exact congrArg Subtype.val this
  set B := pairedSympForm F 2 with hB
  set Wp := B.orthogonal W with hWp
  have hgg : ∀ (h : StatedSp 2 F) (v : Fin 2 ⊕ Fin 2 → F),
      ((h : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
        ((((h⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v) = v := by
    intro h v
    rw [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      Units.val_one, one_mulVec]
  have hgg' : ∀ (h : StatedSp 2 F) (v : Fin 2 ⊕ Fin 2 → F),
      (((h⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
        (((h : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v) = v := by
    intro h v
    rw [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
      Units.val_one, one_mulVec]
  have hPWp : ∀ p ∈ P, ∀ u ∈ Wp, ((p : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ u ∈ Wp := by
    intro p hp u hu
    rw [hWp, LinearMap.BilinForm.mem_orthogonal_iff] at hu ⊢
    intro w hw
    have hw' := hPW p⁻¹ (P.inv_mem hp) w hw
    have h3 := SymplecticHigher.pairedSympForm_mulVec p
      ((((p⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w) u
    rw [hgg] at h3
    rw [hB, h3]
    exact hu _ hw'
  have hWp0 : Wp ≠ ⊥ := by
    intro h
    have h3 := LinearMap.BilinForm.finrank_add_finrank_orthogonal
      SymplecticFlag.pairedSympForm_isAlt.isRefl W
    rw [LinearMap.BilinForm.orthogonal_top_eq_bot SymplecticFlag.pairedSympForm_nondegenerate,
      inf_bot_eq, finrank_bot, add_zero, hW, ← hB, ← hWp, h, finrank_bot] at h3
    simp at h3
  have hW0 : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hW
    exact absurd hW (by norm_num)
  obtain ⟨a, haW, ha0, hafix⟩ := hfix W hW0 hPW
  obtain ⟨b, hbW, hb0, hbfix⟩ := hfix Wp hWp0 hPWp
  have hconj : ∀ v, (((g * regUnip F * g⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v = v →
      v = ((((g⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v) (Sum.inl 0) •
          (((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
            Pi.single (Sum.inl 0) 1) := by
    intro v hv
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← mulVec_mulVec,
      ← mulVec_mulVec] at hv
    have h3 : (((regUnip F : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
        ((((g⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v) =
        (((g⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v := by
      have h4 := congrArg (fun w => (((g⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w) hv
      rwa [hgg'] at h4
    have h5 := eq_smul_of_regUnip_mulVec_eq h3
    calc v = ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
          ((((g⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v) := (hgg g v).symm
      _ = _ := by
        conv_lhs => rw [h5]
        rw [mulVec_smul]
  have ha := hconj a (hafix _ hgu)
  have hb := hconj b (hbfix _ hgu)
  set α := ((((g⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ a) (Sum.inl 0)
  set β := ((((g⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ b) (Sum.inl 0)
  have hβ : β ≠ 0 := fun h => hb0 (by rw [hb, h, zero_smul])
  have haWp : a ∈ Wp := by
    have e : a = (α * β⁻¹) • b := by
      rw [hb, smul_smul, mul_assoc, inv_mul_cancel₀ hβ, mul_one]
      exact ha
    rw [e]
    exact Wp.smul_mem _ hbW
  exact isTotallyIsotropic_of_mem_orthogonal hW haW haWp ha0

end Sylow

end CFSG.Quasithin.H13.Ch4.Sp4

module

public import CFSG.Quasithin.Recognition.RuTypeDefs

public section

namespace CFSG.Quasithin.RuType.Sigma


open scoped MatrixGroups

theorem frobVec_add (k : Multiplicative (ZMod 2)) (v w : Fin 2 → F4) :
    frobVec k (v + w) = frobVec k v + frobVec k w := by
  unfold frobVec
  split_ifs <;> funext i <;> simp [map_add]

theorem frobVec_one (v : Fin 2 → F4) : frobVec 1 v = v := by
  simp [frobVec]

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem slFrobAct_of_eq_zero {k : Multiplicative (ZMod 2)} (hk : Multiplicative.toAdd k = 0) :
    slFrobAct k = 1 := by
  unfold slFrobAct
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, hk, ↓reduceIte]

theorem slFrobAct_of_eq_one {k : Multiplicative (ZMod 2)} (hk : Multiplicative.toAdd k = 1) :
    slFrobAct k = frobSL := by
  unfold slFrobAct
  have : (1 : ZMod 2) ≠ 0 := by decide
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, hk, this, ↓reduceIte]

theorem frobVec_of_eq_zero {k : Multiplicative (ZMod 2)} (hk : Multiplicative.toAdd k = 0)
    (v : Fin 2 → F4) : frobVec k v = v := by
  unfold frobVec
  simp only [hk, ↓reduceIte]

theorem frobVec_of_eq_one {k : Multiplicative (ZMod 2)} (hk : Multiplicative.toAdd k = 1)
    (v : Fin 2 → F4) : frobVec k v = fun i => frobF4 (v i) := by
  unfold frobVec
  have : (1 : ZMod 2) ≠ 0 := by decide
  simp only [hk, this, ↓reduceIte]

theorem frobVec_mul (k l : Multiplicative (ZMod 2)) (v : Fin 2 → F4) :
    frobVec (k * l) v = frobVec k (frobVec l v) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rcases zmod2_cases (Multiplicative.toAdd k) with hk | hk <;>
    rcases zmod2_cases (Multiplicative.toAdd l) with hl | hl
  · rw [frobVec_of_eq_zero (by rw [toAdd_mul, hk, hl]; rfl), frobVec_of_eq_zero hk,
      frobVec_of_eq_zero hl]
  · rw [frobVec_of_eq_one (by rw [toAdd_mul, hk, hl]; rfl), frobVec_of_eq_zero hk,
      frobVec_of_eq_one hl]
  · rw [frobVec_of_eq_one (by rw [toAdd_mul, hk, hl]; rfl), frobVec_of_eq_one hk,
      frobVec_of_eq_zero hl]
  · rw [frobVec_of_eq_zero (by rw [toAdd_mul, hk, hl]; rfl), frobVec_of_eq_one hk,
      frobVec_of_eq_one hl]
    funext i
    rw [frobF4_frobF4]

theorem frobVec_mulVec (k : Multiplicative (ZMod 2)) (A : SL(2, F4)) (v : Fin 2 → F4) :
    frobVec k ((A : Matrix (Fin 2) (Fin 2) F4).mulVec v) =
      ((slFrobAct k A : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec (frobVec k v) := by
  rcases zmod2_cases (Multiplicative.toAdd k) with hk | hk
  · rw [frobVec_of_eq_zero hk, frobVec_of_eq_zero hk, slFrobAct_of_eq_zero hk]
    rfl
  · rw [frobVec_of_eq_one hk, frobVec_of_eq_one hk, slFrobAct_of_eq_one hk]
    funext i
    simp [frobSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two, map_add, map_mul]

theorem sigmaAct_mul (x y : SigmaL2F4) (v : Fin 2 → F4) :
    sigmaAct (x * y) v = sigmaAct x (sigmaAct y v) := by
  unfold sigmaAct
  rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right, frobVec_mul, frobVec_mulVec,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]

theorem sigmaAct_one (v : Fin 2 → F4) : sigmaAct 1 v = v := by
  simp [sigmaAct, frobVec_one]

theorem sigmaAct_add (x : SigmaL2F4) (v w : Fin 2 → F4) :
    sigmaAct x (v + w) = sigmaAct x v + sigmaAct x w := by
  simp [sigmaAct, frobVec_add, Matrix.mulVec_add]

theorem sigmaAct_zero (x : SigmaL2F4) : sigmaAct x 0 = 0 := by
  have := sigmaAct_add x 0 0
  simp only [add_zero] at this
  exact (add_eq_left.mp this.symm)

theorem sigmaAct_inl (A : SL(2, F4)) (v : Fin 2 → F4) :
    sigmaAct (SemidirectProduct.inl A) v = (A : Matrix (Fin 2) (Fin 2) F4).mulVec v := by
  simp [sigmaAct, frobVec_one]

abbrev e0 : Fin 2 → F4 := ![1, 0]

theorem exists_sl_e0 {w : Fin 2 → F4} (hw : w ≠ 0) :
    ∃ A : SL(2, F4), (A : Matrix (Fin 2) (Fin 2) F4).mulVec e0 = w := by
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      intro h1
      apply hw
      funext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨⟨!![0, (w 1)⁻¹; w 1, 0], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two_of]
      have : (w 1)⁻¹ * w 1 = 1 := inv_mul_cancel₀ h1
      have h2 : ∀ x : F4, 0 - x = x := by decide
      simp [h2, this]
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
  · refine ⟨⟨!![w 0, 0; w 1, (w 0)⁻¹], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two_of]
      simp [mul_inv_cancel₀ h0]
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_sl_smul_eq {v w : Fin 2 → F4} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ A : SL(2, F4), (A : Matrix (Fin 2) (Fin 2) F4).mulVec v = w := by
  obtain ⟨A, hA⟩ := exists_sl_e0 hv
  obtain ⟨B, hB⟩ := exists_sl_e0 hw
  refine ⟨B * A⁻¹, ?_⟩
  have hA' : ((A⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec v = e0 := by
    rw [← hA, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hA', hB]

theorem exists_sigmaAct_eq {v w : Fin 2 → F4} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ x : SigmaL2F4, sigmaAct x v = w := by
  obtain ⟨A, hA⟩ := exists_sl_smul_eq hv hw
  exact ⟨SemidirectProduct.inl A, by rw [sigmaAct_inl, hA]⟩

theorem sigmaAct_mk (A : SL(2, F4)) (k : Multiplicative (ZMod 2)) (v : Fin 2 → F4) :
    sigmaAct ⟨A, k⟩ v = (A : Matrix (Fin 2) (Fin 2) F4).mulVec (frobVec k v) := rfl

theorem faithful_mk : ∀ (A : SL(2, F4)) (k : Multiplicative (ZMod 2)),
    (∀ v : Fin 2 → F4, (A : Matrix (Fin 2) (Fin 2) F4).mulVec (frobVec k v) = v) →
      A = 1 ∧ k = 1 := by
  decide +kernel

theorem eq_one_of_sigmaAct_eq {x : SigmaL2F4} (h : ∀ v, sigmaAct x v = v) : x = 1 := by
  obtain ⟨A, k⟩ := x
  obtain ⟨hA, hk⟩ := faithful_mk A k (fun v => by rw [← sigmaAct_mk]; exact h v)
  subst hA hk
  rfl

theorem card_fix_le_four_mk : ∀ (A : SL(2, F4)) (k : Multiplicative (ZMod 2)),
    ¬ (A = 1 ∧ k = 1) →
      (Finset.univ.filter (fun v : Fin 2 → F4 =>
        (A : Matrix (Fin 2) (Fin 2) F4).mulVec (frobVec k v) = v)).card ≤ 4 := by
  decide +kernel

theorem card_fix_le_four {x : SigmaL2F4} (hx : x ≠ 1) :
    (Finset.univ.filter (fun v : Fin 2 → F4 => sigmaAct x v = v)).card ≤ 4 := by
  obtain ⟨A, k⟩ := x
  exact card_fix_le_four_mk A k (by
    rintro ⟨rfl, rfl⟩
    exact hx rfl)

theorem exists_sl_smul_ne : ∀ v : Fin 2 → F4, v ≠ 0 →
    ∃ A : SL(2, F4), (A : Matrix (Fin 2) (Fin 2) F4).mulVec v ≠ v := by
  decide +kernel

@[expose] def detF (v w : Fin 2 → F4) : F4 := v 0 * w 1 + v 1 * w 0

@[expose] def formB (v w : Fin 2 → F4) : F4 := detF v w + detF v w * detF v w

theorem formB_val : ∀ v w : Fin 2 → F4, formB v w = 0 ∨ formB v w = 1 := by
  decide +kernel

theorem formB_sl : ∀ (A : SL(2, F4)) (v w : Fin 2 → F4),
    formB ((A : Matrix (Fin 2) (Fin 2) F4).mulVec v) ((A : Matrix (Fin 2) (Fin 2) F4).mulVec w) =
      formB v w := by
  decide +kernel

theorem formB_frob : ∀ (k : Multiplicative (ZMod 2)) (v w : Fin 2 → F4),
    formB (frobVec k v) (frobVec k w) = formB v w := by
  decide +kernel

theorem formB_sigmaAct (x : SigmaL2F4) (v w : Fin 2 → F4) :
    formB (sigmaAct x v) (sigmaAct x w) = formB v w := by
  obtain ⟨A, k⟩ := x
  rw [sigmaAct_mk, sigmaAct_mk, formB_sl, formB_frob]

theorem formB_add_right : ∀ v w w' : Fin 2 → F4, formB v (w + w') = formB v w + formB v w' := by
  decide +kernel

theorem formB_add_left : ∀ v v' w : Fin 2 → F4, formB (v + v') w = formB v w + formB v' w := by
  decide +kernel

theorem formB_nondeg : ∀ v : Fin 2 → F4, (∀ w, formB v w = 0) → v = 0 := by
  decide +kernel

theorem formB_comm : ∀ v w : Fin 2 → F4, formB v w = formB w v := by
  decide +kernel

theorem formB_values_basis : ∀ a b c d : F4, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) →
    (c = 0 ∨ c = 1) → (d = 0 ∨ d = 1) →
    ∃ w : Fin 2 → F4, formB w ![1, 0] = a ∧ formB w ![F4.ω, 0] = b ∧ formB w ![0, 1] = c ∧
      formB w ![0, F4.ω] = d := by
  decide +kernel

theorem vec_decomp (x : Fin 2 → F4) : x = ![x 0, 0] + ![0, x 1] := by
  funext i
  fin_cases i <;> simp

theorem F4_cases : ∀ x : F4, x = 0 ∨ x = 1 ∨ x = F4.ω ∨ x = 1 + F4.ω := by
  decide +kernel

theorem exists_formB_eq (f : (Fin 2 → F4) → F4) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hval : ∀ x, f x = 0 ∨ f x = 1) : ∃ w, ∀ x, formB w x = f x := by
  obtain ⟨w, ha, hb, hc, hd⟩ := formB_values_basis (f ![1, 0]) (f ![F4.ω, 0]) (f ![0, 1])
    (f ![0, F4.ω]) (hval _) (hval _) (hval _) (hval _)
  refine ⟨w, fun x => ?_⟩
  have h0 : f 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact (add_eq_left.mp this.symm)
  have hf1 : ∀ a : F4, f ![a, 0] = formB w ![a, 0] := by
    intro a
    rcases F4_cases a with rfl | rfl | rfl | rfl
    · have e : (![0, 0] : Fin 2 → F4) = 0 := by funext i; fin_cases i <;> rfl
      rw [e, h0]
      have := formB_add_right w 0 0
      rw [add_zero] at this
      exact (add_eq_left.mp this.symm).symm
    · exact ha.symm
    · exact hb.symm
    · have e : (![1 + F4.ω, 0] : Fin 2 → F4) = ![1, 0] + ![F4.ω, 0] := by
        funext i; fin_cases i <;> simp
      rw [e, hadd, formB_add_right, ha, hb]
  have hf2 : ∀ a : F4, f ![0, a] = formB w ![0, a] := by
    intro a
    rcases F4_cases a with rfl | rfl | rfl | rfl
    · have e : (![0, 0] : Fin 2 → F4) = 0 := by funext i; fin_cases i <;> rfl
      rw [e, h0]
      have := formB_add_right w 0 0
      rw [add_zero] at this
      exact (add_eq_left.mp this.symm).symm
    · exact hc.symm
    · exact hd.symm
    · have e : (![0, 1 + F4.ω] : Fin 2 → F4) = ![0, 1] + ![0, F4.ω] := by
        funext i; fin_cases i <;> simp
      rw [e, hadd, formB_add_right, hc, hd]
  rw [vec_decomp x, hadd, formB_add_right, hf1, hf2]

theorem formB_inj {w w' : Fin 2 → F4} (h : ∀ x, formB w x = formB w' x) : w = w' := by
  have key : ∀ x, formB (w + w') x = 0 := fun x => by
    rw [formB_add_left, h]
    have : ∀ a : F4, a + a = 0 := by decide
    exact this _
  have := formB_nondeg _ key
  have e : ∀ v : Fin 2 → F4, v + v = 0 := fun v => by
    funext i
    have : ∀ a : F4, a + a = 0 := by decide
    exact this _
  exact (eq_neg_of_add_eq_zero_left this).trans (neg_eq_of_add_eq_zero_left (e w'))

theorem exists_mul_pow_five : ∀ A : SL(2, F4), ∃ C : SL(2, F4), C ^ 5 = 1 ∧ (C⁻¹ * A) ^ 5 = 1 := by
  decide +kernel

theorem card_formB_perp : ∀ x : Fin 2 → F4, x ≠ 0 →
    (Finset.univ.filter (fun w : Fin 2 → F4 => formB w x = 0)).card = 8 := by
  decide +kernel

theorem eq_one_of_fix_perp {g : SigmaL2F4} {x : Fin 2 → F4} (hx : x ≠ 0)
    (h : ∀ w, formB w x = 0 → sigmaAct g w = w) : g = 1 := by
  by_contra hg
  have h1 := card_fix_le_four hg
  have h2 : (Finset.univ.filter (fun w : Fin 2 → F4 => formB w x = 0)) ⊆
      Finset.univ.filter (fun v : Fin 2 → F4 => sigmaAct g v = v) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact h w hw
  have := Finset.card_le_card h2
  rw [card_formB_perp x hx] at this
  omega

instance : DecidableEq SigmaL2F4 := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact SemidirectProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

instance : Fintype SigmaL2F4 := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

@[expose] def SP0 : Subgroup SigmaL2F4 where
  carrier := {x | (x.left : Matrix (Fin 2) (Fin 2) F4) 1 0 = 0 ∧
    (x.left : Matrix (Fin 2) (Fin 2) F4) 0 0 = 1}
  mul_mem' := by
    rintro ⟨A, k⟩ ⟨B, l⟩ ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
    simp only [Set.mem_ofPred_eq] at hA1 hA2 hB1 hB2 ⊢
    rw [SemidirectProduct.mul_left]
    rcases zmod2_cases (Multiplicative.toAdd k) with hk | hk
    · rw [slFrobAct_of_eq_zero hk]
      simp [Matrix.mul_apply, Fin.sum_univ_two, hA1, hA2, hB1, hB2]
    · rw [slFrobAct_of_eq_one hk]
      simp [frobSL, Matrix.mul_apply, Fin.sum_univ_two, hA1, hA2, hB1, hB2, frobF4_apply]
  one_mem' := by simp
  inv_mem' := by
    have key : ∀ x : SigmaL2F4, ((x.left : Matrix (Fin 2) (Fin 2) F4) 1 0 = 0 ∧
        (x.left : Matrix (Fin 2) (Fin 2) F4) 0 0 = 1) →
        ((x⁻¹.left : Matrix (Fin 2) (Fin 2) F4) 1 0 = 0 ∧
        (x⁻¹.left : Matrix (Fin 2) (Fin 2) F4) 0 0 = 1) := by
      decide +kernel
    intro x hx
    exact key x hx

instance : DecidablePred (· ∈ SP0) := fun x =>
  inferInstanceAs (Decidable ((x.left : Matrix (Fin 2) (Fin 2) F4) 1 0 = 0 ∧
    (x.left : Matrix (Fin 2) (Fin 2) F4) 0 0 = 1))

theorem card_Sigma : Fintype.card SigmaL2F4 = 120 := by
  decide +kernel

theorem card_SP0 : Nat.card SP0 = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_Sigma' : Nat.card SigmaL2F4 = 120 := by
  rw [Nat.card_eq_fintype_card, card_Sigma]

@[expose] noncomputable def sylowSP0 : Sylow 2 SigmaL2F4 :=
  Sylow.ofCard SP0 (by
    rw [card_SP0, card_Sigma']
    have : (120 : ℕ).factorization 2 = 3 := by
      rw [show (120 : ℕ) = 2 ^ 3 * 15 by norm_num, Nat.factorization_mul (by norm_num)
        (by norm_num), Nat.Prime.factorization_pow Nat.prime_two]
      simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 15 by norm_num)]
    rw [this]
    norm_num)

theorem exists_conj_eq_SP0 {P : Subgroup SigmaL2F4} (hP : Nat.card P = 8) :
    ∃ g : SigmaL2F4, P = SP0.map (MulAut.conj g).toMonoidHom := by
  have hfact : (Nat.card SigmaL2F4).factorization 2 = 3 := by
    rw [card_Sigma', show (120 : ℕ) = 2 ^ 3 * 15 by norm_num, Nat.factorization_mul (by norm_num)
      (by norm_num), Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 15 by norm_num)]
  let SP : Sylow 2 SigmaL2F4 := Sylow.ofCard P (by rw [hP, hfact]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SigmaL2F4 sylowSP0 SP
  refine ⟨g, ?_⟩
  have := congrArg (fun Q : Sylow 2 SigmaL2F4 => (Q : Subgroup SigmaL2F4)) hg
  simp only [Sylow.coe_subgroup_smul, SP, Sylow.coe_ofCard] at this
  rw [← this]
  rfl

theorem SP0_moves : ∀ x y : Fin 2 → F4, x 1 ≠ 0 → y 1 = 0 →
    ∃ g ∈ SP0, sigmaAct g x + x = y := by
  decide +kernel

theorem SP0_fix_line : ∀ g ∈ SP0, ∀ x : Fin 2 → F4, x 1 = 0 → (sigmaAct g x) 1 = 0 := by
  decide +kernel

@[expose] def U0 : Subgroup SigmaL2F4 where
  carrier := {x | x ∈ SP0 ∧ x.right = 1}
  mul_mem' := fun {a b} ha hb => ⟨SP0.mul_mem ha.1 hb.1, by
    rw [SemidirectProduct.mul_right, ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨SP0.one_mem, rfl⟩
  inv_mem' := fun {a} ha => ⟨SP0.inv_mem ha.1, by rw [SemidirectProduct.inv_right, ha.2]; rfl⟩

instance : DecidablePred (· ∈ U0) := fun x => inferInstanceAs (Decidable (x ∈ SP0 ∧ x.right = 1))

theorem card_U0 : Nat.card U0 = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem mem_U0_of_trivial : ∀ g : SigmaL2F4, (∀ x : Fin 2 → F4, x 1 = 0 → sigmaAct g x = x) →
    (∀ x : Fin 2 → F4, (sigmaAct g x + x) 1 = 0) → g ∈ U0 := by
  decide +kernel

theorem U0_moves : ∀ x y : Fin 2 → F4, x 1 ≠ 0 → y 1 = 0 →
    ∃ g ∈ U0, sigmaAct g x + x = y := by
  decide +kernel

end CFSG.Quasithin.RuType.Sigma

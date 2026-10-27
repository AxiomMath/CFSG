module

public import CFSG.Monster.B.TwoA.Unitary.CliquePlane
import all CFSG.Fischer.F4
public import CFSG.Monster.B.Classical.UnitarySixBeta

public section

namespace CFSG.Monster.B.TwoA.Unitary.Clique

open CFSG.Fischer CFSG.LinearGroups CFSG.LieType.Universal.Unitary Matrix
  CFSG.Monster.B.Classical.UnitarySix

@[expose] def hypEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6 where
  toFun := Sum.elim (fun i => ⟨i, by omega⟩) (fun j => ⟨5 - j, by omega⟩)
  invFun k := if h : (k : ℕ) < 3 then Sum.inl ⟨k, h⟩ else Sum.inr ⟨5 - k, by omega⟩
  left_inv := by decide
  right_inv := by decide

@[expose] def ofHyp (a b : Fin 3 → F4) : V := Sum.elim a b ∘ hypEquiv.symm

@[expose] def hypA (v : V) : Fin 3 → F4 := fun i => v (hypEquiv (Sum.inl i))

@[expose] def hypB (v : V) : Fin 3 → F4 := fun j => v (hypEquiv (Sum.inr j))

theorem ofHyp_apply_hypEquiv (a b : Fin 3 → F4) (x : Fin 3 ⊕ Fin 3) :
    ofHyp a b (hypEquiv x) = Sum.elim a b x := by
  rw [ofHyp, Function.comp_apply, Equiv.symm_apply_apply]

theorem hypA_ofHyp (a b : Fin 3 → F4) : hypA (ofHyp a b) = a :=
  funext fun i => ofHyp_apply_hypEquiv a b (Sum.inl i)

theorem hypB_ofHyp (a b : Fin 3 → F4) : hypB (ofHyp a b) = b :=
  funext fun j => ofHyp_apply_hypEquiv a b (Sum.inr j)

theorem ofHyp_hyp (v : V) : ofHyp (hypA v) (hypB v) = v := by
  funext k
  obtain ⟨x, rfl⟩ := hypEquiv.surjective k
  rw [ofHyp_apply_hypEquiv]
  cases x <;> rfl

theorem ofHyp_inj {a b a' b' : Fin 3 → F4} : ofHyp a b = ofHyp a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    exact ⟨by rw [← hypA_ofHyp a b, h, hypA_ofHyp], by rw [← hypB_ofHyp a b, h, hypB_ofHyp]⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem ofHyp_add (a b a' b' : Fin 3 → F4) :
    ofHyp a b + ofHyp a' b' = ofHyp (a + a') (b + b') := by
  funext k
  obtain ⟨x, rfl⟩ := hypEquiv.surjective k
  rw [Pi.add_apply, ofHyp_apply_hypEquiv, ofHyp_apply_hypEquiv, ofHyp_apply_hypEquiv]
  cases x <;> rfl

theorem ofHyp_smul (c : F4) (a b : Fin 3 → F4) : c • ofHyp a b = ofHyp (c • a) (c • b) := by
  funext k
  obtain ⟨x, rfl⟩ := hypEquiv.surjective k
  rw [Pi.smul_apply, ofHyp_apply_hypEquiv, ofHyp_apply_hypEquiv]
  cases x <;> rfl

theorem ofHyp_zero : ofHyp 0 0 = 0 := by
  funext k
  obtain ⟨x, rfl⟩ := hypEquiv.surjective k
  rw [ofHyp_apply_hypEquiv]
  cases x <;> rfl

theorem ofHyp_eq_zero_iff {a b : Fin 3 → F4} : ofHyp a b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [← ofHyp_zero, ofHyp_inj]

theorem ofHyp_0 (a b : Fin 3 → F4) : ofHyp a b 0 = a 0 := rfl
theorem ofHyp_1 (a b : Fin 3 → F4) : ofHyp a b 1 = a 1 := rfl
theorem ofHyp_2 (a b : Fin 3 → F4) : ofHyp a b 2 = a 2 := rfl
theorem ofHyp_3 (a b : Fin 3 → F4) : ofHyp a b 3 = b 2 := rfl
theorem ofHyp_4 (a b : Fin 3 → F4) : ofHyp a b 4 = b 1 := rfl
theorem ofHyp_5 (a b : Fin 3 → F4) : ofHyp a b 5 = b 0 := rfl

theorem herm_ofHyp (a b a' b' : Fin 3 → F4) :
    herm (ofHyp a b) (ofHyp a' b') = (∑ i, a i * bar (b' i)) + ∑ j, b j * bar (a' j) := by
  rw [herm_expand, ofHyp_0, ofHyp_1, ofHyp_2, ofHyp_3, ofHyp_4, ofHyp_5, ofHyp_0, ofHyp_1,
    ofHyp_2, ofHyp_3, ofHyp_4, ofHyp_5, Fin.sum_univ_three, Fin.sum_univ_three]
  ring

abbrev lift3 (w : Fin 3 → F4) : V := ofHyp w 0

theorem mem_W0_iff_hypB {v : V} : v ∈ W0 ↔ hypB v = 0 := by
  rw [mem_W0_iff]
  constructor
  · rintro ⟨h3, h4, h5⟩
    funext j
    fin_cases j
    · exact h5
    · exact h4
    · exact h3
  · intro h
    exact ⟨congrFun h 2, congrFun h 1, congrFun h 0⟩

theorem lift3_mem_W0 (w : Fin 3 → F4) : lift3 w ∈ W0 := by
  rw [mem_W0_iff_hypB, hypB_ofHyp]

theorem eq_lift3_of_mem_W0 {v : V} (hv : v ∈ W0) : v = lift3 (hypA v) := by
  conv_lhs => rw [← ofHyp_hyp v, mem_W0_iff_hypB.1 hv]

theorem lift3_injective : Function.Injective lift3 := fun _ _ h => (ofHyp_inj.1 h).1

theorem lift3_eq_zero_iff {w : Fin 3 → F4} : lift3 w = 0 ↔ w = 0 := by
  rw [ofHyp_eq_zero_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

theorem lift3_smul (c : F4) (w : Fin 3 → F4) : c • lift3 w = lift3 (c • w) := by
  rw [ofHyp_smul, smul_zero]

theorem herm_lift3 (w w' : Fin 3 → F4) : herm (lift3 w) (lift3 w') = 0 :=
  isTotIso_W0 _ (lift3_mem_W0 w) _ (lift3_mem_W0 w')

@[expose] def hyp (M : Matrix (Fin 6) (Fin 6) F4) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F4 :=
  M.submatrix hypEquiv hypEquiv

@[expose] def ofHypMat (N : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F4) :
    Matrix (Fin 6) (Fin 6) F4 :=
  N.submatrix hypEquiv.symm hypEquiv.symm

theorem hyp_ofHypMat (N : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F4) : hyp (ofHypMat N) = N := by
  ext x y
  simp [hyp, ofHypMat]

theorem ofHypMat_hyp (M : Matrix (Fin 6) (Fin 6) F4) : ofHypMat (hyp M) = M := by
  ext i k
  simp [hyp, ofHypMat]

theorem hyp_injective : Function.Injective hyp := fun M N h => by
  rw [← ofHypMat_hyp M, h, ofHypMat_hyp]

theorem hyp_mul (M N : Matrix (Fin 6) (Fin 6) F4) : hyp (M * N) = hyp M * hyp N :=
  (submatrix_mul_equiv M N hypEquiv hypEquiv hypEquiv).symm

theorem hyp_one : hyp 1 = 1 := submatrix_one_equiv hypEquiv

theorem hyp_smul (c : F4) (M : Matrix (Fin 6) (Fin 6) F4) : hyp (c • M) = c • hyp M := rfl

theorem hyp_map_bar_transpose (M : Matrix (Fin 6) (Fin 6) F4) :
    hyp ((M.map bar)ᵀ) = ((hyp M).map bar)ᵀ := rfl

theorem det_hyp (M : Matrix (Fin 6) (Fin 6) F4) : (hyp M).det = M.det :=
  det_submatrix_equiv_self hypEquiv M

theorem hyp_antidiag : hyp (antidiag 6) = fromBlocks 0 1 1 0 := by
  decide

theorem mulVec_ofHyp (M : Matrix (Fin 6) (Fin 6) F4) (a b : Fin 3 → F4) :
    M *ᵥ ofHyp a b = ofHyp ((hyp M *ᵥ Sum.elim a b) ∘ Sum.inl)
      ((hyp M *ᵥ Sum.elim a b) ∘ Sum.inr) := by
  have h : hyp M *ᵥ Sum.elim a b = (M *ᵥ ofHyp a b) ∘ hypEquiv :=
    submatrix_mulVec_equiv M (Sum.elim a b) hypEquiv hypEquiv
  rw [h]
  exact (ofHyp_hyp _).symm

theorem mulVec_ofHyp_blocks {M : Matrix (Fin 6) (Fin 6) F4} {A B C D : Matrix (Fin 3) (Fin 3) F4}
    (h : hyp M = fromBlocks A B C D) (a b : Fin 3 → F4) :
    M *ᵥ ofHyp a b = ofHyp (A *ᵥ a + B *ᵥ b) (C *ᵥ a + D *ᵥ b) := by
  rw [mulVec_ofHyp, h, fromBlocks_mulVec]
  rfl

theorem mulVec_u_hypEquiv (M : Matrix (Fin 6) (Fin 6) F4) (d : Fin 3 ⊕ Fin 3) :
    M *ᵥ u (hypEquiv d) = ∑ c, hyp M c d • u (hypEquiv c) := by
  change _ = ∑ c, M (hypEquiv c) (hypEquiv d) • u (hypEquiv c)
  rw [Equiv.sum_comp hypEquiv (fun k => M k (hypEquiv d) • u k)]
  funext i
  rw [mulVec_single_one, Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [Pi.single_eq_of_ne' hk]
  · simp

theorem isIsometry_iff_hyp (M : Matrix (Fin 6) (Fin 6) F4) :
    IsIsometry M ↔
      ((hyp M).map bar)ᵀ * fromBlocks 0 1 1 0 * hyp M = fromBlocks 0 1 1 0 := by
  rw [isIsometry_iff_map_bar, ← hyp_antidiag, ← hyp_map_bar_transpose, ← hyp_mul, ← hyp_mul]
  exact hyp_injective.eq_iff.symm

theorem fromBlocks_isometry_iff (A B D : Matrix (Fin 3) (Fin 3) F4) :
    ((fromBlocks A B 0 D).map bar)ᵀ * fromBlocks 0 1 1 0 * fromBlocks A B 0 D =
        fromBlocks 0 1 1 0 ↔
      (A.map bar)ᵀ * D = 1 ∧ (D.map bar)ᵀ * A = 1 ∧
        (D.map bar)ᵀ * B + (B.map bar)ᵀ * D = 0 := by
  rw [fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj]
  have h0 : (0 : Matrix (Fin 3) (Fin 3) F4).map bar = 0 := Matrix.map_zero _ bar_zero
  simp [h0]

theorem map_bar_one : (1 : Matrix (Fin 3) (Fin 3) F4).map bar = 1 :=
  Matrix.map_one _ bar_zero bar_one

theorem det_map_bar (A : Matrix (Fin 3) (Fin 3) F4) : (A.map bar).det = bar A.det := by
  have := RingHom.map_det barHom A
  rw [coe_barHom] at this
  exact this.symm

theorem map_bar_smul (c : F4) (A : Matrix (Fin 3) (Fin 3) F4) :
    (c • A).map bar = bar c • A.map bar := by
  ext i j
  simp [bar_mul]

theorem mapsTo_W0_iff (M : Matrix (Fin 6) (Fin 6) F4) :
    (∀ v ∈ W0, M *ᵥ v ∈ W0) ↔ (hyp M).toBlocks₂₁ = 0 := by
  have hM := (fromBlocks_toBlocks (hyp M)).symm
  constructor
  · intro h
    refine Matrix.ext_of_mulVec_single fun i => ?_
    have h1 := h _ (lift3_mem_W0 (Pi.single i 1))
    rw [mulVec_ofHyp_blocks hM, mem_W0_iff_hypB, hypB_ofHyp] at h1
    simp only [mulVec_zero, add_zero] at h1
    rw [h1, zero_mulVec]
  · intro h v hv
    rw [eq_lift3_of_mem_W0 hv, mulVec_ofHyp_blocks hM, h]
    simp only [zero_mulVec, mulVec_zero, add_zero]
    exact lift3_mem_W0 _

theorem mulVec_lift3_of_mapsTo {M : Matrix (Fin 6) (Fin 6) F4} (h : (hyp M).toBlocks₂₁ = 0)
    (w : Fin 3 → F4) : M *ᵥ lift3 w = lift3 ((hyp M).toBlocks₁₁ *ᵥ w) := by
  rw [mulVec_ofHyp_blocks (fromBlocks_toBlocks (hyp M)).symm, h, zero_mulVec, mulVec_zero,
    mulVec_zero, add_zero, zero_add]

theorem hyp_eq_fromBlocks {M : Matrix (Fin 6) (Fin 6) F4} (h : (hyp M).toBlocks₂₁ = 0) :
    hyp M = fromBlocks (hyp M).toBlocks₁₁ (hyp M).toBlocks₁₂ 0 (hyp M).toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks (hyp M), h]

theorem det_blockA_eq_one {M : Matrix (Fin 6) (Fin 6) F4} (hM : IsIsometry M) (hdet : M.det = 1)
    (h : (hyp M).toBlocks₂₁ = 0) : (hyp M).toBlocks₁₁.det = 1 := by
  set A := (hyp M).toBlocks₁₁
  set D := (hyp M).toBlocks₂₂
  have hb := hyp_eq_fromBlocks h
  rw [isIsometry_iff_hyp, hb, fromBlocks_isometry_iff] at hM
  have h1 := congrArg Matrix.det hM.1
  rw [det_mul, det_transpose, det_map_bar, det_one] at h1
  have h2 : A.det * D.det = 1 := by
    rw [← det_fromBlocks_zero₂₁ A (hyp M).toBlocks₁₂ D, ← hb, det_hyp, hdet]
  have hD : D.det ≠ 0 := fun h0 => by rw [h0, mul_zero] at h2; exact zero_ne_one h2
  have hA : A.det ≠ 0 := fun h0 => by rw [h0, zero_mul] at h2; exact zero_ne_one h2
  refine eq_one_of_bar_eq (mul_right_cancel₀ hD (h1.trans h2.symm)) hA

theorem eq_smul_one_of_forall {A : Matrix (Fin 3) (Fin 3) F4}
    (h : ∀ w : Fin 3 → F4, w ≠ 0 → ∃ c : F4, A *ᵥ w = c • w) : A = A 0 0 • 1 := by
  have hoff : ∀ i k : Fin 3, i ≠ k → A i k = 0 := by
    intro i k hik
    obtain ⟨c, hc⟩ := h (Pi.single k 1) (by simp)
    have := congrFun hc i
    rwa [mulVec_single_one, Pi.smul_apply, Pi.single_eq_of_ne hik, smul_zero] at this
  obtain ⟨c, hc⟩ := h 1 (by decide)
  have hdiag : ∀ i : Fin 3, A i i = c := by
    intro i
    have := congrFun hc i
    simp only [mulVec, dotProduct, Pi.one_apply, mul_one, Pi.smul_apply, smul_eq_mul] at this
    rwa [Finset.sum_eq_single i (fun b _ hb => hoff i b (Ne.symm hb)) (by simp)] at this
  ext i k
  rw [Matrix.smul_apply, smul_eq_mul, hdiag 0]
  by_cases hik : i = k
  · rw [hik, hdiag k, Matrix.one_apply_eq, mul_one]
  · rw [hoff i k hik, Matrix.one_apply_ne hik, mul_zero]

@[expose] def IsHerm (C : Matrix (Fin 3) (Fin 3) F4) : Prop := (C.map bar)ᵀ = C

instance (C : Matrix (Fin 3) (Fin 3) F4) : Decidable (IsHerm C) :=
  inferInstanceAs (Decidable ((C.map bar)ᵀ = C))

theorem isHerm_iff {C : Matrix (Fin 3) (Fin 3) F4} : IsHerm C ↔ ∀ i j, bar (C j i) = C i j := by
  rw [IsHerm, ← Matrix.ext_iff]
  rfl

theorem IsHerm.add {C C' : Matrix (Fin 3) (Fin 3) F4} (h : IsHerm C) (h' : IsHerm C') :
    IsHerm (C + C') := by
  rw [isHerm_iff] at *
  intro i j
  rw [Matrix.add_apply, Matrix.add_apply, bar_add, h, h']

theorem isHerm_zero : IsHerm 0 := by
  rw [isHerm_iff]
  intro i j
  exact bar_zero

theorem add_self_matrix (X : Matrix (Fin 3) (Fin 3) F4) : X + X = 0 := by
  ext i j
  exact add_self_eq_zero' _

@[expose] def unipMat (C : Matrix (Fin 3) (Fin 3) F4) : Matrix (Fin 6) (Fin 6) F4 :=
  ofHypMat (fromBlocks 1 C 0 1)

theorem hyp_unipMat (C : Matrix (Fin 3) (Fin 3) F4) : hyp (unipMat C) = fromBlocks 1 C 0 1 :=
  hyp_ofHypMat _

theorem det_unipMat (C : Matrix (Fin 3) (Fin 3) F4) : (unipMat C).det = 1 := by
  rw [← det_hyp, hyp_unipMat, det_fromBlocks_zero₂₁, det_one, one_mul]

theorem isIsometry_unipMat {C : Matrix (Fin 3) (Fin 3) F4} (hC : IsHerm C) :
    IsIsometry (unipMat C) := by
  rw [isIsometry_iff_hyp, hyp_unipMat, fromBlocks_isometry_iff, map_bar_one, transpose_one,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
  refine ⟨rfl, rfl, ?_⟩
  rw [show (C.map bar)ᵀ = C from hC]
  exact add_self_matrix C

theorem unipMat_mul (C C' : Matrix (Fin 3) (Fin 3) F4) :
    unipMat C * unipMat C' = unipMat (C + C') := by
  apply hyp_injective
  rw [hyp_mul, hyp_unipMat, hyp_unipMat, hyp_unipMat, fromBlocks_multiply]
  simp [add_comm]

theorem unipMat_zero : unipMat 0 = 1 := by
  apply hyp_injective
  rw [hyp_unipMat, hyp_one, fromBlocks_one]

theorem unipMat_mulVec_ofHyp (C : Matrix (Fin 3) (Fin 3) F4) (a b : Fin 3 → F4) :
    unipMat C *ᵥ ofHyp a b = ofHyp (a + C *ᵥ b) b := by
  rw [mulVec_ofHyp_blocks (hyp_unipMat C), one_mulVec, one_mulVec, zero_mulVec, zero_add]

theorem unipMat_mulVec_lift3 (C : Matrix (Fin 3) (Fin 3) F4) (w : Fin 3 → F4) :
    unipMat C *ᵥ lift3 w = lift3 w := by
  rw [unipMat_mulVec_ofHyp, mulVec_zero, add_zero]

@[expose] noncomputable def unipSU (C : Matrix (Fin 3) (Fin 3) F4) (hC : IsHerm C) :
    SU frobeniusF4 6 :=
  mkSU (unipMat C) (det_unipMat C) (isIsometry_unipMat hC)

@[simp] theorem coe_unipSU (C : Matrix (Fin 3) (Fin 3) F4) (hC : IsHerm C) :
    (((unipSU C hC : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      unipMat C :=
  rfl

theorem unipSU_mul {C C' : Matrix (Fin 3) (Fin 3) F4} (hC : IsHerm C) (hC' : IsHerm C') :
    unipSU C hC * unipSU C' hC' = unipSU (C + C') (hC.add hC') :=
  SU_ext (by rw [coe_SU_mul, coe_unipSU, coe_unipSU, coe_unipSU, unipMat_mul])

theorem unipSU_zero : unipSU 0 isHerm_zero = 1 :=
  SU_ext (by rw [coe_unipSU, unipMat_zero, coe_SU_one])

@[expose] def rk (w : Fin 3 → F4) : Matrix (Fin 3) (Fin 3) F4 := vecMulVec w fun j => bar (w j)

theorem isHerm_rk (w : Fin 3 → F4) : IsHerm (rk w) := by
  rw [isHerm_iff]
  intro i j
  simp only [rk, vecMulVec_apply, bar_mul, bar_bar]
  exact mul_comm _ _

theorem rk_mulVec (w b : Fin 3 → F4) : rk w *ᵥ b = (∑ j, b j * bar (w j)) • w := by
  rw [rk, vecMulVec_mulVec, op_smul_eq_smul]
  congr 1
  simp only [dotProduct]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem transvecMat_lift3 (w : Fin 3 → F4) : transvecMat (lift3 w) = unipMat (rk w) := by
  refine Matrix.ext_of_mulVec_single fun k => ?_
  rw [← ofHyp_hyp (Pi.single k 1), transvecMat_mulVec, unipMat_mulVec_ofHyp, rk_mulVec,
    herm_ofHyp, ofHyp_smul, ofHyp_add]
  simp only [Pi.zero_apply, bar_zero, mul_zero, Finset.sum_const_zero, zero_add, smul_zero,
    add_zero]

theorem bar_eq_inv_F4 : ∀ a : F4, a ≠ 0 → bar a = a⁻¹ := by decide

theorem eq_of_add_eq_zero_matrix {X Y : Matrix (Fin 3) (Fin 3) F4} (h : X + Y = 0) : Y = X := by
  ext i j
  have := congrFun (congrFun h i) j
  rw [Matrix.add_apply, Matrix.zero_apply] at this
  revert this
  generalize X i j = a
  generalize Y i j = b
  revert a b
  decide

theorem exists_eq_smul_unipMat {M : Matrix (Fin 6) (Fin 6) F4} (hM : IsIsometry M)
    (hfix : ∀ w : Fin 3 → F4, w ≠ 0 → ∃ c : F4, M *ᵥ lift3 w = c • lift3 w) :
    ∃ (c : F4) (C : Matrix (Fin 3) (Fin 3) F4), c ≠ 0 ∧ IsHerm C ∧ M = c • unipMat C := by
  have hst : (hyp M).toBlocks₂₁ = 0 := by
    rw [← mapsTo_W0_iff]
    intro v hv
    by_cases hv0 : hypA v = 0
    · rw [eq_lift3_of_mem_W0 hv, hv0, show lift3 0 = 0 from ofHyp_zero, mulVec_zero]
      exact Submodule.zero_mem _
    · obtain ⟨c, hc⟩ := hfix _ hv0
      rw [eq_lift3_of_mem_W0 hv, hc]
      exact Submodule.smul_mem _ _ (lift3_mem_W0 _)
  set A := (hyp M).toBlocks₁₁ with hAdef
  set B := (hyp M).toBlocks₁₂ with hBdef
  set D := (hyp M).toBlocks₂₂ with hDdef
  have hb : hyp M = fromBlocks A B 0 D := hyp_eq_fromBlocks hst
  have hA : A = A 0 0 • 1 := by
    refine eq_smul_one_of_forall fun w hw => ?_
    obtain ⟨c, hc⟩ := hfix w hw
    refine ⟨c, lift3_injective ?_⟩
    rw [← mulVec_lift3_of_mapsTo hst, hc, lift3_smul]
  set l := A 0 0
  rw [isIsometry_iff_hyp, hb, fromBlocks_isometry_iff] at hM
  obtain ⟨h1, -, h3⟩ := hM
  have hl0 : l ≠ 0 := by
    intro h0
    rw [hA, h0, zero_smul, Matrix.map_zero _ bar_zero, transpose_zero, Matrix.zero_mul] at h1
    exact zero_ne_one h1
  have hbl : bar l = l⁻¹ := bar_eq_inv_F4 l hl0
  have hAs : (A.map bar)ᵀ = bar l • 1 := by
    rw [hA, map_bar_smul, map_bar_one, transpose_smul, transpose_one]
  have hD : D = l • 1 := by
    rw [hAs, Matrix.smul_mul, Matrix.one_mul] at h1
    calc D = (l * bar l) • D := by rw [mul_bar_of_ne_zero hl0, one_smul]
      _ = l • 1 := by rw [mul_smul, h1]
  have hDs : (D.map bar)ᵀ = bar l • 1 := by
    rw [hD, map_bar_smul, map_bar_one, transpose_smul, transpose_one]
  rw [hDs, hD, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at h3
  refine ⟨l, bar l • B, hl0, ?_, ?_⟩
  · have e := eq_of_add_eq_zero_matrix h3
    rw [IsHerm, map_bar_smul, bar_bar, transpose_smul, e]
  · apply hyp_injective
    rw [hb, hyp_smul, hyp_unipMat, fromBlocks_smul, hA, hD, smul_smul, mul_bar_of_ne_zero hl0,
      one_smul, smul_zero]

end CFSG.Monster.B.TwoA.Unitary.Clique

module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

namespace BK10.L2

open Matrix CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem eq_one_of_sq_eq_one [CharP K 2] {c : K} (h : c ^ 2 = 1) : c = 1 := by
  have h1 : (c + 1) ^ 2 = 0 := by
    rw [CharTwo.add_sq, h, one_pow, CharTwo.add_self_eq_zero]
  have h2 : c + 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
  rw [eq_neg_of_add_eq_zero_left h2, CharTwo.neg_eq]

theorem center_sl_eq_bot [CharP K 2] : Subgroup.center (SL(2, K)) = ⊥ := by
  refine eq_bot_iff.mpr fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  rw [eq_one_of_sq_eq_one hr, map_one] at hrA
  rw [Subgroup.mem_bot]
  exact Subtype.ext hrA.symm

theorem psl2QuotientMap_injective [CharP K 2] : Function.Injective (psl2QuotientMap K) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  change (QuotientGroup.mk' (Subgroup.center (SL(2, K)))).ker = ⊥
  rw [QuotientGroup.ker_mk', center_sl_eq_bot]

@[expose] noncomputable def conjSL (G : GL (Fin 2) K) (A : SL(2, K)) : SL(2, K) :=
  ⟨(G : Matrix (Fin 2) (Fin 2) K) * A * ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), by
    rw [Matrix.det_mul, Matrix.det_mul, A.2, mul_one, ← Matrix.det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.det_one]⟩

theorem coe_conjSL (G : GL (Fin 2) K) (A : SL(2, K)) :
    ((conjSL G A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      (G : Matrix (Fin 2) (Fin 2) K) * A * ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem conjSL_mul (G : GL (Fin 2) K) (A : SL(2, K)) :
    ((conjSL G A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * (G : Matrix (Fin 2) (Fin 2) K) =
      (G : Matrix (Fin 2) (Fin 2) K) * A := by
  rw [coe_conjSL, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.mul_one]

theorem pglAction_mk (G : GL (Fin 2) K) (A : SL(2, K)) :
    pglAction K (ProjGenLinGroup.mk G) (psl2QuotientMap K A) =
      psl2QuotientMap K (conjSL G A) := by
  apply ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_pglAction]
  change ProjGenLinGroup.mk G * ProjGenLinGroup.mk (SpecialLinearGroup.toGL A) *
      (ProjGenLinGroup.mk G)⁻¹ = ProjGenLinGroup.mk (SpecialLinearGroup.toGL (conjSL G A))
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  ext i j
  simp [coe_conjSL]

theorem psl2FieldAut_mk (σ : K ≃+* K) (A : SL(2, K)) :
    psl2FieldAut K σ (psl2QuotientMap K A) =
      psl2QuotientMap K (SpecialLinearGroup.map σ.toRingHom A) := by
  rw [psl2FieldAut_apply]
  exact psl2RingEquiv_mk σ A

theorem mem_unip_iff [CharP K 2] (A : SL(2, K)) :
    psl2QuotientMap K A ∈ psl2UpperUnipotentSubgroup K ↔
      (A : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 ∧ (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
        (A : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
  rw [mem_psl2UpperUnipotentSubgroup_iff]
  constructor
  · rintro ⟨x, hx⟩
    have h := psl2QuotientMap_injective hx
    subst h
    simp [sl2UpperUnipotent]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨(A : Matrix (Fin 2) (Fin 2) K) 0 1, congrArg _ (Subtype.ext ?_)⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2UpperUnipotent, h00, h10, h11]

theorem lower_eq_zero_of_conj_mem [CharP K 2] (G : GL (Fin 2) K)
    (h : pglAction K (ProjGenLinGroup.mk G) (psl2QuotientMap K (sl2UpperUnipotent 1)) ∈
      psl2UpperUnipotentSubgroup K) :
    (G : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  rw [pglAction_mk, mem_unip_iff] at h
  obtain ⟨-, h10, h11⟩ := h
  have h1 := congrFun (congrFun (conjSL_mul G (sl2UpperUnipotent 1)) 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, h10, h11] at h1
  simp [sl2UpperUnipotent] at h1
  exact h1

@[expose] noncomputable def diagSL (u : Kˣ) : SL(2, K) :=
  ⟨!![(u : K), 0; 0, ((u⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two_of]⟩

theorem coe_diagSL (u : Kˣ) :
    ((diagSL u : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      !![(u : K), 0; 0, ((u⁻¹ : Kˣ) : K)] := rfl

@[expose] noncomputable def diagHom : Kˣ →* SL(2, K) where
  toFun := diagSL
  map_one' := by
    ext i j
    rw [coe_diagSL]
    fin_cases i <;> fin_cases j <;> simp
  map_mul' u v := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_diagSL, coe_diagSL, coe_diagSL]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem diagHom_apply (u : Kˣ) (i j : Fin 2) :
    ((diagHom u : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) i j =
      !![(u : K), 0; 0, ((u⁻¹ : Kˣ) : K)] i j := rfl

theorem conjSL_diagHom (G : GL (Fin 2) K) (hG : (G : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (u : Kˣ) :
    ((conjSL G (diagHom u) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 = u ∧
      ((conjSL G (diagHom u) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
      ((conjSL G (diagHom u) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1 =
        ((u⁻¹ : Kˣ) : K) := by
  have hdet : (G : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).mp
    (Units.isUnit G) |>.ne_zero
  rw [Matrix.det_fin_two, hG, mul_zero, sub_zero] at hdet
  have h00 : (G : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have h11 : (G : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  have hW := conjSL_mul G (diagHom u)
  have e00 := congrFun (congrFun hW 0) 0
  have e10 := congrFun (congrFun hW 1) 0
  have e11 := congrFun (congrFun hW 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, diagHom_apply, hG, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, mul_zero, zero_mul, add_zero, zero_add] at e00 e10 e11
  have hw10 : ((conjSL G (diagHom u) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    rcases mul_eq_zero.mp e10 with h | h
    · exact h
    · exact absurd h h00
  refine ⟨?_, hw10, ?_⟩
  · apply mul_right_cancel₀ h00
    rw [e00, mul_comm]
  · rw [hw10, zero_mul, zero_add] at e11
    apply mul_right_cancel₀ h11
    rw [e11, mul_comm]

theorem unitriangular_mul_inv (Y W : SL(2, K)) (hY : (Y : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (hW : (W : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h00 : (Y : Matrix (Fin 2) (Fin 2) K) 0 0 = (W : Matrix (Fin 2) (Fin 2) K) 0 0)
    (h11 : (Y : Matrix (Fin 2) (Fin 2) K) 1 1 = (W : Matrix (Fin 2) (Fin 2) K) 1 1) :
    ((Y * W⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 ∧
      ((Y * W⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
      ((Y * W⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
  have hdet := W.2
  rw [Matrix.det_fin_two, hW, mul_zero, sub_zero] at hdet
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    hY, hW, h00, h11]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination hdet
  · ring
  · linear_combination hdet

theorem eq_or_eq_inv_of_add_inv {μ l : K} (hμ : μ ≠ 0) (hl : l ≠ 0)
    (h : μ + μ⁻¹ = l + l⁻¹) : μ = l ∨ μ = l⁻¹ := by
  have e1 : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ
  have e2 : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
  have h1 : (μ - l) * (μ - l⁻¹) = 0 := by linear_combination μ * h - e1 + e2
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact Or.inl (sub_eq_zero.mp h2)
  · exact Or.inr (sub_eq_zero.mp h2)

variable [Finite K]

@[expose] noncomputable def galPart : MulAut (PSL2 K) →* (K ≃+* K) :=
  SemidirectProduct.rightHom.comp (semilinearEquivAut K).symm.toMonoidHom

theorem exists_rep (β : MulAut (PSL2 K)) :
    ∃ G : GL (Fin 2) K, β = pglAction K (ProjGenLinGroup.mk G) * psl2FieldAut K (galPart β) := by
  set γ := (semilinearEquivAut K).symm β with hγ
  obtain ⟨G, hG⟩ := ProjGenLinGroup.mk_surjective γ.left
  refine ⟨G, ?_⟩
  have h1 : β = semilinearAction K γ := by
    change β = semilinearEquivAut K γ
    rw [hγ, MulEquiv.apply_symm_apply]
  have h2 : γ = SemidirectProduct.inl γ.left * SemidirectProduct.inr γ.right :=
    (SemidirectProduct.inl_left_mul_inr_right γ).symm
  have hgal : galPart β = γ.right := rfl
  rw [hgal, h1, h2, map_mul, semilinearAction_inl, semilinearAction_inr, hG]
  simp

theorem isSylowTwoOf_unip [CharP K 2] :
    QuasithinUnique.IsSylowTwoOf (psl2UpperUnipotentSubgroup K) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  obtain ⟨Q, hQ⟩ := psl2UpperUnipotent_isSylow K (p := 2) (f := n)
    (by rw [Nat.card_eq_fintype_card, hn])
  rw [← hQ]
  refine ⟨le_top, Q.isPGroup', ?_⟩
  change ¬ 2 ∣ (Q : Subgroup (PSL2 K)).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact Q.not_dvd_index

theorem pglAction_mem_inner [CharP K 2] (g : PGL2 K) : pglAction K g ∈ inner (PSL2 K) := by
  have hsurj : Function.Surjective
      (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)) := by
    apply ProjectiveSpecialLinearGroup.toPGL_surj_of_roots
    intro r
    obtain ⟨k, hk⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (r : K)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact r.ne_zero (by rw [hk, mul_zero])
    refine ⟨Units.mk0 k hk0, Units.ext ?_⟩
    rw [Fintype.card_fin, Units.val_pow_eq_pow_val, Units.val_mk0, sq, ← hk]
  obtain ⟨x, rfl⟩ := hsurj g
  rw [pglAction_toPGL]
  exact ⟨x, rfl⟩

end BK10.L2

end CFSG.Quasithin.Vol2.Ch11.SecD

module

public import CFSG.RankThree.PartOne.AUTSL.L4Push
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis

public section

namespace CFSG.RankThree.PartOne.AUTSL.L4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

local macro "l4simp" : tactic =>
  `(tactic| simp only [coe_mul_apply, Fin.sum_univ_four, coe_corner, cornerM_00, cornerM_01,
    cornerM_02, cornerM_03, cornerM_10, cornerM_11, cornerM_12, cornerM_13, cornerM_20, cornerM_21,
    cornerM_22, cornerM_23, cornerM_30, cornerM_31, cornerM_32, cornerM_33, Fin.zero_eta,
    Fin.mk_one, Fin.reduceFinMk, Fin.isValue])

@[expose] def tE (a d : K) : SpecialLinearGroup (Fin 4) K :=
  ⟨!![1, a, 0, 0; 0, 1, 0, 0; 0, 0, 1, d; 0, 0, 0, 1], by
    have h : (!![1, a, 0, 0; 0, 1, 0, 0; 0, 0, 1, d; 0, 0, 0, 1] :
        Matrix (Fin 4) (Fin 4) K).BlockTriangular id := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
    rw [Matrix.det_of_isUpperTriangular h]
    simp [Fin.prod_univ_four]⟩

theorem tE_mem (a d : K) : tE a d ∈ Uge K := by
  rw [mem_Uge_iff]
  simp [tE]

@[simp] theorem tE_01 (a d : K) :
    ((tE a d : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 1 = a := rfl

@[simp] theorem tE_23 (a d : K) :
    ((tE a d : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 3 = d := rfl

theorem center_Uge {u : SpecialLinearGroup (Fin 4) K} (hu : u ∈ Uge K)
    (hc : ∀ v ∈ Uge K, v * u = u * v) : ∃ c : K, u = corner !![0, c; 0, 0] := by
  obtain ⟨Y, rfl⟩ := mem_Vge.1 (centralizer_Uge_Vge hu fun v hv => hc v (Vge_le_Uge hv))
  have h1 := (mul_corner_eq_iff (tE_mem (1 : K) 0) Y).1 (hc _ (tE_mem 1 0))
  have h2 := (mul_corner_eq_iff (tE_mem (0 : K) 1) Y).1 (hc _ (tE_mem 0 1))
  simp only [tE_01, tE_23, one_mul, zero_mul] at h1 h2
  refine ⟨Y 0 1, congrArg corner ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h1.1, h1.2.2, h2.2.2.symm]

@[expose] def IsDiag4 (d : SpecialLinearGroup (Fin 4) K) : Prop :=
  ((d : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag

theorem IsDiag4.ne_zero {d : SpecialLinearGroup (Fin 4) K} (hd : IsDiag4 d) (i : Fin 4) :
    (d : Matrix (Fin 4) (Fin 4) K) i i ≠ 0 := by
  have h := congrArg Matrix.det hd.diagonal_diag
  rw [det_diagonal, Matrix.SpecialLinearGroup.det_coe] at h
  intro h0
  have : ∏ j, Matrix.diag (d : Matrix (Fin 4) (Fin 4) K) j = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) h0
  rw [this] at h
  exact zero_ne_one h

theorem IsDiag4.mul_corner {d : SpecialLinearGroup (Fin 4) K} (hd : IsDiag4 d)
    (X : Matrix (Fin 2) (Fin 2) K) : ∃ Y, d * corner X = corner Y * d := by
  have h01 : (d : Matrix (Fin 4) (Fin 4) K) 0 1 = 0 := hd (by decide)
  have h02 : (d : Matrix (Fin 4) (Fin 4) K) 0 2 = 0 := hd (by decide)
  have h03 : (d : Matrix (Fin 4) (Fin 4) K) 0 3 = 0 := hd (by decide)
  have h10 : (d : Matrix (Fin 4) (Fin 4) K) 1 0 = 0 := hd (by decide)
  have h12 : (d : Matrix (Fin 4) (Fin 4) K) 1 2 = 0 := hd (by decide)
  have h13 : (d : Matrix (Fin 4) (Fin 4) K) 1 3 = 0 := hd (by decide)
  have h20 : (d : Matrix (Fin 4) (Fin 4) K) 2 0 = 0 := hd (by decide)
  have h21 : (d : Matrix (Fin 4) (Fin 4) K) 2 1 = 0 := hd (by decide)
  have h23 : (d : Matrix (Fin 4) (Fin 4) K) 2 3 = 0 := hd (by decide)
  have h30 : (d : Matrix (Fin 4) (Fin 4) K) 3 0 = 0 := hd (by decide)
  have h31 : (d : Matrix (Fin 4) (Fin 4) K) 3 1 = 0 := hd (by decide)
  have h32 : (d : Matrix (Fin 4) (Fin 4) K) 3 2 = 0 := hd (by decide)
  have n2 := hd.ne_zero 2
  have n3 := hd.ne_zero 3
  refine ⟨!![(d : Matrix (Fin 4) (Fin 4) K) 0 0 * X 0 0 / (d : Matrix (Fin 4) (Fin 4) K) 2 2,
    (d : Matrix (Fin 4) (Fin 4) K) 0 0 * X 0 1 / (d : Matrix (Fin 4) (Fin 4) K) 3 3;
    (d : Matrix (Fin 4) (Fin 4) K) 1 1 * X 1 0 / (d : Matrix (Fin 4) (Fin 4) K) 2 2,
    (d : Matrix (Fin 4) (Fin 4) K) 1 1 * X 1 1 / (d : Matrix (Fin 4) (Fin 4) K) 3 3], ?_⟩
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> l4simp <;>
    simp [h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32] <;> field_simp

theorem IsDiag4.mem_normalizer [Finite K] {d : SpecialLinearGroup (Fin 4) K} (hd : IsDiag4 d) :
    d ∈ Subgroup.normalizer (Vge K : Set (SpecialLinearGroup (Fin 4) K)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨X, rfl⟩ := mem_Vge.1 hv
    obtain ⟨Y, hY⟩ := hd.mul_corner X
    have : (MulAut.conj d).toMonoidHom (corner X) = corner Y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hY]
      group
    change (MulAut.conj d).toMonoidHom (corner X) ∈ Vge K
    rw [this]
    exact corner_mem_Vge Y
  · rw [Subgroup.card_map_of_injective (MulAut.conj d).injective]

theorem IsDiag4.mul_root {d : SpecialLinearGroup (Fin 4) K} (hd : IsDiag4 d)
    (h : (d : Matrix (Fin 4) (Fin 4) K) 0 0 = (d : Matrix (Fin 4) (Fin 4) K) 3 3) (c : K) :
    d * corner !![0, c; 0, 0] = corner !![0, c; 0, 0] * d := by
  have h01 : (d : Matrix (Fin 4) (Fin 4) K) 0 1 = 0 := hd (by decide)
  have h02 : (d : Matrix (Fin 4) (Fin 4) K) 0 2 = 0 := hd (by decide)
  have h03 : (d : Matrix (Fin 4) (Fin 4) K) 0 3 = 0 := hd (by decide)
  have h10 : (d : Matrix (Fin 4) (Fin 4) K) 1 0 = 0 := hd (by decide)
  have h12 : (d : Matrix (Fin 4) (Fin 4) K) 1 2 = 0 := hd (by decide)
  have h13 : (d : Matrix (Fin 4) (Fin 4) K) 1 3 = 0 := hd (by decide)
  have h20 : (d : Matrix (Fin 4) (Fin 4) K) 2 0 = 0 := hd (by decide)
  have h21 : (d : Matrix (Fin 4) (Fin 4) K) 2 1 = 0 := hd (by decide)
  have h23 : (d : Matrix (Fin 4) (Fin 4) K) 2 3 = 0 := hd (by decide)
  have h30 : (d : Matrix (Fin 4) (Fin 4) K) 3 0 = 0 := hd (by decide)
  have h31 : (d : Matrix (Fin 4) (Fin 4) K) 3 1 = 0 := hd (by decide)
  have h32 : (d : Matrix (Fin 4) (Fin 4) K) 3 2 = 0 := hd (by decide)
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> l4simp <;>
    simp [h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32, h]
  ring

theorem exists_pow_four_eq [Finite K] [CharP K 2] (a : K) : ∃ l : K, l ^ 4 = a := by
  have hs : Function.Surjective (frobenius K 2) :=
    Finite.surjective_of_injective (frobenius_inj K 2)
  obtain ⟨m, hm⟩ := hs a
  obtain ⟨l, hl⟩ := hs m
  refine ⟨l, ?_⟩
  simp only [frobenius_def] at hl hm
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hl, hm]

theorem exists_sl_conj [Finite K] [CharP K 2] (A : GL (Fin 4) K) :
    ∃ g : SpecialLinearGroup (Fin 4) K, ∀ M : Matrix (Fin 4) (Fin 4) K,
      (g : Matrix (Fin 4) (Fin 4) K) * M *
          ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (A : Matrix (Fin 4) (Fin 4) K) * M * ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  obtain ⟨l, hl⟩ := exists_pow_four_eq (K := K) (A : Matrix (Fin 4) (Fin 4) K).det
  have hdet : (A : Matrix (Fin 4) (Fin 4) K).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det A).ne_zero
    simpa using this
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hdet (by rw [← hl]; norm_num)
  let g : SpecialLinearGroup (Fin 4) K :=
    ⟨l⁻¹ • (A : Matrix (Fin 4) (Fin 4) K), by
      rw [Matrix.det_smul, Fintype.card_fin, ← hl, inv_pow, inv_mul_cancel₀ (pow_ne_zero 4 hl0)]⟩
  refine ⟨g, fun M => ?_⟩
  have e1 : (g : Matrix (Fin 4) (Fin 4) K) * (l • ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
      = 1 := by
    show (l⁻¹ • (A : Matrix (Fin 4) (Fin 4) K)) *
      (l • ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) = 1
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hl0, one_smul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e2 : ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      (g : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have e3 : ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      l • ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    calc ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
        = ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            ((g : Matrix (Fin 4) (Fin 4) K) *
              (l • ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))) := by rw [e1, mul_one]
      _ = (((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            (g : Matrix (Fin 4) (Fin 4) K)) *
              (l • ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by rw [mul_assoc]
      _ = _ := by rw [e2, one_mul]
  rw [e3]
  show (l⁻¹ • (A : Matrix (Fin 4) (Fin 4) K)) * M *
    (l • ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) = _
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hl0, one_smul]

theorem IsDiag4.mul_apply_diag {d d' : SpecialLinearGroup (Fin 4) K} (hd' : IsDiag4 d')
    (i : Fin 4) :
    ((d * d' : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i i =
      (d : Matrix (Fin 4) (Fin 4) K) i i * (d' : Matrix (Fin 4) (Fin 4) K) i i := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hki
    rw [hd' hki, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

section Torus

variable [Finite K] [CharP K 2]

theorem torus_data {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (E₀ : Subgroup (SpecialLinearGroup (Fin 4) K))
    (hcomm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x) (hpow : ∀ x ∈ E₀, x ^ p = 1) :
    ∃ g : SpecialLinearGroup (Fin 4) K, (∀ x ∈ E₀, IsDiag4 (g * x * g⁻¹)) ∧
      ∃ B : Subgroup (SpecialLinearGroup (Fin 4) K), B ≤ E₀ ∧ Nat.card E₀ ≤ p * Nat.card B ∧
        ∀ x ∈ B, ((g * x * g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0 =
          ((g * x * g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 3 := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨A, hA⟩ := exists_conj_diagonal_of_commuting_pow_eq_one hζ E₀ hcomm hpow
  obtain ⟨g, hg⟩ := exists_sl_conj A
  have hdiag : ∀ x ∈ E₀, IsDiag4 (g * x * g⁻¹) := by
    intro x hx i j hij
    have := hA x hx i j hij
    rw [← hg] at this
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this
  refine ⟨g, hdiag, ?_⟩
  have hne3 : ∀ x ∈ E₀, ((g * x * g⁻¹ : SpecialLinearGroup (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) 3 3 ≠ 0 := fun x hx => (hdiag x hx).ne_zero 3
  let ψ : E₀ →* K :=
    { toFun := fun x =>
        ((g * x * g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0 *
          (((g * x * g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 3)⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        have e : g * ((x * y : E₀) : SpecialLinearGroup (Fin 4) K) * g⁻¹ =
            (g * x * g⁻¹) * (g * y * g⁻¹) := by
          simp only [Subgroup.coe_mul]
          group
        simp only [e, (hdiag y y.2).mul_apply_diag, mul_inv]
        ring }
  let ψ' : E₀ →* Kˣ := ψ.toHomUnits
  have hψ'p : ∀ x : E₀, ψ' x ^ p = 1 := fun x => by
    rw [← map_pow, show x ^ p = 1 from Subtype.ext (hpow x x.2), map_one]
  have hrange : Nat.card ψ'.range ≤ p := by
    have : Fintype Kˣ := Fintype.ofFinite _
    calc Nat.card ψ'.range ≤ Nat.card {u : Kˣ // u ^ p = 1} := by
          refine Nat.card_le_card_of_injective
            (fun u : ψ'.range => ⟨u.1, ?_⟩) ?_
          · obtain ⟨x, hx⟩ := u.2
            rw [← hx]
            exact hψ'p x
          · intro u v h
            apply Subtype.ext
            have := congrArg Subtype.val h
            exact this
      _ ≤ p := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
          exact IsCyclic.card_pow_eq_one_le hp.pos
  refine ⟨ψ'.ker.map E₀.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective E₀.subtype_injective, ← Subgroup.card_mul_index ψ'.ker,
      Subgroup.index_ker, mul_comm]
    exact Nat.mul_le_mul_right _ hrange
  · rintro x ⟨y, hy, rfl⟩
    have h1 : ψ y = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) (MonoidHom.mem_ker.1 hy)
      simpa [ψ'] using this
    have h2 : ((g * y * g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0 *
        (((g * y * g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 3)⁻¹ = 1 := h1
    exact (mul_inv_eq_one₀ (hne3 y y.2)).1 h2

end Torus

end CFSG.RankThree.PartOne.AUTSL.L4

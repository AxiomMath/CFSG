module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData

public section

namespace CFSG.SignalizerFunctorTheorem.NonLocal

open scoped Matrix
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable (r : ℕ) (k : Type) [Field k]

@[expose] def spSiegel : Subgroup (StatedSp r k) where
  carrier := {g | ∃ C : Matrix (Fin r) (Fin r) k, C.IsSymm ∧
    ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      Matrix.fromBlocks 1 C 0 1}
  one_mem' := ⟨0, Matrix.isSymm_zero, by simp⟩
  mul_mem' := by
    rintro x y ⟨C, hC, hx⟩ ⟨D, hD, hy⟩
    refine ⟨C + D, hC.add hD, ?_⟩
    simp [hx, hy, Matrix.fromBlocks_multiply, add_comm]
  inv_mem' := by
    rintro x ⟨C, hC, hx⟩
    refine ⟨-C, hC.neg, ?_⟩
    have h : ((x : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) *
        Matrix.fromBlocks 1 (-C) 0 1 = 1 := by
      simp [hx, Matrix.fromBlocks_multiply]
    exact Units.inv_eq_of_mul_eq_one_right h

theorem mem_spSiegel {g : StatedSp r k} :
    g ∈ spSiegel r k ↔ ∃ C : Matrix (Fin r) (Fin r) k, C.IsSymm ∧
      ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
        Matrix.fromBlocks 1 C 0 1 :=
  Iff.rfl

theorem exists_spSiegel (C : Matrix (Fin r) (Fin r) k) (hC : C.IsSymm) :
    ∃ g : StatedSp r k, g ∈ spSiegel r k ∧
      ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
        Matrix.fromBlocks 1 C 0 1 := by
  let u : GL (Fin r ⊕ Fin r) k :=
    ⟨Matrix.fromBlocks 1 C 0 1, Matrix.fromBlocks 1 (-C) 0 1,
      by simp [Matrix.fromBlocks_multiply], by simp [Matrix.fromBlocks_multiply]⟩
  have hu : u ∈ StatedSp r k := by
    rw [mem_statedSp_iff]
    show (Matrix.fromBlocks 1 C 0 1)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
      Matrix.fromBlocks 1 C 0 1 = Matrix.fromBlocks 0 1 (-1) 0
    simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hC.eq]
  exact ⟨⟨u, hu⟩, ⟨C, hC, rfl⟩, rfl⟩

theorem spSiegel_isMulCommutative : IsMulCommutative (spSiegel r k) :=
  ⟨⟨fun x y => by
    obtain ⟨C, -, hx⟩ := x.2
    obtain ⟨D, -, hy⟩ := y.2
    refine Subtype.ext (Subtype.ext (Units.ext ?_))
    simp [hx, hy, Matrix.fromBlocks_multiply, add_comm]⟩⟩

section Aux

variable {r k}

theorem coe_pow_of_coe_eq {g : StatedSp r k} {C : Matrix (Fin r) (Fin r) k}
    (hg : ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      Matrix.fromBlocks 1 C 0 1) (n : ℕ) :
    (((g ^ n : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) = Matrix.fromBlocks 1 (n • C) 0 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Subgroup.coe_mul, Units.val_mul, ih, hg, Matrix.fromBlocks_multiply, succ_nsmul]
    simp [add_comm]

end Aux

theorem pow_eq_one_of_mem_spSiegel {p : ℕ} [CharP k p] {g : StatedSp r k}
    (hg : g ∈ spSiegel r k) : g ^ p = 1 := by
  obtain ⟨C, -, hM⟩ := hg
  refine Subtype.ext (Units.ext ?_)
  rw [coe_pow_of_coe_eq hM p]
  have hp : p • C = 0 := by
    ext i j
    simp [nsmul_eq_mul]
  rw [hp]
  simp

theorem card_spSiegel [Finite k] : Nat.card (spSiegel r k) = Nat.card k ^ (r * (r + 1) / 2) := by
  let f : spSiegel r k → {C : Matrix (Fin r) (Fin r) k // C.IsSymm} := fun g =>
    ⟨(((g : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k).toBlocks₁₂, by
      obtain ⟨C, hC, hM⟩ := g.2
      rw [hM, Matrix.toBlocks_fromBlocks₁₂]
      exact hC⟩
  have hf : Function.Bijective f := by
    constructor
    · intro g g' h
      obtain ⟨C, -, hM⟩ := g.2
      obtain ⟨C', -, hM'⟩ := g'.2
      have hC : C = C' := by
        have := congrArg Subtype.val h
        simpa [f, hM, hM'] using this
      exact Subtype.ext (Subtype.ext (Units.ext (by rw [hM, hM', hC])))
    · rintro ⟨C, hC⟩
      obtain ⟨g, hg, hM⟩ := exists_spSiegel r k C hC
      exact ⟨⟨g, hg⟩, Subtype.ext (by simp [f, hM])⟩
  let e : {C : Matrix (Fin r) (Fin r) k // C.IsSymm} ≃ (Sym2 (Fin r) → k) :=
    (Equiv.subtypeEquivRight (q := fun C : Matrix (Fin r) (Fin r) k => ∀ a b, C a b = C b a)
      (fun C => ⟨fun h a b => Matrix.IsSymm.apply h b a,
        fun h => Matrix.ext fun a b => h b a⟩)).trans Sym2.lift
  rw [Nat.card_eq_of_bijective f hf, Nat.card_congr e, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Sym2 (Fin r)), Sym2.card, Fintype.card_fin,
    Nat.choose_two_right]
  simp [mul_comm]

theorem eq_one_of_mem_spSiegel_of_mem_spScalars {g : StatedSp r k} (hg : g ∈ spSiegel r k)
    (hz : g ∈ spScalars r k) : g = 1 := by
  obtain ⟨C, -, hM⟩ := hg
  rw [spScalars, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hz
  obtain ⟨c, hc⟩ := hz
  have hsc : ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      Matrix.diagonal fun _ => (c : k) := by
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  refine Subtype.ext (Units.ext ?_)
  ext x y
  by_cases hxy : x = y
  · subst hxy
    have hdiag :
        ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) x x = 1 := by
      rw [hM]
      rcases x with i | i <;> simp
    simpa using hdiag
  · simp [hsc, Matrix.diagonal_apply_ne _ hxy, Matrix.one_apply_ne hxy]

section Transvection

variable {n : Type} [Fintype n] [DecidableEq n]

theorem single_mul_self_eq_zero {i j : n} (h : i ≠ j) :
    Matrix.single i j (1 : k) * Matrix.single i j 1 = 0 :=
  Matrix.single_mul_single_of_ne 1 i j i h.symm 1

@[expose] def transvGL (i j : n) (hij : i ≠ j) : GL n k where
  val := 1 + Matrix.single i j 1
  inv := 1 - Matrix.single i j 1
  val_inv := by simp [add_mul, mul_sub, single_mul_self_eq_zero k hij]
  inv_val := by simp [sub_mul, mul_add, single_mul_self_eq_zero k hij]

theorem coe_transvGL (i j : n) (hij : i ≠ j) :
    ((transvGL k i j hij : GL n k) : Matrix n n k) = 1 + Matrix.single i j 1 := rfl

theorem coe_transvGL_inv (i j : n) (hij : i ≠ j) :
    (((transvGL k i j hij)⁻¹ : GL n k) : Matrix n n k) = 1 - Matrix.single i j 1 := rfl

theorem coe_transvGL_pow (i j : n) (hij : i ≠ j) (m : ℕ) :
    (((transvGL k i j hij) ^ m : GL n k) : Matrix n n k) = 1 + m • Matrix.single i j 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Units.val_mul, ih, coe_transvGL, succ_nsmul]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, single_mul_self_eq_zero k hij,
      smul_zero, add_zero]
    abel

theorem transv_mul_single_mul_transpose (i j : n) :
    (1 + Matrix.single i j (1 : k)) * Matrix.single j j 1 * (1 + Matrix.single i j (1 : k))ᵀ =
      Matrix.single j j 1 + Matrix.single i j 1 + Matrix.single j i 1 + Matrix.single i i 1 := by
  simp [add_mul, mul_add]
  abel

end Transvection

@[expose] noncomputable def spLevi (hr : 2 ≤ r) : StatedSp r k :=
  leviSp (transvGL k (⟨0, by omega⟩ : Fin r) ⟨1, hr⟩ (by simp))

theorem coe_spLevi (hr : 2 ≤ r) :
    ((spLevi r k hr : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      Matrix.fromBlocks (1 + Matrix.single (⟨0, by omega⟩ : Fin r) ⟨1, hr⟩ 1) 0 0
        (1 - Matrix.single (⟨1, hr⟩ : Fin r) ⟨0, by omega⟩ 1) := by
  rw [spLevi, coe_leviSp, coe_transvGL, coe_transvGL_inv]
  simp [Matrix.transpose_sub, Matrix.transpose_single]

theorem spLevi_pow {p : ℕ} [CharP k p] (hr : 2 ≤ r) : (spLevi r k hr) ^ p = 1 := by
  rw [spLevi, ← map_pow]
  have : (transvGL k (⟨0, by omega⟩ : Fin r) ⟨1, hr⟩ (by simp)) ^ p = 1 := by
    refine Units.ext ?_
    rw [coe_transvGL_pow]
    have hp : p • Matrix.single (⟨0, by omega⟩ : Fin r) (⟨1, hr⟩ : Fin r) (1 : k) = 0 := by
      ext i j
      simp [nsmul_eq_mul]
    rw [hp]
    simp
  rw [this, map_one]

section Conj

variable {r k}

theorem coe_leviSp_conj (A : GL (Fin r) k) {e : StatedSp r k} {C : Matrix (Fin r) (Fin r) k}
    (he : ((e : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      Matrix.fromBlocks 1 C 0 1) :
    (((leviSp A * e * (leviSp A)⁻¹ : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      Matrix.fromBlocks 1
        ((A : Matrix (Fin r) (Fin r) k) * C * (A : Matrix (Fin r) (Fin r) k)ᵀ) 0 1 := by
  have h1 : (A : Matrix (Fin r) (Fin r) k) *
      ((A⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = 1 := A.mul_inv
  have h2 : ((A⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k)ᵀ *
      (A : Matrix (Fin r) (Fin r) k)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  rw [← map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, he,
    coe_leviSp, coe_leviSp, inv_inv]
  generalize ((A⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = B at h1 h2 ⊢
  simp [Matrix.fromBlocks_multiply, h1, h2]

theorem leviSp_conj_mem (A : GL (Fin r) k) {e : StatedSp r k} (he : e ∈ spSiegel r k) :
    leviSp A * e * (leviSp A)⁻¹ ∈ spSiegel r k := by
  obtain ⟨C, hC, hM⟩ := he
  refine ⟨_, ?_, coe_leviSp_conj A hM⟩
  simp [Matrix.IsSymm, Matrix.transpose_mul, hC.eq, Matrix.mul_assoc]

end Conj

theorem spLevi_conj_mem (hr : 2 ≤ r) {e : StatedSp r k} (he : e ∈ spSiegel r k) :
    spLevi r k hr * e * (spLevi r k hr)⁻¹ ∈ spSiegel r k :=
  leviSp_conj_mem _ he

theorem spLevi_conj_ne (hr : 2 ≤ r) :
    ∃ e ∈ spSiegel r k, spLevi r k hr * e * (spLevi r k hr)⁻¹ ≠ e := by
  obtain ⟨e, he, hM⟩ := exists_spSiegel r k (Matrix.single (⟨1, hr⟩ : Fin r) ⟨1, hr⟩ (1 : k))
    (by simp [Matrix.IsSymm, Matrix.transpose_single])
  refine ⟨e, he, fun h => ?_⟩
  have h1 := coe_leviSp_conj (transvGL k (⟨0, by omega⟩ : Fin r) ⟨1, hr⟩ (by simp)) hM
  have h2 := congrArg (fun x : StatedSp r k => ((x : GL (Fin r ⊕ Fin r) k) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)) h
  simp only [spLevi] at h2
  rw [h1, hM, Matrix.fromBlocks_inj] at h2
  have h3 := congrFun (congrFun h2.2.1 ⟨0, by omega⟩) ⟨0, by omega⟩
  rw [coe_transvGL, transv_mul_single_mul_transpose] at h3
  simp at h3

end CFSG.SignalizerFunctorTheorem.NonLocal

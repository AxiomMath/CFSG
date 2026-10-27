module

public import CFSG.RankThree.PartOne.KF1514B.Count

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.KF1514B

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail QuadraticMap Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c]

@[expose] def Calt (x y z : K) : Matrix (Fin 3) (Fin 3) K := !![0, x, y; x, 0, z; y, z, 0]

theorem Calt_transpose (x y z : K) : (Calt x y z)ᵀ = -(Calt x y z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Calt, neg_K]

theorem Calt_diag (x y z : K) (i : Fin 3) : Calt x y z i i = 0 := by
  fin_cases i <;> simp [Calt]

@[expose] noncomputable def mkU (b c : K) (w : Fin 2 → K) (α : Fin 3 → K) (x y z : K) :
    Vt K ≃ₗ[K] Vt K :=
  dMap (1 : GL (Fin 3) K) 1 * uMap (minusTailForm K b c) (fun i => α i • w) (Calt x y z)

theorem mkU_mem (w : Fin 2 → K) (α : Fin 3 → K) (x y z : K) : mkU b c w α x y z ∈ U0 b c := by
  refine dMap_mul_uMap_mem_tailUnipotent (D := 1) ?_ ?_ (fun i => α i • w)
    (Calt_transpose x y z) (Calt_diag x y z)
  · intro i j h
    rw [Units.val_one]
    exact Matrix.one_apply_ne (ne_of_gt h)
  · intro i
    rw [Units.val_one, Matrix.one_apply_eq]

@[expose] noncomputable def mkE (w : Fin 2 → K) (α : Fin 3 → K) (x y z : K) : ↥(U0 b c) :=
  ⟨mkU b c w α x y z, mkU_mem w α x y z⟩

theorem isPar_mkE (w : Fin 2 → K) (α : Fin 3 → K) (x y z : K) :
    IsPar (b := b) (c := c) ((mkE (b := b) (c := c) w α x y z : ↥(U0 b c)) : Vt K ≃ₗ[K] Vt K)
      1 (fun i => α i • w) (Calt x y z) :=
  ⟨fun i j h => by rw [Units.val_one]; exact Matrix.one_apply_ne (ne_of_gt h),
    fun i => by rw [Units.val_one, Matrix.one_apply_eq], Calt_transpose x y z,
    Calt_diag x y z, rfl⟩

theorem Dm_mkE (w : Fin 2 → K) (α : Fin 3 → K) (x y z : K) :
    Dm (mkE (b := b) (c := c) w α x y z) = 1 := (par_eq (isPar_mkE w α x y z)).1

theorem Lp_mkE (w : Fin 2 → K) (α : Fin 3 → K) (x y z : K) :
    Lp (mkE (b := b) (c := c) w α x y z) = fun i => α i • w := (par_eq (isPar_mkE w α x y z)).2.1

theorem Cp_mkE (w : Fin 2 → K) (α : Fin 3 → K) (x y z : K) :
    Cp (mkE (b := b) (c := c) w α x y z) = Calt x y z := (par_eq (isPar_mkE w α x y z)).2.2

@[expose] noncomputable def Aw (w : Fin 2 → K) : Subgroup ↥(U0 b c) where
  carrier := {g | Dm g = 1 ∧ ∃ α : Fin 3 → K, ∀ i, Lp g i = α i • w}
  one_mem' := ⟨Dm_one, 0, fun i => by simp [Lp_one]⟩
  mul_mem' := by
    rintro g g' ⟨hg, α, hα⟩ ⟨hg', α', hα'⟩
    refine ⟨by rw [Dm_mul, hg, hg', one_mul], fun i => α i + α' i, fun i => ?_⟩
    rw [Lp_mul_of_Dm_one hg', Pi.add_apply, hα i, hα' i, add_smul]
  inv_mem' := by
    rintro g ⟨hg, α, hα⟩
    have hDinv : Dm g⁻¹ = 1 := by
      have := Dm_mul g g⁻¹
      rw [mul_inv_cancel, Dm_one, hg, one_mul] at this
      exact this.symm
    refine ⟨hDinv, fun i => -α i, fun i => ?_⟩
    have h1 := Lp_mul_of_Dm_one (n := g) (n' := g⁻¹) hDinv
    rw [mul_inv_cancel, Lp_one] at h1
    have h2 : Lp g⁻¹ i = -(Lp g i) := by
      have := congrFun h1 i
      simp only [Pi.zero_apply, Pi.add_apply] at this
      exact eq_neg_of_add_eq_zero_right this.symm
    rw [h2, hα i, neg_smul]

theorem polar_line (w : Fin 2 → K) (s t : K) :
    QuadraticMap.polar (minusTailForm K b c) (s • w) (t • w) = 0 := by
  rw [polar_minusTail, det2_smul_left, det2_smul_right, det2_self]
  ring

theorem cross_line {w : Fin 2 → K} {L L' : Fin 3 → Fin 2 → K} {α α' : Fin 3 → K}
    (h : ∀ i, L i = α i • w) (h' : ∀ i, L' i = α' i • w) :
    crossMat (minusTailForm K b c) L L' = 0 := by
  ext i j
  simp only [crossMat, Matrix.of_apply, Matrix.zero_apply, h i, h' j]
  exact polar_line w _ _

theorem mulParam_comm {L L' : Fin 3 → Fin 2 → K} (C C' : Matrix (Fin 3) (Fin 3) K)
    (h : crossMat (minusTailForm K b c) L L' = crossMat (minusTailForm K b c) L' L) :
    mulParam (minusTailForm K b c) L L' C C' = mulParam (minusTailForm K b c) L' L C' C := by
  simp only [mulParam, h, add_comm L' L]
  abel

theorem elemAb_Aw (w : Fin 2 → K) : ElemAb (Aw (b := b) (c := c) w) := by
  have hone : ((1 : ↥(U0 b c)) : Vt K ≃ₗ[K] Vt K) = 1 := rfl
  refine ⟨fun n hn n' hn' => ?_, fun n hn => ?_⟩
  · obtain ⟨hD, α, hα⟩ := hn
    obtain ⟨hD', α', hα'⟩ := hn'
    have p1 := IsPar.mul (par_spec n) (par_spec n')
    have p2 := IsPar.mul (par_spec n') (par_spec n)
    rw [hD, hD', inv_one, conjL_one, conjC_one] at p1
    rw [hD, hD', inv_one, conjL_one, conjC_one] at p2
    apply Subtype.ext
    have e1 := p1.eq
    have e2 := p2.eq
    simp only [Subgroup.coe_mul] at e1 e2 ⊢
    rw [e1, e2, add_comm (Lp n) (Lp n'), mulParam_comm (Cp n) (Cp n')]
    rw [cross_line (fun i => hα i) (fun i => hα' i), cross_line (fun i => hα' i) (fun i => hα i)]
  · obtain ⟨hD, α, hα⟩ := hn
    have p1 := IsPar.mul (par_spec n) (par_spec n)
    rw [hD, inv_one, conjL_one, conjC_one, mulParam_self] at p1
    apply Subtype.ext
    have e1 := p1.eq
    simp only [Subgroup.coe_mul] at e1 ⊢
    rw [e1, add_self_fun, cross_line (fun i => hα i) (fun i => hα i), one_mul, uMap_zero_zero]
    rw [dMap_one_one, mul_one]
    rfl

theorem mkE_mem_Aw (w : Fin 2 → K) (α : Fin 3 → K) (x y z : K) :
    mkE (b := b) (c := c) w α x y z ∈ Aw (b := b) (c := c) w :=
  ⟨Dm_mkE w α x y z, α, fun i => by rw [Lp_mkE]⟩

theorem card_Aw_ge {w : Fin 2 → K} (hw : w ≠ 0) :
    Nat.card K ^ 6 ≤ Nat.card ↥(Aw (b := b) (c := c) w) := by
  obtain ⟨k, hk⟩ := exists_ne_zero_coord hw
  have hq : Nat.card ((Fin 3 → K) × (K × K × K)) = Nat.card K ^ 6 := by
    rw [Nat.card_prod, card_fin_fun, card_prod_three]; ring
  rw [← hq]
  refine Nat.card_le_card_of_injective
    (fun p => (⟨mkE w p.1 p.2.1 p.2.2.1 p.2.2.2, mkE_mem_Aw w _ _ _ _⟩ : ↥(Aw (b := b) (c := c) w)))
    ?_
  intro p p' h
  have h1 : mkE (b := b) (c := c) w p.1 p.2.1 p.2.2.1 p.2.2.2 =
      mkE (b := b) (c := c) w p'.1 p'.2.1 p'.2.2.1 p'.2.2.2 := congrArg Subtype.val h
  have hC := congrArg Cp h1
  have hL := congrArg Lp h1
  rw [Cp_mkE, Cp_mkE] at hC
  rw [Lp_mkE, Lp_mkE] at hL
  have c01 := congrFun (congrFun hC 0) 1
  have c02 := congrFun (congrFun hC 0) 2
  have c12 := congrFun (congrFun hC 1) 2
  simp only [Calt, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one] at c01 c02 c12
  have hα : p.1 = p'.1 := by
    funext i
    have := congrFun (congrFun hL i) k
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hk this
  exact Prod.ext hα (Prod.ext c01 (Prod.ext c02 c12))

@[expose] noncomputable def z0 (w : Fin 2 → K) : ↥(U0 b c) := mkE w 0 0 1 0

theorem z0_mem_Aw (w : Fin 2 → K) : z0 (b := b) (c := c) w ∈ Aw (b := b) (c := c) w :=
  mkE_mem_Aw w 0 0 1 0

theorem Dm_z0 (w : Fin 2 → K) : Dm (z0 (b := b) (c := c) w) = 1 := Dm_mkE w 0 0 1 0

theorem Lp_z0 (w : Fin 2 → K) : Lp (z0 (b := b) (c := c) w) = 0 := by
  rw [z0, Lp_mkE]
  funext i k
  simp

theorem Cp_z0_02 (w : Fin 2 → K) : Cp (z0 (b := b) (c := c) w) 0 2 = 1 := by
  rw [z0, Cp_mkE]
  simp [Calt]

theorem conj_Calt (g : ↥(U0 b c)) (x y w : K) :
    ((Dm g)⁻¹ : GL (Fin 3) K).val * Calt x y w * ((Dm g)⁻¹ : GL (Fin 3) K).valᵀ =
      Calt (x + (db g * y + dc g * w)) (y + da g * w) w := by
  obtain ⟨E00, E11, E22, E01, E12, E02, E10, E20, E21⟩ :=
    inv_entries (Dm g) (par_spec g).upper (par_spec g).diag
  generalize ((Dm g)⁻¹ : GL (Fin 3) K).val = E at E00 E11 E22 E01 E12 E02 E10 E20 E21 ⊢
  have h2 := two_eq_zero_K (K := K)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Calt, E00, E11, E22, E01,
      E12, E02, E10, E20, E21, da, db, dc]
  all_goals first | done | (ring_nf; done) | (ring_nf; simp [h2])

theorem commute_of_Cp_fixed {g z : ↥(U0 b c)} (hz : Dm z = 1) (hLz : Lp z = 0)
    (h : Cp z = ((Dm g)⁻¹ : GL (Fin 3) K).val * Cp z * ((Dm g)⁻¹ : GL (Fin 3) K).valᵀ) :
    g * z = z * g := by
  have p1 := IsPar.mul (par_spec g) (par_spec z)
  have p2 := IsPar.mul (par_spec z) (par_spec g)
  rw [hz, inv_one, conjL_one, conjC_one, hLz, mulParam_zero_right] at p1
  rw [hz, hLz, conjL_zero, mulParam_zero_left, conjC_zero_eq] at p2
  apply Subtype.ext
  have e1 := p1.eq
  have e2 := p2.eq
  simp only [Subgroup.coe_mul] at e1 e2 ⊢
  rw [e1, e2]
  simp only [mul_one, one_mul, add_zero, zero_add]
  rw [← h, add_comm (Cp g) (Cp z)]

theorem commute_z0 {g : ↥(U0 b c)} (hg : db g = 0) (w : Fin 2 → K) : g * z0 w = z0 w * g := by
  refine commute_of_Cp_fixed (Dm_z0 w) (Lp_z0 w) ?_
  have hC : Cp (z0 (b := b) (c := c) w) = Calt 0 1 0 := by rw [z0, Cp_mkE]
  rw [hC, conj_Calt, hg]
  simp

theorem db_eq_zero_of_commute_z0 {g : ↥(U0 b c)} (w : Fin 2 → K) (h : g * z0 w = z0 w * g) :
    db g = 0 := by
  have := (Cp_constraints (Dm_z0 w) (Lp_z0 w) h).1
  have h12 : Cp (z0 (b := b) (c := c) w) 1 2 = 0 := by rw [z0, Cp_mkE]; simp [Calt]
  rw [Cp_z0_02, h12, mul_one, mul_zero, add_zero] at this
  exact this

end CFSG.RankThree.PartOne.KF1514B

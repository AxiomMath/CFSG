module

public import CFSG.Quasithin.Vol2.Ch11SecB414PB
public import CFSG.Quasithin.Vol2.Ch11SecB414MH

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open Matrix

variable {F : Type} [Field F]

@[expose] def gr (M : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F := w0 * Mᵀ * w0

theorem gr_add (M N : Matrix (Fin 3) (Fin 3) F) : gr (M + N) = gr M + gr N := by
  simp only [gr, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem gr_zero : gr (0 : Matrix (Fin 3) (Fin 3) F) = 0 := by
  simp only [gr, Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul]

theorem gr_smul (c : F) (M : Matrix (Fin 3) (Fin 3) F) : gr (c • M) = c • gr M := by
  simp only [gr, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem w0_mul_w0_mul (X : Matrix (Fin 3) (Fin 3) F) : w0 * (w0 * X) = X := by
  rw [← Matrix.mul_assoc, w0_mul_w0, Matrix.one_mul]

theorem gr_gr (M : Matrix (Fin 3) (Fin 3) F) : gr (gr M) = M := by
  simp only [gr, Matrix.transpose_mul, Matrix.transpose_transpose, w0_transpose,
    Matrix.mul_assoc, w0_mul_w0_mul, w0_mul_w0, Matrix.mul_one]

theorem trace_gr (M : Matrix (Fin 3) (Fin 3) F) : (gr M).trace = M.trace := by
  rw [gr, Matrix.trace_mul_comm, ← Matrix.mul_assoc, w0_mul_w0, Matrix.one_mul,
    Matrix.trace_transpose]

theorem gr_conj (g : GL (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) :
    gr ((thetaGL g : Matrix (Fin 3) (Fin 3) F) * M *
        (((thetaGL g)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) =
      (g : Matrix (Fin 3) (Fin 3) F) * gr M *
        ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  rw [coe_thetaGL, thetaMat, coe_thetaGL_inv]
  simp only [gr, Matrix.transpose_mul, Matrix.transpose_transpose, w0_transpose,
    Matrix.mul_assoc, w0_mul_w0_mul, w0_mul_w0, Matrix.mul_one]

theorem det_thetaGL (g : GL (Fin 3) F) :
    (thetaGL g : Matrix (Fin 3) (Fin 3) F).det = ((g : Matrix (Fin 3) (Fin 3) F).det)⁻¹ := by
  have h1 : (((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).det *
      (g : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
  rw [coe_thetaGL, thetaMat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_comm,
    ← mul_assoc, det_w0_mul_self, one_mul]
  exact eq_inv_of_mul_eq_one_left h1

theorem inv_pow_eq (hF : Nat.card F = 4) {d : F} (hd : d ≠ 0) {k : ℕ} (hk : k < 3) :
    d⁻¹ ^ k = d ^ ((3 - k) % 3) := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  have h3 : d ^ 3 = 1 := by
    have hU : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
    have h := pow_card_eq_one' (G := Fˣ) (x := Units.mk0 d hd)
    rw [hU] at h
    have := congrArg Units.val h
    simpa using this
  interval_cases k
  · simp
  · rw [pow_one]
    exact inv_eq_of_mul_eq_one_right (by rw [show (3 - 1) % 3 = 2 by rfl, ← pow_succ', h3])
  · rw [show (3 - 2) % 3 = 1 by rfl, pow_one, inv_pow]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ, h3])

section Model

variable {G : Type} [Group G] {Γ V Z : Subgroup G} {k : ℕ} {α : ↥Γ →* PGL3 F}

@[expose] noncomputable def Model.graph (m : Model Γ V Z F k α) (hF : Nat.card F = 4)
    (hk : k < 3) : Model Γ V Z F ((3 - k) % 3) ((graphAut F).toMonoidHom.comp α) where
  β :=
    { toFun := fun v => Multiplicative.ofAdd (gr (Multiplicative.toAdd (m.β v)))
      map_one' := by
        rw [map_one, toAdd_one, gr_zero]
        rfl
      map_mul' := fun v w => by
        rw [map_mul, toAdd_mul, gr_add]
        rfl }
  sl := fun v => by
    show (gr (Multiplicative.toAdd (m.β v))).trace = 0
    rw [trace_gr, m.sl]
  onto := fun M hM => by
    obtain ⟨v, hv⟩ := m.onto (gr M) (by rw [trace_gr, hM])
    exact ⟨v, show gr (Multiplicative.toAdd (m.β v)) = M by rw [hv, gr_gr]⟩
  ker := fun v => by
    rw [← m.ker v]
    show Multiplicative.ofAdd (gr (Multiplicative.toAdd (m.β v))) = 1 ↔ _
    constructor
    · intro h
      have h1 : gr (Multiplicative.toAdd (m.β v)) = 0 := congrArg Multiplicative.toAdd h
      have h2 := gr_gr (Multiplicative.toAdd (m.β v))
      rw [h1, gr_zero] at h2
      exact Multiplicative.toAdd.injective h2.symm
    · intro h
      rw [h, toAdd_one, gr_zero]
      rfl
  act := fun γ u v huv g hg => by
    have hg' : ProjGenLinGroup.mk (thetaGL g) = α γ := by
      rw [← graphAut_mk, hg]
      exact graphAut_graphAut _
    show gr (Multiplicative.toAdd (m.β v)) =
      twAdj ((3 - k) % 3) g (gr (Multiplicative.toAdd (m.β u)))
    have hd : (g : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact (Matrix.GeneralLinearGroup.det g).ne_zero
    rw [m.act γ u v huv _ hg', twAdj, twAdj, gr_smul, gr_conj, det_thetaGL, inv_pow_eq hF hd hk]
  normV := m.normV
  le := m.le

end Model

end CFSG.Quasithin.H13.Ch4.B414.M

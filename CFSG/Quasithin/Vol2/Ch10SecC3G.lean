module

public import CFSG.Quasithin.H13.StatementsCh7
public import CFSG.Quasithin.Background.HDefs

public section

namespace CFSG.Quasithin.Vol2.Ch10.C3.Om

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.H13 (tensorPairModel)
open scoped Matrix

variable {K : Type} [Field K]

abbrev SL (K : Type) [Field K] : Type := Matrix.SpecialLinearGroup (Fin 2) K

theorem mem_statedSL_iff {g : GL (Fin 2) K} :
    g ∈ StatedSL 2 K ↔ (g : Matrix (Fin 2) (Fin 2) K).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

variable (K) in
@[expose] noncomputable def slEquiv : SL K ≃* ↥(StatedSL 2 K) :=
  MulEquiv.ofBijective
    ((Matrix.SpecialLinearGroup.toGL).codRestrict (StatedSL 2 K) fun g =>
      mem_statedSL_iff.mpr g.2)
    ⟨fun _ _ hgh => Matrix.SpecialLinearGroup.toGL_injective (congrArg Subtype.val hgh),
      fun γ => ⟨⟨(γ : GL (Fin 2) K), mem_statedSL_iff.mp γ.2⟩, Subtype.ext (Units.ext rfl)⟩⟩

theorem coe_slEquiv_symm (γ : ↥(StatedSL 2 K)) :
    (((slEquiv K).symm γ : SL K) : Matrix (Fin 2) (Fin 2) K) =
      ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  conv_rhs => rw [← (slEquiv K).apply_symm_apply γ]
  rfl

variable (K) in
abbrev WM (K : Type) [Field K] : Type := Multiplicative (Matrix (Fin 2) (Fin 2) K)

@[expose] def act (g : SL K × SL K) (X : WM K) : WM K :=
  Multiplicative.ofAdd ((g.1 : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd X *
    (g.2 : Matrix (Fin 2) (Fin 2) K)ᵀ)

theorem toAdd_act (g : SL K × SL K) (X : WM K) :
    Multiplicative.toAdd (act g X) = (g.1 : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd X *
      (g.2 : Matrix (Fin 2) (Fin 2) K)ᵀ := rfl

theorem act_mul (g h : SL K × SL K) (X : WM K) : act (g * h) X = act g (act h X) := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_act, Prod.fst_mul, Prod.snd_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.transpose_mul, Matrix.mul_assoc]

theorem act_one (X : WM K) : act 1 X = X := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_act, Prod.fst_one, Prod.snd_one, Matrix.SpecialLinearGroup.coe_one,
    Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem act_mul_right (g : SL K × SL K) (X Y : WM K) : act g (X * Y) = act g X * act g Y := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_act, toAdd_mul, Matrix.mul_add, Matrix.add_mul]

variable (K) in
@[expose] def rho : SL K × SL K →* MulAut (WM K) where
  toFun g :=
    { toFun := act g
      invFun := act g⁻¹
      left_inv := fun X => by rw [← act_mul, inv_mul_cancel, act_one]
      right_inv := fun X => by rw [← act_mul, mul_inv_cancel, act_one]
      map_mul' := act_mul_right g }
  map_one' := MulEquiv.ext act_one
  map_mul' g h := MulEquiv.ext fun X => act_mul g h X

theorem toAdd_rho (g : SL K × SL K) (X : WM K) :
    Multiplicative.toAdd (rho K g X) = (g.1 : Matrix (Fin 2) (Fin 2) K) *
      Multiplicative.toAdd X * (g.2 : Matrix (Fin 2) (Fin 2) K)ᵀ := rfl

theorem eq_one_of_sq_eq_one [CharP K 2] {c : K} (hc : c * c = 1) : c = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h : (c - 1) * (c - 1) = 0 := by
    calc (c - 1) * (c - 1) = c * c - 2 * c + 1 := by ring
      _ = 0 := by rw [hc, h2, zero_mul, sub_zero]; exact CharTwo.add_self_eq_zero 1
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h)

theorem rho_injective [CharP K 2] : Function.Injective (rho K) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨g, h⟩ hγ
  have key : ∀ X : Matrix (Fin 2) (Fin 2) K,
      (g : Matrix (Fin 2) (Fin 2) K) * X * (h : Matrix (Fin 2) (Fin 2) K)ᵀ = X := fun X => by
    have := congrArg (fun φ : MulAut (WM K) => Multiplicative.toAdd (φ (Multiplicative.ofAdd X))) hγ
    simpa [toAdd_rho] using this
  have hinv : (h : Matrix (Fin 2) (Fin 2) K)ᵀ = ((g⁻¹ : SL K) : Matrix (Fin 2) (Fin 2) K) := by
    have h1 := key 1
    rw [Matrix.mul_one] at h1
    calc (h : Matrix (Fin 2) (Fin 2) K)ᵀ =
          ((g⁻¹ : SL K) : Matrix (Fin 2) (Fin 2) K) * ((g : Matrix (Fin 2) (Fin 2) K) *
            (h : Matrix (Fin 2) (Fin 2) K)ᵀ) := by
          rw [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
            Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
      _ = ((g⁻¹ : SL K) : Matrix (Fin 2) (Fin 2) K) := by rw [h1, Matrix.mul_one]
  have hcomm : ∀ X : Matrix (Fin 2) (Fin 2) K, Commute X (g : Matrix (Fin 2) (Fin 2) K) := by
    intro X
    have h1 := key X
    rw [hinv] at h1
    calc X * (g : Matrix (Fin 2) (Fin 2) K) = (g : Matrix (Fin 2) (Fin 2) K) * X *
          ((g⁻¹ : SL K) : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := by
          rw [h1]
      _ = (g : Matrix (Fin 2) (Fin 2) K) * X := by
          rw [Matrix.mul_assoc _ ((g⁻¹ : SL K) : Matrix (Fin 2) (Fin 2) K),
            ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
            Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single fun i j _ => hcomm _
  have hc1 : c = 1 := by
    have hdet := g.2
    rw [← hc, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two] at hdet
    exact eq_one_of_sq_eq_one hdet
  have hg1 : g = 1 := by
    apply Subtype.ext
    rw [← hc, hc1, Matrix.SpecialLinearGroup.coe_one]
    simp
  have hh1 : h = 1 := by
    rw [hg1, inv_one, Matrix.SpecialLinearGroup.coe_one] at hinv
    apply Subtype.ext
    rw [← Matrix.transpose_transpose (h : Matrix (Fin 2) (Fin 2) K), hinv, Matrix.transpose_one,
      Matrix.SpecialLinearGroup.coe_one]
  rw [hg1, hh1]
  rfl

end CFSG.Quasithin.Vol2.Ch10.C3.Om

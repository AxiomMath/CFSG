module

public import CFSG.Quasithin.Background.G9GolayModels
public import CFSG.Monster.Code.Weights
public import CFSG.Blueprint.SourceBinaryGolayCodeProperties

public section

namespace CFSG.Quasithin.G11

@[expose] def golayRelabel : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 8, 13, 15, 23, 7, 20, 18, 19, 10, 17, 14, 11, 21, 5, 16, 22, 6, 12, 9]
  invFun := ![0, 1, 2, 3, 4, 18, 21, 9, 5, 23, 13, 16, 22, 6, 15, 7, 19, 14, 11, 12, 10, 17, 20, 8]
  left_inv := by decide
  right_inv := by decide

theorem golayRelabel_zero : golayRelabel 0 = 0 := by decide

theorem golayRelabel_one : golayRelabel 1 = 1 := by decide

theorem golay_permAct_mul (σ τ : Equiv.Perm (Fin 24)) (w : GolayAmbient) :
    permAct (σ * τ) w = permAct σ (permAct τ w) := by
  funext i
  simp only [permAct, mul_inv_rev, Equiv.Perm.mul_apply]

theorem golay_permAct_one (w : GolayAmbient) : permAct (1 : Equiv.Perm (Fin 24)) w = w := by
  funext i
  simp only [permAct, inv_one, Equiv.Perm.one_apply]

theorem golay_permAct_add (σ : Equiv.Perm (Fin 24)) (v w : GolayAmbient) :
    permAct σ (v + w) = permAct σ v + permAct σ w := by
  funext i
  rfl

theorem golay_permAct_zero (σ : Equiv.Perm (Fin 24)) : permAct σ (0 : GolayAmbient) = 0 := by
  funext i
  rfl

theorem golay_permAct_smul (σ : Equiv.Perm (Fin 24)) (a : ZMod 2) (w : GolayAmbient) :
    permAct σ (a • w) = a • permAct σ w := by
  funext i
  rfl

theorem golay_permAct_inv_cancel (σ : Equiv.Perm (Fin 24)) (w : GolayAmbient) :
    permAct σ (permAct σ⁻¹ w) = w := by
  rw [← golay_permAct_mul, mul_inv_cancel, golay_permAct_one]

theorem golay_permAct_injective (σ : Equiv.Perm (Fin 24)) :
    Function.Injective (permAct σ : GolayAmbient → GolayAmbient) := by
  intro a b h
  have h1 : permAct σ⁻¹ (permAct σ a) = a := by
    have := golay_permAct_inv_cancel σ⁻¹ a
    rwa [inv_inv] at this
  have h2 : permAct σ⁻¹ (permAct σ b) = b := by
    have := golay_permAct_inv_cancel σ⁻¹ b
    rwa [inv_inv] at this
  have hh := congrArg (permAct σ⁻¹) h
  rwa [h1, h2] at hh

@[expose] def golayPermLin (σ : Equiv.Perm (Fin 24)) : GolayAmbient ≃ₗ[ZMod 2] GolayAmbient where
  toFun := permAct σ
  map_add' := golay_permAct_add σ
  map_smul' := fun a w => golay_permAct_smul σ a w
  invFun := permAct σ⁻¹
  left_inv := fun w => by
    have h := golay_permAct_inv_cancel σ⁻¹ w
    rwa [inv_inv] at h
  right_inv := golay_permAct_inv_cancel σ

private theorem permAct_golayRelabel_generator :
    ∀ i : Fin 12, permAct golayRelabel (CFSG.Blueprint.EvenSource.sourceGolayGenerator i) ∈
      CFSG.Monster.Code.C := by
  decide +kernel

theorem golay_permAct_dotProduct (σ : Equiv.Perm (Fin 24)) (v w : GolayAmbient) :
    permAct σ v ⬝ᵥ permAct σ w = v ⬝ᵥ w := by
  simp only [dotProduct, permAct]
  exact Equiv.sum_comp σ⁻¹ (fun i => v i * w i)

theorem mem_sourceGolayCode_iff_permAct_golayRelabel_mem_C (w : GolayAmbient) :
    w ∈ CFSG.Blueprint.EvenSource.sourceGolayCode ↔
      permAct golayRelabel w ∈ CFSG.Monster.Code.C := by
  have hle : CFSG.Blueprint.EvenSource.sourceGolayCode.map
      (golayPermLin golayRelabel).toLinearMap ≤ CFSG.Monster.Code.C := by
    rw [CFSG.Blueprint.EvenSource.sourceGolayCode, Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, ⟨i, rfl⟩, rfl⟩
    exact permAct_golayRelabel_generator i
  have hfwd : ∀ x : GolayAmbient, x ∈ CFSG.Blueprint.EvenSource.sourceGolayCode →
      permAct golayRelabel x ∈ CFSG.Monster.Code.C := fun x hx =>
    hle (Submodule.mem_map_of_mem hx)
  refine ⟨hfwd w, fun hw => ?_⟩
  rw [CFSG.Blueprint.EvenSource.mem_iff_forall_dotProduct]
  intro y hy
  exact (golay_permAct_dotProduct golayRelabel w y).symm.trans
    (CFSG.Monster.Code.dotProduct_eq_zero hw (hfwd y hy))

end CFSG.Quasithin.G11

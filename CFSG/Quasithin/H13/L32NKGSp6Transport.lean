module

public import CFSG.Quasithin.H13.L32NKGSp6Group

public section

namespace CFSG.Quasithin.H13.KGSp6

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def phi (b : Module.Basis (Fin 6) (ZMod 2) V) :
    (V ≃ₗ[ZMod 2] V) →* Mat6ˣ where
  toFun γ := ⟨LinearMap.toMatrix b b (γ : V →ₗ[ZMod 2] V),
    LinearMap.toMatrix b b (γ.symm : V →ₗ[ZMod 2] V), by
      rw [← LinearMap.toMatrix_mul]
      convert LinearMap.toMatrix_id b using 2
      ext v; simp, by
      rw [← LinearMap.toMatrix_mul]
      convert LinearMap.toMatrix_id b using 2
      ext v; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' γ δ := Units.ext (by
    simp only [Units.val_mul, LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul])

theorem coe_phi (b : Module.Basis (Fin 6) (ZMod 2) V) (γ : V ≃ₗ[ZMod 2] V) :
    ((phi b γ : Mat6ˣ) : Mat6) = LinearMap.toMatrix b b (γ : V →ₗ[ZMod 2] V) := rfl

theorem phi_injective (b : Module.Basis (Fin 6) (ZMod 2) V) : Function.Injective (phi b) := by
  intro γ δ h
  have h1 := congrArg Units.val h
  rw [coe_phi, coe_phi] at h1
  exact LinearEquiv.toLinearMap_injective ((LinearMap.toMatrix b b).injective h1)


theorem form_eq_sum (b : Module.Basis (Fin 6) (ZMod 2) V) (B : LinearMap.BilinForm (ZMod 2) V)
    (x y : V) :
    B x y = ∑ k, ∑ l, b.repr x k * (b.repr y l * B (b k) (b l)) := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem isIso_toMatrix (b : Module.Basis (Fin 6) (ZMod 2) V) (B : LinearMap.BilinForm (ZMod 2) V)
    (hgram : ∀ i j, B (b i) (b j) = KGCert.g22Form i j) {γ : V →ₗ[ZMod 2] V}
    (hγ : ∀ v w, B (γ v) (γ w) = B v w) : IsIso (LinearMap.toMatrix b b γ) := by
  unfold IsIso
  ext i j
  have h := hγ (b i) (b j)
  rw [hgram, form_eq_sum b B] at h
  simp only [hgram] at h
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, LinearMap.toMatrix_apply]
  rw [Finset.sum_comm, ← h]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem toMatrix_map (b : Module.Basis (Fin 6) (ZMod 2) V) (e γ : V ≃ₗ[ZMod 2] V) :
    LinearMap.toMatrix (b.map e) (b.map e) (γ : V →ₗ[ZMod 2] V) =
      ((phi b (e⁻¹ * γ * e) : Mat6ˣ) : Mat6) := by
  rw [coe_phi]
  ext i j
  simp only [LinearMap.toMatrix_apply, Module.Basis.map_apply, Module.Basis.map_repr,
    LinearEquiv.coe_coe]
  rfl

theorem phi_surjective (b : Module.Basis (Fin 6) (ZMod 2) V) : Function.Surjective (phi b) := by
  intro u
  let e : V ≃ₗ[ZMod 2] V := LinearEquiv.ofLinearMap (Matrix.toLin b b (u : Mat6))
    (Matrix.toLin b b ((u⁻¹ : Mat6ˣ) : Mat6)) (by
      rw [← Matrix.toLin_mul, Units.mul_inv, Matrix.toLin_one]) (by
      rw [← Matrix.toLin_mul, Units.inv_mul, Matrix.toLin_one])
  refine ⟨e, Units.ext ?_⟩
  rw [coe_phi]
  exact LinearMap.toMatrix_toLin b b (u : Mat6)

end CFSG.Quasithin.H13.KGSp6

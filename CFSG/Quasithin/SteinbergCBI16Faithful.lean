module

public import CFSG.Quasithin.SteinbergCBI16A7

public section

namespace CFSG.Quasithin.SteinbergCB.I16

open CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem finrank_H1_faithful_alt7 {ρ : Representation (ZMod 2) Γ W}
    (θ : Γ ≃* ↥(alternatingGroup (Fin 7))) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) W = 4) : Module.finrank (ZMod 2) (H1 ρ) = 0 := by
  have : Module.Finite (ZMod 2) W := Module.finite_of_finrank_pos (by omega)
  let b := Module.finBasisOfFinrankEq (ZMod 2) W hdim
  have hT : ∀ f : Module.End (ZMod 2) W,
      LinearMap.toMatrixAlgEquiv b f = LinearMap.toMatrix b b f := fun f => by
    ext i j
    rw [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  let T : Module.End (ZMod 2) W →* Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    MonoidHom.ofClass (LinearMap.toMatrixAlgEquiv b)
  let M : A7 →* GL (Fin 4) (ZMod 2) :=
    (Units.map T).comp ((MonoidHom.toHomUnits ρ).comp θ.symm.toMonoidHom)
  have hM : Function.Injective M := by
    intro x y hxy
    have h1 : T (ρ (θ.symm x)) = T (ρ (θ.symm y)) := congrArg Units.val hxy
    exact θ.symm.injective (hρ ((LinearMap.toMatrixAlgEquiv b).injective h1))
  let β : W ≃+ Vec4 := b.equivFun.toAddEquiv
  have hβ : ∀ γ w, β (ρ γ w) = matAct M (θ γ) (β w) := by
    intro γ w
    rw [matAct_apply]
    change b.equivFun (ρ γ w) = T (ρ (θ.symm (θ γ))) *ᵥ b.equivFun w
    rw [θ.symm_apply_apply, Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
    change _ = LinearMap.toMatrixAlgEquiv b (ρ γ) *ᵥ _
    rw [hT, LinearMap.toMatrix_mulVec_repr]
  exact finrank_H1_eq_zero_of_le (Z1_le_B1_of_transport hβ (Z1A_le_B1A_A7 M hM))

theorem finrank_H1_faithful_center {ρ : Representation (ZMod 2) Γ W}
    (e : Subgroup.center Γ ≃* Multiplicative (ZMod 3)) (hρ : Function.Injective ρ)
    (hirr : ρ.IsIrreducible) (hdim : 0 < Module.finrank (ZMod 2) W) :
    Module.finrank (ZMod 2) (H1 ρ) = 0 := by
  have : Module.Finite (ZMod 2) W := Module.finite_of_finrank_pos hdim
  set z : Γ := (e.symm (Multiplicative.ofAdd 1) : Γ) with hz
  have hzc : ∀ g, z * g = g * z := fun g =>
    (Subgroup.mem_center_iff.1 (e.symm (Multiplicative.ofAdd 1)).2 g).symm
  have hz1 : z ≠ 1 := by
    intro h
    have h' : e.symm (Multiplicative.ofAdd 1) = 1 := Subtype.ext h
    have h'' : Multiplicative.ofAdd (1 : ZMod 3) = 1 := by
      rw [← e.apply_symm_apply (Multiplicative.ofAdd 1), h', map_one]
    exact absurd h'' (by decide)
  let U : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker (ρ z - 1)
      apply_mem_toSubmodule := fun g v hv => by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply] at hv ⊢
        rw [← Module.End.mul_apply, ← map_mul, hzc g, map_mul, Module.End.mul_apply,
          sub_eq_zero.1 hv, sub_self] }
  have hker : LinearMap.ker (ρ z - 1) = ⊥ := by
    rcases hirr.eq_bot_or_eq_top U with h | h
    · exact congrArg Subrepresentation.toSubmodule h
    · exfalso
      apply hz1
      apply hρ
      rw [map_one]
      ext v
      have hv : v ∈ LinearMap.ker (ρ z - 1) := by
        change v ∈ U.toSubmodule
        rw [h]
        exact Submodule.mem_top
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
      exact hv
  have hinj : Function.Injective (ρ z - 1 : Module.End (ZMod 2) W) := LinearMap.ker_eq_bot.1 hker
  have hbij : Function.Bijective (ρ z - 1 : Module.End (ZMod 2) W) :=
    ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  exact finrank_H1_eq_zero_of_le (Z1_le_B1_of_central ρ z hzc hbij)

end CFSG.Quasithin.SteinbergCB.I16

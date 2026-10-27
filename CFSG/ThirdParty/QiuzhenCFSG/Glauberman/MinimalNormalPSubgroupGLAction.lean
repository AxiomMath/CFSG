module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.MinimalNormalPSubgroupFaithfulIrreducibleAction
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# The faithful irreducible linear action of a minimal normal p-subgroup
-/

namespace CFSG.Glauberman

open scoped IsMulCommutative

universe u

private def mulAutLinearEquiv
    (p : ℕ) [Fact p.Prime] {A : Type u} [Group A] [IsElementaryAbelian p A]
    (a : MulAut (Multiplicative (Additive A))) :
    Additive A ≃ₗ[ZMod p] Additive A :=
  let e : Multiplicative (Additive A) ≃* A :=
    MulEquiv.multiplicativeAdditive A
  let aA : MulAut A := MulAut.congr e a
  let eAdd : Additive A ≃+ Additive A := MulEquiv.toAdditive aA
  eAdd.toLinearEquiv (fun c x => by
    simpa using (ZMod.map_smul eAdd.toAddMonoidHom c x))

@[simp] private theorem mulAutLinearEquiv_apply
    {p : ℕ} [Fact p.Prime] {A : Type u} [Group A] [IsElementaryAbelian p A]
    (a : MulAut (Multiplicative (Additive A))) (x : Additive A) :
    Additive.toMul (mulAutLinearEquiv p a x) =
      MulEquiv.multiplicativeAdditive A
        (a ((MulEquiv.multiplicativeAdditive A).symm (Additive.toMul x))) := by
  rfl

private def mulAutToGeneralLinear
    (p : ℕ) [Fact p.Prime] (A : Type u) [Group A] [IsElementaryAbelian p A] :
    MulAut (Multiplicative (Additive A)) →*
      LinearMap.GeneralLinearGroup (ZMod p) (Additive A) where
  toFun a := LinearMap.GeneralLinearGroup.ofLinearEquiv (mulAutLinearEquiv p a)
  map_one' := by
    apply Units.ext
    ext x
    apply Additive.toMul.injective
    simp
  map_mul' a b := by
    apply Units.ext
    ext x
    apply Additive.toMul.injective
    simp

@[simp] private theorem mulAutToGeneralLinear_apply
    {p : ℕ} [Fact p.Prime] {A : Type u} [Group A] [IsElementaryAbelian p A]
    (a : MulAut (Multiplicative (Additive A))) (x : Additive A) :
    (((mulAutToGeneralLinear p A) a :
        LinearMap.GeneralLinearGroup (ZMod p) (Additive A)) :
      Additive A →ₗ[ZMod p] Additive A) x =
      mulAutLinearEquiv p a x := by
  rfl

private theorem mulAutToGeneralLinear_injective
    {p : ℕ} [Fact p.Prime] {A : Type u} [Group A] [IsElementaryAbelian p A] :
    Function.Injective (mulAutToGeneralLinear p A) := by
  intro a b hab
  ext x
  let e : Multiplicative (Additive A) ≃* A :=
    MulEquiv.multiplicativeAdditive A
  let xAdd : Additive A := Additive.ofMul (e x)
  have happ := congrArg
    (fun g : LinearMap.GeneralLinearGroup (ZMod p) (Additive A) =>
      (g : Additive A →ₗ[ZMod p] Additive A) xAdd) hab
  have happ' := congrArg Additive.toMul happ
  simpa [xAdd, e] using happ'

public theorem exists_minimalNormal_pSubgroup_GL_faithful_irreducible_action
    {p : ℕ} [Fact p.Prime] {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) [H.Normal] [IsMinimalNormal H]
    (hHne : H ≠ ⊥) (hHp : IsPGroup p H) :
    letI : IsElementaryAbelian p H :=
      minimalNormal_pSubgroup_isElementaryAbelian H hHne hHp
    letI : Module (ZMod p) (Additive H) :=
      IsElementaryAbelian.isVectorSpace p
    ∃ ρ : Q ⧸ Subgroup.centralizer (H : Set Q) →*
        LinearMap.GeneralLinearGroup (ZMod p) (Additive H),
      Function.Injective ρ ∧
        (∀ W : Submodule (ZMod p) (Additive H),
          (∀ g : Q ⧸ Subgroup.centralizer (H : Set Q),
            ∀ v : Additive H, v ∈ W →
              ((ρ g : LinearMap.GeneralLinearGroup (ZMod p) (Additive H)) :
                Additive H →ₗ[ZMod p] Additive H) v ∈ W) →
          W = ⊥ ∨ W = ⊤) ∧
        ∀ (q : Q) (h : Additive H),
          Additive.toMul
              ((((ρ (QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) q) :
                  LinearMap.GeneralLinearGroup (ZMod p) (Additive H)) :
                Additive H →ₗ[ZMod p] Additive H) h)) =
            MulAut.conjNormal (H := H) q (Additive.toMul h) := by
  let : IsElementaryAbelian p H :=
    minimalNormal_pSubgroup_isElementaryAbelian H hHne hHp
  let : IsMulCommutative H :=
    (inferInstance : IsElementaryAbelian p H).toIsMulCommutative
  let : Module (ZMod p) (Additive H) :=
    IsElementaryAbelian.isVectorSpace p
  obtain ⟨σ, hσinj, hσirr, hσeval⟩ :=
    exists_minimalNormal_pSubgroup_faithful_irreducible_action H hHne hHp
  let ρ : Q ⧸ Subgroup.centralizer (H : Set Q) →*
      LinearMap.GeneralLinearGroup (ZMod p) (Additive H) :=
    (mulAutToGeneralLinear p H).comp σ
  have hρinj : Function.Injective ρ :=
    (mulAutToGeneralLinear_injective (p := p) (A := H)).comp hσinj
  have hρirr : ∀ W : Submodule (ZMod p) (Additive H),
      (∀ g : Q ⧸ Subgroup.centralizer (H : Set Q),
        ∀ v : Additive H, v ∈ W →
          ((ρ g : LinearMap.GeneralLinearGroup (ZMod p) (Additive H)) :
            Additive H →ₗ[ZMod p] Additive H) v ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
    intro W hWinv
    let Wg : Subgroup (Multiplicative (Additive H)) :=
      W.toAddSubgroup.toSubgroup
    have hWginv : ∀ g : Q ⧸ Subgroup.centralizer (H : Set Q),
        ∀ w : Multiplicative (Additive H), w ∈ Wg → σ g w ∈ Wg := by
      intro g w hw
      let v : Additive H := Multiplicative.toAdd w
      have hv : v ∈ W := by simpa [Wg, v] using hw
      have himage := hWinv g v hv
      let e : Multiplicative (Additive H) ≃* H :=
        MulEquiv.multiplicativeAdditive H
      have hin : e.symm (Additive.toMul v) = w := by
        calc
          e.symm (Additive.toMul v) = e.symm (e w) := by rfl
          _ = w := e.symm_apply_apply w
      have hout : Additive.toMul (Multiplicative.toAdd (σ g w)) = e (σ g w) := by
        rfl
      have heq :
          (((ρ g : LinearMap.GeneralLinearGroup (ZMod p) (Additive H)) :
            Additive H →ₗ[ZMod p] Additive H) v) =
            Multiplicative.toAdd (σ g w) := by
        apply Additive.toMul.injective
        change Additive.toMul (mulAutLinearEquiv p (σ g) v) =
          Additive.toMul (Multiplicative.toAdd (σ g w))
        rw [mulAutLinearEquiv_apply, hin, hout]
      change Multiplicative.toAdd (σ g w) ∈ W
      rw [← heq]
      exact himage
    rcases (irreducibleAction_iff.mp hσirr) Wg hWginv with hbot | htop
    · left
      exact Submodule.toAddSubgroup_injective
        (AddSubgroup.toSubgroup.injective (by simpa [Wg] using hbot))
    · right
      exact Submodule.toAddSubgroup_injective
        (AddSubgroup.toSubgroup.injective (by simpa [Wg] using htop))
  refine ⟨ρ, hρinj, hρirr, ?_⟩
  intro q h
  let e : Multiplicative (Additive H) ≃* H :=
    MulEquiv.multiplicativeAdditive H
  let w : Multiplicative (Additive H) := e.symm (Additive.toMul h)
  calc
    Additive.toMul
        ((((ρ (QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) q) :
            LinearMap.GeneralLinearGroup (ZMod p) (Additive H)) :
          Additive H →ₗ[ZMod p] Additive H) h)) =
        e (σ (QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) q) w) := by
          change Additive.toMul
              (mulAutLinearEquiv p
                (σ (QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) q)) h) = _
          rw [mulAutLinearEquiv_apply]
    _ = MulAut.conjNormal (H := H) q (e w) := hσeval q w
    _ = MulAut.conjNormal (H := H) q (Additive.toMul h) := by
      simp [w]

end CFSG.Glauberman

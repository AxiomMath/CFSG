module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2ActualFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogue

public section

namespace CFSG.StandardType.GGQ2Frame.OrthPlacement

open CFSG CFSG.Assembly CFSG.StandardType Matrix
open CFSG.Open (IsElemAbelian)
open CFSG.StandardType.GGQ2Frame.OrthBlocks

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {δ : Fin 2}
  {K : Type} [Field K] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
  {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}

structure OrthFrame (H E : Subgroup G) (hEN : E ≤ Subgroup.normalizer (H : Set G)) (K : Type)
    [Field K] (t : ℕ) (δ : Fin 2) (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) :
    Type where
  π : ↥H →* ↥(omegaQ (K := K) t δ)
  surj : Function.Surjective π
  ker_le : π.ker ≤ Subgroup.center ↥H
  τ : (Fin t → Multiplicative (ZMod 3)) ≃* ↥E
  intertwine : ∀ (u : Fin t → Multiplicative (ZMod 3)) (h : ↥H),
    ((π (H.normalizerMonoidHom ⟨((τ u : ↥E) : G), hEN (τ u).2⟩ h) :
        GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)) =
      otau ζ t δ (fun i => Multiplicative.toAdd (u i)) *
        ((π h : ↥(omegaQ (K := K) t δ)) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *
        (otau ζ t δ (fun i => Multiplicative.toAdd (u i)))⁻¹

@[expose] def OrthFrame.coord (fr : OrthFrame H E hEN K t δ ζ) : Additive ↥E ≃+ PlaneRaw.V t where
  toFun x := fun i => Multiplicative.toAdd (fr.τ.symm (Additive.toMul x) i)
  invFun u := Additive.ofMul (fr.τ (fun i => Multiplicative.ofAdd (u i)))
  left_inv x := by simp
  right_inv u := by ext i; simp
  map_add' x y := by ext i; simp

@[expose] def OrthFrame.component (fr : OrthFrame H E hEN K t δ ζ) (c : PlaneRaw.Code t) :
    Subgroup G :=
  (⁅(oYcode ζ t δ c).comap fr.π, (oYcode ζ t δ c).comap fr.π⁆).map H.subtype

structure OrthCtx (H E : Subgroup G) (hEN : E ≤ Subgroup.normalizer (H : Set G)) (K : Type)
    [Field K] (t : ℕ) (δ : Fin 2) (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) :
    Type where
  fr : OrthFrame H E hEN K t δ ζ
  hK : Nat.card K = 2
  hζ : Function.Injective ζ
  hHp : commutator H = ⊤
  hEab : IsElemAbelian 3 E
  hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥H)
  hEH : E ≤ H
  ht : 4 ≤ t
  innerDiag : GGInnerDiagOnLabel (fun _ lab => lab = planeAmbientLabel (.orthogonal δ) t) 3 E H

end

end CFSG.StandardType.GGQ2Frame.OrthPlacement

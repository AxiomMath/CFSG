module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogue

public section

namespace CFSG.StandardType.GGQ2Frame.LinPlacement

open CFSG CFSG.Assembly CFSG.StandardType Matrix
open CFSG.Open (IsElemAbelian)
open CFSG.StandardType.GGQ2Frame.LinBlocks

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {G : Type} [Group G] {H E : Subgroup G} {t : ℕ} {ε : Fin 2} {K : Type} [Field K]
  {hEN : E ≤ Subgroup.normalizer (H : Set G)}
  {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}

structure LinFrame (H E : Subgroup G) (hEN : E ≤ Subgroup.normalizer (H : Set G)) (K : Type)
    [Field K] (t : ℕ) (ε : Fin 2) (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) :
    Type where
  π : ↥H →* GL (LinIdx t ε) K
  surj : Function.Surjective π
  ker_le : π.ker ≤ Subgroup.center ↥H
  τ : (Fin t → Multiplicative (ZMod 3)) ≃* ↥E
  intertwine : ∀ (u : Fin t → Multiplicative (ZMod 3)) (h : ↥H),
    π (H.normalizerMonoidHom ⟨((τ u : ↥E) : G), hEN (τ u).2⟩ h) =
      linTorus ζ t ε u * π h * (linTorus ζ t ε u)⁻¹

@[expose] def LinFrame.coord (fr : LinFrame H E hEN K t ε ζ) : Additive ↥E ≃+ PlaneRaw.V t where
  toFun x := fun i => Multiplicative.toAdd (fr.τ.symm (Additive.toMul x) i)
  invFun u := Additive.ofMul (fr.τ (fun i => Multiplicative.ofAdd (u i)))
  left_inv x := by simp
  right_inv u := by ext i; simp
  map_add' x y := by ext i; simp

@[expose] def LinFrame.rho (fr : LinFrame H E hEN K t ε ζ) : ↥E →* GL (LinIdx t ε) K :=
  (linTorus ζ t ε).comp fr.τ.symm.toMonoidHom

@[expose] def LinFrame.component (fr : LinFrame H E hEN K t ε ζ) (c : PlaneRaw.Code t) :
    Subgroup G :=
  (⁅(Ycode ζ t ε c).comap fr.π, (Ycode ζ t ε c).comap fr.π⁆).map H.subtype

structure LinCtx (H E : Subgroup G) (hEN : E ≤ Subgroup.normalizer (H : Set G)) (K : Type)
    [Field K] (t : ℕ) (ε : Fin 2) (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) :
    Type where
  fr : LinFrame H E hEN K t ε ζ
  hK : Nat.card K = 2
  hζ : Function.Injective ζ
  hHp : commutator H = ⊤
  hEab : IsElemAbelian 3 E
  hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥H)
  hEH : E ≤ H
  ht : 3 ≤ t
  innerDiag : GGInnerDiagOnLabel (fun _ lab => lab = planeAmbientLabel (.linear ε) t) 3 E H

end

end CFSG.StandardType.GGQ2Frame.LinPlacement

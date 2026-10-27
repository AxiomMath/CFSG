module

public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogue
public import CFSG.LocalAnalysis.StandardType.GGQ2SpFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksDefs

public section

namespace CFSG.StandardType.GGQ2Frame.SpPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin Matrix
open CFSG.Open (StatedSp IsElemAbelian)
open CFSG.StandardType.GGQ2Frame.SpBlocks

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {G : Type} [Group G] [Finite G] {H E : Subgroup G} {m : ℕ}
  {K : Type} [Field K] [Finite K] [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
  {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}

@[expose] def SpFrame.coord (fr : SpFrame H E hEN K m ζ) : Additive ↥E ≃+ PlaneRaw.V m where
  toFun x := fun i => Multiplicative.toAdd (fr.τ.symm (Additive.toMul x) i)
  invFun u := Additive.ofMul (fr.τ (fun i => Multiplicative.ofAdd (u i)))
  left_inv x := by simp
  right_inv u := by ext i; simp
  map_add' x y := by ext i; simp

@[expose] def SpFrame.rho (fr : SpFrame H E hEN K m ζ) : ↥E →* ↥(StatedSp m K) :=
  (spPlaneTorus m ζ).comp fr.τ.symm.toMonoidHom

@[expose] def SpFrame.component (fr : SpFrame H E hEN K m ζ) (c : PlaneRaw.Code m) : Subgroup G :=
  (⁅(Ycode ζ m c).comap fr.π, (Ycode ζ m c).comap fr.π⁆).map H.subtype

structure SpCtx (H E : Subgroup G) (hEN : E ≤ Subgroup.normalizer (H : Set G)) (K : Type) [Field K]
    (m : ℕ) (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) : Type where
  fr : SpFrame H E hEN K m ζ
  hK : Nat.card K = 2
  hζ : Function.Injective ζ
  hHp : commutator H = ⊤
  hEab : IsElemAbelian 3 E
  hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥H)
  hEH : E ≤ H
  hm : 3 ≤ m
  innerDiag : GGInnerDiagOnLabel (fun _ lab => lab = planeAmbientLabel .symplectic m) 3 E H

end

end CFSG.StandardType.GGQ2Frame.SpPlacement

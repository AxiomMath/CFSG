module

public import CFSG.Quasithin.EmptyFaithful.ModHBr

public section

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.R3c14

@[expose] def SolvNineNS (X : Type) [Group X] : Prop := ¬ Group.IsSolvable X → SolvNine X

section Main

variable {G : Type} [Group G] [Finite G]

theorem not_isSolvable_of_ctx {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) {X : Type} [Group X] (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* X) :
    ¬ Group.IsSolvable X := by
  intro hX
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hpc := SBd13.pCore_eq_center_of_center_eq hZ
  obtain ⟨-, hs, a, b, hab⟩ := c.c33.quasisimple
  have hsolv : Group.IsSolvable (↥L ⧸ Subgroup.center ↥L) := by
    have e' : (↥L ⧸ Subgroup.center ↥L) ≃* X := (QuotientGroup.quotientMulEquivOfEq hpc.symm).trans e
    have := hX
    exact Group.isSolvable_of_isSolvable_injective (f := e'.toMonoidHom) e'.injective
  have := hs
  exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := ↥L ⧸ Subgroup.center ↥L)).2 hsolv a b)

theorem false_of_solvNineNS {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hN : I ≤ Subgroup.normalizer (L : Set G)) (hYL : Yp ≤ L)
    {X : Type} [Group X] (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* X) (hX : SolvNineNS X) : False :=
  false_of_solvNine c hN hYL e (hX (not_isSolvable_of_ctx c e))

end Main

end CFSG.Quasithin.ModH

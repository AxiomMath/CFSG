module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PairProj
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.KAPIDeg
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Basic

public section

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T516

open AChief SolQuot CFSG.SignalizerFunctorTheorem.Nonsolvable

theorem kOf_map_eq_self {H : Type*} [Group H] [Finite H] {Γ' : Type*} [Group Γ']
    {X : Subgroup H} (hX : kOf X = X) (f : H →* Γ') : kOf (X.map f) = X.map f :=
  (kOf_eq_self_iff_oStar_eq_top _).mpr (Near.KAPI.oStar_eq_top_of_surjective
    ((kOf_eq_self_iff_oStar_eq_top X).mp hX) (f := f.subgroupMap X) (f.subgroupMap_surjective X))

theorem kOf_qimg_eq_self {Γ : Type u} [Group Γ] [Finite Γ] {N X : Subgroup Γ} (hXN : X ≤ nrm N)
    (hK : kOf X = X) : kOf (qimg N X) = qimg N X :=
  (kOf_eq_self_iff_oStar_eq_top _).mpr (Near.KAPI.oStar_eq_top_of_surjective
    ((kOf_eq_self_iff_oStar_eq_top X).mp hK) (qres_surjective hXN))

theorem kOf_proj_eq_self {Γ : Type*} [Group Γ] [Finite Γ] {K L W X : Subgroup Γ}
    (h : IsDirectPair K L W) (hXW : X ≤ W) (hK : kOf X = X) :
    kOf (proj K L X) = proj K L X := by
  have hX' : kOf (X.subgroupOf W) = X.subgroupOf W :=
    (kOf_eq_self_iff_oStar_eq_top _).mpr (Near.KAPI.oStar_eq_top_of_surjective
      ((kOf_eq_self_iff_oStar_eq_top X).mp hK)
      (f := (Subgroup.subgroupOfEquivOfLe hXW).symm.toMonoidHom) (MulEquiv.surjective _))
  rw [proj_eq_map_pairProj h hXW, Subgroup.map_map]
  exact kOf_map_eq_self hX' _

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T516

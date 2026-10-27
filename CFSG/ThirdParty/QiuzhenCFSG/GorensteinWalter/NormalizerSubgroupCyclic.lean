module
public import Mathlib.GroupTheory.Complement
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG
noncomputable section
namespace CFSG.GorensteinWalter
universe u
open scoped Pointwise

public theorem normalizer_subgroupOf_eq_subgroupOf_inf_normalizer
    {H : Type u} [Group H]
    (J P : Subgroup H) (hPleJ : P ≤ J) :
    Subgroup.normalizer (P.subgroupOf J : Set J) =
      (J ⊓ Subgroup.normalizer (P : Set H)).subgroupOf J := by
  have hPmap : (P.subgroupOf J).map J.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPleJ]
  have hconv : ∀ d : J, J.subtype.comp (MulAut.conj d).toMonoidHom =
      (MulAut.conj (d : H)).toMonoidHom.comp J.subtype := by
    intro d
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have htransfer : ∀ d : J,
      (P.subgroupOf J).map (MulAut.conj d).toMonoidHom = P.subgroupOf J ↔
        P.map (MulAut.conj (d : H)).toMonoidHom = P := by
    intro d
    have hleft :
        ((P.subgroupOf J).map (MulAut.conj d).toMonoidHom = P.subgroupOf J) ↔
          (((P.subgroupOf J).map (MulAut.conj d).toMonoidHom).map J.subtype =
            (P.subgroupOf J).map J.subtype) := by
      constructor
      · intro h; rw [h]
      · intro h; exact Subgroup.map_injective J.subtype_injective h
    have hsimpl :
        ((P.subgroupOf J).map (MulAut.conj d).toMonoidHom).map J.subtype =
          P.map (MulAut.conj (d : H)).toMonoidHom := by
      calc
        ((P.subgroupOf J).map (MulAut.conj d).toMonoidHom).map J.subtype =
            (P.subgroupOf J).map
              (J.subtype.comp (MulAut.conj d).toMonoidHom) := by
                rw [Subgroup.map_map]
        _ = (P.subgroupOf J).map
            ((MulAut.conj (d : H)).toMonoidHom.comp J.subtype) := by rw [hconv d]
        _ = ((P.subgroupOf J).map J.subtype).map
            (MulAut.conj (d : H)).toMonoidHom := by rw [Subgroup.map_map]
        _ = P.map (MulAut.conj (d : H)).toMonoidHom := by rw [hPmap]
    rw [hleft, hsimpl, hPmap]
  ext d
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hd
    refine ⟨d.2, ?_⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact (htransfer d).1 (Subgroup.mem_normalizer_iff_map_conj_eq.mp hd)
  · intro hd
    rcases hd with ⟨hd1, hd2⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact (htransfer d).2 (Subgroup.mem_normalizer_iff_map_conj_eq.mp hd2)

public theorem isCyclic_normalizer_subgroupOf
    {H : Type u} [Group H] [Finite H]
    (J P : Subgroup H) (hPleJ : P ≤ J)
    (hNcyc : IsCyclic (Subgroup.normalizer (P : Set H))) :
    IsCyclic (Subgroup.normalizer (P.subgroupOf J : Set J)) := by
  have hnormeq :=
    normalizer_subgroupOf_eq_subgroupOf_inf_normalizer J P hPleJ
  let eN : Subgroup.normalizer (P.subgroupOf J : Set J) ≃*
      (J ⊓ Subgroup.normalizer (P : Set H)).subgroupOf J := by
    rw [hnormeq]
  let I : Subgroup H := J ⊓ Subgroup.normalizer (P : Set H)
  have hInfcyc : IsCyclic (I.subgroupOf J) := by
    let eInf : I.subgroupOf J ≃* I :=
      Subgroup.subgroupOfEquivOfLe (H := I) (K := J) inf_le_left
    have hcycInf : IsCyclic I := by
      letI : IsCyclic (Subgroup.normalizer (P : Set H)) := hNcyc
      exact Subgroup.isCyclic_of_le inf_le_right
    exact (MulEquiv.isCyclic eInf).mpr hcycInf
  exact (MulEquiv.isCyclic eN).mpr hInfcyc

end CFSG.GorensteinWalter

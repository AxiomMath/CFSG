module

public import CFSG.LocalAnalysis.SteinbergCCCComponentIsomorphism
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis

open CFSG Subgroup CFSG.ComponentClassification.OuterAutomorphisms

theorem map_conj_map_conj_eq {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      H.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one_eq {G : Type*} [Group G] (H : Subgroup G) :
    H.map (MulAut.conj (1 : G)).toMonoidHom = H := by
  rw [map_one]
  exact Subgroup.map_id H

@[expose] noncomputable def cComponentConjAction (G : Type*) [Group G] :
    G →* Equiv.Perm {L : Subgroup G // IsCComponent L} where
  toFun g :=
    { toFun := fun L => ⟨L.1.map (MulAut.conj g).toMonoidHom,
        CComponentIsomorphism.map (MulAut.conj g) L.2⟩
      invFun := fun L => ⟨L.1.map (MulAut.conj g⁻¹).toMonoidHom,
        CComponentIsomorphism.map (MulAut.conj g⁻¹) L.2⟩
      left_inv := fun L => Subtype.ext <| by
        simp only [map_conj_map_conj_eq, inv_mul_cancel, map_conj_one_eq]
      right_inv := fun L => Subtype.ext <| by
        simp only [map_conj_map_conj_eq, mul_inv_cancel, map_conj_one_eq] }
  map_one' := Equiv.ext fun L => Subtype.ext (map_conj_one_eq L.1)
  map_mul' g h := Equiv.ext fun L => Subtype.ext (map_conj_map_conj_eq L.1 g h).symm

@[simp] theorem cComponentConjAction_apply_coe {G : Type*} [Group G] (g : G)
    (L : {L : Subgroup G // IsCComponent L}) :
    ((cComponentConjAction G g L : {L : Subgroup G // IsCComponent L}) : Subgroup G) =
      L.1.map (MulAut.conj g).toMonoidHom :=
  rfl

theorem eq_bot_of_isPerfect_of_isSolvable {G : Type*} [Group G] {S : Subgroup G}
    (hp : Group.IsPerfect S) (hs : Group.IsSolvable S) : S = ⊥ := by
  by_contra h
  have : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr h
  exact Group.IsPerfect.not_isSolvable S hs

end CFSG.LocalAnalysis

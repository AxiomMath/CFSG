module

public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.Constraint

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG

theorem odd_card_radical_residual_of_solvable_normal {Y : Type*} [Group Y] [Finite Y]
    (h : ∀ V : Subgroup Y, V.Normal → Group.IsSolvable ↥V → Odd (Nat.card ↥V)) :
    Odd (Nat.card ↥(solvableRadical ↥(perfectResidual Y))) := by
  classical
  set P : Subgroup Y := perfectResidual Y with hP
  set R : Subgroup ↥P := solvableRadical ↥P with hR
  have hRs : Group.IsSolvable ↥R := CFSG.ABGLocalTools.solvableRadical_isSolvable
  let V : Subgroup Y := R.map P.subtype
  have hVcard : Nat.card ↥V = Nat.card ↥R := Subgroup.card_map_of_injective P.subtype_injective
  have hVsolv : Group.IsSolvable ↥V := by
    let e := R.equivMapOfInjective P.subtype P.subtype_injective
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hVn : V.Normal := by
    refine ⟨fun v hv y => ?_⟩
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hv
    have hmap : P.map (MulAut.conj y).toMonoidHom = P :=
      CFSG.LieType.SteinbergBR.perfectResidual_map_equiv (MulAut.conj y)
    let c : ↥P ≃* ↥P :=
      (Subgroup.equivMapOfInjective P (MulAut.conj y).toMonoidHom
        (MulAut.conj y).injective).trans (MulEquiv.subgroupCongr hmap)
    have hc : ∀ p : ↥P, ((c p : ↥P) : Y) = y * (p : Y) * y⁻¹ := fun p => rfl
    have h1 : c r ∈ R := by
      have := CFSG.LieType.SteinbergBR.solvableRadical_map_equiv c
      rw [← hR] at this
      rw [← this]
      exact Subgroup.mem_map_of_mem _ hr
    exact ⟨c r, h1, by rw [Subgroup.coe_subtype, hc]⟩
  rw [← hVcard]
  exact h V hVn hVsolv

end CFSG.RankThree.PartOne.F106

module

public import CFSG.Open.FusionDefs
public import CFSG.Quasithin.Background.A1bBasic
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Over

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Quasithin Subgroup

theorem isSolvable_or_le_of_bender {Y : Type} [Group Y] [Finite Y]
    {E : Subgroup Y} [E.Normal] (hB : fusionIsBenderGroup ↥E) (hq : Group.IsSolvable (Y ⧸ E))
    {T X : Subgroup Y} (hT : IsSylowIn 2 T ⊤) (hTX : T ≤ X) :
    Group.IsSolvable ↥X ∨ E ≤ X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTE : IsSylowIn 2 (T ⊓ E) E := hT.inf_normal le_top inferInstance
  have hUM : (hTE.toSylow : Subgroup ↥E) ≤ X.subgroupOf E := by
    intro x hx
    rw [IsSylowIn.coe_toSylow, mem_subgroupOf] at hx
    exact mem_subgroupOf.mpr (hTX hx.1)
  by_cases hM : X.subgroupOf E = ⊤
  · exact Or.inr (subgroupOf_eq_top.mp hM)
  left
  haveI : IsSimpleGroup ↥E :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  haveI : Group.IsSolvable ↥(X.subgroupOf E) :=
    CFSG.QuasithinUnique.Unc25G2.A312Sub.bender_overgroups hB hTE.toSylow hUM hM
  let f : ↥(X.subgroupOf E) →* ↥X :=
    (E.subtype.comp (X.subgroupOf E).subtype).codRestrict X fun m => m.2
  let g : ↥X →* Y ⧸ E := (QuotientGroup.mk' E).comp X.subtype
  refine Group.isSolvable_of_ker_le_range f g fun x hx => ?_
  have hxE : (x : Y) ∈ E := (QuotientGroup.eq_one_iff (x : Y)).mp (MonoidHom.mem_ker.mp hx)
  exact ⟨⟨⟨x, hxE⟩, x.2⟩, rfl⟩

end CFSG.LocalAnalysis.WeakClosure81

end

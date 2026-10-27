module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

namespace CFSG
end CFSG
open CFSG

/-!
# Intersecting a `p`-subgroup with a normal nilpotent subgroup

The `p`-part of a normal nilpotent subgroup is characteristic, hence normal
in the ambient group.  This puts the intersection with any ambient
`p`-subgroup inside the ambient `p`-core.
-/

namespace CFSG.GorensteinWalter

universe u

/-- If `F` is normal and nilpotent, the part of an ambient `p`-subgroup
lying in `F` is contained in the ambient `p`-core. -/
public theorem pSubgroup_inf_normal_nilpotent_le_pCore
    {X : Type u} [Group X] [Finite X]
    (U F : Subgroup X) (p : ℕ)
    (hp : p.Prime)
    (hUp : IsPGroup p U)
    (hFnormal : F.Normal)
    (hFnil : Group.IsNilpotent F) :
    U ⊓ F ≤ pCore p X := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hIFp : IsPGroup p (↑(U ⊓ F)) := hUp.to_inf_left
  have hIFpF : IsPGroup p (↑((U ⊓ F).subgroupOf F)) :=
    hIFp.of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (H := U ⊓ F) (K := F) (show U ⊓ F ≤ F from inf_le_right)).symm
  obtain ⟨S, hIFleS⟩ :=
    IsPGroup.exists_le_sylow (G := F) (p := p) hIFpF
  have hSnormal : (S : Subgroup F).Normal :=
    Group.IsNilpotent.sylow_normal (p := p) hFnil S
  have hIFleCoreF : (U ⊓ F).subgroupOf F ≤ pCore p F :=
    hIFleS.trans (le_sSup ⟨hSnormal, S.isPGroup'⟩)
  let P : Subgroup X := (pCore p F).map F.subtype
  have hIFleP : U ⊓ F ≤ P := by
    have hmap := Subgroup.map_mono (f := F.subtype) hIFleCoreF
    have hmapEq : ((U ⊓ F).subgroupOf F).map F.subtype = U ⊓ F :=
      Subgroup.map_subgroupOf_eq_of_le (show U ⊓ F ≤ F from inf_le_right)
    simpa [P, hmapEq] using hmap
  have hFinTop : IsNormalIn F (⊤ : Subgroup X) := by
    refine ⟨le_top, ?_⟩
    intro g _hg x hx
    exact hFnormal.conj_mem x hx g
  have hPnormalInTop : IsNormalIn P (⊤ : Subgroup X) := by
    simpa [P] using
      (map_characteristic_isNormalIn_of_isNormalIn
        (H := F) (N := (⊤ : Subgroup X)) (pCore p F)
        (pCore_characteristic (p := p)) hFinTop)
  have hPnormal : P.Normal :=
    (Subgroup.normalizer_eq_top_iff).mp
      (top_le_iff.mp (le_normalizer_of_isNormalIn hPnormalInTop))
  have hPp : IsPGroup p P := by
    simpa [P] using
      (IsPGroup.map (p := p) (H := pCore p F)
        (pCore_isPGroup (G := F) (p := p)) F.subtype)
  have hPleCore : P ≤ pCore p X := le_sSup ⟨hPnormal, hPp⟩
  exact hIFleP.trans hPleCore

end CFSG.GorensteinWalter

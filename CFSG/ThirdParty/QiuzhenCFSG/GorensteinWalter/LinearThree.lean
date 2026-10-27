module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearULift

namespace CFSG
end CFSG
open CFSG

universe u

namespace CFSG.GorensteinWalter

noncomputable section

private lemma hasCyclicOrDihedral_of_hasDihedral_linear {G : Type u} [Group G]
    (h : HasDihedralSylowTwo G) : HasCyclicOrDihedralSylowTwo G := by
  intro S
  exact Or.inr (h S)

/-- D-group closure for the `PSL(2,3)` branch, with all universe-heavy terms
pre-elaborated in this small module. -/
public theorem isDGroup_of_iso_PSL2_three
    {G : Type u} [Group G] [Finite G]
    (hcore : pPrimeCore 2 G = ⊥)
    (hSylow : HasDihedralSylowTwo G)
    (e : Nonempty (G ≃* PSL2 (ZMod 3))) : IsDGroup G := by
  let : Field (ZMod 3) := inferInstance
  let : Field (ULift.{u} (ZMod 3)) := ULift.field
  refine IsDGroup.quotientHasLinearNormalSubgroup
    (hasCyclicOrDihedral_of_hasDihedral_linear hSylow) (ULift (ZMod 3)) ?_
    (⊤ : Subgroup (G ⧸ pPrimeCore 2 G)) inferInstance (by simp) ?_
  · exact ⟨3, 1, Nat.prime_three, by decide, by omega, by simp⟩
  · left
    refine ⟨Subgroup.topEquiv.trans ?_⟩
    exact ((QuotientGroup.quotientMulEquivOfEq (G := G) hcore).trans
      (QuotientGroup.quotientBot (G := G))).trans
        (e.some.trans (psl2ULiftEquiv (R := ZMod 3)).symm)

/-- D-group closure for the `PGL(2,3)` branch, with all universe-heavy terms
pre-elaborated in this small module. -/
public theorem isDGroup_of_iso_PGL2_three
    {G : Type u} [Group G] [Finite G]
    (hcore : pPrimeCore 2 G = ⊥)
    (hSylow : HasDihedralSylowTwo G)
    (e : Nonempty (G ≃* PGL2 (ZMod 3))) : IsDGroup G := by
  let : Field (ZMod 3) := inferInstance
  let : Field (ULift.{u} (ZMod 3)) := ULift.field
  refine IsDGroup.quotientHasLinearNormalSubgroup
    (hasCyclicOrDihedral_of_hasDihedral_linear hSylow) (ULift (ZMod 3)) ?_
    (⊤ : Subgroup (G ⧸ pPrimeCore 2 G)) inferInstance (by simp) ?_
  · exact ⟨3, 1, Nat.prime_three, by decide, by omega, by simp⟩
  · right
    refine ⟨Subgroup.topEquiv.trans ?_⟩
    exact ((QuotientGroup.quotientMulEquivOfEq (G := G) hcore).trans
      (QuotientGroup.quotientBot (G := G))).trans
        (e.some.trans (pgl2ULiftEquiv (R := ZMod 3)).symm)

end

end CFSG.GorensteinWalter

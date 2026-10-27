module

public import CFSG.LieType.Universal.Spin.Twisted.Frame
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import CFSG.ClassicalGroups.PCoreSection
public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizer
public import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer
public import CFSG.LieType.Universal.Spin.Chevalley.Odd
public import CFSG.LieType.Universal.SpinOmega.Range
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType.RCKC1

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.Open

variable {K : Type} [Field K] {m : ℕ} {b c : K}

theorem rckSOmM_spinAction_twShortRoot_eq_eichler
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) (i : Fin (m - 1)) (s : Bool) (p : Fin 2 → K) :
    spinAction (quadMinus m K b c) (twShortRoot m hirr i s (.ofAdd p)) =
      eichler (quadMinus m K b c) (minusVec m i s) (planeVec m p) := by
  refine LinearEquiv.ext fun v => ?_
  rw [spinAction_twShortRoot, eichler_apply (quadMinus_minusVec m b c i s)
    (polar_minusVec_planeVec m b c i s p), quadMinus_planeVec']
  module

theorem rckSOmM_spinAction_injective [Finite K] [CharP K 2]
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) :
    Function.Injective (spinAction (quadMinus m K b c)) := by
  rw [← MonoidHom.ker_eq_bot_iff, ← ker_spinMatrix,
    ker_spinMatrix_quadMinus_eq_bot hirr CharTwo.two_eq_zero]

private theorem rckSOmM_spinAction_twShortRoot_mem_rootGroup
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) (i : Fin (m - 1)) (s : Bool) (p : Fin 2 → K) :
    spinAction (quadMinus m K b c) (twShortRoot m hirr i s (.ofAdd p)) ∈
      rootGroup (quadMinus m K b c) (minusVec m i s) :=
  mem_rootGroup.mpr ⟨planeVec m p, polar_minusVec_planeVec m b c i s p,
    (rckSOmM_spinAction_twShortRoot_eq_eichler hirr i s p).symm⟩

private theorem rckSOmM_shortRootRange_le_comap
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) (i : Fin (m - 1)) (s : Bool) :
    (twShortRoot m hirr i s).range ≤
      (rootGroup (quadMinus m K b c) (minusVec m i s)).comap
        (spinAction (quadMinus m K b c)) := by
  rintro g ⟨p, rfl⟩
  rw [Subgroup.mem_comap]
  exact rckSOmM_spinAction_twShortRoot_mem_rootGroup hirr i s p.toAdd

theorem rckSOmM_rootGroup_comap_le_centralizer
    [Finite K] [CharP K 2] (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) {m : ℕ}
    (i : Fin (m - 1)) (s : Bool) :
    (rootGroup (quadMinus m K b c) (minusVec m i s)).comap
        (spinAction (quadMinus m K b c)) ≤
      Subgroup.centralizer ((twShortRoot m hirr i s).range :
        Set (spinGroup (quadMinus m K b c))) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hg' : spinAction (quadMinus m K b c) g ∈ rootGroup (quadMinus m K b c)
      (minusVec m i s) := Subgroup.mem_comap.mp hg
  have hr' : spinAction (quadMinus m K b c) r ∈ rootGroup (quadMinus m K b c)
      (minusVec m i s) := rckSOmM_shortRootRange_le_comap hirr i s hr
  refine rckSOmM_spinAction_injective hirr ?_
  rw [map_mul, map_mul]
  exact (rootGroup_commute hg' hr').symm

theorem rckSOmM_core_of_pCore
    [Finite K] [CharP K 2] (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) {m : ℕ}
    {i : Fin (m - 1)} {s : Bool} {p : Fin 2 → K}
    (hcore : pCoreOf 2 (Subgroup.centralizer
        ({twShortRoot m hirr i s (.ofAdd p)} : Set (spinGroup (quadMinus m K b c)))) ≤
      (rootGroup (quadMinus m K b c) (minusVec m i s)).comap
        (spinAction (quadMinus m K b c))) :
    pCoreOf 2 (Subgroup.centralizer
        ({twShortRoot m hirr i s (.ofAdd p)} : Set (spinGroup (quadMinus m K b c)))) ≤
      Subgroup.centralizer ((twShortRoot m hirr i s).range :
        Set (spinGroup (quadMinus m K b c))) :=
  hcore.trans (rckSOmM_rootGroup_comap_le_centralizer hirr i s)

end CFSG.StandardType.RCKC1

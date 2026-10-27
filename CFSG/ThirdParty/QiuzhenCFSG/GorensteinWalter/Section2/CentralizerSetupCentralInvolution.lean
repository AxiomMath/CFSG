module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralUniqueCentralInvolution

namespace CFSG
end CFSG
open CFSG

/-!
# The central involution in a Section 2 setup

The distinguished involution is the central rotation in every chosen
dihedral model of the fixed Sylow `2`-subgroup.
-/

namespace CFSG.GorensteinWalter

universe u

/-- In a dihedral model of order at least eight, the distinguished setup
involution is the transported central rotation. -/
public theorem centralizerSetup_t_eq_dihedralCentralRotation
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (hm : 2 ≤ c.m)
    (e : c.S ≃* DihedralGroup (2 ^ c.m)) :
    c.t = ((e.symm (DihedralGroup.r
      (2 ^ (c.m - 1) : ZMod (2 ^ c.m))) : c.S) : G) := by
  let tS : c.S := ⟨c.t, c.S0_le_S c.t_mem_S0⟩
  have htcenterS : tS ∈ Subgroup.center (c.S : Subgroup G) := by
    apply Subgroup.mem_center_iff.mpr
    intro s
    apply Subtype.ext
    have hsH : (s : G) ∈ c.H := centralizerSetup_S_le_H c s.property
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_iff] at hsH
    exact (hsH c.t (by simp)).symm
  have htcenter : e tS ∈ Subgroup.center (DihedralGroup (2 ^ c.m)) := by
    rw [Subgroup.mem_center_iff]
    intro x
    calc
      x * e tS = e (e.symm x * tS) := by simp
      _ = e (tS * e.symm x) := by
        rw [Subgroup.mem_center_iff.mp htcenterS (e.symm x)]
      _ = e tS * x := by simp
  have htS2 : tS ^ 2 = 1 := by
    apply Subtype.ext
    exact c.t_involution.2
  have ht2 : (e tS) ^ 2 = 1 := by
    simpa using congrArg e htS2
  have ht1 : e tS ≠ 1 := by
    intro h
    apply c.t_involution.1
    have htS1 : tS = 1 := e.injective (by simpa using h)
    exact congrArg Subtype.val htS1
  have heq := unique_central_involution_of_dihedral_two_pow hm (e tS)
    htcenter ht2 ht1
  have htS : tS = e.symm (DihedralGroup.r
      (2 ^ (c.m - 1) : ZMod (2 ^ c.m))) := by
    apply e.injective
    simpa using heq
  exact congrArg Subtype.val htS

end CFSG.GorensteinWalter

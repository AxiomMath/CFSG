module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SA9Defs
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PermPerfectCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open Equiv Equiv.Perm Subgroup

theorem mem_a9Alt6_of_perfect {P : Subgroup (alternatingGroup (Fin 9))} (hP : Group.IsPerfect P)
    (hPc : ∀ p ∈ P, p * a9fT0 = a9fT0 * p) : P ≤ a9fAlt6 := by
  set H : Subgroup (Perm (Fin 9)) := P.map (alternatingGroup (Fin 9)).subtype with hHdef
  have hPP : ⁅P, P⁆ = P := Subgroup.isPerfect_iff.mp hP
  have hH : ⁅H, H⁆ = H := by
    rw [hHdef, ← Subgroup.map_commutator, hPP]
  have hg3 : (a9fT0 : Perm (Fin 9)) ^ 3 = 1 := by decide
  have hgH : ∀ h ∈ H, Commute (a9fT0 : Perm (Fin 9)) h := by
    intro h hh
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hh
    exact (congrArg Subtype.val (hPc p hp)).symm
  have hfix := CFSG.HardMathSupport.Curtis.UnitaryLevi.fixes_of_commute_three (α := Fin 9)
    (by simp) hH hg3 hgH
  have key : ∀ x : Fin 9, x ∉ a9fS → (a9fT0 : Perm (Fin 9)) x ≠ x := by decide
  intro p hp
  have hpH : ((p : alternatingGroup (Fin 9)) : Perm (Fin 9)) ∈ H :=
    Subgroup.mem_map.mpr ⟨p, hp, rfl⟩
  rw [a9fAlt6, alternatingGroup.mem_range_ofSubtype_iff]
  intro x hx
  by_contra hxS
  exact (Equiv.Perm.mem_support.mp hx) (hfix _ hpH x (key x hxS))

end CFSG.RankThree.PartTwo.Sec8.Hering611

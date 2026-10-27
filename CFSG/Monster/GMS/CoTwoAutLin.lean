module

public import CFSG.Assembly.Defs
public import CFSG.Monster.GMS.CoTwoModule

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module hiding co1Act

namespace CoTwoAutLin

theorem exists_dual_vec
    {v : Fin 24 → ZMod 2} (hv : v ≠ 0) {F : (Fin 24 → ZMod 2) → ZMod 2}
    (hadd : ∀ a b, bil₀ a v = 0 → bil₀ b v = 0 → F (a + b) = F a + F b) (hFv : F v = 0) :
    ∃ m, bil₀ m v = 0 ∧ ∀ w, bil₀ w v = 0 → F w = bil₀ w m := by
  obtain ⟨u₀, hu₀⟩ := Leech.exists_bil₀_eq_one hv
  have hu₀' : bil₀ u₀ v = 1 := by rw [bil₀_comm]; exact hu₀
  have hproj : ∀ y, bil₀ (y + bil₀ y v • u₀) v = 0 := fun y => by
    rw [Leech.bil₀_add_left, CoTwoModule.bil₀_smul_left, hu₀', mul_one]
    exact CharTwo.add_self_eq_zero _
  let F' : (Fin 24 → ZMod 2) → ZMod 2 := fun y => F (y + bil₀ y v • u₀)
  have hF'add : ∀ a b, F' (a + b) = F' a + F' b := fun a b => by
    show F ((a + b) + bil₀ (a + b) v • u₀) = F (a + bil₀ a v • u₀) + F (b + bil₀ b v • u₀)
    rw [← hadd _ _ (hproj a) (hproj b), Leech.bil₀_add_left, add_smul]
    exact congrArg F (add_add_add_comm _ _ _ _)
  obtain ⟨m, hm⟩ := Leech.exists_bil₀_eq_of_additive hF'add
  have hF'perp : ∀ w, bil₀ w v = 0 → F' w = F w := fun w hw => by
    show F (w + bil₀ w v • u₀) = F w
    rw [hw, zero_smul, add_zero]
  refine ⟨m, ?_, fun w hw => ?_⟩
  · have h := hm v
    rw [hF'perp v (bil₀_self v), hFv] at h
    exact h.symm
  · rw [← hF'perp w hw, hm w, bil₀_comm]

end CoTwoAutLin

end CFSG.Monster.GMS

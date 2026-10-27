module

public import CFSG.LieType.Multipliers.U43Bridge
import CFSG.ClassicalGroups.Unitary.Simple

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.LieType.Multipliers.U43

theorem isSimpleGroup_X₀ : IsSimpleGroup X₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F9 3 1
    (by rw [Nat.card_eq_fintype_card, F9.card_eq]; norm_num) 4 (by norm_num) (by decide)
  rwa [pow_one] at h

theorem psi_inj : Function.Injective psi := by
  have := isSimpleGroup_X₀
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal psi.ker with h | h
  · exact h
  · exfalso
    have h1 : psi xElt = 1 := MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top xElt)
    have h2 := rep_tabA ⟨0, by norm_num⟩
    rw [h1] at h2
    have h3 : tabA[0]! = 288 := by decide +kernel
    simp [h3] at h2

end CFSG.Quasithin.H13.U43

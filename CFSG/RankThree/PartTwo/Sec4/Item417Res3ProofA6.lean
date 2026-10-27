module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

namespace Res417Three

set_option maxRecDepth 10000 in
theorem perm_six_pow_six : ∀ g : Equiv.Perm (Fin 6), Equiv.Perm.sign g = 1 → g ^ 6 = 1 →
    g ^ 2 = 1 ∨ g ^ 3 = 1 := by
  decide

theorem noSix_alternatingGroup_six : NoSix (alternatingGroup (Fin 6)) := by
  intro y t hy ht hyt
  have hc : Commute y t := hyt
  have hy6 : y ^ 6 = 1 := by
    calc y ^ 6 = (y ^ 3) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [hy, one_pow]
  have ht6 : t ^ 6 = 1 := by
    calc t ^ 6 = (t ^ 2) ^ 3 := by rw [← pow_mul]
      _ = 1 := by rw [ht, one_pow]
  have h6' : (y * t) ^ 6 = 1 := by rw [hc.mul_pow, hy6, ht6, one_mul]
  have h6 : ((y * t : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) ^ 6 = 1 := by
    rw [← Subgroup.coe_pow, h6', Subgroup.coe_one]
  have hsign : Equiv.Perm.sign ((y * t : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp (y * t).2
  rcases perm_six_pow_six _ hsign h6 with h2 | h3
  · left
    have h2' : (y * t) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h2)
    rw [hc.mul_pow, ht, mul_one] at h2'
    calc y = y ^ 3 * (y ^ 2)⁻¹ := by group
      _ = 1 := by rw [hy, h2']; group
  · right
    have h3' : (y * t) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h3)
    rw [hc.mul_pow, hy, one_mul] at h3'
    calc t = t ^ 3 * (t ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3', ht]; group

end Res417Three

open Res417Three

section Certs


theorem item417InA6_holds : Item417InA6 := by
  intro G _ _ L A E c m hconf ⟨e⟩
  exact (hconf.false_of_noSix (noSix_alternatingGroup_six.of_mulEquiv e)).elim

end Certs

end CFSG.RankThree.PartTwo.Sec4

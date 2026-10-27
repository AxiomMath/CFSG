module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

/-- Every odd-prime subgroup of a dihedral group is normal: it lies in the
rotation subgroup, and conjugation by a reflection acts there by inversion. -/
public theorem dihedral_odd_subgroup_normal
    {p z : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (P : Subgroup (DihedralGroup z)) (hPp : IsPGroup p P) : P.Normal := by
  refine ⟨?_⟩
  intro n hn g
  cases n with
  | r j =>
      cases g with
      | r i =>
          simpa [DihedralGroup.r_mul_r, DihedralGroup.r_zero,
            DihedralGroup.inv_r, mul_assoc] using hn
      | sr i =>
          have hinv : DihedralGroup.r (-j) ∈ P := by
            simpa using P.inv_mem hn
          simpa [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr,
            DihedralGroup.inv_sr, DihedralGroup.inv_r, mul_assoc] using hinv
  | sr j =>
      have hnne : (DihedralGroup.sr j : DihedralGroup z) ≠ 1 := by
        intro h
        have h' := congrArg DihedralGroup.equivSum h
        cases h'
      have hnne' : (⟨DihedralGroup.sr j, hn⟩ : P) ≠ 1 := by
        intro h
        apply hnne
        exact congrArg Subtype.val h
      have hdvd : p ∣ orderOf (DihedralGroup.sr j : DihedralGroup z) := by
        have h0 := hPp.dvd_orderOf hnne'
        have ho : orderOf (⟨DihedralGroup.sr j, hn⟩ : P) =
            orderOf (DihedralGroup.sr j : DihedralGroup z) := by
          exact (Subgroup.orderOf_coe
            (⟨DihedralGroup.sr j, hn⟩ : P)).symm
        rw [ho] at h0
        exact h0
      rw [DihedralGroup.orderOf_sr] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hp1 | hp2
      · exact False.elim ((Fact.out : Nat.Prime p).ne_one hp1)
      · exact False.elim (hpodd.not_two_dvd_nat (by rw [hp2]))

end CFSG.GorensteinWalter

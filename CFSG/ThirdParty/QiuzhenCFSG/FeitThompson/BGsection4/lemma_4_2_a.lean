module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Defs

namespace CFSG
end CFSG
open CFSG

open scoped commutatorElement

section Main

public theorem CFSG.lemma_4_2_a {G : Type*} [Group G] {x y : G} (n : ℕ) (hn : 1 < n)
    (hcomm : ⁅x, y⁆ ∈ Subgroup.center G) :
    ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n ∧ ⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n := by
  let _ := hn
  have hcomm' : ⁅y, x⁆ ∈ Subgroup.center G := by
    simpa [commutatorElement_inv] using (Subgroup.center G).inv_mem hcomm
  have hleft : ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
    have hxy :
        x ^ n * y = y * x ^ n * ⁅x, y⁆ ^ n :=
      pow_mul_eq_mul_pow_commutator_pow_of_mem_center (x := y) (y := x) hcomm n
    have hpow_cent : ⁅x, y⁆ ^ n ∈ Subgroup.center G := (Subgroup.center G).pow_mem hcomm n
    have hyc : y * ⁅x, y⁆ ^ n = ⁅x, y⁆ ^ n * y := (Subgroup.mem_center_iff.mp hpow_cent) y
    have hxnc : x ^ n * ⁅x, y⁆ ^ n = ⁅x, y⁆ ^ n * x ^ n :=
      (Subgroup.mem_center_iff.mp hpow_cent) (x ^ n)
    rw [commutatorElement_def, hxy]
    simp [mul_assoc, hyc, hxnc]
  have hrightAux : ⁅y ^ n, x⁆ = ⁅y, x⁆ ^ n := by
    have hyx :
        y ^ n * x = x * y ^ n * ⁅y, x⁆ ^ n :=
      pow_mul_eq_mul_pow_commutator_pow_of_mem_center (x := x) (y := y) hcomm' n
    have hpow_cent : ⁅y, x⁆ ^ n ∈ Subgroup.center G := (Subgroup.center G).pow_mem hcomm' n
    have hxc : x * ⁅y, x⁆ ^ n = ⁅y, x⁆ ^ n * x := (Subgroup.mem_center_iff.mp hpow_cent) x
    have hync : y ^ n * ⁅y, x⁆ ^ n = ⁅y, x⁆ ^ n * y ^ n :=
      (Subgroup.mem_center_iff.mp hpow_cent) (y ^ n)
    rw [commutatorElement_def, hyx]
    simp [mul_assoc, hxc, hync]
  have hright : ⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n := by
    calc
      ⁅x, y ^ n⁆ = (⁅y ^ n, x⁆)⁻¹ := by simp [commutatorElement_inv]
      _ = (⁅y, x⁆ ^ n)⁻¹ := by rw [hrightAux]
      _ = ⁅x, y⁆ ^ n := by
        have hyx : ⁅y, x⁆ = ⁅x, y⁆⁻¹ := by
          simp [commutatorElement_inv]
        calc
          (⁅y, x⁆ ^ n)⁻¹ = ((⁅x, y⁆⁻¹) ^ n)⁻¹ := by rw [hyx]
          _ = ((⁅x, y⁆ ^ n)⁻¹)⁻¹ := by rw [inv_pow]
          _ = ⁅x, y⁆ ^ n := by simp
  exact ⟨hleft, hright⟩

end Main

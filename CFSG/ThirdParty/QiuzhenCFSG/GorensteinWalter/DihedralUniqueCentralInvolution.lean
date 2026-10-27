module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The unique central involution of a dihedral two-group
-/

namespace CFSG.GorensteinWalter

/-- In a dihedral `2`-group with `m ≥ 2`, the only non-identity central
involution is the central rotation `r (2^(m-1))`. -/
public theorem unique_central_involution_of_dihedral_two_pow
    {m : ℕ} (hm : 2 ≤ m)
    (x : DihedralGroup (2 ^ m))
    (hxcenter : x ∈ Subgroup.center (DihedralGroup (2 ^ m)))
    (hxpow : x ^ 2 = 1) (hxne : x ≠ 1) :
    x = DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) := by
  rcases dihedralGroup_cases x with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · have hsq : DihedralGroup.r (i + i) = 1 := by
      simpa [pow_two, DihedralGroup.r_mul_r] using hxpow
    have hzero : i + i = 0 := by
      have h := (DihedralGroup.r.injEq (i + i) 0).mp hsq
      simpa using h
    have h2i : (2 : ZMod (2 ^ m)) * i = 0 := by
      rw [two_mul, hzero]
    rcases (zmod_two_mul_eq_zero_iff hm i).mp h2i with hi0 | hic
    · exfalso
      apply hxne
      rw [hi0]
      simp
    · rw [hic]
  · have hcomm : DihedralGroup.sr i * DihedralGroup.r 1 =
        DihedralGroup.r 1 * DihedralGroup.sr i :=
      (Subgroup.mem_center_iff.mp hxcenter (DihedralGroup.r 1)).symm
    have hieq : i + 1 = i - 1 := by
      simpa [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr] using hcomm
    have h2zero : (2 : ZMod (2 ^ m)) = 0 := by
      have hz := congrArg (fun z : ZMod (2 ^ m) => z - i) hieq
      have hone : (1 : ZMod (2 ^ m)) = -(1 : ZMod (2 ^ m)) := by
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz
      calc
        (2 : ZMod (2 ^ m)) =
            (1 : ZMod (2 ^ m)) + (1 : ZMod (2 ^ m)) := by norm_num
        _ = (1 : ZMod (2 ^ m)) + -(1 : ZMod (2 ^ m)) := by
          nth_rw 2 [hone]
        _ = 0 := by simp
    have h1mul : (2 : ZMod (2 ^ m)) * (1 : ZMod (2 ^ m)) = 0 := by
      rw [h2zero]
      simp
    rcases (zmod_two_mul_eq_zero_iff hm (1 : ZMod (2 ^ m))).mp h1mul with
      h10 | h1half
    · have hdvd : 2 ^ m ∣ 1 :=
        (ZMod.natCast_eq_zero_iff (1 : ℕ) (2 ^ m)).mp (by simpa using h10)
      have hle : 2 ≤ 2 ^ m := by
        calc
          2 ≤ 4 := by norm_num
          _ ≤ 2 ^ m :=
            Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 2 ≤ m)
      have hpow_le_one : 2 ^ m ≤ 1 :=
        Nat.le_of_dvd (by norm_num : 0 < 1) hdvd
      have htwo_le_one : 2 ≤ 1 := hle.trans hpow_le_one
      norm_num at htwo_le_one
    · have heqnat : ((1 : ℕ) : ZMod (2 ^ m)) =
          ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
        simpa using h1half
      have hval1 : (1 : ZMod (2 ^ m)).val = 1 := by
        rw [show (1 : ZMod (2 ^ m)) =
          ((1 : ℕ) : ZMod (2 ^ m)) by norm_num]
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by
          calc
            1 < 2 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right
              (by norm_num : 0 < 2) (by omega : 1 ≤ m))]
      have hvalh : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)).val =
          2 ^ (m - 1) := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt
          (Nat.pow_lt_pow_right (by norm_num : 1 < 2)
            (by omega : m - 1 < m))]
      have hnat : 1 = 2 ^ (m - 1) := by
        have h := congrArg ZMod.val heqnat
        have hval1' : ((1 : ℕ) : ZMod (2 ^ m)).val = 1 := by
          simpa using hval1
        rw [hval1'] at h
        rw [hvalh] at h
        exact h
      have hlt1 : 1 < 2 ^ (m - 1) := by
        calc
          1 < 2 := by norm_num
          _ ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right
            (by norm_num : 0 < 2) (by omega : 1 ≤ m - 1)
      omega

end CFSG.GorensteinWalter

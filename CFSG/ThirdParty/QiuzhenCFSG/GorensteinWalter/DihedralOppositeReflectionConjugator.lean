module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# An involutory conjugator for opposite dihedral reflections

This is the model calculation behind the involution `y ∈ C_G(st)` in the
component branch of Gorenstein--Walter Theorem 2.6.  Opposite reflections in
a dihedral `2`-group are interchanged by a reflection one quarter-turn away,
and that conjugator fixes their central half-rotation product.
-/

namespace CFSG.GorensteinWalter

/-- In a dihedral `2`-group of order at least eight, two reflections whose
product is the central half-rotation are conjugate by an involution which
centralizes that product. -/
public theorem exists_involution_conjugator_of_opposite_dihedral_reflections
    {m : ℕ} (hm : 2 ≤ m) (i j : ZMod (2 ^ m))
    (hprod : DihedralGroup.sr i * DihedralGroup.sr j =
      DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m))) :
    ∃ y : DihedralGroup (2 ^ m),
      IsInvolution y ∧
      y * DihedralGroup.sr i * y⁻¹ = DihedralGroup.sr j ∧
      y * (DihedralGroup.sr i * DihedralGroup.sr j) * y⁻¹ =
        DihedralGroup.sr i * DihedralGroup.sr j := by
  let h : ZMod (2 ^ m) := (2 ^ (m - 1) : ZMod (2 ^ m))
  let k : ZMod (2 ^ m) := (2 ^ (m - 2) : ZMod (2 ^ m))
  have hpowNat : 2 * 2 ^ (m - 2) = 2 ^ (m - 1) := by
    calc
      2 * 2 ^ (m - 2) = 2 ^ ((m - 2) + 1) := by rw [pow_succ']
      _ = 2 ^ (m - 1) := by congr 1; omega
  have hk : (2 : ZMod (2 ^ m)) * k = h := by
    have hcast := congrArg
      (fun n : ℕ => (n : ZMod (2 ^ m))) hpowNat
    simpa [h, k, Nat.cast_mul, Nat.cast_pow] using hcast
  have htwo : (2 : ZMod (2 ^ m)) * h = 0 :=
    (zmod_two_mul_eq_zero_iff hm h).mpr (Or.inr rfl)
  have hneg : -h = h := by
    apply neg_eq_iff_add_eq_zero.mpr
    simpa [two_mul] using htwo
  have hji : j - i = h := by
    apply DihedralGroup.r.inj
    simpa [h] using hprod
  have hj : j = i + h := by
    rw [← hji]
    abel
  let y : DihedralGroup (2 ^ m) := DihedralGroup.sr (i + k)
  have hyI : IsInvolution y := by
    constructor
    · intro hyone
      have hord := congrArg orderOf hyone
      simp [y, DihedralGroup.orderOf_sr] at hord
    · simp [y, pow_two]
  have hyconj :
      y * DihedralGroup.sr i * y⁻¹ = DihedralGroup.sr j := by
    dsimp [y]
    congr 1
    rw [hj, ← hk]
    ring
  have hycentral :
      y * (DihedralGroup.sr i * DihedralGroup.sr j) * y⁻¹ =
        DihedralGroup.sr i * DihedralGroup.sr j := by
    rw [hprod]
    change DihedralGroup.sr (i + k) * DihedralGroup.r h *
      (DihedralGroup.sr (i + k))⁻¹ = DihedralGroup.r h
    simp only [DihedralGroup.inv_sr, DihedralGroup.sr_mul_r,
      DihedralGroup.sr_mul_sr]
    congr 1
    calc
      i + k - (i + k + h) = -h := by ring
      _ = h := hneg
  exact ⟨y, hyI, hyconj, hycentral⟩

end CFSG.GorensteinWalter

module

public import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockFive
public import CFSG.OddTranspositions.PartThree.FiveReflectionFischer
public import CFSG.RankThree.GF2n.Tim79aSec2
public import CFSG.Timmesfeld.Bridge.OddLocalDefs

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix
open scoped Function

theorem exists_ne_zero_perp_five {k : ℕ} (hk : 2 ≤ k) (ε π : Bool)
    (v w : Fin (k + 1) → ZMod 5) :
    ∃ x : Fin (k + 1) → ZMod 5, x ≠ 0 ∧ fiveForm k ε x v = 0 ∧ fiveForm k ε x w = 0 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hk2 : (2 : ℕ) < k + 1 := by omega
  obtain ⟨x, hx0, hx⟩ :=
    CFSG.OddTranspositions.PartFour.TableE1Five.exists_ne_zero_perp
      (b := fiveBilin k ε π) (n := k + 1) (k := 2) hk2
      (fun i : Fin 2 => if i = 0 then v else w)
  have hxv : (fiveSignRep π)⁻¹ * fiveForm k ε x v = 0 := by
    simpa [fiveBilin_apply] using hx 0
  have hxw : (fiveSignRep π)⁻¹ * fiveForm k ε x w = 0 := by
    simpa [fiveBilin_apply] using hx 1
  exact ⟨x, hx0, (mul_eq_zero.mp hxv).resolve_left (inv_ne_zero (fiveSignRep_ne_zero π)),
    (mul_eq_zero.mp hxw).resolve_left (inv_ne_zero (fiveSignRep_ne_zero π))⟩

theorem ne_neg_of_mem_fiveReflections {k : ℕ} (hk : 2 ≤ k) {ε π : Bool}
    {r s : GL (Fin (k + 1)) (ZMod 5)} (hr : r ∈ fiveReflections k ε π)
    (hs : s ∈ fiveReflections k ε π) : s ≠ -r := by
  have h2ne : (2 : ZMod 5) ≠ 0 := by decide
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rintro hsr
  obtain ⟨v, _, -, hrv⟩ := hr
  obtain ⟨w, _, -, hsw⟩ := hs
  obtain ⟨x, hx0, hxv, hxw⟩ := exists_ne_zero_perp_five hk ε π v w
  have hrx : (r : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x = x := by
    rw [hrv x]
    simp [hxv]
  have hsx : (s : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x = x := by
    rw [hsw x]
    simp [hxw]
  have hneg : (s : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x =
      -((r : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x) := by
    simp only [hsr, Units.val_neg, Matrix.neg_mulVec]
    rfl
  rw [hsx, hrx] at hneg
  have hsum : x + x = 0 := (eq_neg_iff_add_eq_zero).mp hneg
  have h2 : (2 : ZMod 5) • x = 0 := by rw [two_smul, hsum]
  exact hx0 ((smul_eq_zero.mp h2).resolve_left h2ne)

end CFSG.OddTranspositions.PartThree

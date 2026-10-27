module

public import CFSG.LieType.Seitz.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RowsProof

theorem seitzHyperGamma_eq_top_of_closure {X : Type*} [Group X] {F : Subgroup (MulAut X)}
    (hF : ∀ φ ∈ F, φ ^ 3 = 1) (hF9 : Nat.card F = 9)
    (htop : Subgroup.closure {x : X | ∃ φ ∈ F, φ ≠ 1 ∧ φ x = x} = ⊤) :
    CFSG.LieType.Seitz.seitzHyperGamma 3 F = ⊤ := by
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  rintro x ⟨φ, hφF, hφ1, hφx⟩
  have hord : orderOf φ = 3 := orderOf_eq_prime (hF φ hφF) hφ1
  have hle : Subgroup.zpowers φ ≤ F := (Subgroup.zpowers_le).mpr hφF
  have hrel : (Subgroup.zpowers φ).relIndex F = 3 := by
    have h1 := Subgroup.relIndex_mul_card (H := Subgroup.zpowers φ) (K := F)
    rw [inf_eq_left.mpr hle, Nat.card_zpowers, hord, hF9] at h1
    omega
  have hfix : x ∈ CFSG.LieType.Seitz.fixedPoints (Subgroup.zpowers φ) := by
    rw [CFSG.LieType.Seitz.mem_fixedPoints]
    rintro ψ ⟨k, rfl⟩
    have hφk : ∀ n : ℕ, (φ ^ n) x = x := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, MulAut.mul_apply, hφx, ih]
    dsimp only
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · rw [zpow_natCast]
      exact hφk n
    · rw [zpow_neg, zpow_natCast]
      conv_lhs => rw [← hφk n]
      exact (φ ^ n).symm_apply_apply x
  exact (le_iSup₂_of_le (Subgroup.zpowers φ) ⟨hle, hrel⟩ le_rfl :
    CFSG.LieType.Seitz.fixedPoints (Subgroup.zpowers φ) ≤
      CFSG.LieType.Seitz.seitzHyperGamma 3 F) hfix

end CFSG.RankThree.PartTwo.Sec4.Item434RowsProof

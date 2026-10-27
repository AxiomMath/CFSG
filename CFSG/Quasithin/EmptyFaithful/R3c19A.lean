module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutionsAction

public section

namespace CFSG.Quasithin

namespace R3c19

open CFSG.Assembly.LowTwoRank CFSG.LinearGroups.UnitaryThreeOverNine

theorem isConj_of_u33_model {L : Type} [Group L] (h : StatedClassicalModel L .PSU 3 3 1) {a b : L}
    (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  obtain ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ := h
  have hF9 : Nat.card F = 9 := by simpa using hcard
  let e2 : L ≃* StatedProj (StatedSU 3 3 F) := e
  let e' : L ≃* StatedSU 3 3 F :=
    e2.trans ((QuotientGroup.quotientMulEquivOfEq
      (statedScalars_subgroupOf_statedSU_eq_bot hF9)).trans QuotientGroup.quotientBot)
  have h1 := isConj_of_orderOf_eq_two hF9 (a := e' a) (b := e' b)
    (by rw [MulEquiv.orderOf_eq]; exact ha) (by rw [MulEquiv.orderOf_eq]; exact hb)
  obtain ⟨c, hc⟩ := isConj_iff.1 h1
  exact isConj_iff.2 ⟨e'.symm c, e'.injective (by rw [map_mul, map_mul, map_inv]; simpa using hc)⟩

theorem exists_conj_of_u33_subgroup {G : Type} [Group G] {L : Subgroup G}
    (h : StatedClassicalModel ↥L .PSU 3 3 1) :
    ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ * l₁ = 1 → l₁ ≠ 1 → l₂ * l₂ = 1 → l₂ ≠ 1 →
      ∃ m ∈ L, m * l₁ * m⁻¹ = l₂ := by
  intro l₁ h₁ l₂ h₂ h11 h1 h22 h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha : orderOf (⟨l₁, h₁⟩ : ↥L) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext h11)
      (fun h' => h1 (congrArg Subtype.val h'))
  have hb : orderOf (⟨l₂, h₂⟩ : ↥L) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext h22)
      (fun h' => h2 (congrArg Subtype.val h'))
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_of_u33_model h ha hb)
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

end R3c19

end CFSG.Quasithin

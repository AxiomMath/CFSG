module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.StandardType.FrameRoute

theorem tmIdx_simple_le_or_card_dvd_factorial {H : Type*} [Group H] [Finite H] (M J : Subgroup H)
    [IsSimpleGroup J] {n : ℕ} (hidx : M.index ≤ n) : J ≤ M ∨ Nat.card J ∣ n.factorial := by
  let φ : J →* Equiv.Perm (H ⧸ M) := (MulAction.toPermHom H (H ⧸ M)).comp J.subtype
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hker | hker
  · right
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
    have h1 : Nat.card J ∣ Nat.card (Equiv.Perm (H ⧸ M)) := Subgroup.card_dvd_of_injective φ hinj
    have h2 : Nat.card (Equiv.Perm (H ⧸ M)) = (M.index).factorial := by
      classical
      haveI : Fintype (H ⧸ M) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card]
      rfl
    rw [h2] at h1
    exact h1.trans (Nat.factorial_dvd_factorial hidx)
  · left
    intro j hj
    have h0 : φ ⟨j, hj⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      trivial
    have h2 := congrArg (fun σ => σ ((1 : H) : H ⧸ M)) h0
    simp only [φ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAction.toPermHom_apply,
      MulAction.toPerm_apply, Equiv.Perm.coe_one, id_eq] at h2
    have h3 : ((j * 1 : H) : H ⧸ M) = ((1 : H) : H ⧸ M) := h2
    have h4 : (j * 1)⁻¹ * 1 ∈ M := QuotientGroup.eq.1 h3
    simpa using h4

theorem tmIdx_not_dvd_factorial_26 : ¬ (3 ^ 12 ∣ Nat.factorial 26) := by
  decide +kernel

theorem tmIdx_omega8plus3_excluded {H : Type*} [Group H] [Finite H] (M J : Subgroup H)
    [IsSimpleGroup J] (hJ : Nat.card J = 2 ^ 12 * 3 ^ 12 * 5 ^ 2 * 7 * 13)
    (hM : ¬ 13 ∣ Nat.card M) (hidx : M.index ≤ 26) : False := by
  rcases tmIdx_simple_le_or_card_dvd_factorial M J hidx with h | h
  · apply hM
    have h13 : 13 ∣ Nat.card J := by rw [hJ]; exact Dvd.intro_left _ rfl
    exact h13.trans (Subgroup.card_dvd_of_le h)
  · rw [hJ] at h
    have h3 : 3 ^ 12 ∣ 2 ^ 12 * 3 ^ 12 * 5 ^ 2 * 7 * 13 :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _) _
    exact tmIdx_not_dvd_factorial_26 (h3.trans h)

theorem tmIdx_index_le_of_card_le {H : Type*} [Group H] [Finite H] (M : Subgroup H) {k : ℕ}
    (hk : Nat.card H ≤ k * Nat.card M) : M.index ≤ k := by
  have h1 : Nat.card M * M.index = Nat.card H := Subgroup.card_mul_index M
  have hpos : 0 < Nat.card M := Nat.card_pos
  rw [← h1, mul_comm k] at hk
  exact Nat.le_of_mul_le_mul_left hk hpos

end CFSG.StandardType.FrameRoute

end

module

public import CFSG.Permutation.FiveTransitive.ThreeSwapTwoGroup

public section

namespace CFSG

namespace FiveTransitive.SevenDoubleSwapEmbedding

open Equiv

theorem exists_embedding {F : Type*} [Fintype F] [DecidableEq F]
    (hF : Nat.card F = 7) (u : Perm F) (hu : u ^ 2 = 1)
    (hfixed : Nat.card (Function.fixedPoints u) = 3) :
    ∃ e : Fin 6 ↪ F,
      u = Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3) := by
  have htype := Perm.cycleType_of_pow_prime_eq_one hu
  have hcount := u.card_fixedPoints
  rw [← Nat.card_eq_fintype_card, hfixed, ← Nat.card_eq_fintype_card, hF, htype,
    Multiset.sum_replicate, nsmul_eq_mul] at hcount
  have hbound := u.sum_cycleType_le
  rw [htype, Multiset.sum_replicate, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hF] at hbound
  simp only [Nat.cast_id] at hcount hbound
  have hk : u.cycleType.card = 2 := by omega
  have ht : u.cycleType = {2, 2} := by rw [htype, hk]; rfl
  obtain ⟨e₀⟩ := (Function.Embedding.nonempty_iff_card_le (α := Fin 6) (β := F)).mpr (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_fin, hF] using (by decide : 6 ≤ 7))
  let v := Equiv.swap (e₀ 0) (e₀ 1) * Equiv.swap (e₀ 2) (e₀ 3)
  have hv : v.cycleType = {2, 2} := Perm.cycleType_swap_mul_swap_of_nodup (by
    simpa only [List.map_cons, List.map_nil] using
      (show ([0, 1, 2, 3] : List (Fin 6)).Nodup by decide).map e₀.injective)
  obtain ⟨c, hc⟩ := isConj_iff.mp (Perm.isConj_of_cycleType_eq (ht.trans hv.symm))
  let e := e₀.trans c.symm.toEmbedding
  refine ⟨e, ?_⟩
  have hswap (a b : F) : c⁻¹ * Equiv.swap a b * c = Equiv.swap (c⁻¹ a) (c⁻¹ b) := by
    rw [Equiv.mul_swap_eq_swap_mul]
    simp only [inv_mul_cancel_right]
  calc
    u = c⁻¹ * v * c := by rw [← hc]; group
    _ = (c⁻¹ * Equiv.swap (e₀ 0) (e₀ 1) * c) *
        (c⁻¹ * Equiv.swap (e₀ 2) (e₀ 3) * c) := by dsimp [v]; group
    _ = _ := by rw [hswap, hswap]; rfl

end FiveTransitive.SevenDoubleSwapEmbedding

end CFSG

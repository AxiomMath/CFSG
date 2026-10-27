module

public import CFSG.Permutation.FiveTransitive.ThreeSwapTwoGroup

public section

namespace CFSG

namespace FiveTransitive.SevenTripleSwapEmbedding

open Equiv

theorem exists_embedding {F : Type*} [Fintype F] [DecidableEq F]
    (hF : Nat.card F = 7) (u : Perm F) (hu : u ^ 2 = 1)
    (hfixed : Nat.card (Function.fixedPoints u) = 1) :
    ∃ e : Fin 6 ↪ F,
      u = Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3) * Equiv.swap (e 4) (e 5) := by
  have htype := Perm.cycleType_of_pow_prime_eq_one hu
  have hcount := u.card_fixedPoints
  rw [← Nat.card_eq_fintype_card, hfixed, ← Nat.card_eq_fintype_card, hF, htype,
    Multiset.sum_replicate, nsmul_eq_mul] at hcount
  have hbound := u.sum_cycleType_le
  rw [htype, Multiset.sum_replicate, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hF] at hbound
  simp only [Nat.cast_id] at hcount hbound
  have hk : u.cycleType.card = 3 := by omega
  have ht : u.cycleType = {2, 2, 2} := by rw [htype, hk]; rfl
  obtain ⟨e₀⟩ := (Function.Embedding.nonempty_iff_card_le (α := Fin 6) (β := F)).mpr (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_fin, hF] using (by decide : 6 ≤ 7))
  let t0 := Equiv.swap (e₀ 0) (e₀ 1)
  let t1 := Equiv.swap (e₀ 2) (e₀ 3)
  let t2 := Equiv.swap (e₀ 4) (e₀ 5)
  let v := t0 * t1 * t2
  have hd (i j k l : Fin 6) (h : [i, j, k, l].Nodup) :
      (Equiv.swap (e₀ i) (e₀ j)).Disjoint (Equiv.swap (e₀ k) (e₀ l)) :=
    Perm.disjoint_swap_swap (by simpa only [List.map_cons, List.map_nil] using h.map e₀.injective)
  have hd01 : t0.Disjoint t1 := hd 0 1 2 3 (by decide)
  have hd02 : t0.Disjoint t2 := hd 0 1 4 5 (by decide)
  have hd12 : t1.Disjoint t2 := hd 2 3 4 5 (by decide)
  have hswaptype (i j : Fin 6) (hij : i ≠ j) : (Equiv.swap (e₀ i) (e₀ j)).cycleType = {2} :=
    Perm.isSwap_iff_cycleType.mp ⟨e₀ i, e₀ j, e₀.injective.ne hij, rfl⟩
  have ht0 : t0.cycleType = {2} := hswaptype 0 1 (by decide)
  have ht1 : t1.cycleType = {2} := hswaptype 2 3 (by decide)
  have ht2 : t2.cycleType = {2} := hswaptype 4 5 (by decide)
  have hv : v.cycleType = {2, 2, 2} := by
    rw [(hd02.mul_left hd12).cycleType_mul, hd01.cycleType_mul, ht0, ht1, ht2]
    rfl
  obtain ⟨c, hc⟩ := isConj_iff.mp (Perm.isConj_of_cycleType_eq (ht.trans hv.symm))
  let e := e₀.trans c.symm.toEmbedding
  refine ⟨e, ?_⟩
  have hswap (a b : F) : c⁻¹ * Equiv.swap a b * c = Equiv.swap (c⁻¹ a) (c⁻¹ b) := by
    rw [Equiv.mul_swap_eq_swap_mul]
    simp only [inv_mul_cancel_right]
  calc
    u = c⁻¹ * v * c := by rw [← hc]; group
    _ = (c⁻¹ * Equiv.swap (e₀ 0) (e₀ 1) * c) *
        (c⁻¹ * Equiv.swap (e₀ 2) (e₀ 3) * c) *
        (c⁻¹ * Equiv.swap (e₀ 4) (e₀ 5) * c) := by dsimp [v, t0, t1, t2]; group
    _ = _ := by rw [hswap, hswap, hswap]; rfl

end FiveTransitive.SevenTripleSwapEmbedding

end CFSG

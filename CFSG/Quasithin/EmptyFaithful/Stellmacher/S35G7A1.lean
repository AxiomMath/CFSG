module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin5

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.G7.A

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.Fin

@[expose] def P0 : Subgroup orth.W := commW orth (Subgroup.zpowers zStd) ⊤

theorem mem_P0_iff (w : orth.W) : w ∈ P0 ↔ w ∈ commF zStd := mem_commW_zpowers_iff zStd w

theorem P0_eq_of_card {U : Subgroup orth.W} (hU : IsInvSub orth S5Syl U) (hc : Nat.card U = 4) :
    U = P0 :=
  eq_commW_z_of_card_four card_S5Syl ((isCentInv_std_iff zStd).mpr rfl) hU hc

theorem eq_one_of_forall_mem_mp {w : orth.W} (h : ∀ σ : Perm (Fin 5), w ∈ mp σ P0) : w = 1 := by
  have key : ∀ w : orth.W, (∀ σ : Perm (Fin 5), orth.act σ⁻¹ w ∈ commF zStd) → w = 1 := by
    decide +kernel
  exact key w fun σ => (mem_P0_iff _).mp (mem_mp.mp (h σ))

theorem eq_of_forall_mem_mp_fix {w : orth.W} {q : Fin 5}
    (h : ∀ σ : Perm (Fin 5), σ 4 = q → w ∈ mp σ P0) : w = 1 ∨ w = vp q := by
  have key : ∀ q : Fin 5, ∀ w : orth.W,
      (∀ σ : Perm (Fin 5), σ 4 = q → orth.act σ⁻¹ w ∈ commF zStd) → w = 1 ∨ w = vp q := by
    decide +kernel
  exact key q w fun σ hσ => (mem_P0_iff _).mp (mem_mp.mp (h σ hσ))

theorem ep_zero_two_mem : ep 0 2 ∈ P0 := by
  rw [mem_P0_iff]; decide +kernel

theorem exists_swap_plane : ∃ d ∈ S5Syl, orth.act d (ep 0 2) * (ep 0 2)⁻¹ = vp 4 := by
  have key : ∃ d ∈ S5SylF, orth.act d (ep 0 2) * (ep 0 2)⁻¹ = vp 4 := by decide +kernel
  obtain ⟨d, hd, h⟩ := key
  exact ⟨d, (mem_S5Syl_iff d).mpr hd, h⟩

theorem vp_prod : vp 0 * vp 1 * vp 2 * vp 3 * vp 4 = 1 := by decide +kernel

theorem eq_one_of_prod_eq_one (y : Fin 5 → orth.W) (hy : ∀ q, y q = 1 ∨ y q = vp q)
    (hp : y 0 * y 1 * y 2 * y 3 * y 4 = 1) {q : Fin 5} (hq : y q = 1) (q' : Fin 5) :
    y q' = 1 := by
  have key : ∀ a : Fin 5 → Bool, ∀ q : Fin 5,
      (if a 0 then vp 0 else 1) * (if a 1 then vp 1 else 1) * (if a 2 then vp 2 else 1) *
        (if a 3 then vp 3 else 1) * (if a 4 then vp 4 else 1) = 1 → a q = false →
      ∀ q', a q' = false := by decide +kernel
  have hyq : ∀ q, y q = if decide (y q ≠ 1) then vp q else 1 := by
    intro q
    rcases hy q with h | h
    · simp [h]
    · simp [h, vp_ne_one]
  have h1 := key (fun q => decide (y q ≠ 1)) q (by simp only [← hyq]; exact hp)
    (by simpa using hq) q'
  simpa using h1

theorem closure_vp : Subgroup.closure (Set.range vp) = ⊤ := by
  set Y := Subgroup.closure (Set.range vp) with hY
  have hinv : ∀ σ : Perm (Fin 5), ∀ y ∈ Y, orth.act σ y ∈ Y := by
    intro σ y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      rw [act_vp]; exact Subgroup.subset_closure ⟨_, rfl⟩
    | one => rw [map_one]; exact Y.one_mem
    | mul x y _ _ hx hy => rw [map_mul]; exact Y.mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact Y.inv_mem hx
  rcases irreducible_orth Y hinv with h | h
  · exfalso
    have : vp 0 ∈ Y := Subgroup.subset_closure ⟨0, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact vp_ne_one 0 this
  · exact h

end CFSG.Quasithin.F53.Stellmacher.S35.G7.A

module

public import CFSG.Permutation.FinPackCount

public section

namespace CFSG.Quasithin.S14620HK

open Equiv Finset CFSG.Permutation.FinPack

@[expose] def iffB (x y : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false y) y x

theorem iffB_eq (x y : Bool) : iffB x y = true ↔ (x = true ↔ y = true) := by
  cases x <;> cases y <;> decide

@[expose] noncomputable def wrBlkB (c : ℕ) : Bool :=
  allLtK (fun i => iffB (Nat.beq (Nat.shiftRight i 2) 0)
    (Nat.beq (Nat.shiftRight (rd c i) 2) (Nat.shiftRight (rd c 0) 2))) 8

theorem blk_iff (x y p q r : ℕ) (hx : x < 2) (hy : y < 2) (hp : p < 2) (hq : q < 2) (hr : r < 2)
    (h1 : x = 0 ↔ p = r) (h2 : y = 0 ↔ q = r) : (x = y ↔ p = q) := by
  omega

theorem wrBlkB_iff (g : Perm (Fin 8)) :
    (∀ i j : Fin 8, (i.val / 4 = j.val / 4 ↔ (g i).val / 4 = (g j).val / 4)) ↔
      wrBlkB (enc g) = true := by
  have hr : ∀ i : Fin 8, rd (enc g) i = g i := rd_enc (by norm_num) g
  have hs : ∀ m : ℕ, Nat.shiftRight m 2 = m / 4 := fun m => by
    change m >>> 2 = _
    rw [Nat.shiftRight_eq_div_pow]
  have r0 : rd (enc g) 0 = g 0 := hr 0
  rw [wrBlkB, allLtK_iff]
  constructor
  · intro H i hi
    have e := H ⟨i, hi⟩ 0
    rw [iffB_eq, Nat.beq_eq, Nat.beq_eq, hs, hs, hs, hr ⟨i, hi⟩, r0]
    exact e
  · intro H i j
    have hi := H i i.isLt
    have hj := H j j.isLt
    rw [iffB_eq, Nat.beq_eq, Nat.beq_eq, hs, hs, hs, hr i, r0] at hi
    rw [iffB_eq, Nat.beq_eq, Nat.beq_eq, hs, hs, hs, hr j, r0] at hj
    exact blk_iff _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) hi hj

theorem cnt_wr8 : cntK 8 wrBlkB 8 0 0 0 = 1152 := by decide +kernel

theorem card_wr8 :
    (univ.filter fun g : Perm (Fin 8) =>
      ∀ i j : Fin 8, (i.val / 4 = j.val / 4 ↔ (g i).val / 4 = (g j).val / 4)).card = 1152 := by
  rw [Finset.filter_congr fun g _ => wrBlkB_iff g, card_filter_eq_cntK, cnt_wr8]

end CFSG.Quasithin.S14620HK

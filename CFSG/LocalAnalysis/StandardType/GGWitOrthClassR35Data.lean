module

public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.StandardType.ZS.DataR35

@[expose] def wcan (k : ℕ) : Fin 5 → ZMod 3 := fun i => if (i : ℕ) < k then 2 else 1

def qw (w a : Fin 5 → ZMod 3) : ℕ := (∑ i, w i * (a i) ^ 2 : ZMod 3).val

def bw (w a b : Fin 5 → ZMod 3) : ℕ := (2 * ∑ i, w i * (a i * b i) : ZMod 3).val

def digits (n : ℕ) : Fin 5 → ZMod 3 := fun i => (((n / 3 ^ (i : ℕ)) % 3 : ℕ) : ZMod 3)

def allV : List (Fin 5 → ZMod 3) := (List.finRange 243).map fun n => digits n

@[expose] def secondCheck (w : Fin 5 → ZMod 3) : Bool :=
  allV.all fun a =>
    !(qw w a == 1) ||
    (allV.all fun u =>
      !(qw w u == 0) || !(bw w a u == 0) || (u == 0) ||
      (allV.any fun u' =>
        (u' != 0) && (qw w u' == 0) && (bw w a u' == 0) &&
          (bw w u u' == 0) && (u' != u) && (u' != -u)))

theorem secondCheck_0 : secondCheck (wcan 0) = true := by decide +kernel
theorem secondCheck_2 : secondCheck (wcan 2) = true := by decide +kernel
theorem secondCheck_4 : secondCheck (wcan 4) = true := by decide +kernel

theorem allV_nodup : allV.Nodup := by decide +kernel

theorem allV_length : allV.length = 243 := by decide +kernel

theorem mem_allV (a : Fin 5 → ZMod 3) : a ∈ allV := by
  rw [← List.mem_toFinset]
  have hcard : allV.toFinset.card = Fintype.card (Fin 5 → ZMod 3) := by
    rw [List.toFinset_card_of_nodup allV_nodup, allV_length, Fintype.card_pi]
    simp [Fintype.card_fin]
  rw [Finset.eq_univ_of_card allV.toFinset hcard]
  exact Finset.mem_univ a

theorem qw_eq_iff (w a : Fin 5 → ZMod 3) (k : ZMod 3) :
    qw w a = k.val ↔ (∑ i, w i * (a i) ^ 2 : ZMod 3) = k := by
  unfold qw
  exact ⟨fun h => (ZMod.val_injective 3) h, fun h => by rw [h]⟩

theorem bw_eq_iff (w a b : Fin 5 → ZMod 3) (k : ZMod 3) :
    bw w a b = k.val ↔ (2 * ∑ i, w i * (a i * b i) : ZMod 3) = k := by
  unfold bw
  exact ⟨fun h => (ZMod.val_injective 3) h, fun h => by rw [h]⟩

end CFSG.StandardType.ZS.DataR35

end

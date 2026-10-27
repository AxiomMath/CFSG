module

public import CFSG.Quasithin.Vol2.Ch10SecQ6WrPM

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Equiv

theorem zmod_two_neg (x : ZMod 2) : -x = x := by
  revert x
  decide

@[expose] def Mmod : AddSubgroup PMod where
  carrier := {p | ∃ a b, IsO a ∧ IsO b ∧ p = sumv a b}
  zero_mem' := ⟨0, 0, by simp [IsO], by simp [IsO], by funext i j; simp [sumv]⟩
  add_mem' := by
    rintro _ _ ⟨a, b, ha, hb, rfl⟩ ⟨a', b', ha', hb', rfl⟩
    refine ⟨a + a', b + b', isO_add ha ha', isO_add hb hb', ?_⟩
    funext i j
    simp only [sumv, Pi.add_apply]
    ring
  neg_mem' := by
    rintro _ ⟨a, b, ha, hb, rfl⟩
    refine ⟨a, b, ha, hb, ?_⟩
    funext i j
    simp only [Pi.neg_apply]
    exact zmod_two_neg _

theorem sumv_mem_Mmod {a b : Fin 5 → ZMod 2} (ha : IsO a) (hb : IsO b) : sumv a b ∈ Mmod :=
  ⟨a, b, ha, hb, rfl⟩

@[expose] def Nmod : AddSubgroup PMod where
  carrier := {p | (∀ i, ∑ j, p i j = 0) ∧ ∀ j, ∑ i, p i j = 0}
  zero_mem' := ⟨fun _ => by simp, fun _ => by simp⟩
  add_mem' := by
    rintro p p' ⟨hr, hc⟩ ⟨hr', hc'⟩
    refine ⟨fun i => ?_, fun j => ?_⟩
    · simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, hr, hr', add_zero]
    · simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, hc, hc', add_zero]
  neg_mem' := by
    rintro p ⟨hr, hc⟩
    refine ⟨fun i => ?_, fun j => ?_⟩
    · calc ∑ x, (-p) i x = ∑ x, p i x := Finset.sum_congr rfl fun x _ => zmod_two_neg (p i x)
        _ = 0 := hr i
    · calc ∑ x, (-p) x j = ∑ x, p x j := Finset.sum_congr rfl fun x _ => zmod_two_neg (p x j)
        _ = 0 := hc j

theorem tens_mem_Nmod {a b : Fin 5 → ZMod 2} (ha : IsO a) (hb : IsO b) : tens a b ∈ Nmod := by
  refine ⟨fun i => ?_, fun j => ?_⟩
  · simp only [tens]
    rw [← Finset.mul_sum, hb, mul_zero]
  · simp only [tens]
    rw [← Finset.sum_mul, ha, zero_mul]

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD

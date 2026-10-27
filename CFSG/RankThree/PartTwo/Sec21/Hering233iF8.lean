module

public import CFSG.RankThree.PartTwo.KFacts.KS21U58

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K card_K)

@[expose] def F8 : AddSubgroup K where
  carrier := {c | c ^ 8 = c}
  zero_mem' := by
    show (0 : K) ^ 8 = 0
    exact zero_pow (by norm_num)
  add_mem' := by
    intro a b ha hb
    have ha' : a ^ 2 ^ 3 = a := ha
    have hb' : b ^ 2 ^ 3 = b := hb
    show (a + b) ^ 2 ^ 3 = a + b
    rw [add_pow_char_pow, ha', hb']
  neg_mem' := by
    intro c hc
    have hc' : c ^ 8 = c := hc
    show (-c) ^ 8 = -c
    rw [CharTwo.neg_eq, hc']

theorem mem_F8 {c : K} : c ∈ F8 ↔ c ^ 8 = c := Iff.rfl

theorem eight_le_card_F8 : 8 ≤ Nat.card F8 := by
  have hcard : Nat.card (GaloisField 2 3) = 8 :=
    (GaloisField.card 2 3 (by norm_num)).trans (by norm_num)
  have hdvd : Module.finrank (ZMod 2) (GaloisField 2 3) ∣ Module.finrank (ZMod 2) K := by
    rw [GaloisField.finrank 2 (by norm_num : (3 : ℕ) ≠ 0),
      GaloisField.finrank 2 (by norm_num : (2 * 3 : ℕ) ≠ 0)]
    exact dvd_mul_left 3 2
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdvd
  have h8 : ∀ x : GaloisField 2 3, x ^ 8 = x := by
    intro x
    letI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
    have hc : Fintype.card (GaloisField 2 3) = 8 := by
      rw [Fintype.card_eq_nat_card]
      exact hcard
    calc x ^ 8 = x ^ Fintype.card (GaloisField 2 3) := by rw [hc]
      _ = x := FiniteField.pow_card x
  have hmem : ∀ x : GaloisField 2 3, f x ∈ F8 := by
    intro x
    rw [mem_F8]
    calc f x ^ 8 = f (x ^ 8) := (map_pow f x 8).symm
      _ = f x := by rw [h8 x]
  have hinj : Function.Injective (fun x : GaloisField 2 3 => (⟨f x, hmem x⟩ : ↥F8)) := by
    intro x y hxy
    have h1 : f.toRingHom x = f.toRingHom y := congrArg Subtype.val hxy
    exact f.toRingHom.injective h1
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [hcard] at hle
  exact hle

end CFSG.RankThree.PartTwo.Sec21.Hering233i

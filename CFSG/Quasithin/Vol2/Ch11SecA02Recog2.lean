module

public import CFSG.Quasithin.Vol2.Ch11SecA02Recog

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint

variable {X Y : Type} [Group X] [Group Y] {n : ℕ} {f : X →* Y}

theorem recog_G2 [Finite X] (hX : ShapeData X n) (hn : 2 ≤ n) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center X) (hodd : Odd (Nat.card f.ker)) {m : ℕ} (hm : 1 ≤ m)
    (hY : Nat.card Y = 2 ^ (6 * m) * oG2 m) : m = n ∧ Function.Injective f := by
  rcases shape_eq hX hn hf hodd (odd_oG2 hm) hY with
    ⟨-, -, -, c, -, hc, h1, h2, hcZ, -⟩ | ⟨c, -, h1, h2⟩ | ⟨h1, h2⟩
  · obtain rfl : n = 2 * m := by omega
    rw [oSL3_two_mul] at h2
    have hpos : 0 < oG2 m := (odd_oG2 hm).pos
    have h3 : c * Nat.card f.ker = 2 ^ (2 * m) + 1 := Nat.eq_of_mul_eq_mul_right hpos h2
    have hc1 : c = 1 := by
      have hd1 : c ∣ 2 ^ (2 * m) + 1 := ⟨Nat.card f.ker, h3.symm⟩
      have hd2 : c ∣ (2 ^ (2 * m) + 1) - (2 ^ (2 * m) - 1) := Nat.dvd_sub hd1 hc
      have he : (2 ^ (2 * m) + 1) - (2 ^ (2 * m) - 1) = 2 := by
        have : 1 ≤ 2 ^ (2 * m) := Nat.one_le_two_pow
        omega
      rw [he] at hd2
      have hodd' := odd_of_dvd_two_pow_sub_one (by omega) hc
      rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
      · exact h
      · rw [h] at hodd'
        exact absurd hodd' (by decide)
    have hz : Nat.card f.ker ≤ 3 :=
      (Subgroup.card_le_of_le hker).trans (hcZ hc1)
    rw [hc1, one_mul] at h3
    have : 4 ≤ 2 ^ (2 * m) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · obtain ⟨k, rfl, rfl⟩ : ∃ k, m = 2 * k ∧ n = 3 * k := ⟨n - m, by omega, by omega⟩
    exact (not_dvd_oG2_oSp4 (k := k) (by omega) ⟨c * Nat.card f.ker, by rw [← h2]; ring⟩).elim
  · have hmn : m = n := by omega
    subst hmn
    have hpos : 0 < oG2 m := (odd_oG2 hm).pos
    have h3 : Nat.card f.ker = 1 := by
      have : Nat.card f.ker * oG2 m = 1 * oG2 m := by rw [h2, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hpos this
    exact ⟨rfl, injective_of_card_ker h3⟩

theorem recog_small (hX : ShapeData X n) (hn : 2 ≤ n) (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker)) {e o : ℕ} (ho : Odd o) (he : e ≤ 5)
    (hY : Nat.card Y = 2 ^ e * o) : False := by
  rcases shape_eq hX hn hf hodd ho hY with ⟨-, -, -, -, -, -, h1, -⟩ | ⟨-, -, h1, -⟩ | ⟨h1, -⟩ <;>
    omega

theorem recog_ten (hX : ShapeData X n) (hn : 2 ≤ n) (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker)) {o : ℕ} (ho : Odd o) (hY : Nat.card Y = 2 ^ 10 * o) :
    False := by
  rcases shape_eq hX hn hf hodd ho hY with ⟨-, -, -, -, -, -, h1, -⟩ | ⟨-, -, h1, -⟩ | ⟨h1, -⟩ <;>
    omega

theorem card_SL_four_two :
    Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 2 ^ 6 * 315 := by
  rw [OrderReductions.LinearOrders.card_specialLinear (ZMod 2) 4 (by norm_num), Nat.card_zmod]
  decide

theorem recog_SL42 (hL34 : FactL34) (hX : ShapeData X n) (hn : 2 ≤ n)
    (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    (e : Y ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) : False := by
  have hY : Nat.card Y = 2 ^ 6 * 315 := by rw [Nat.card_congr e.toEquiv, card_SL_four_two]
  rcases shape_eq hX hn hf hodd (by decide) hY with
    ⟨K, _, _, -, hK, -, h1, -, -, g, hg⟩ | ⟨-, -, h1, -⟩ | ⟨h1, -⟩
  · obtain rfl : n = 2 := by omega
    exact hL34 K hK ((e.toMonoidHom.comp f).comp g) (e.surjective.comp (hf.comp hg))
  · omega
  · omega

end CFSG.Quasithin.Vol2.Ch11.SecA

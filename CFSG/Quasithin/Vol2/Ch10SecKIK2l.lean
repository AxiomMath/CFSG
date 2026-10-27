module

public import CFSG.Quasithin.Vol2.Ch10SecKIK2j

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Blueprint

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q} {s : ℕ}

namespace OddData

variable (hD : OddData B s) (h3 : ¬ 3 ∣ s)
include hD h3

omit [Finite Q] in
theorem not_three_dvd : ¬ 3 ∣ Nat.card ↥B := by
  obtain ⟨a, ha⟩ := hD.card
  rw [ha]
  intro h
  exact h3 ((Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_left h)

omit [Finite Q] in
theorem not_three_dvd' : ¬ 3 ∣ Nat.card (ModO2 B) := by
  rw [hD.cardQ]
  exact h3

theorem not_three_dvd_ext {PV PY : ∀ (V : Type) [Group V], Prop} (h : IsExt ↥B PV PY)
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → ∃ k, Nat.card V = 2 ^ k) {N : ℕ}
    (hN : 3 ∣ N) (hPY : ∀ (Y : Type) [Group Y], PY Y → Nat.card Y = N) : False := by
  obtain ⟨V, _, hY, k, hk⟩ := card_of_isExt h hPV
  apply hD.not_three_dvd h3
  rw [hk, hPY _ hY]
  exact dvd_mul_of_dvd_right hN _

end OddData

omit [Finite Q] in
theorem three_dvd_mul_sq_sub_one {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : 3 ∣ p * (p ^ 2 - 1) := by
  have h3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1 h
    omega
  have hmod : p % 3 = 1 ∨ p % 3 = 2 := by omega
  have hsq : p ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod]
    rcases hmod with h | h <;> rw [h]
  refine dvd_mul_of_dvd_right ?_ _
  have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  omega

theorem rows_Sz (hD : OddData B s) (h3 : ¬ 3 ∣ s) (h : A312Case B L) : ∃ f, Is2F4 f ↥L := by
  have hE := two_pow_of_isE2
  have hX : ∀ (V : Type) [Group V] [Finite V], ∀ m, IsExtraspecial2 m V →
      ∃ k, Nat.card V = 2 ^ k := fun V _ _ m hV => ⟨_, card_isExtraspecial2 hV⟩
  have hB3 := hD.not_three_dvd h3
  have hQ3 := hD.not_three_dvd' h3
  have hM22 : 3 ∣ Nat.card ↥NativeSporadic.M22 := by
    rw [CFSG.Sporadic.Mathieu.card_M22]
    norm_num
  have hM24 : 3 ∣ Nat.card ↥NativeSporadic.M24 := by
    rw [CFSG.Sporadic.Mathieu.card_M24]
    norm_num
  rcases h with ⟨⟨m, hm⟩, -⟩ | ⟨f, -, hL, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩ | ⟨hB | hB, -⟩ |
      (⟨hB, -⟩ | ⟨hB, -⟩) | h | h | h | h | h | h | h | h | h | h | h | h | h
  · obtain ⟨-, hc⟩ := card_of_isPSL_two_two hm
    exact absurd (by rw [hc]; exact dvd_mul_of_dvd_right (three_dvd_oSL2 m) _) hQ3
  · exact ⟨f, hL⟩
  · exact absurd (by rw [card_L32 hB]; norm_num) hQ3
  · exact absurd (by rw [card_L42 hB]; norm_num) hQ3
  · exact absurd (by rw [card_alt5 hB]; norm_num) hB3
  · exact absurd (by rw [card_L32 hB]; norm_num) hB3
  · exact absurd (by rw [card_alt6 hB]; norm_num) hB3
  · exact absurd (by rw [card_hat6 hB]; norm_num) hB3
  · rcases h with ⟨p, hp, hp3, hB, -⟩ | ⟨hB, -⟩
    · refine absurd ?_ hB3
      have h2 := two_mul_card_of_isPSL_two hp (by omega) hB
      have h3' : 3 ∣ 2 * Nat.card ↥B := h2 ▸ three_dvd_mul_sq_sub_one hp hp3
      exact (by norm_num : Nat.Coprime 3 2).dvd_of_dvd_mul_left h3'
    · exact absurd (by rw [card_alt5 hB]; norm_num) hB3
  · rcases h with ⟨-, p, hp, hp3, hB, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
    · exact absurd (by rw [card_of_isSL2 hp hB]; exact three_dvd_mul_sq_sub_one hp hp3) hB3
    · exact absurd (by rw [card_alt6 hB]; norm_num) hB3
    · exact absurd (by rw [card_hat6 hB]; norm_num) hB3
  · exfalso
    obtain ⟨p, hp, hp3, ⟨V, hV, ⟨e⟩, -⟩, -⟩ := h
    have : NeZero p := ⟨hp.ne_zero⟩
    have hcard : Nat.card ↥V = p ^ 2 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Fin 2 → ZMod p) = p ^ 2
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    have hodd : Odd (Nat.card ↥V) := by
      rw [hcard]
      exact (hp.odd_of_ne_two (by omega)).pow
    have hbot := hD.odd V hV hodd
    rw [hbot, Subgroup.card_bot] at hcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  · exact absurd (by rw [card_alt6 h.1]; norm_num) hB3
  · exfalso
    rcases h with ⟨hB | hB, -⟩ | ⟨hB | hB, -⟩
    · exact hD.not_three_dvd_ext h3 hB (hE 4) (by norm_num) (fun Y _ hY => card_alt5 hY)
    · exact hD.not_three_dvd_ext h3 hB (hE 4) (by norm_num) (fun Y _ hY => card_alt6 hY)
    · exact hD.not_three_dvd_ext h3 hB (hE 4) (by norm_num) (fun Y _ hY => card_alt5 hY)
    · exact hD.not_three_dvd_ext h3 hB (hE 4) (by norm_num) (fun Y _ hY => card_hat6 hY)
  · exfalso
    rcases h with ⟨⟨⟨e⟩⟩ | hB | hB | hB | hB | hB | hB, -⟩
    · exact hB3 (by rw [Nat.card_congr e.toEquiv]; exact hM22)
    · exact hB3 (by rw [card_L34 hB]; norm_num)
    · exact hD.not_three_dvd_ext h3 hB (hE 4) (by norm_num)
        (fun Y _ hY => Ch11.SecA.card_alt7 hY)
    · exact hD.not_three_dvd_ext h3 hB (hE 4) (by norm_num) (fun Y _ hY => card_L32 hY)
    · exact hD.not_three_dvd_ext h3 hB (hE 3) (by norm_num) (fun Y _ hY => card_L32 hY)
    · exact hD.not_three_dvd_ext h3 hB (hE 4) (by norm_num) (fun Y _ hY => card_alt6 hY)
    · exact hD.not_three_dvd_ext h3 hB (hE 4) (by norm_num) (fun Y _ hY => card_alt5 hY)
  · exfalso
    rcases h with ⟨hB | hB | hB | hB, -⟩
    · exact hD.not_three_dvd_ext h3 hB (hE 4) (by norm_num) (fun Y _ hY => card_L42 hY)
    · exact hD.not_three_dvd_ext h3 hB (hE 6) (by norm_num) (fun Y _ hY => card_L32 hY)
    · exact hD.not_three_dvd_ext h3 hB (fun V _ _ hV => hX V _ hV) (by norm_num)
        (fun Y _ hY => card_L32 hY)
    · exact hD.not_three_dvd_ext h3 hB (hE 6) (by norm_num) (fun Y _ hY => card_hat6 hY)
  · exact absurd (by rw [card_alt5 h.1]; norm_num) hB3
  · exact absurd (hD.not_three_dvd_ext h3 h.1 (fun V _ _ hV => hX V _ hV) (by norm_num)
      (fun Y _ hY => card_alt5 hY)) id
  · exfalso
    rcases h with ⟨-, hB | hB | hB | hB | hB | hB⟩
    · obtain ⟨V, _, hY, k, hk⟩ := card_of_isExt hB (fun V _ _ hV => hX V _ hV)
      exact hB3 (by rw [hk, card_of_isHat hY]; exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _)
    · obtain ⟨V, _, ⟨e⟩, k, hk⟩ := card_of_isExt hB (hE 11)
      exact hB3 (by rw [hk, Nat.card_congr e.toEquiv]; exact dvd_mul_of_dvd_right hM24 _)
    · exact hQ3 (by rw [card_alt5 hB]; norm_num)
    · exact hQ3 (by rw [card_hat6 hB]; norm_num)
    · exact hQ3 (by rw [card_L42 hB]; norm_num)
    · exact hQ3 (by rw [card_L32 hB]; norm_num)
  · exfalso
    rcases h with ⟨hB | hB, -⟩
    · exact hD.not_three_dvd_ext h3 hB (fun V _ _ hV => card_isZ4StarExtra2 hV) (by norm_num)
        (fun Y _ hY => card_alt5 hY)
    · exact hD.not_three_dvd_ext h3 hB (fun V _ _ hV => ⟨6, card_isZ4Cubed hV⟩) (by norm_num)
        (fun Y _ hY => card_L32 hY)
  · exfalso
    rcases h with ⟨hB | hB, -⟩
    · exact hD.not_three_dvd_ext h3 hB (fun V _ _ hV => hX V _ hV) (by norm_num)
        (fun Y _ hY => card_L32 hY)
    · exact hD.not_three_dvd_ext h3 hB (hE 6) (by norm_num) (fun Y _ hY => card_hat6 hY)
  · exfalso
    rcases h with ⟨hB | hB, -, -⟩
    · exact hQ3 (by rw [card_alt5 hB]; norm_num)
    · exact hQ3 (by rw [card_L32 hB]; norm_num)

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

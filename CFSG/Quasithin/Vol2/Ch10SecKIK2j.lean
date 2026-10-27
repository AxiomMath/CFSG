module

public import CFSG.Quasithin.Vol2.Ch10SecKIK2i
public import CFSG.Quasithin.Vol2.Ch11SecA11Cases2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Blueprint

@[expose] def Out168 (X : Type) [Group X] : Prop :=
  (IsPSL 4 2 1 X ∨ IsPSL 5 2 1 X) ∨ (IsAlt 7 X ∨ IsHat X ↥(alternatingGroup (Fin 7))) ∨
    IsPSL 2 7 2 X ∨ (∃ s : Bool, IsPSLEps3 s 7 1 X ∨ IsSLEps3 s 7 X) ∨ IsSporadic .M23 X ∨
    IsSporadic .M24 X ∨ IsSporadic .J4 X ∨ IsSporadic .HS X ∨ IsSporadic .He X ∨
    IsSporadic .Ru X

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q}

theorem two_pow_of_isE2 : ∀ m, ∀ (V : Type) [Group V] [Finite V], IsE2 m V →
    ∃ k, Nat.card V = 2 ^ k := fun m _ _ _ hV => ⟨m, card_isE2 hV⟩

omit [Finite Q] in
theorem prime_dvd_card_of_isPSL_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hB : IsPSL 2 p 1 ↥B) :
    p ∣ Nat.card ↥B := by
  have h := two_mul_card_of_isPSL_two hp hp2 hB
  have h1 : p ∣ 2 * Nat.card ↥B := Dvd.intro _ h.symm
  exact ((Nat.coprime_primes hp Nat.prime_two).2 hp2).dvd_of_dvd_mul_left h1

theorem rows_L32 (hD : OddData B 168) (h : A312Case B L) : Out168 ↥L := by
  have hE := two_pow_of_isE2
  have hX : ∀ (V : Type) [Group V] [Finite V], ∀ m, IsExtraspecial2 m V →
      ∃ k, Nat.card V = 2 ^ k := fun V _ _ m hV => ⟨_, card_isExtraspecial2 hV⟩
  have h11 : ¬ 11 ∣ 168 := by decide
  have h23 : ¬ 23 ∣ 168 := by decide
  rcases h with ⟨⟨m, hm⟩, -⟩ | ⟨f, hf, -⟩ | ⟨-, hL, -⟩ | ⟨hB, -⟩ | ⟨hB | hB, hL⟩ |
      (⟨hB, -⟩ | ⟨hB, -⟩) | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exfalso
    obtain ⟨hm1, hc⟩ := card_of_isPSL_two_two hm
    exact oSL2_ne_21 (hD.odd21' (odd_oSL2 hm1) hc)
  · exfalso
    apply not_three_dvd_card_of_isSz hf
    rw [hD.cardQ]
    norm_num
  · exact Or.inl hL
  · exact absurd (hD.odd21' (by decide) (card_L42 hB)) (by decide)
  · exact absurd (hD.odd21 (by decide) (card_alt5 hB)) (by decide)
  · exact Or.inr (Or.inl hL)
  · exact absurd (hD.odd21 (by decide) (card_alt6 hB)) (by decide)
  · exact absurd (hD.odd21 (by decide) (card_hat6 hB)) (by decide)
  ·
    rcases h with ⟨p, hp, hp3, hB, hL⟩ | ⟨hB, -⟩
    · obtain rfl := hD.eq_seven hp hp3 (prime_dvd_card_of_isPSL_two hp (by omega) hB)
      exact Or.inr (Or.inr (Or.inl hL))
    · exact absurd (hD.odd21 (by decide) (card_alt5 hB)) (by decide)
  ·
    rcases h with ⟨s, p, hp, hp3, hB, hL⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
    · obtain rfl := hD.eq_seven hp hp3 ⟨p ^ 2 - 1, card_of_isSL2 hp hB⟩
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hL⟩)))
    · exact absurd (hD.odd21 (by decide) (card_alt6 hB)) (by decide)
    · exact absurd (hD.odd21 (by decide) (card_hat6 hB)) (by decide)
  ·
    exfalso
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
  · exact absurd (hD.odd21 (by decide) (card_alt6 h.1)) (by decide)
  ·
    exfalso
    rcases h with ⟨hB | hB, -⟩ | ⟨hB | hB, -⟩
    · exact absurd (hD.odd21_ext hB (hE 4) (by decide) (fun Y _ hY => card_alt5 hY)) (by decide)
    · exact absurd (hD.odd21_ext hB (hE 4) (by decide) (fun Y _ hY => card_alt6 hY)) (by decide)
    · exact absurd (hD.odd21_ext hB (hE 4) (by decide) (fun Y _ hY => card_alt5 hY)) (by decide)
    · exact absurd (hD.odd21_ext hB (hE 4) (by decide) (fun Y _ hY => card_hat6 hY)) (by decide)
  ·
    rcases h with ⟨⟨⟨e⟩⟩ | hB | hB | hB | hB | hB | hB, hL⟩
    · exfalso
      refine h11 (hD.dvd_of_prime_dvd (by norm_num) (by norm_num) ?_)
      rw [Nat.card_congr e.toEquiv]
      exact eleven_dvd_card_M22
    · exact absurd (hD.odd21 (by decide) (card_L34 hB)) (by decide)
    · exact absurd (hD.odd21_ext hB (hE 4) (by decide)
        (fun Y _ hY => Ch11.SecA.card_alt7 hY)) (by decide)
    · iterate 4 right
      exact Or.inl hL
    · iterate 4 right
      exact Or.inl hL
    · exact absurd (hD.odd21_ext hB (hE 4) (by decide) (fun Y _ hY => card_alt6 hY)) (by decide)
    · exact absurd (hD.odd21_ext hB (hE 4) (by decide) (fun Y _ hY => card_alt5 hY)) (by decide)
  ·
    rcases h with ⟨hB | hB | hB | hB, hL⟩
    · exact absurd (hD.odd21_ext hB (hE 4) (by decide) (fun Y _ hY => card_L42 hY)) (by decide)
    · iterate 5 right
      exact Or.inl hL
    · iterate 5 right
      exact Or.inl hL
    · exact absurd (hD.odd21_ext hB (hE 6) (by decide) (fun Y _ hY => card_hat6 hY)) (by decide)
  · exact absurd (hD.odd21 (by decide) (card_alt5 h.1)) (by decide)
  · exact absurd (hD.odd21_ext h.1 (fun V _ _ hV => hX V _ hV) (by decide)
      (fun Y _ hY => card_alt5 hY)) (by decide)
  ·
    rcases h with ⟨hL, hB | hB | hB | hB | hB | hB⟩
    · exfalso
      obtain ⟨V, _, hY, k, hk⟩ := card_of_isExt hB (fun V _ _ hV => hX V _ hV)
      refine h11 (hD.dvd_of_prime_dvd (by norm_num) (by norm_num) ?_)
      rw [hk, card_of_isHat hY]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left eleven_dvd_card_M22 _) _
    · exfalso
      obtain ⟨V, _, ⟨e⟩, k, hk⟩ := card_of_isExt hB (hE 11)
      refine h23 (hD.dvd_of_prime_dvd (by norm_num) (by norm_num) ?_)
      rw [hk, Nat.card_congr e.toEquiv]
      exact dvd_mul_of_dvd_right twentythree_dvd_card_M24 _
    · exact absurd (hD.odd21' (by decide) (card_alt5 hB)) (by decide)
    · exact absurd (hD.odd21' (by decide) (card_hat6 hB)) (by decide)
    · exact absurd (hD.odd21' (by decide) (card_L42 hB)) (by decide)
    · iterate 6 right
      exact Or.inl hL
  ·
    rcases h with ⟨hB | hB, hL⟩
    · exact absurd (hD.odd21_ext hB (fun V _ _ hV => card_isZ4StarExtra2 hV) (by decide)
        (fun Y _ hY => card_alt5 hY)) (by decide)
    · iterate 7 right
      exact Or.inl hL
  ·
    rcases h with ⟨hB | hB, hL⟩
    · iterate 8 right
      exact Or.inl hL
    · exact absurd (hD.odd21_ext hB (hE 6) (by decide) (fun Y _ hY => card_hat6 hY)) (by decide)
  ·
    rcases h with ⟨hB | hB, -, hL⟩
    · exact absurd (hD.odd21' (by decide) (card_alt5 hB)) (by decide)
    · iterate 9 right
      exact hL

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

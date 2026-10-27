module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteSevenAlg
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteSevenConj
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCoreCases
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcPalin

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H] {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

theorem not_seven_case7 (h : IsTutteSys s r l ξ Hs) (h7 : ξ * r * ξ = r⁻¹ ∧ ξ * l * ξ = l⁻¹) :
    s ≠ 7 := by
  intro hs
  subst hs
  have habel : Abel Hs 4 := abel_of_le_two_thirds h (by norm_num) (by norm_num)
  have hnab : ¬ Abel Hs 5 := fun hab5 =>
    no_two_cores7 h h7 2 3 (by norm_num) (by norm_num) (by norm_num) hab5
  have hx5 := Seven.x5_sq h habel hnab
  have h62 : tx r l 6 ^ 2 ∈ Hs 5 := by
    have := tx_sq_mem h (k := 6) (by norm_num) (by norm_num)
    simpa using this
  obtain ⟨L, hL, hL1, hLeq⟩ := nf_exists h (k := 5) (by norm_num) (-1) (Or.inr rfl) h62
  have hL7 : ∀ t ∈ L, 1 ≤ t ∧ t < ((7 : ℕ) : ℤ) := fun t ht =>
    ⟨(hL1 t ht).1, by have := (hL1 t ht).2; simp; omega⟩
  have hL6 : ∀ t ∈ L, 1 ≤ t ∧ t < ((6 : ℕ) : ℤ) := fun t ht =>
    ⟨(hL1 t ht).1, by have := (hL1 t ht).2; simp; omega⟩
  obtain ⟨ε, hε1, -⟩ := exists_parity h
  obtain ⟨hm, hεL⟩ := parity_nfw h ε hε1 (-1) (Or.inr rfl) hL7
  obtain ⟨hk6, hε6⟩ := hε1 6 (by norm_num) (by norm_num)
  have hev : Even L.length := by
    have e : (⟨nfw r l (-1) L, hm⟩ : Hs (7 - 1)) =
        ⟨tx r l ((6 : ℕ) : ℤ), hk6⟩ * ⟨tx r l ((6 : ℕ) : ℤ), hk6⟩ := by
      apply Subtype.ext
      show nfw r l (-1) L = tx r l ((6 : ℕ) : ℤ) * tx r l ((6 : ℕ) : ℤ)
      rw [hLeq, pow_two]
      simp
    rw [e, map_mul, hε6] at hεL
    have h0 : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 =
        Multiplicative.ofAdd ((0 : ℕ) : ZMod 2) := by decide
    rw [h0] at hεL
    have := Multiplicative.ofAdd.injective hεL
    exact (ZMod.natCast_eq_zero_iff_even).1 this.symm
  have hpal := sq_nf_palindromic h h7 (i := 6) (by norm_num) (by norm_num) (-1) (Or.inr rfl) hL
    hL6 (by simpa using hLeq)
  have hpal' : L = (L.map (fun t : ℤ => 6 - t)).reverse := by simpa using hpal
  have hL5 : ∀ t ∈ L, 1 ≤ t ∧ t < 6 := fun t ht => ⟨(hL1 t ht).1, by
    have := (hL1 t ht).2; simp at this; omega⟩
  obtain ⟨hw42, hw51, hw5421⟩ := Seven.words h habel hnab
  have key : (∃ d ∈ Hs 5, tx r l 7 * tx r l 1 * tx r l 7 = d) → False := by
    rintro ⟨d, hd, hdeq⟩
    have hc := x_conj7 h h7 1
    refine Seven.contra_of_conj (hh := rho r ξ 7 * tx r l ((7 : ℕ) : ℤ))
      (hs := rho r ξ 7 * (rho r ξ 7 * tx r l ((7 : ℕ) : ℤ)) * rho r ξ 7 *
        (tx r l ((7 : ℕ) : ℤ))⁻¹) h ?_ ?_ ?_ hd ?_
    · obtain ⟨L, hL, hL1, hodd, hLh⟩ := parity_h7 h h7
      exact ⟨L, hL, fun t ht => ⟨(hL1 t ht).1, by simpa using (hL1 t ht).2⟩, hodd, hLh⟩
    · intro L hodd hLh
      simpa using hstar7 h h7 L hodd hLh
    · intro L hL hL1 hodd hLh
      have := support7 h h7 (i := 3) (by norm_num) (by norm_num) (by simpa using habel) L hL
        (fun t ht => ⟨(hL1 t ht).1, by simpa using (hL1 t ht).2⟩) hodd hLh 6 (by norm_num)
        (by norm_num)
      simpa using this
    · have e7 : tx r l ((7 : ℕ) : ℤ) = tx r l 7 := by norm_num
      have e6 : tx r l (((7 : ℕ) : ℤ) - 1) = tx r l 6 := by norm_num
      rw [e6] at hc
      rw [← hdeq, ← e7]
      exact hc.symm
  rcases Seven.classify hL hL5 hpal' hev with rfl | rfl | rfl | rfl
  ·
    have hc6 : tx r l 6 * tx r l 6 = 1 := by
      rw [← pow_two, ← hLeq]
      simp [nfw]
    exact key (Seven.caseA h habel (Or.inl hc6))
  ·
    have := sq_nf_palindromic h h7 (i := 6) (by norm_num) (by norm_num) 1 (Or.inl rfl)
      (L := [5, 3, 2, 1]) (by simp) (by simp) (by simpa using hw51.symm.trans hLeq)
    simp at this
  ·
    have hc6 : tx r l 6 * tx r l 6 = tx r l 4 * tx r l 2 := by
      rw [← pow_two, ← hLeq]
      simp [nfw, Seven.inv4 h habel (k := 4) (by norm_num) (by norm_num)]
    exact key (Seven.caseA h habel (Or.inr hc6))
  ·
    have := sq_nf_palindromic h h7 (i := 6) (by norm_num) (by norm_num) 1 (Or.inl rfl)
      (L := [5, 4, 3, 1]) (by simp) (by simp) (by simpa using hw5421.symm.trans hLeq)
    simp at this

end CFSG.Quasithin.Fan86.Tutte

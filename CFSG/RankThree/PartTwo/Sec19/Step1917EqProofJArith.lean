module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
public import CFSG.RankThree.PartTwo.Sec4.Statements
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofArith
import CFSG.RankThree.PartTwo.Sec19.Step1917StepsOrders
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartTwo.KFacts.K72SLPiIdent

public section

namespace CFSG.RankThree.PartTwo.Sec19.Step1917EqProof

open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Open (ordA)

theorem eq_of_slOrder_eq {π : Bool} {Q Q' : ℕ} (hQ : 2 ≤ Q) (hQ' : 2 ≤ Q')
    (h : Q ^ 3 * (Q ^ 2 - 1) * cond π (Q ^ 3 - 1) (Q ^ 3 + 1) =
      Q' ^ 3 * (Q' ^ 2 - 1) * (Q' ^ 3 - 1)) : π = true ∧ Q = Q' := by
  cases π
  · exact absurd h.symm (sl3Order_ne_su3Order hQ' hQ)
  · refine ⟨rfl, ?_⟩
    rcases Nat.lt_trichotomy Q Q' with hlt | heq | hlt
    · exact absurd h (KFacts.sl3Order_lt (by omega) hlt).ne
    · exact heq
    · exact absurd h.symm (KFacts.sl3Order_lt (by omega) hlt).ne

theorem three_mul_cube_lt {x : ℕ} (hx : 3 ≤ x) : 3 * x ^ 3 < (2 * x - 1) ^ 3 := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 3 := ⟨x - 3, by omega⟩
  have e : 2 * (y + 3) - 1 = 2 * y + 5 := by omega
  rw [e]
  nlinarith [sq_nonneg y, mul_nonneg (sq_nonneg y) (Nat.zero_le y)]

theorem slOrder_ne_three_mul {π : Bool} {p f n : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hn : 1 ≤ n)
    (hq : Sec4.ModThree π (p ^ f)) :
    (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * cond π ((p ^ f) ^ 3 - 1) ((p ^ f) ^ 3 + 1) ≠
      3 * ((2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
  intro h
  obtain ⟨x, hxdef⟩ : ∃ x, x = 2 ^ n := ⟨_, rfl⟩
  rw [← hxdef] at h
  have hx2 : 2 ≤ x := hxdef ▸ le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  have hQ2 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  have hle : (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) ≤
      (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * cond π ((p ^ f) ^ 3 - 1) ((p ^ f) ^ 3 + 1) := by
    cases π
    · exact (sl3Order_lt_su3Order hQ2).le
    · exact le_rfl
  have hx3 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hx2' : 4 ≤ x ^ 2 := by nlinarith
  by_cases hp2 : p = 2
  · subst hp2
    have hodd : Odd (((2 ^ f) ^ 2 - 1) * cond π ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1)) := by
      refine (Timmesfeld.Orders.odd_pow_sub_one (by omega) two_pos).mul ?_
      cases π
      · exact Timmesfeld.Orders.odd_pow_add_one (by omega) three_pos
      · exact Timmesfeld.Orders.odd_pow_sub_one (by omega) three_pos
    have hodd' : Odd (3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1))) :=
      (by decide : Odd 3).mul ((Timmesfeld.Orders.odd_pow_sub_one (by omega) two_pos).mul
        (Timmesfeld.Orders.odd_pow_sub_one (by omega) three_pos))
    have h' : 2 ^ (f * 3) * (((2 ^ f) ^ 2 - 1) * cond π ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1)) =
        2 ^ (n * 3) * (3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1))) := by
      rw [pow_mul, pow_mul, ← mul_assoc, h, hxdef]
      ring
    have hfn : f = n := by
      have := Timmesfeld.Orders.eq_of_two_pow_mul_odd hodd hodd' h'
      omega
    subst hfn
    rw [← hxdef] at h
    have hpos : 0 < x ^ 3 * (x ^ 2 - 1) := Nat.mul_pos (by omega) (by omega)
    cases π
    ·
      have h2 : x ^ 3 * (x ^ 2 - 1) * (x ^ 3 + 1) = x ^ 3 * (x ^ 2 - 1) * (3 * (x ^ 3 - 1)) := by
        simp only [Bool.cond_false] at h
        rw [h]
        ring
      have h3 := Nat.eq_of_mul_eq_mul_left hpos h2
      have : 8 ≤ x ^ 3 := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ x ^ 3 := Nat.pow_le_pow_left hx2 3
      omega
    · have h2 : x ^ 3 * (x ^ 2 - 1) * (x ^ 3 - 1) = 3 * (x ^ 3 * (x ^ 2 - 1) * (x ^ 3 - 1)) := by
        simpa only [Bool.cond_true] using h
      have hpos' : 0 < x ^ 3 * (x ^ 2 - 1) * (x ^ 3 - 1) := Nat.mul_pos hpos (by
        have : 8 ≤ x ^ 3 := by
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ x ^ 3 := Nat.pow_le_pow_left hx2 3
        omega)
      omega
  ·
    have hp3 : p ≠ 3 := by
      rintro rfl
      have : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
      cases π
      · change 3 ^ f % 3 = 2 at hq
        omega
      · change 3 ^ f % 3 = 1 at hq
        omega
    have hp5 : 5 ≤ p := by
      have := hp.two_le
      by_contra hlt
      push Not at hlt
      interval_cases p <;> first | omega | exact absurd hp (by norm_num)
    set Q := p ^ f with hQdef
    have hQ5 : 5 ≤ Q := le_trans hp5 (Nat.le_self_pow (by omega) p)
    have hQodd : Odd Q := (hp.odd_of_ne_two hp2).pow
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    ·
      obtain rfl : n = 1 := by omega
      have hx : x = 2 := by rw [hxdef]; norm_num
      subst hx
      have h5 := Step1917Steps.sl3Order_le (x := 5) (y := Q) (by norm_num) hQ5
      have h6 := h5.trans (hle.trans h.le)
      norm_num at h6
    ·
      have hdvd : (2 ^ (n * 3) ∣ Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1)) ∨
          (2 ^ (n * 3) ∣ Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1)) := by
        have hd : 2 ^ (n * 3) ∣ Q ^ 3 * (Q ^ 2 - 1) * cond π (Q ^ 3 - 1) (Q ^ 3 + 1) := by
          rw [h, pow_mul, ← hxdef]
          exact Dvd.intro ((3 * ((x ^ 2 - 1) * (x ^ 3 - 1)))) (by ring)
        cases π
        · exact Or.inr hd
        · exact Or.inl hd
      have h2 := Step1917Steps.two_pow_le_of_dvd_sl3Order hQodd (by omega) (by omega) hdvd
      have h3 : 2 * x ≤ 2 ^ (n * 3 / 2) := by
        rw [hxdef, ← pow_succ']
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hx4 : 4 ≤ x := by
        rw [hxdef]
        exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2)
      have hQx : 2 * x - 1 ≤ Q := by omega
      have hmono := Step1917Steps.sl3Order_le (x := 2 * x - 1) (y := Q) (by omega) hQx
      set y := 2 * x - 1 with hydef
      have hxy : x ≤ y := by omega
      have hy3 : 3 * x ^ 3 < y ^ 3 := three_mul_cube_lt (by omega)
      have hy2 : x ^ 2 - 1 ≤ y ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hxy 2) 1
      have hy3' : x ^ 3 - 1 ≤ y ^ 3 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hxy 3) 1
      have hpos : 0 < (x ^ 2 - 1) * (x ^ 3 - 1) := Nat.mul_pos (by omega) (by
        have : 8 ≤ x ^ 3 := by
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ x ^ 3 := Nat.pow_le_pow_left hx2 3
        omega)
      have hkey : 3 * (x ^ 3 * (x ^ 2 - 1) * (x ^ 3 - 1)) < y ^ 3 * (y ^ 2 - 1) * (y ^ 3 - 1) := by
        calc 3 * (x ^ 3 * (x ^ 2 - 1) * (x ^ 3 - 1))
            = (3 * x ^ 3) * ((x ^ 2 - 1) * (x ^ 3 - 1)) := by ring
          _ < y ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) := Nat.mul_lt_mul_of_pos_right hy3 hpos
          _ ≤ y ^ 3 * ((y ^ 2 - 1) * (y ^ 3 - 1)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul hy2 hy3')
          _ = y ^ 3 * (y ^ 2 - 1) * (y ^ 3 - 1) := by ring
      omega

theorem eq_two_of_card {π : Bool} {p f n N : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hn : 1 ≤ n)
    (hq : Sec4.ModThree π (p ^ f))
    (h3 : N * 3 = (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * cond π ((p ^ f) ^ 3 - 1) ((p ^ f) ^ 3 + 1))
    (hN : N = (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) ∨
      N * Nat.gcd 3 (2 ^ n - 1) = (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :
    π = true ∧ p = 2 ∧ f = n := by
  have hQ2 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  have hx2 : 2 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  have hne := slOrder_ne_three_mul hp hf hn hq
  have hg : Nat.gcd 3 (2 ^ n - 1) = 1 ∨ Nat.gcd 3 (2 ^ n - 1) = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 _)
  have hfin : N * 3 = (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) → π = true ∧ p = 2 ∧
      f = n := by
    intro hN3
    obtain ⟨hπ, hQ⟩ := eq_of_slOrder_eq hQ2 hx2 (h3.symm.trans hN3)
    have hp2 : p = 2 := by
      have : p ∣ 2 ^ n := hQ ▸ dvd_pow_self p (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this)
    subst hp2
    exact ⟨hπ, rfl, Nat.pow_right_injective le_rfl hQ⟩
  rcases hN with hN | hN
  · exact absurd (by rw [← h3, hN]; ring) hne
  · rcases hg with hg | hg
    · rw [hg, mul_one] at hN
      exact absurd (by rw [← h3, hN]; ring) hne
    · rw [hg] at hN
      exact hfin hN

theorem card_kStar {Y : Type} [Group Y] {n : ℕ} (hn : 1 ≤ n)
    (hY : Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) ∨
      Nonempty (Y ≃* projSL 3 (GaloisField 2 n))) :
    Nat.card Y = (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) ∨
      Nat.card Y * Nat.gcd 3 (2 ^ n - 1) = (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := by
  rcases hY with hY | hY
  · obtain ⟨ψ⟩ := hY
    left
    rw [Nat.card_congr ψ.toEquiv, Step1911Proof.card_SL3 hn, pow_mul]
    ring
  · obtain ⟨ψ⟩ := hY
    right
    rw [Nat.card_congr ψ.toEquiv, Step1911Proof.card_projSL (by norm_num) hn,
      show 3 - 1 = 2 from rfl, Step1911Proof.ordA_two_mul_gcd, pow_mul]
    ring

theorem psl_of_card {Y : Type} [Group Y] {π : Bool} {p f n : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hn : 1 ≤ n) (hq : Sec4.ModThree π (p ^ f))
    (h3 : Nat.card Y * 3 =
      (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * cond π ((p ^ f) ^ 3 - 1) ((p ^ f) ^ 3 + 1))
    (hY : Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) ∨
      Nonempty (Y ≃* projSL 3 (GaloisField 2 n))) :
    Nonempty (Y ≃* projSL 3 (GaloisField 2 n)) ∧ 2 ^ n % 3 = 1 := by
  have hne := slOrder_ne_three_mul hp hf hn hq
  rcases hY with ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩
  · exfalso
    have hc : Nat.card Y = (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := by
      rw [Nat.card_congr ψ.toEquiv, Step1911Proof.card_SL3 hn, pow_mul]
      ring
    exact hne (by rw [← h3, hc]; ring)
  · refine ⟨⟨ψ⟩, ?_⟩
    have hc : Nat.card Y * Nat.gcd 3 (2 ^ n - 1) =
        (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := by
      rw [Nat.card_congr ψ.toEquiv, Step1911Proof.card_projSL (by norm_num) hn,
        show 3 - 1 = 2 from rfl, Step1911Proof.ordA_two_mul_gcd, pow_mul]
      ring
    have hg : Nat.gcd 3 (2 ^ n - 1) = 1 ∨ Nat.gcd 3 (2 ^ n - 1) = 3 :=
      (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 _)
    rcases hg with hg | hg
    · rw [hg, mul_one] at hc
      exact absurd (by rw [← h3, hc]; ring) hne
    · have h3d : 3 ∣ 2 ^ n - 1 := hg ▸ Nat.gcd_dvd_right 3 (2 ^ n - 1)
      have h2 : 2 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
      omega

theorem false_of_kStar_card {Y : Type} [Group Y] {n : ℕ} (hn : 1 ≤ n)
    (hY : Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) ∨
      Nonempty (Y ≃* projSL 3 (GaloisField 2 n)))
    (hc : Nat.card Y = 2520 ∨ Nat.card Y = 443520 ∨ Nat.card Y = 95040 ∨
      Nat.card Y = 604800) : False := by
  have hcard := card_kStar hn hY
  have hg : Nat.gcd 3 (2 ^ n - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 _)
  have hle : Nat.card Y ≤ 604800 := by omega
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · interval_cases n <;> norm_num at hcard <;> omega
  · have hx : 8 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn3)
    have hm := Step1917Steps.sl3Order_le (x := 8) (y := 2 ^ n) (by norm_num) hx
    norm_num at hm
    rcases hcard with h | h
    · omega
    · have : Nat.card Y * Nat.gcd 3 (2 ^ n - 1) ≤ Nat.card Y * 3 := Nat.mul_le_mul_left _ hg
      omega

theorem false_of_isoLThreePi_card {Y : Type} [Group Y] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h : Sec4.IsoLThreePi Y p e)
    (hc : Nat.card Y = 2520 ∨ Nat.card Y = 443520 ∨ Nat.card Y = 95040 ∨
      Nat.card Y = 604800) : False := by
  have hp : p.Prime := Fact.out
  have hQ : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
  rcases Step1917Steps.three_mul_card_of_isoLThreePi he h with ⟨-, hf, -⟩ | ⟨-, hf⟩
  · rcases hc with hc | hc | hc | hc <;> rw [hc] at hf
    · exact Step1917Steps.sl3Order_ne_of_bracket (a := 3) hQ (by norm_num) (by norm_num)
        (by norm_num) hf
    · exact Step1917Steps.sl3Order_ne_of_bracket (a := 5) hQ (by norm_num) (by norm_num)
        (by norm_num) hf
    · exact Step1917Steps.sl3Order_ne_of_bracket (a := 4) hQ (by norm_num) (by norm_num)
        (by norm_num) hf
    · exact Step1917Steps.sl3Order_ne_of_bracket (a := 6) hQ (by norm_num) (by norm_num)
        (by norm_num) hf
  · rcases hc with hc | hc | hc | hc <;> rw [hc] at hf
    · exact Step1917Steps.su3Order_ne_of_bracket (a := 3) hQ (by norm_num) (by norm_num)
        (by norm_num) hf
    · exact Step1917Steps.su3Order_ne_of_bracket (a := 5) hQ (by norm_num) (by norm_num)
        (by norm_num) hf
    · exact Step1917Steps.su3Order_ne_of_bracket (a := 4) hQ (by norm_num) (by norm_num)
        (by norm_num) hf
    · exact Step1917Steps.su3Order_ne_of_bracket (a := 6) hQ (by norm_num) (by norm_num)
        (by norm_num) hf

end CFSG.RankThree.PartTwo.Sec19.Step1917EqProof

module

public import CFSG.Monster.B.Recog.GenericGoldschmidtArith

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Recog

open CFSG.Open CFSG.SignalizerFunctorTheorem.McBride Matrix
open scoped MatrixGroups

namespace GoldschmidtArithOmega

open GoldschmidtArith

theorem psl2_odd_factorization {p f : ℕ} [hp : Fact p.Prime] (hpo : Odd p) (hf : 0 < f)
    (hq : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) {L : Type} [Group L]
    (e : L ≃* PSL(2, GaloisField p f)) : (Nat.card L).factorization 2 = 2 := by
  have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf.ne'
  have hcard := CFSG.GorensteinWalter.psl2_card_formula (GaloisField p f)
    ⟨p, f, hp.out, hpo, hf, hK⟩
  rw [hK] at hcard
  have h16 := sq_mod_sixteen hq
  have hq1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos hp.out.pos f)
  obtain ⟨a, ha⟩ : ∃ a, (p ^ f) ^ 2 - 1 = 8 * (2 * a + 1) := ⟨(p ^ f) ^ 2 / 16, by omega⟩
  have hodd : Odd (p ^ f * (2 * a + 1)) := (hpo.pow).mul (odd_two_mul_add_one a)
  have e2 : p ^ f * ((p ^ f) ^ 2 - 1) / 2 = 2 ^ 2 * (p ^ f * (2 * a + 1)) := by
    rw [ha, show p ^ f * (8 * (2 * a + 1)) = 2 * (2 ^ 2 * (p ^ f * (2 * a + 1))) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
  rw [Nat.card_congr e.toEquiv, show Nat.card (PSL(2, GaloisField p f)) =
    Nat.card (CFSG.GorensteinWalter.PSL2 (GaloisField p f)) from rfl, hcard, e2,
    factorization_two_pow_mul_odd 2 hodd]

theorem ree_factorization {m : ℕ} {L : Type} [Group L]
    (h : Nat.card L = ordRee (3 ^ (2 * m + 1))) : (Nat.card L).factorization 2 = 3 := by
  have hq := three_pow_odd_mod_eight m
  have hq3 : (3 ^ (2 * m + 1)) ^ 3 % 8 = 3 := by
    rw [Nat.pow_mod, hq]
  obtain ⟨a, ha⟩ : ∃ a, (3 ^ (2 * m + 1)) ^ 3 + 1 = 4 * (2 * a + 1) :=
    ⟨(3 ^ (2 * m + 1)) ^ 3 / 8, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, 3 ^ (2 * m + 1) - 1 = 2 * (2 * b + 1) :=
    ⟨3 ^ (2 * m + 1) / 8 * 2, by omega⟩
  have hodd : Odd ((3 ^ (2 * m + 1)) ^ 3 * (2 * a + 1) * (2 * b + 1)) :=
    ((Odd.pow (by decide)).pow.mul (odd_two_mul_add_one a)).mul (odd_two_mul_add_one b)
  rw [h, ordRee, ha, hb, show (3 ^ (2 * m + 1)) ^ 3 * (4 * (2 * a + 1)) * (2 * (2 * b + 1)) =
    2 ^ 3 * ((3 ^ (2 * m + 1)) ^ 3 * (2 * a + 1) * (2 * b + 1)) by ring,
    factorization_two_pow_mul_odd 3 hodd]

theorem sz_not_three_dvd
    {n : ℕ} {L : Type} [Group L] (e : L ≃* Sz n) : ¬ 3 ∣ Nat.card L := by
  have hq : 2 ^ (2 * n + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hq2 : (2 ^ (2 * n + 1)) ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  have hq1 : 1 ≤ 2 ^ (2 * n + 1) := Nat.one_le_two_pow
  rw [Nat.card_congr e.toEquiv, NearSolvable.card_sz n, Nat.dvd_iff_mod_eq_zero, Nat.mul_mod,
    Nat.mul_mod ((2 ^ (2 * n + 1)) ^ 2), hq2,
    show ((2 ^ (2 * n + 1)) ^ 2 + 1) % 3 = 2 by omega,
    show (2 ^ (2 * n + 1) - 1) % 3 = 1 by omega]
  norm_num

theorem not_dvd_card_GL_seven_three : ¬ 3 ^ 5 ∣ Nat.card (GL (Fin 7) (ZMod 11)) := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have h : Nat.card (GL (Fin 7) (ZMod 11)) =
      ∏ i : Fin 7, (Fintype.card (ZMod 11) ^ 7 - Fintype.card (ZMod 11) ^ (i : ℕ)) :=
    Matrix.card_GL_field (𝔽 := ZMod 11) 7
  rw [h, ZMod.card, Fin.prod_univ_seven]
  norm_num

theorem factorization_bounds {L X : Type} [Group L] [Finite L] [Group X] [Finite X]
    (hX : (Nat.card X).factorization 2 = 37) (h12 : 2 ^ 12 ∣ Nat.card L)
    (hLX : Nat.card L ∣ Nat.card X) :
    12 ≤ (Nat.card L).factorization 2 ∧ (Nat.card L).factorization 2 ≤ 37 :=
  ⟨(Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.card_pos (α := L)).ne').1 h12,
    hX ▸ (Nat.factorization_le_iff_dvd (Nat.card_pos (α := L)).ne'
      (Nat.card_pos (α := X)).ne').2 hLX 2⟩

end GoldschmidtArithOmega

open GoldschmidtArith GoldschmidtArithOmega

theorem hAr_of_card_omega8 {X : Type} [Group X] [Finite X]
    (hX : (Nat.card X).factorization 2 = 37) {n₀ : ℕ} (hn₀ : 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7 ∣ n₀) :
    ∀ (L : Type) [Group L] [Finite L], CFSG.Open.goldschmidtSimpleType L →
      n₀ ∣ Nat.card L → Nat.card L ∣ Nat.card X → False := by
  intro L _ _ hL hnL hLX
  have hdvd := hn₀.trans hnL
  have h12 : 2 ^ 12 ∣ Nat.card L :=
    (by norm_num : 2 ^ 12 ∣ 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7).trans hdvd
  have h3 : 3 ^ 5 ∣ Nat.card L :=
    (by norm_num : 3 ^ 5 ∣ 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7).trans hdvd
  obtain ⟨hlo, hhi⟩ := factorization_bounds hX h12 hLX
  rcases hL with ⟨f, hf, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpo, hf, -, hq, ⟨e⟩⟩ |
    ⟨m, -, hm⟩ | ⟨⟨e⟩⟩
  ·
    have hcard : Nat.card L = 2 ^ f * ((2 ^ f) ^ 2 - 1) :=
      (Nat.card_congr e.toEquiv).trans (NearSolvable.card_psl2_even (by omega))
    have hodd : Odd ((2 ^ f) ^ 2 - 1) := by
      rw [← pow_mul]
      exact odd_two_pow_sub_one (by omega)
    rw [hcard, factorization_two_pow_mul_odd f hodd] at hlo hhi
    rw [hcard] at h3
    interval_cases f <;> norm_num at h3
  · exact sz_not_three_dvd e ((by norm_num : 3 ∣ 3 ^ 5).trans h3)
  ·
    have h := NearSolvable.card_psu3_mul_gcd (p := f) (by omega)
    rw [← Nat.card_congr e.toEquiv] at h
    have hg : Odd (Nat.gcd 3 (2 ^ f + 1)) := Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left _ _)
    have hodd : Odd (((2 ^ f) ^ 2 - 1) * (2 ^ (f * 3) + 1)) := by
      rw [← pow_mul]
      exact (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_add_one (by omega))
    have hfac : (Nat.card L * Nat.gcd 3 (2 ^ f + 1)).factorization 2 =
        ((2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1))).factorization 2 := by
      rw [h]
    rw [Nat.factorization_mul Nat.card_pos.ne' hg.pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hg.not_two_dvd_nat, add_zero, ← pow_mul,
      factorization_two_pow_mul_odd _ hodd] at hfac
    rw [hfac] at hlo hhi
    have hdvd' : 3 ^ 5 * 5 ^ 2 * 7 ∣ (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) := by
      rw [← h]
      exact ((by norm_num : 3 ^ 5 * 5 ^ 2 * 7 ∣ 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7).trans hdvd).trans
        (Dvd.intro _ rfl)
    have hf4 : 4 ≤ f := by omega
    have hf12 : f ≤ 12 := by omega
    interval_cases f <;> norm_num at hdvd'
  · have h2 := psl2_odd_factorization hpo hf hq e
    omega
  · have h2 := ree_factorization hm
    omega
  · have hdvdGL : Nat.card L ∣ Nat.card (GL (Fin 7) (ZMod 11)) := by
      rw [Nat.card_congr e.toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    exact not_dvd_card_GL_seven_three (h3.trans hdvdGL)

end CFSG.Monster.B.Recog

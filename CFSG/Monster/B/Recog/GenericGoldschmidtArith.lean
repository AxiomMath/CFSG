module

public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Recog

open CFSG.Open CFSG.SignalizerFunctorTheorem.McBride Matrix
open scoped MatrixGroups

namespace GoldschmidtArith

theorem factorization_two_pow_mul_odd (f : ℕ) {m : ℕ} (hm : Odd m) :
    (2 ^ f * m).factorization 2 = f := by
  rw [Nat.factorization_mul (by positivity) hm.pos.ne', Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hm.not_two_dvd_nat, smul_eq_mul, mul_one, add_zero]

theorem odd_two_pow_sub_one {k : ℕ} (hk : k ≠ 0) : Odd (2 ^ k - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, hk⟩) odd_one

theorem odd_two_pow_add_one {k : ℕ} (hk : k ≠ 0) : Odd (2 ^ k + 1) :=
  (Nat.even_pow.2 ⟨even_two, hk⟩).add_one

theorem psl2_even_case {f : ℕ} (hf : 3 ≤ f) {L : Type} [Group L]
    (e : L ≃* PSL(2, GaloisField 2 f)) (h40 : (Nat.card L).factorization 2 = 40) :
    ¬ 23 ∣ Nat.card L := by
  have hcard : Nat.card L = 2 ^ f * ((2 ^ f) ^ 2 - 1) :=
    (Nat.card_congr e.toEquiv).trans (NearSolvable.card_psl2_even (by omega))
  have hodd : Odd ((2 ^ f) ^ 2 - 1) := by
    rw [← pow_mul]
    exact odd_two_pow_sub_one (by omega)
  rw [hcard, factorization_two_pow_mul_odd f hodd] at h40
  subst h40
  rw [hcard]
  norm_num

theorem sz_case {n : ℕ} {L : Type} [Group L] (e : L ≃* Sz n) :
    (Nat.card L).factorization 2 ≠ 40 := by
  rw [Nat.card_congr e.toEquiv, NearSolvable.card_sz n, mul_assoc, ← pow_mul,
    factorization_two_pow_mul_odd _
      ((odd_two_pow_add_one (by omega)).mul (odd_two_pow_sub_one (by omega)))]
  omega

theorem psu3_case {f : ℕ} (hf : 2 ≤ f) {L : Type} [Group L] [Finite L] (e : L ≃* PSU3 2 f) :
    (Nat.card L).factorization 2 ≠ 40 := by
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
  rw [hfac]
  omega

theorem sq_mod_sixteen {q : ℕ} (hq : q % 8 = 3 ∨ q % 8 = 5) : q ^ 2 % 16 = 9 := by
  have h : q % 16 = 3 ∨ q % 16 = 11 ∨ q % 16 = 5 ∨ q % 16 = 13 := by omega
  rw [Nat.pow_mod]
  rcases h with h | h | h | h <;> rw [h]

theorem psl2_odd_case {p f : ℕ} [hp : Fact p.Prime] (hpo : Odd p) (hf : 0 < f)
    (hq : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) {L : Type} [Group L]
    (e : L ≃* PSL(2, GaloisField p f)) : (Nat.card L).factorization 2 ≠ 40 := by
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
  norm_num

theorem three_pow_odd_mod_eight (m : ℕ) : 3 ^ (2 * m + 1) % 8 = 3 := by
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem ree_case {m : ℕ} {L : Type} [Group L] (h : Nat.card L = ordRee (3 ^ (2 * m + 1))) :
    (Nat.card L).factorization 2 ≠ 40 := by
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
  norm_num

theorem not_dvd_card_GL_seven : ¬ 2 ^ 15 ∣ Nat.card (GL (Fin 7) (ZMod 11)) := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have h : Nat.card (GL (Fin 7) (ZMod 11)) =
      ∏ i : Fin 7, (Fintype.card (ZMod 11) ^ 7 - Fintype.card (ZMod 11) ^ (i : ℕ)) :=
    Matrix.card_GL_field (𝔽 := ZMod 11) 7
  rw [h, ZMod.card, Fin.prod_univ_seven]
  norm_num

theorem j1_case {L : Type} [Group L] (e : L ≃* goldschmidtJ1) :
    (Nat.card L).factorization 2 ≠ 40 := by
  intro h40
  have hdvd : Nat.card L ∣ Nat.card (GL (Fin 7) (ZMod 11)) := by
    rw [Nat.card_congr e.toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have h2 : 2 ^ 40 ∣ Nat.card L := by
    have h := Nat.ordProj_dvd (Nat.card L) 2
    rwa [h40] at h
  exact not_dvd_card_GL_seven ((pow_dvd_pow 2 (by norm_num)).trans (h2.trans hdvd))

end GoldschmidtArith

open GoldschmidtArith

theorem goldschmidtSimpleType_two_part {L : Type} [Group L] [Finite L]
    (hL : goldschmidtSimpleType L) (h40 : (Nat.card L).factorization 2 = 40) :
    ¬ 23 ∣ Nat.card L := by
  rcases hL with ⟨f, hf, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpo, hf, -, hq, ⟨e⟩⟩ |
    ⟨m, -, hm⟩ | ⟨⟨e⟩⟩
  · exact psl2_even_case hf e h40
  · exact absurd h40 (sz_case e)
  · exact absurd h40 (psu3_case hf e)
  · exact absurd h40 (psl2_odd_case hpo hf hq e)
  · exact absurd h40 (ree_case hm)
  · exact absurd h40 (j1_case e)

theorem hAr_of_card {X : Type*} [Group X] [Finite X] {N : Subgroup X}
    (h2N : 2 ^ 40 ∣ Nat.card N) (h23 : 23 ∣ Nat.card N) (hX : (Nat.card X).factorization 2 = 40) :
    ∀ (L : Type) [Group L] [Finite L], goldschmidtSimpleType L →
      Nat.card N ∣ Nat.card L → Nat.card L ∣ Nat.card X → False := by
  intro L _ _ hL hNL hLX
  have hL40 : (Nat.card L).factorization 2 = 40 := by
    apply le_antisymm
    · rw [← hX]
      exact (Nat.factorization_le_iff_dvd (Nat.card_pos (α := L)).ne'
        (Nat.card_pos (α := X)).ne').2 hLX 2
    · exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.card_pos (α := L)).ne').1
        (h2N.trans hNL)
  exact goldschmidtSimpleType_two_part hL hL40 (h23.trans hNL)

end CFSG.Monster.B.Recog

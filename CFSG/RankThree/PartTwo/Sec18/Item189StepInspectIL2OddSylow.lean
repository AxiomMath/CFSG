module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow
import CFSG.Quasithin.Background.F6CatDickson
import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIL2OddTools

public section

namespace CFSG.RankThree.PartTwo.Sec18

open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

theorem card_mul_two_l2odd189 (hp2 : p ≠ 2) {m : ℕ} (hm : m ≠ 0) :
    Nat.card PSL(2, GaloisField p m) * 2 = p ^ m * ((p ^ m) ^ 2 - 1) := by
  have hK := GaloisField.card p m hm
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p m)) :=
    ⟨p, m, Fact.out, hpodd, Nat.one_le_iff_ne_zero.mpr hm, hK⟩
  rw [CFSG.GorensteinWalter.psl2_card_formula _ hodd, hK]
  apply Nat.div_mul_cancel
  exact dvd_mul_of_dvd_right (even_iff_two_dvd.mp (Nat.Odd.sub_odd hpodd.pow.pow odd_one)) _

theorem prime_dvd_card_psl2_l2odd189 (hp2 : p ≠ 2) {m : ℕ} (hm : m ≠ 0) :
    p ∣ Nat.card PSL(2, GaloisField p m) := by
  have h : p ∣ Nat.card PSL(2, GaloisField p m) * 2 :=
    card_mul_two_l2odd189 hp2 hm ▸ dvd_mul_of_dvd_left (dvd_pow_self p hm) _
  exact ((Nat.Prime.dvd_mul Fact.out).mp h).resolve_right fun h2 =>
    hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h2)

theorem prime_dvd_card_pgl2_l2odd189 {m : ℕ} (hm : m ≠ 0) :
    p ∣ Nat.card PGL(2, GaloisField p m) := by
  rw [CFSG.GorensteinWalter.pgl2_card_formula, GaloisField.card p m hm]
  exact dvd_mul_of_dvd_left (dvd_pow_self p hm) _

theorem not_isCyclic_sylow_l2odd189 (hp2 : p ≠ 2) {f : ℕ} (hf : 1 ≤ f)
    {T : Subgroup PSL(2, GaloisField p f)}
    (hT : Nat.card T = 2 ^ (Nat.card PSL(2, GaloisField p f)).factorization 2) :
    ¬ IsCyclic T ∧ 4 ≤ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p f)) :=
    ⟨p, f, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp2, hf, GaloisField.card p f (by omega)⟩
  obtain ⟨m, hm, ⟨e⟩⟩ :=
    CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model _ hodd (Sylow.ofCard T hT)
  have hm2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hcard : Nat.card T = 2 * 2 ^ m := (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  refine ⟨fun hc => ?_, by omega⟩
  have : IsCyclic ↥(Sylow.ofCard T hT : Subgroup PSL(2, GaloisField p f)) := hc
  exact DihedralGroup.not_isCyclic (n := 2 ^ m) (by omega)
    (isCyclic_of_surjective e.toMonoidHom e.surjective)

theorem card_sylow_eq_four_l2odd189 (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {f : ℕ} (hf : 1 ≤ f) {T : Subgroup PSL(2, GaloisField p f)}
    (hT : Nat.card T = 2 ^ (Nat.card PSL(2, GaloisField p f)).factorization 2)
    {x : PSL(2, GaloisField p f)} (hx : orderOf x = 3)
    (hxT : x ∈ Subgroup.normalizer (T : Set PSL(2, GaloisField p f))) : Nat.card T = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hTc, hT4⟩ := not_isCyclic_sylow_l2odd189 hp2 hf hT
  have hT2 : IsPGroup 2 T := IsPGroup.of_card hT
  have hx3 : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  set B := T ⊔ Subgroup.zpowers x with hB
  have hBcard : Nat.card B = Nat.card T * 3 := by
    rw [hB, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer T _
      (Subgroup.zpowers_le.mpr hxT) (IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ hT2 hx3),
      Nat.card_zpowers, hx]
  have hTB : T ≤ B := le_sup_left
  have hxB : x ∈ B := (le_sup_right : Subgroup.zpowers x ≤ B) (Subgroup.mem_zpowers x)
  have hBN : B ≤ Subgroup.normalizer (T : Set PSL(2, GaloisField p f)) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxT)
  have hpB : ¬ p ∣ Nat.card B := by
    rw [hBcard, hT]
    intro h
    rcases (Nat.Prime.dvd_mul Fact.out).mp h with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
        ((Fact.out : p.Prime).dvd_of_dvd_pow h))
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp h)
  rcases CFSG.Quasithin.F6.dicksonPSL2_holds p f hf B with
      ⟨-, m, -, hm⟩ | ⟨hc, -⟩ | ⟨z, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, P, hPn, -, hPcard, hPc, -⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  ·
    have h2 : 2 ∣ p ^ m := by
      rw [← hm, hBcard, hT]
      exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by
        intro h0
        rw [h0, pow_zero] at hT
        omega)) _
    exact (hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two Fact.out).mp
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm).elim
  · exact (hTc (Subgroup.isCyclic_of_le (H' := B) hTB)).elim
  · exact (false_of_dihedral_l2odd189 e hTB hTc hT2 hxB hx hxT).elim
  ·
    have h12 : Nat.card B = 12 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
      rfl
    omega
  · exact (false_of_perm_four_l2odd189 e hTB hBN hBcard).elim
  ·
    have h60 : Nat.card B = 60 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
      rfl
    have h5 : 5 ∣ Nat.card T := ⟨4, by omega⟩
    rw [hT] at h5
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h5) (by norm_num)
  · have := hPn
    exact (false_of_borel_l2odd189 hTB hTc hT2 hp2 (IsPGroup.of_card hPcard) hPc).elim
  · have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at hm
      omega
    exact (hpB (Nat.card_congr e.toEquiv ▸ prime_dvd_card_psl2_l2odd189 hp2 hm0)).elim
  · have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero, zero_dvd_iff] at hm
      omega
    exact (hpB (Nat.card_congr e.toEquiv ▸ prime_dvd_card_pgl2_l2odd189 hm0)).elim

theorem mod_eight_l2odd189 (hp2 : p ≠ 2) {f : ℕ} (hf : 1 ≤ f)
    {T : Subgroup PSL(2, GaloisField p f)}
    (hT : Nat.card T = 2 ^ (Nat.card PSL(2, GaloisField p f)).factorization 2)
    (hT4 : Nat.card T = 4) : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5 := by
  have hfac : (Nat.card PSL(2, GaloisField p f)).factorization 2 = 2 :=
    Nat.pow_right_injective (le_refl 2)
      (show 2 ^ (Nat.card PSL(2, GaloisField p f)).factorization 2 = 2 ^ 2 by rw [← hT, hT4])
  have hc := card_mul_two_l2odd189 hp2 (m := f) (by omega)
  have hqodd : p ^ f % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  by_contra hne
  have h16 : (p ^ f) ^ 2 % 16 = 1 := by
    have h : p ^ f % 16 = 1 ∨ p ^ f % 16 = 7 ∨ p ^ f % 16 = 9 ∨ p ^ f % 16 = 15 := by omega
    rw [Nat.pow_mod]
    rcases h with h | h | h | h <;> rw [h]
  obtain ⟨s, hs⟩ : 16 ∣ (p ^ f) ^ 2 - 1 := by omega
  have h8 : 2 ^ 3 ∣ Nat.card PSL(2, GaloisField p f) := by
    have h : Nat.card PSL(2, GaloisField p f) * 2 = 16 * (p ^ f * s) := by rw [hc, hs]; ring
    exact ⟨p ^ f * s, by omega⟩
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h8
  omega

end CFSG.RankThree.PartTwo.Sec18

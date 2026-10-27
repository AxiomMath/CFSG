module

public import CFSG.LocalAnalysis.StandardType.GGExcMaxToral
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.RankThree.PartOne.K133H.WeylKey
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLBstar
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNFix
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNGenFix
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNGenTorus
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNTorus

public section

namespace CFSG.StandardType.ExcMaxToral

section OrderFiveFour

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.ExcMaxToral Polynomial
open scoped Matrix

private def ggB2a_E8list : List ℕ := [30, 24, 20, 18, 14, 12, 8, 2]

private lemma ggB2a_mem_E8list {x : ℕ} (hx : x ∈ ggB2a_E8list) : x ≠ 0 := by
  simp only [ggB2a_E8list, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private lemma ggB2a_ordE8_eq_prod (q : ℕ) :
    ordE8 q = q ^ 120 * (ggB2a_E8list.map fun e => q ^ e - 1).prod := by
  simp only [ggB2a_E8list, ordE8, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  ring

private lemma ggB2a_ordProj_list_prod (p : ℕ) (L : List ℕ) (hL : ∀ x ∈ L, x ≠ 0) :
    p ^ (L.prod).factorization p = (L.map fun x => p ^ x.factorization p).prod := by
  induction L with
  | nil => simp
  | cons a t ih =>
      have ha : a ≠ 0 := hL a (by simp)
      have ht : ∀ x ∈ t, x ≠ 0 := fun x hx => hL x (by simp [hx])
      have htprod : t.prod ≠ 0 := List.prod_ne_zero fun h0 => ht 0 h0 rfl
      rw [List.prod_cons, List.map_cons, List.prod_cons,
        Nat.ordProj_mul p ha htprod, ih ht]

private lemma ggB2a_prod_ne_zero {q : ℕ} (hq2 : 2 ≤ q) :
    (ggB2a_E8list.map fun e => q ^ e - 1).prod ≠ 0 :=
  List.prod_ne_zero fun h0 => by
    obtain ⟨e, he, hq0⟩ := List.mem_map.1 h0
    have he0 : e ≠ 0 := ggB2a_mem_E8list he
    have hlt : 1 < q ^ e := Nat.one_lt_pow he0 (by omega)
    omega

private lemma ggB2a_not_dvd_q {q : ℕ} (hq5 : orderOf (q : ZMod 5) = 4) : ¬ 5 ∣ q := by
  intro h
  have hq0 : (q : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff q 5).2 h
  have hpow : (q : ZMod 5) ^ 4 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hq5]
  rw [hq0, zero_pow (by norm_num : (4 : ℕ) ≠ 0)] at hpow
  exact zero_ne_one hpow

private lemma ggB2a_prod_eq {q : ℕ} (hq2 : 2 ≤ q) (hq5 : orderOf (q : ZMod 5) = 4) :
    (ggB2a_E8list.map fun e => 5 ^ (q ^ e - 1).factorization 5).prod =
      5 ^ (4 * (q ^ 4 - 1).factorization 5 + 1) := by
  have hpq : ¬ 5 ∣ q := ggB2a_not_dvd_q hq5
  have h30 : 5 ^ (q ^ 30 - 1).factorization 5 = 1 :=
    ordProj_pow_sub_one_of_not_dvd (p := 5) (q := q) (e := 4) (d := 30)
      (by omega) hq5 (by norm_num)
  have h18 : 5 ^ (q ^ 18 - 1).factorization 5 = 1 :=
    ordProj_pow_sub_one_of_not_dvd (p := 5) (q := q) (e := 4) (d := 18)
      (by omega) hq5 (by norm_num)
  have h14 : 5 ^ (q ^ 14 - 1).factorization 5 = 1 :=
    ordProj_pow_sub_one_of_not_dvd (p := 5) (q := q) (e := 4) (d := 14)
      (by omega) hq5 (by norm_num)
  have h2 : 5 ^ (q ^ 2 - 1).factorization 5 = 1 :=
    ordProj_pow_sub_one_of_not_dvd (p := 5) (q := q) (e := 4) (d := 2)
      (by omega) hq5 (by norm_num)
  have h24 : 5 ^ (q ^ 24 - 1).factorization 5 = 5 ^ (q ^ 4 - 1).factorization 5 := by
    have h := ordProj_pow_sub_one_of_dvd (p := 5) (q := q) (e := 4) (k := 6)
      (by norm_num) (by norm_num) hpq hq2 hq5 (by norm_num)
    rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 6), pow_zero, mul_one] at h
    simpa using h
  have h12 : 5 ^ (q ^ 12 - 1).factorization 5 = 5 ^ (q ^ 4 - 1).factorization 5 := by
    have h := ordProj_pow_sub_one_of_dvd (p := 5) (q := q) (e := 4) (k := 3)
      (by norm_num) (by norm_num) hpq hq2 hq5 (by norm_num)
    rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 3), pow_zero, mul_one] at h
    simpa using h
  have h8 : 5 ^ (q ^ 8 - 1).factorization 5 = 5 ^ (q ^ 4 - 1).factorization 5 := by
    have h := ordProj_pow_sub_one_of_dvd (p := 5) (q := q) (e := 4) (k := 2)
      (by norm_num) (by norm_num) hpq hq2 hq5 (by norm_num)
    rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 2), pow_zero, mul_one] at h
    simpa using h
  have h20 : 5 ^ (q ^ 20 - 1).factorization 5 =
      5 ^ (q ^ 4 - 1).factorization 5 * 5 := by
    have h := ordProj_pow_sub_one_of_dvd (p := 5) (q := q) (e := 4) (k := 5)
      (by norm_num) (by norm_num) hpq hq2 hq5 (by norm_num)
    rw [Nat.Prime.factorization_self (by norm_num : Nat.Prime 5), pow_one] at h
    simpa using h
  simp only [ggB2a_E8list, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [h30, h24, h20, h18, h14, h12, h8, h2]
  have hrhs : 5 ^ (4 * (q ^ 4 - 1).factorization 5 + 1)
      = (5 ^ (q ^ 4 - 1).factorization 5) ^ 4 * 5 := by
    rw [pow_add, pow_one, pow_mul']
  rw [hrhs]
  ring

private lemma ggB2a_factorization_eq {q : ℕ} (hq2 : 2 ≤ q)
    (hq5 : orderOf (q : ZMod 5) = 4) :
    (ordE8 q).factorization 5 = 4 * (q ^ 4 - 1).factorization 5 + 1 := by
  have hpq : ¬ 5 ∣ q := ggB2a_not_dvd_q hq5
  have hpow : 5 ^ ((ordE8 q).factorization 5) =
      5 ^ (4 * (q ^ 4 - 1).factorization 5 + 1) := by
    rw [ggB2a_ordE8_eq_prod q]
    rw [Nat.ordProj_mul 5 (pow_ne_zero 120 (by omega)) (ggB2a_prod_ne_zero hq2)]
    rw [ordProj_eq_one_of_not_dvd'
        (fun h => hpq ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow h)), one_mul]
    rw [ggB2a_ordProj_list_prod 5 _ (fun x hx => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
      have he0 : e ≠ 0 := ggB2a_mem_E8list he
      have hlt : 1 < q ^ e := Nat.one_lt_pow he0 (by omega)
      omega)]
    rw [List.map_map]
    exact ggB2a_prod_eq hq2 hq5
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 5) hpow

theorem factorization_card_adjointGroup_E8_five_four
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq : orderOf (Nat.card K : ZMod 5) = 4) :
    (Nat.card (adjointGroup .E8 K)).factorization 5 =
      ((((cyclotomic 4 ℤ) ^ 4).eval (Nat.card K : ℤ)).natAbs).factorization 5 + 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  set q : ℕ := Nat.card K with hqdef
  have hq5 : orderOf (q : ZMod 5) = 4 := by rw [hqdef]; exact hq
  have hq2 : 2 ≤ q := by
    rw [hqdef, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hcard : Nat.card (adjointGroup .E8 K) = ordE8 q := by
    rw [hqdef]
    exact CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8
  have hR1 : ¬ (5 : ℤ) ∣ (1 : ℤ[X]).eval (q : ℤ) := by
    intro h
    exact (by norm_num : ¬ (5 : ℤ) ∣ 1) (by simpa using h)
  have hRpow : 5 ^ ((((cyclotomic 4 ℤ) ^ 4).eval (q : ℤ)).natAbs.factorization 5)
      = 5 ^ (4 * (q ^ 4 - 1).factorization 5) := by
    have hR := ordProj_cyclotomic_pow_mul_eval (p := 5) (q := q) (e := 4) (m := 4)
      (by norm_num) hq2 hq5 (by norm_num) (R := (1 : ℤ[X])) hR1
    rw [mul_one] at hR
    rw [hR, ← pow_mul, Nat.mul_comm]
  have hReq : ((((cyclotomic 4 ℤ) ^ 4).eval (q : ℤ)).natAbs).factorization 5
      = 4 * (q ^ 4 - 1).factorization 5 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 5) hRpow
  rw [hcard, ggB2a_factorization_eq hq2 hq5, hReq]

end OrderFiveFour

section PairingNeZero

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.ExcMaxToral Polynomial
open scoped Matrix

private lemma ggB2b_q_d_pos {d : ℕ} (hdeg : (cyclotomic d ℚ).natDegree = 2) : 0 < d := by
  rw [natDegree_cyclotomic] at hdeg
  exact Nat.pos_of_ne_zero fun hd => by subst hd; simp at hdeg

private lemma ggB2b_q_aeval_mapMatrix {R S : Type*} [CommRing R] [CommRing S]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : R →+* S)
    (M : Matrix ι ι R) (p : R[X]) :
    aeval (M.map f) (p.map f) = (aeval M p).map f := by
  have key := Polynomial.map_aeval_eq_aeval_map
    (R := R) (S := Matrix ι ι R) (T := S) (U := Matrix ι ι S)
    (φ := f) (ψ := RingHom.mapMatrix f) ?_ p M
  · simpa [RingHom.mapMatrix_apply] using key.symm
  · ext r a b
    by_cases hab : a = b
    · simp [RingHom.mapMatrix_apply, Matrix.algebraMap_matrix_apply, hab]
    · simp [RingHom.mapMatrix_apply, Matrix.algebraMap_matrix_apply, hab]

private lemma ggB2b_q_minpoly_rat {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {d : ℕ}
    (hd : 0 < d) (M : Matrix ι ι ℤ) (h : aeval M (cyclotomic d ℤ) = 0) :
    minpoly ℚ (M.map (Int.castRingHom ℚ)) = cyclotomic d ℚ := by
  have hq : aeval (M.map (Int.castRingHom ℚ)) (cyclotomic d ℚ) = 0 := by
    have key := ggB2b_q_aeval_mapMatrix (Int.castRingHom ℚ) M (cyclotomic d ℤ)
    rw [Polynomial.map_cyclotomic] at key
    rw [key, h]
    simp
  exact (minpoly.eq_of_irreducible_of_monic (Polynomial.cyclotomic.irreducible_rat hd) hq
    (Polynomial.cyclotomic.monic d ℚ)).symm

private lemma ggB2b_q_charpoly_dvd_pow_rat {ι : Type*} [Fintype ι] [DecidableEq ι] {d m : ℕ}
    (hd : 0 < d) (hcard : Fintype.card ι = 2 * m)
    (Mq : Matrix ι ι ℚ) (hmin : minpoly ℚ Mq = cyclotomic d ℚ) :
    Mq.charpoly ∣ (cyclotomic d ℚ) ^ (2 * m) := by
  let Mc : Matrix ι ι ℂ := Mq.map (algebraMap ℚ ℂ)
  let gc : ℂ[X] := cyclotomic d ℂ
  have hgc : gc = (cyclotomic d ℚ).map (algebraMap ℚ ℂ) :=
    (Polynomial.map_cyclotomic d (algebraMap ℚ ℂ)).symm
  have hq0 : aeval Mq (cyclotomic d ℚ) = 0 := by
    rw [← hmin]
    exact minpoly.aeval ℚ Mq
  have hc0 : aeval Mc gc = 0 := by
    have key := ggB2b_q_aeval_mapMatrix (algebraMap ℚ ℂ) Mq (cyclotomic d ℚ)
    rw [hgc]
    rw [key, hq0]
    simp
  have hminc : minpoly ℂ Mc ∣ gc := minpoly.dvd ℂ Mc hc0
  have hroot : ∀ a, Mc.charpoly.IsRoot a → gc.IsRoot a := by
    intro a ha
    have hev : Module.End.HasEigenvalue (Matrix.toLin' Mc) a := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
      rwa [Matrix.charpoly_toLin']
    have hminroot : (minpoly ℂ (Matrix.toLin' Mc)).IsRoot a :=
      (Module.End.hasEigenvalue_iff_isRoot).mp hev
    rw [Matrix.minpoly_toLin'] at hminroot
    exact hminroot.dvd hminc
  have hf0 : Mc.charpoly ≠ 0 := (Matrix.charpoly_monic Mc).ne_zero
  have hg0 : gc ≠ 0 := (Polynomial.cyclotomic.monic d ℂ).ne_zero
  have hgp0 : gc ^ (2 * m) ≠ 0 := pow_ne_zero _ hg0
  have hle : Mc.charpoly.roots ≤ (gc ^ (2 * m)).roots := by
    rw [Multiset.le_iff_count]
    intro a
    rw [Polynomial.roots_pow, Multiset.count_nsmul]
    by_cases ha : a ∈ gc.roots
    · have hpos : 0 < Multiset.count a gc.roots := Multiset.count_pos.mpr ha
      have hcard_le : Multiset.count a Mc.charpoly.roots ≤ 2 * m := by
        calc Multiset.count a Mc.charpoly.roots ≤ (Mc.charpoly.roots).card :=
              Multiset.count_le_card a _
          _ ≤ Mc.charpoly.natDegree := Polynomial.card_roots' _
          _ = Fintype.card ι := Matrix.charpoly_natDegree_eq_dim Mc
          _ = 2 * m := hcard
      calc Multiset.count a Mc.charpoly.roots ≤ 2 * m := hcard_le
        _ ≤ 2 * m * Multiset.count a gc.roots := Nat.le_mul_of_pos_right (2 * m) hpos
    · have hnotmem : a ∉ Mc.charpoly.roots := by
        intro hmem
        exact ha ((mem_roots hg0).mpr (hroot a ((mem_roots hf0).mp hmem)))
      rw [Multiset.count_eq_zero.mpr hnotmem, Multiset.count_eq_zero.mpr ha, Nat.mul_zero]
  have hdvdc : Mc.charpoly ∣ gc ^ (2 * m) :=
    (IsAlgClosed.dvd_iff_roots_le_roots hf0 hgp0).mpr hle
  have hmapf : Mc.charpoly = Mq.charpoly.map (algebraMap ℚ ℂ) :=
    Matrix.charpoly_map Mq (algebraMap ℚ ℂ)
  have hmapg : gc ^ (2 * m) = ((cyclotomic d ℚ) ^ (2 * m)).map (algebraMap ℚ ℂ) := by
    rw [hgc, Polynomial.map_pow]
  rw [hmapf, hmapg] at hdvdc
  exact (Polynomial.map_dvd_map' (algebraMap ℚ ℂ)).mp hdvdc

private lemma ggB2b_q_charpoly_eq_rat {ι : Type*} [Fintype ι] [DecidableEq ι] {d m : ℕ}
    (hdeg : (cyclotomic d ℚ).natDegree = 2) (hcard : Fintype.card ι = 2 * m)
    (Mq : Matrix ι ι ℚ) (hmin : minpoly ℚ Mq = cyclotomic d ℚ) :
    Mq.charpoly = (cyclotomic d ℚ) ^ m := by
  have hd := ggB2b_q_d_pos hdeg
  have hdiv := ggB2b_q_charpoly_dvd_pow_rat hd hcard Mq hmin
  have hprime : Prime (cyclotomic d ℚ) :=
    (Polynomial.cyclotomic.irreducible_rat hd).prime
  obtain ⟨i, _hi, hassoc⟩ := (dvd_prime_pow hprime (2 * m)).mp hdiv
  have heq : Mq.charpoly = (cyclotomic d ℚ) ^ i :=
    Polynomial.eq_of_monic_of_associated (Matrix.charpoly_monic Mq)
      ((Polynomial.cyclotomic.monic d ℚ).pow i) hassoc
  have hdegf : Mq.charpoly.natDegree = 2 * m := by
    rw [Matrix.charpoly_natDegree_eq_dim, hcard]
  have hdegi : ((cyclotomic d ℚ) ^ i).natDegree = 2 * i := by
    rw [Polynomial.natDegree_pow, hdeg, mul_comm]
  have him : i = m := by
    have h2 : 2 * m = 2 * i := by rw [← hdegf, heq, hdegi]
    omega
  rw [heq, him]

private theorem ggB2b1_charpoly_eq_cyclotomic_pow {ι : Type} [Fintype ι] [DecidableEq ι]
    {d m : ℕ} (hdeg : (cyclotomic d ℚ).natDegree = 2) (hcard : Fintype.card ι = 2 * m)
    (M : Matrix ι ι ℤ) (h : aeval M (cyclotomic d ℤ) = 0) :
    M.charpoly = (cyclotomic d ℤ) ^ m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp (by simpa using hcard)
    simp [Matrix.charpoly_isEmpty]
  · haveI : Nonempty ι := Fintype.card_pos_iff.mp (by rw [hcard]; omega)
    have hd := ggB2b_q_d_pos hdeg
    have hmin := ggB2b_q_minpoly_rat hd M h
    have hrat := ggB2b_q_charpoly_eq_rat hdeg hcard (M.map (Int.castRingHom ℚ)) hmin
    refine Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective ?_
    rw [← Matrix.charpoly_map M (Int.castRingHom ℚ), hrat, Polynomial.map_pow,
      Polynomial.map_cyclotomic]

private def ggB2b_S0 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![-1, 0, 1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggB2b_S1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, -1, 0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggB2b_S2 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     1, 0, -1, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggB2b_S3 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 1, 1, -1, 1, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggB2b_S4 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, -1, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggB2b_S5 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 1, -1, 1, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggB2b_S6 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, -1, 1;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggB2b_S7 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1, -1]

private def ggB2b_S : Fin Tag.E8.rank →
    Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  ![ggB2b_S0, ggB2b_S1, ggB2b_S2, ggB2b_S3, ggB2b_S4, ggB2b_S5, ggB2b_S6, ggB2b_S7]

private lemma ggB2b_weylMatrix_simple (i : Fin Tag.E8.rank) :
    weylMatrix (simple .E8 i) = ggB2b_S i := by
  ext k j
  rw [weylMatrix_apply, simple_smul]
  fin_cases i <;> fin_cases k <;> fin_cases j <;> decide

private lemma ggB2b_weylMatrix_foldr (W : List (Fin Tag.E8.rank)) :
    weylMatrix ((coxeterSystem .E8).wordProd W) =
      W.foldr (fun i M => ggB2b_S i * M) 1 := by
  induction W with
  | nil => rw [CoxeterSystem.wordProd_nil, weylMatrix_one]; rfl
  | cons i W ih =>
    rw [CoxeterSystem.wordProd_cons, weylMatrix_mul, ggB2b_weylMatrix_simple, ih]
    rfl

private def ggB2b_V1 : List (Fin Tag.E8.rank) :=
  [0, 3, 1, 2, 3, 4, 3, 1, 2, 3]

private def ggB2b_V2 : List (Fin Tag.E8.rank) :=
  [5, 4, 3, 1, 2, 0, 3, 2, 4, 6]

private def ggB2b_V3 : List (Fin Tag.E8.rank) :=
  [5, 4, 3, 1, 2, 0, 3, 2, 4, 3]

private def ggB2b_V4 : List (Fin Tag.E8.rank) :=
  [1, 5, 4, 3, 2, 0, 6, 5, 4, 7]

private def ggB2b_V5 : List (Fin Tag.E8.rank) :=
  [6, 5, 4, 3, 1, 2, 0, 3, 2, 4]

private def ggB2b_V6 : List (Fin Tag.E8.rank) :=
  [3, 1, 5, 4, 3, 2, 6, 5, 4, 7]

private def ggB2b_w4 : WeylGroup .E8 :=
  (coxeterSystem .E8).wordProd
    (ggB2b_V1 ++ ggB2b_V2 ++ ggB2b_V3 ++ ggB2b_V4 ++ ggB2b_V5 ++ ggB2b_V6)

private def ggB2b_M4 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![2, 0, -2, 1, -1, 1, 0, -1;
     3, 0, -3, 1, 0, 0, 1, -2;
     4, 0, -4, 2, -1, 1, 0, -2;
     6, 0, -6, 3, -1, 0, 1, -3;
     5, -1, -5, 3, -1, 0, 1, -2;
     3, -1, -4, 3, -1, 0, 1, -2;
     2, -1, -2, 2, -1, 0, 1, -2;
     1, 0, -1, 1, -1, 0, 1, -1]

private def ggB2b_D1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![0, 0, 1, -1, 0, 1, 0, 0;
     1, 1, 0, -1, 0, 1, 0, 0;
     1, 0, 1, -1, 0, 1, 0, 0;
     2, 0, 0, -1, 0, 2, 0, 0;
     1, 0, 0, -1, 1, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggB2b_D2 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![0, 0, -1, 1, 0, 0, 0, 0;
     1, 0, -1, 1, -1, 1, 0, 0;
     0, 1, -1, 1, -1, 1, 0, 0;
     0, 0, -1, 2, -2, 2, 0, 0;
     0, 0, -1, 1, -1, 2, 0, 0;
     0, 0, -1, 1, -1, 2, -1, 1;
     0, 0, 0, 0, 0, 1, -1, 1;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggB2b_D3 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![0, 1, 0, -1, 1, 0, 0, 0;
     1, 1, 0, -1, 0, 1, 0, 0;
     0, 2, 0, -1, 0, 1, 0, 0;
     0, 2, 1, -2, 0, 2, 0, 0;
     0, 1, 0, -1, 0, 2, 0, 0;
     0, 1, 0, -1, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggB2b_D4 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![-1, 0, 1, 0, 0, 0, 0, 0;
     -1, 0, 0, 1, -1, 1, 0, 0;
     -1, 0, 0, 1, 0, 0, 0, 0;
     -1, 1, 0, 1, -1, 1, 0, 0;
     -1, 1, 0, 1, -1, 0, 1, 0;
     -1, 1, 0, 1, -1, 0, 1, -1;
     0, 0, 0, 1, -1, 0, 1, -1;
     0, 0, 0, 0, 0, 0, 1, -1]

private def ggB2b_D5 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![0, 0, -1, 1, 0, 0, 0, 0;
     1, 0, -1, 1, -1, 1, 0, 0;
     0, 1, -1, 1, -1, 1, 0, 0;
     0, 0, -1, 2, -2, 2, 0, 0;
     0, 0, -1, 1, -1, 2, 0, 0;
     0, 0, -1, 1, -1, 1, 1, 0;
     0, 0, -1, 1, -1, 1, 0, 1;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggB2b_D6 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     1, 0, -1, 1, -1, 1, 0, 0;
     1, 0, -1, 1, 0, 0, 0, 0;
     2, 0, -2, 2, -1, 0, 1, 0;
     1, 1, -1, 1, -1, 0, 1, 0;
     1, 1, -1, 1, -1, 0, 1, -1;
     0, 0, 0, 1, -1, 0, 1, -1;
     0, 0, 0, 0, 0, 0, 1, -1]

private lemma ggB2b_V1_matrix :
    weylMatrix ((coxeterSystem .E8).wordProd ggB2b_V1) = ggB2b_D1 := by
  rw [ggB2b_weylMatrix_foldr]
  decide

private lemma ggB2b_V2_matrix :
    weylMatrix ((coxeterSystem .E8).wordProd ggB2b_V2) = ggB2b_D2 := by
  rw [ggB2b_weylMatrix_foldr]
  decide

private lemma ggB2b_V3_matrix :
    weylMatrix ((coxeterSystem .E8).wordProd ggB2b_V3) = ggB2b_D3 := by
  rw [ggB2b_weylMatrix_foldr]
  decide

private lemma ggB2b_V4_matrix :
    weylMatrix ((coxeterSystem .E8).wordProd ggB2b_V4) = ggB2b_D4 := by
  rw [ggB2b_weylMatrix_foldr]
  decide

private lemma ggB2b_V5_matrix :
    weylMatrix ((coxeterSystem .E8).wordProd ggB2b_V5) = ggB2b_D5 := by
  rw [ggB2b_weylMatrix_foldr]
  decide

private lemma ggB2b_V6_matrix :
    weylMatrix ((coxeterSystem .E8).wordProd ggB2b_V6) = ggB2b_D6 := by
  rw [ggB2b_weylMatrix_foldr]
  decide

private lemma ggB2b_w4_matrix : weylMatrix ggB2b_w4 = ggB2b_M4 := by
  unfold ggB2b_w4
  simp only [CoxeterSystem.wordProd_append, weylMatrix_mul, ggB2b_V1_matrix, ggB2b_V2_matrix,
    ggB2b_V3_matrix, ggB2b_V4_matrix, ggB2b_V5_matrix, ggB2b_V6_matrix]
  decide

private lemma ggB2b_M4_quad : ggB2b_M4 ^ 2 + 1 = 0 := by
  decide

private lemma ggB2b_aeval_four : aeval (weylMatrix ggB2b_w4) (cyclotomic 4 ℤ) = 0 := by
  have hcyc : cyclotomic 4 ℤ = (X : ℤ[X]) ^ 2 + 1 := by
    rw [show (4 : ℕ) = 2 ^ (1 + 1) by norm_num,
      Polynomial.cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (p := 2) (n := 1) Nat.prime_two]
    simp only [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]
    ring
  rw [ggB2b_w4_matrix, hcyc]
  simpa [add_comm] using ggB2b_M4_quad

private lemma ggB2b_charpoly_four :
    (weylMatrix ggB2b_w4).charpoly = (cyclotomic 4 ℤ) ^ 4 := by
  refine ggB2b1_charpoly_eq_cyclotomic_pow (d := 4) (m := 4) (hdeg := ?_) (hcard := ?_)
    (M := weylMatrix ggB2b_w4) (h := ?_)
  · rw [Polynomial.natDegree_cyclotomic]; decide
  · decide
  · exact ggB2b_aeval_four

private lemma ggB2b_orderOf_eq_of_matrix {w : WeylGroup .E8} {d : ℕ} (hd : 0 < d)
    {M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ} (hM : weylMatrix w = M)
    (hdec : M ^ d = 1) (hne : ∀ m, 0 < m → m < d → M ^ m ≠ 1) :
    orderOf w = d := by
  rw [orderOf_eq_iff hd]
  refine ⟨?_, ?_⟩
  · apply weylMatrix_injective
    rw [weylMatrix_pow, hM, hdec, weylMatrix_one]
  · intro m hm hpos hwm
    exact hne m hpos hm (by rw [← hM, ← weylMatrix_pow, hwm, weylMatrix_one])

private lemma ggB2b_order_four : orderOf ggB2b_w4 = 4 := by
  refine ggB2b_orderOf_eq_of_matrix (d := 4) (by norm_num) ggB2b_w4_matrix (by decide) ?_
  intro m h1 h2
  have hm : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hm with rfl | rfl | rfl <;> decide

private lemma ggB2b_shape_four : ExcLangShape .E8 4 ggB2b_w4 := by
  refine ⟨fun h => by omega, fun h => by omega, ?_⟩
  intro _
  exact ⟨ggB2b_order_four, weylMatrix ggB2b_w4,
    fun u => (weylMatrix_mulVec ggB2b_w4 u).symm, ggB2b_charpoly_four⟩

private abbrev ggB2b_single (j : Fin Tag.E8.rank) : Fin Tag.E8.rank → ZMod 5 :=
  Pi.single j (1 : ZMod 5)

private lemma ggB2b_sq_eq_neg_one (l : ZMod 5) (hl : l ^ 2 = -1) : l = 2 ∨ l = 3 := by
  revert l
  decide

private lemma ggB2b_sum_eq_dotProduct
    (A : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod 5)) (l : ZMod 5)
    (α : Fin Tag.E8.rank → ℤ) (j : Fin Tag.E8.rank) :
    (∑ i, (α i : ZMod 5) * ((Aᵀ *ᵥ ggB2b_single j) + l • ggB2b_single j) i)
      = (fun i => (α i : ZMod 5)) ⬝ᵥ ((Aᵀ *ᵥ ggB2b_single j) + l • ggB2b_single j) := by
  rfl

private lemma ggB2b_lhs_eq
    (A : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod 5)) (l : ZMod 5)
    (α : Fin Tag.E8.rank → ℤ) (j : Fin Tag.E8.rank) :
    (∑ i, (α i : ZMod 5) * ((Aᵀ *ᵥ ggB2b_single j) + l • ggB2b_single j) i)
      = (fun i => (α i : ZMod 5)) ⬝ᵥ (Aᵀ *ᵥ ggB2b_single j) +
        l • ((fun i => (α i : ZMod 5)) ⬝ᵥ ggB2b_single j) := by
  rw [ggB2b_sum_eq_dotProduct, dotProduct_add, dotProduct_smul]

private lemma ggB2b_rhs_eq
    (A : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod 5)) (l : ZMod 5)
    (α : Fin Tag.E8.rank → ℤ) (j : Fin Tag.E8.rank) :
    ((A + l • 1) *ᵥ (fun i => (α i : ZMod 5))) j
      = (fun i => (α i : ZMod 5)) ⬝ᵥ (Aᵀ *ᵥ ggB2b_single j) +
        l • ((fun i => (α i : ZMod 5)) ⬝ᵥ ggB2b_single j) := by
  rw [← dotProduct_single_one (v := (A + l • 1) *ᵥ (fun i => (α i : ZMod 5)))
    (i := j)]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [add_dotProduct, smul_dotProduct]
  rw [dotProduct_comm (v := A *ᵥ (fun i => (α i : ZMod 5))) (w := ggB2b_single j)]
  rw [← Matrix.dotProduct_transpose_mulVec (A := A) (x := (fun i => (α i : ZMod 5)))
    (y := ggB2b_single j)]

private lemma ggB2b_pairing_dotProduct
    (A : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod 5)) (l : ZMod 5)
    (α : Fin Tag.E8.rank → ℤ) (j : Fin Tag.E8.rank) :
    (∑ i, (α i : ZMod 5) * ((Aᵀ *ᵥ ggB2b_single j) + l • ggB2b_single j) i)
      = ((A + l • 1) *ᵥ (fun i => (α i : ZMod 5))) j := by
  rw [ggB2b_lhs_eq, ggB2b_rhs_eq]

private lemma ggB2b_eigen_of_quad {l : ZMod 5} (hl : l ^ 2 = -1) (u : Fin Tag.E8.rank → ZMod 5) :
    (modMat 5 ggB2b_M4)ᵀ *ᵥ ((modMat 5 ggB2b_M4)ᵀ *ᵥ u + l • u) =
      l • ((modMat 5 ggB2b_M4)ᵀ *ᵥ u + l • u) := by
  have hB2 : (modMat 5 ggB2b_M4)ᵀ * (modMat 5 ggB2b_M4)ᵀ =
      (-1 : ZMod 5) • (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod 5)) := by
    decide
  calc (modMat 5 ggB2b_M4)ᵀ *ᵥ ((modMat 5 ggB2b_M4)ᵀ *ᵥ u + l • u)
      = (modMat 5 ggB2b_M4)ᵀ *ᵥ ((modMat 5 ggB2b_M4)ᵀ *ᵥ u) +
        (modMat 5 ggB2b_M4)ᵀ *ᵥ (l • u) := by rw [Matrix.mulVec_add]
    _ = (((modMat 5 ggB2b_M4)ᵀ * (modMat 5 ggB2b_M4)ᵀ) *ᵥ u) +
        l • ((modMat 5 ggB2b_M4)ᵀ *ᵥ u) := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_smul]
    _ = (((-1 : ZMod 5) • (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod 5))) *ᵥ u) +
        l • ((modMat 5 ggB2b_M4)ᵀ *ᵥ u) := by rw [hB2]
    _ = (-1 : ZMod 5) • u + l • ((modMat 5 ggB2b_M4)ᵀ *ᵥ u) := by
          rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    _ = l • ((modMat 5 ggB2b_M4)ᵀ *ᵥ u) + (-1 : ZMod 5) • u := add_comm _ _
    _ = l • ((modMat 5 ggB2b_M4)ᵀ *ᵥ u) + l • (l • u) := by
          rw [smul_smul, ← pow_two, hl]
    _ = l • ((modMat 5 ggB2b_M4)ᵀ *ᵥ u + l • u) := (smul_add l _ _).symm

private lemma ggB2b_roots_length : (Tag.rootCertificate .E8).roots.length = 240 := by
  rfl

private def ggB2b_pred (l : ZMod 5) (k : ℕ) : Bool :=
  decide (((modMat 5 ggB2b_M4 + l • 1) *ᵥ
    (fun i => (((Tag.rootCertificate .E8).root k) i : ZMod 5))) ≠ 0)

private def ggB2b_chunk (l : ZMod 5) (lo : ℕ) : Bool :=
  (List.range' lo 30).all (ggB2b_pred l)

private lemma ggB2b_chunk_two (lo : ℕ)
    (hlo : lo ∈ [0, 30, 60, 90, 120, 150, 180, 210]) : ggB2b_chunk 2 lo = true := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hlo
  rcases hlo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private lemma ggB2b_chunk_three (lo : ℕ)
    (hlo : lo ∈ [0, 30, 60, 90, 120, 150, 180, 210]) : ggB2b_chunk 3 lo = true := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hlo
  rcases hlo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private lemma ggB2b_mem_range' (k : ℕ) (hk : k < 240) :
    ∃ lo ∈ [0, 30, 60, 90, 120, 150, 180, 210], lo ≤ k ∧ k < lo + 30 := by
  by_cases h0 : k < 30
  · exact ⟨0, by simp, by omega, h0⟩
  by_cases h1 : k < 60
  · exact ⟨30, by simp, by omega, h1⟩
  by_cases h2 : k < 90
  · exact ⟨60, by simp, by omega, h2⟩
  by_cases h3 : k < 120
  · exact ⟨90, by simp, by omega, h3⟩
  by_cases h4 : k < 150
  · exact ⟨120, by simp, by omega, h4⟩
  by_cases h5 : k < 180
  · exact ⟨150, by simp, by omega, h5⟩
  by_cases h6 : k < 210
  · exact ⟨180, by simp, by omega, h6⟩
  · exact ⟨210, by simp, by omega, by omega⟩

private lemma ggB2b_pred_of_chunk {l : ZMod 5} {lo : ℕ}
    (h : ggB2b_chunk l lo = true) {k : ℕ} (hk1 : lo ≤ k) (hk2 : k < lo + 30) :
    ggB2b_pred l k = true := by
  rw [ggB2b_chunk] at h
  exact List.all_eq_true.mp h k (List.mem_range'.mpr ⟨k - lo, by omega, by omega⟩)

private lemma ggB2b_root_ne_eigen {l : ZMod 5} (hl : l ^ 2 = -1)
    (k : ℕ) (hk : k < 240) :
    ((modMat 5 ggB2b_M4 + l • 1) *ᵥ
      (fun i => (((Tag.rootCertificate .E8).root k) i : ZMod 5))) ≠ 0 := by
  obtain ⟨lo, hlo, hk1, hk2⟩ := ggB2b_mem_range' k hk
  have hl23 : l = 2 ∨ l = 3 := ggB2b_sq_eq_neg_one l hl
  rcases hl23 with rfl | rfl
  · exact of_decide_eq_true (ggB2b_pred_of_chunk (ggB2b_chunk_two lo hlo) hk1 hk2)
  · exact of_decide_eq_true (ggB2b_pred_of_chunk (ggB2b_chunk_three lo hlo) hk1 hk2)

theorem exists_regular_weyl_E8_four_pairing_ne_zero :
    ∃ w : WeylGroup .E8, ExcLangShape .E8 4 w ∧
      ∀ l : ZMod 5, l ^ 2 = -1 → ∀ α : Fin Tag.E8.rank → ℤ, IsRoot .E8 α →
        ∃ z : Fin Tag.E8.rank → ZMod 5,
          (modMat 5 (weylMatrix w)).transpose *ᵥ z = l • z ∧ ∑ i, (α i : ZMod 5) * z i ≠ 0 := by
  refine ⟨ggB2b_w4, ggB2b_shape_four, ?_⟩
  intro l hl α hα
  obtain ⟨k, hk, hkα⟩ :=
    RootCertificate.exists_root_eq (Tag.rootCertificate_check .E8) hα
  have hk' : k < 240 := by rw [ggB2b_roots_length] at hk; exact hk
  have hne := ggB2b_root_ne_eigen hl k hk'
  rw [hkα] at hne
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  refine ⟨(modMat 5 (weylMatrix ggB2b_w4)).transpose *ᵥ ggB2b_single j +
    l • ggB2b_single j, ?_, ?_⟩
  · rw [ggB2b_w4_matrix]
    exact ggB2b_eigen_of_quad hl (ggB2b_single j)
  · rw [ggB2b_w4_matrix]
    rw [ggB2b_pairing_dotProduct (A := modMat 5 ggB2b_M4) (l := l) (α := α) (j := j)]
    simpa using hj

end PairingNeZero

section FixedSpace

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.ExcMaxToral Polynomial
open scoped Matrix

private lemma ggB2c_cyclotomic_four_int :
    (cyclotomic 4 ℤ : ℤ[X]) = (X : ℤ[X]) ^ 2 + 1 := by
  rw [show (4 : ℕ) = 2 ^ (1 + 1) by norm_num,
    Polynomial.cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (p := 2) (n := 1) Nat.prime_two]
  simp only [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]
  ring

private lemma ggB2c_cyclotomic_five_rat :
    (cyclotomic 5 ℚ : ℚ[X]) = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Polynomial.cyclotomic_prime ℚ 5]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero]
  ring

private lemma ggB2c_cyclotomic_five_int :
    (cyclotomic 5 ℤ : ℤ[X]) = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Polynomial.cyclotomic_prime ℤ 5]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero]
  ring

private lemma ggB2c_cyclotomic_four_rat :
    (cyclotomic 4 ℚ : ℚ[X]) = (X : ℚ[X]) ^ 2 + 1 := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℚ)) ggB2c_cyclotomic_four_int
  simpa [Polynomial.map_cyclotomic] using h

private lemma ggB2c_cyclotomic_twenty_rat :
    (cyclotomic 20 ℚ : ℚ[X]) = X ^ 8 - X ^ 6 + X ^ 4 - X ^ 2 + 1 := by
  have hP : (X ^ 8 - X ^ 6 + X ^ 4 - X ^ 2 + 1 : ℚ[X]) = cyclotomic 20 ℚ := by
    rw [Polynomial.eq_cyclotomic_iff (R := ℚ) (n := 20) (by norm_num)
      (X ^ 8 - X ^ 6 + X ^ 4 - X ^ 2 + 1)]
    have hset : (20 : ℕ).properDivisors = (10 : ℕ).divisors ∪ ({4} : Finset ℕ) := by decide
    have hdisj : Disjoint ((10 : ℕ).divisors) ({4} : Finset ℕ) := by decide
    rw [hset, Finset.prod_union hdisj, Finset.prod_singleton,
      Polynomial.prod_cyclotomic_eq_X_pow_sub_one (n := 10) (by norm_num) ℚ,
      ggB2c_cyclotomic_four_rat]
    ring
  exact hP.symm

private lemma ggB2c_X_pow_ten_add_one_eq :
    (X ^ 10 + 1 : ℚ[X]) = cyclotomic 4 ℚ * cyclotomic 20 ℚ := by
  rw [ggB2c_cyclotomic_four_rat, ggB2c_cyclotomic_twenty_rat]
  ring

private lemma ggB2c_Phi5_comp_neg_pow_six_eq :
    (cyclotomic 5 ℚ).comp (-(X : ℚ[X]) ^ 6) =
      cyclotomic 20 ℚ *
        (X ^ 16 + X ^ 14 - X ^ 10 - X ^ 8 - X ^ 6 + X ^ 2 + 1 : ℚ[X]) := by
  rw [ggB2c_cyclotomic_five_rat, ggB2c_cyclotomic_twenty_rat, Polynomial.comp_eq_aeval]
  simp only [Polynomial.aeval_X, map_add, map_pow, map_one]
  ring

private lemma ggB2c_sq_eq_neg_one_of_charpoly_four {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ) (h4 : M ^ 4 = 1) (hchar : M.charpoly = (cyclotomic 4 ℤ) ^ 4) :
    M ^ 2 = -1 := by
  have hCH : Polynomial.aeval M ((cyclotomic 4 ℤ) ^ 4) = 0 := by
    rw [← hchar]; exact Matrix.aeval_self_charpoly M
  have hA4 : (Polynomial.aeval M (cyclotomic 4 ℤ)) ^ 4 = 0 := by
    simpa using hCH
  have hcyc : Polynomial.aeval M (cyclotomic 4 ℤ) =
      Polynomial.aeval M ((X : ℤ[X]) ^ 2 + 1) := by
    rw [ggB2c_cyclotomic_four_int]
  have hA : Polynomial.aeval M ((X : ℤ[X]) ^ 2 + 1) = M ^ 2 + 1 := by
    simp [Polynomial.aeval_X, pow_two]
  have hA4' : (M ^ 2 + 1) ^ 4 = 0 := by
    rw [← hA, ← hcyc]; exact hA4
  have hpoly : (X ^ 2 + 1 : ℤ[X]) ^ 4 - 8 * (X ^ 2 + 1) =
      (X ^ 4 + 4 * X ^ 2 + 7) * (X ^ 4 - 1) := by ring
  have hx4 : M ^ 4 - 1 = 0 := by rw [h4]; exact sub_self 1
  have hrel := congrArg (Polynomial.aeval M) hpoly
  simp only [map_sub, map_mul, map_pow, map_add, map_ofNat, map_natCast, map_one,
    Polynomial.aeval_X] at hrel
  rw [hA4', hx4, mul_zero, zero_sub] at hrel
  have h8 : (8 : Matrix ι ι ℤ) * (M ^ 2 + 1) = 0 := neg_eq_zero.mp hrel
  have hA0 : M ^ 2 + 1 = 0 := by
    have hcast : (8 : Matrix ι ι ℤ) = (8 : ℤ) • (1 : Matrix ι ι ℤ) := by
      ext i j
      rw [Matrix.ofNat_apply, Matrix.smul_apply, Matrix.one_apply]
      by_cases h : i = j <;> simp [h]
    have h8' : (8 : ℤ) • (M ^ 2 + 1) = 0 := by
      rwa [hcast, Matrix.smul_mul, one_mul] at h8
    ext i j
    have hentry := congrFun (congrFun h8' i) j
    simp only [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at hentry
    exact (mul_eq_zero.mp hentry).resolve_left (by norm_num)
  have := hA0
  rw [add_eq_zero_iff_eq_neg] at this
  exact this

private lemma ggB2c_shape_data (w : WeylGroup .E8) (hw : ExcLangShape .E8 4 w) :
    orderOf w = 4 ∧ (weylMatrix w).charpoly = (cyclotomic 4 ℤ) ^ 4 := by
  obtain ⟨hord, M, hMact, hMchar⟩ := hw.2.2 ⟨rfl, Or.inr (Or.inl rfl)⟩
  refine ⟨hord, ?_⟩
  have hMeq : M = weylMatrix w := by
    ext i j
    have h := congrFun (hMact (Pi.single j 1)) i
    rw [weylMatrix_apply]
    simpa [Matrix.mulVec_single_one, Matrix.col_apply] using h.symm
  rw [← hMeq]; exact hMchar

private lemma ggB2c_weylMatrix_sq (w : WeylGroup .E8) (hw : ExcLangShape .E8 4 w) :
    (weylMatrix w) ^ 2 = -1 := by
  obtain ⟨hord, hchar⟩ := ggB2c_shape_data w hw
  refine ggB2c_sq_eq_neg_one_of_charpoly_four (weylMatrix w) ?_ hchar
  rw [← weylMatrix_pow w 4, ← hord, pow_orderOf_eq_one, weylMatrix_one]

private lemma ggB2c_transpose_sq (w : WeylGroup .E8) (hw : ExcLangShape .E8 4 w) :
    ((weylMatrix w)ᵀ) ^ 2 = -1 := by
  rw [← Matrix.transpose_pow, ggB2c_weylMatrix_sq w hw, Matrix.transpose_neg, Matrix.transpose_one]

private lemma ggB2c_transpose_pow_five (v : WeylGroup .E8) (hv : orderOf v = 5) :
    ((weylMatrix v)ᵀ) ^ 5 = 1 := by
  rw [← Matrix.transpose_pow, ← weylMatrix_pow v 5, ← hv, pow_orderOf_eq_one, weylMatrix_one,
    Matrix.transpose_one]

private lemma ggB2c_weylMatrix_ne_one (v : WeylGroup .E8) (hv : orderOf v = 5) :
    weylMatrix v ≠ 1 := by
  intro h
  have hv1 : v = 1 := weylMatrix_injective (h.trans weylMatrix_one.symm)
  rw [hv1] at hv
  simp at hv

private lemma ggB2c_transpose_ne_one (v : WeylGroup .E8) (hv : orderOf v = 5) :
    (weylMatrix v)ᵀ ≠ 1 := by
  intro h
  refine ggB2c_weylMatrix_ne_one v hv ?_
  have := congrArg Matrix.transpose h
  rwa [Matrix.transpose_transpose, Matrix.transpose_one] at this

private lemma ggB2c_transpose_comm (w v : WeylGroup .E8) (hvw : v * w = w * v) :
    (weylMatrix w)ᵀ * (weylMatrix v)ᵀ = (weylMatrix v)ᵀ * (weylMatrix w)ᵀ := by
  have h : weylMatrix v * weylMatrix w = weylMatrix w * weylMatrix v := by
    rw [← weylMatrix_mul, hvw, weylMatrix_mul]
  calc (weylMatrix w)ᵀ * (weylMatrix v)ᵀ = (weylMatrix v * weylMatrix w)ᵀ := by
        rw [Matrix.transpose_mul]
    _ = (weylMatrix w * weylMatrix v)ᵀ := by rw [h]
    _ = (weylMatrix v)ᵀ * (weylMatrix w)ᵀ := by rw [Matrix.transpose_mul]

private lemma ggB2c_aeval_mapMatrix {R S : Type*} [CommRing R] [CommRing S]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : R →+* S)
    (M : Matrix ι ι R) (p : R[X]) :
    Polynomial.aeval (M.map f) (p.map f) = (Polynomial.aeval M p).map f := by
  have key := Polynomial.map_aeval_eq_aeval_map
    (R := R) (S := Matrix ι ι R) (T := S) (U := Matrix ι ι S)
    (φ := f) (ψ := RingHom.mapMatrix f) ?_ p M
  · simpa [RingHom.mapMatrix_apply] using key.symm
  · ext r a b
    by_cases hab : a = b
    · simp [RingHom.mapMatrix_apply, Matrix.algebraMap_matrix_apply, hab]
    · simp [RingHom.mapMatrix_apply, Matrix.algebraMap_matrix_apply, hab]

private lemma ggB2c_Phi5_eq_zero_rat {V N : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℚ}
    (hcomm : N * V = V * N) (hN : N ^ 2 = -1) (hV5 : V ^ 5 = 1) (hVne : V ≠ 1) :
    Polynomial.aeval V (cyclotomic 5 ℚ) = 0 := by
  let u : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℚ := N * V
  have hcomm' : Commute N V := hcomm
  have hN4 : N ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hN]; norm_num
  have hN5 : N ^ 5 = N := by
    rw [show (5 : ℕ) = 4 + 1 by norm_num, pow_add, hN4, one_mul, pow_one]
  have hN10 : N ^ 10 = -1 := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num, pow_mul, hN]; norm_num
  have hV10 : V ^ 10 = 1 := by
    rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul, hV5]; norm_num
  have hu10 : u ^ 10 = -1 := by
    rw [show u = N * V from rfl, hcomm'.mul_pow, hN10, hV10, mul_one]
  have hu5 : u ^ 5 = N := by
    rw [show u = N * V from rfl, hcomm'.mul_pow, hV5, mul_one, hN5]
  have hu6 : u ^ 6 = -V := by
    rw [show (6 : ℕ) = 5 + 1 by norm_num, pow_add, hu5, pow_one]
    rw [show u = N * V from rfl, ← mul_assoc, ← pow_two N, hN, neg_mul, one_mul]
  have hu_ann : Polynomial.aeval u (X ^ 10 + 1 : ℚ[X]) = 0 := by
    have h : Polynomial.aeval u (X ^ 10 + 1 : ℚ[X]) = u ^ 10 + 1 := by
      simp [Polynomial.aeval_X]
    rw [h, hu10]; simp
  have hm_dvd : minpoly ℚ u ∣ (X ^ 10 + 1 : ℚ[X]) := minpoly.dvd ℚ u hu_ann
  set m : ℚ[X] := minpoly ℚ u with hm_def
  have hm_dvd' : m ∣ (cyclotomic 4 ℚ) * (cyclotomic 20 ℚ) := by
    rw [hm_def, ← ggB2c_X_pow_ten_add_one_eq]; exact hm_dvd
  have hu2 : u ^ 2 = -(V ^ 2) := by
    rw [show u = N * V from rfl, hcomm'.mul_pow, hN, neg_mul, one_mul]
  have hm_monic : m.Monic := by
    rw [hm_def]; exact minpoly.monic (IsIntegral.of_finite ℚ u)
  have hm_dvd_char : m ∣ u.charpoly := by
    have h := LinearMap.minpoly_dvd_charpoly (Matrix.toLin' u)
    rw [Matrix.minpoly_toLin', Matrix.charpoly_toLin'] at h
    rwa [hm_def]
  have hdegm : m.natDegree ≤ 8 := by
    have hchar : u.charpoly.natDegree = 8 := by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
      rfl
    have h := natDegree_le_of_dvd hm_dvd_char (Matrix.charpoly_monic u).ne_zero
    rwa [hchar] at h
  have hm_not4 : ¬ m ∣ cyclotomic 4 ℚ := by
    rw [ggB2c_cyclotomic_four_rat]
    intro hdv
    have hmin : minpoly ℚ u ∣ (X : ℚ[X]) ^ 2 + 1 := by rwa [hm_def] at hdv
    have hzero : Polynomial.aeval u ((X : ℚ[X]) ^ 2 + 1) = 0 :=
      (minpoly.dvd_iff (x := u)).mp hmin
    have hu2eq : u ^ 2 + 1 = 0 := by
      have h : Polynomial.aeval u ((X : ℚ[X]) ^ 2 + 1) = u ^ 2 + 1 := by
        simp [Polynomial.aeval_X]
      rwa [h] at hzero
    have hV2 : V ^ 2 = 1 := by
      have h1 : -(V ^ 2) + 1 = 0 := by rw [← hu2]; exact hu2eq
      have h2 : (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℚ) = V ^ 2 := by
        rw [← neg_neg (V ^ 2), eq_neg_iff_add_eq_zero]
        simpa [add_comm] using h1
      exact h2.symm
    have hV1 : V = 1 := by
      have hV4 : V ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hV2]; norm_num
      rw [← hV5, show (5 : ℕ) = 4 + 1 by norm_num, pow_add, hV4, one_mul, pow_one]
    exact hVne hV1
  have hm_dvd20 : m ∣ cyclotomic 20 ℚ := by
    by_cases h20 : cyclotomic 20 ℚ ∣ m
    · obtain ⟨m', hm'⟩ := h20
      have hm'monic : m'.Monic :=
        Polynomial.Monic.of_mul_monic_left (Polynomial.cyclotomic.monic 20 ℚ)
          (by rw [← hm']; exact hm_monic)
      have hm'4 : m' ∣ cyclotomic 4 ℚ := by
        obtain ⟨k, hk⟩ := hm_dvd'
        rw [hm'] at hk
        have hcancel : cyclotomic 4 ℚ = m' * k := by
          have : cyclotomic 20 ℚ * (cyclotomic 4 ℚ) = cyclotomic 20 ℚ * (m' * k) := by
            rw [mul_comm (cyclotomic 20 ℚ), hk, mul_assoc]
          exact mul_left_cancel₀ (Polynomial.cyclotomic.monic 20 ℚ).ne_zero this
        exact ⟨k, hcancel⟩
      have hm'1 : m' = 1 := by
        rcases ((Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 4)).dvd_iff).mp
          hm'4 with hunit | hassoc
        · exact Polynomial.Monic.eq_one_of_isUnit hm'monic hunit
        · exfalso
          have hm'eq4 : m' = cyclotomic 4 ℚ :=
            Polynomial.eq_of_monic_of_associated hm'monic
              (Polynomial.cyclotomic.monic 4 ℚ) hassoc.symm
          have hdeg : m.natDegree = 10 := by
            rw [hm', hm'eq4]
            rw [natDegree_mul (Polynomial.cyclotomic.monic 20 ℚ).ne_zero
              (Polynomial.cyclotomic.monic 4 ℚ).ne_zero]
            have h8 : (cyclotomic 20 ℚ).natDegree = 8 := by
              rw [Polynomial.natDegree_cyclotomic]; decide
            have h2 : (cyclotomic 4 ℚ).natDegree = 2 := by
              rw [Polynomial.natDegree_cyclotomic]; decide
            omega
          omega
      rw [hm', hm'1, mul_one]
    · have hcop : IsCoprime m (cyclotomic 20 ℚ) :=
        (((Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 20)).coprime_iff_not_dvd).mpr
          h20).symm
      exact absurd (hcop.dvd_of_dvd_mul_right hm_dvd') hm_not4
  have hPhi20 : Polynomial.aeval u (cyclotomic 20 ℚ) = 0 := by
    obtain ⟨q, hq⟩ := hm_dvd20
    rw [hm_def] at hq
    rw [hq, map_mul, minpoly.aeval, zero_mul]
  have hcomp : Polynomial.aeval u ((cyclotomic 5 ℚ).comp (-(X : ℚ[X]) ^ 6)) = 0 := by
    rw [ggB2c_Phi5_comp_neg_pow_six_eq, map_mul, hPhi20, zero_mul]
  rw [Polynomial.aeval_comp] at hcomp
  have hu6eval : Polynomial.aeval u (-(X : ℚ[X]) ^ 6) = -u ^ 6 := by
    simp [Polynomial.aeval_X]
  rw [hu6eval, hu6, neg_neg] at hcomp
  exact hcomp

private lemma ggB2c_Phi5_eq_zero_int {V N : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ}
    (hcomm : N * V = V * N) (hN : N ^ 2 = -1) (hV5 : V ^ 5 = 1) (hVne : V ≠ 1) :
    Polynomial.aeval V (cyclotomic 5 ℤ) = 0 := by
  have hcommq : (N.map (Int.castRingHom ℚ)) * (V.map (Int.castRingHom ℚ)) =
      (V.map (Int.castRingHom ℚ)) * (N.map (Int.castRingHom ℚ)) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hcomm]
  have hNq : (N.map (Int.castRingHom ℚ)) ^ 2 = -1 := by
    rw [← Matrix.map_pow, hN]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply, hij]
  have hV5q : (V.map (Int.castRingHom ℚ)) ^ 5 = 1 := by
    rw [← Matrix.map_pow, hV5]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.map_apply, Matrix.one_apply, hij]
  have hVneq : (V.map (Int.castRingHom ℚ)) ≠ 1 := by
    intro h
    apply hVne
    ext i j
    refine Int.cast_injective (α := ℚ) ?_
    have hc := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, Matrix.one_apply] at hc
    have hc' : (↑(V i j) : ℚ) = ↑(if i = j then (1 : ℤ) else 0) := by simpa using hc
    rw [hc']
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hrat := ggB2c_Phi5_eq_zero_rat hcommq hNq hV5q hVneq
  have hmap : Polynomial.aeval (V.map (Int.castRingHom ℚ)) (cyclotomic 5 ℚ) =
      (Polynomial.aeval V (cyclotomic 5 ℤ)).map (Int.castRingHom ℚ) := by
    have h := ggB2c_aeval_mapMatrix (Int.castRingHom ℚ) V (cyclotomic 5 ℤ)
    rwa [Polynomial.map_cyclotomic] at h
  rw [hmap] at hrat
  ext i j
  have := congrFun (congrFun hrat i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at this
  exact Int.cast_injective this

private lemma ggB2c_finrank_eq_four_mul_finrank_ker
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V) (h4 : f ^ 4 = 0)
    (hker : LinearMap.ker f = LinearMap.range (f ^ 3)) :
    Module.finrank K V = 4 * Module.finrank K ↥(LinearMap.ker f) := by
  have hle_i : ∀ i ≤ 3, LinearMap.ker (f ^ i) ≤ LinearMap.ker (f ^ (i + 1)) := by
    intro i hi x hx
    have hx' : (f ^ i) x = 0 := hx
    change (f ^ (i + 1)) x = 0
    rw [pow_succ']
    change (f.comp (f ^ i)) x = 0
    rw [LinearMap.comp_apply, hx', map_zero]
  have hker_le : ∀ i ≤ 3, LinearMap.ker f ≤ LinearMap.range (f ^ i) := by
    intro i hi x hx
    rw [hker] at hx
    obtain ⟨z, hz⟩ := hx
    refine ⟨(f ^ (3 - i)) z, ?_⟩
    change (f ^ i * f ^ (3 - i)) z = x
    rw [← pow_add]
    have : i + (3 - i) = 3 := by omega
    rw [this]; exact hz
  have hrec : ∀ i ≤ 3, Module.finrank K ↥(LinearMap.ker (f ^ (i + 1))) =
      Module.finrank K ↥(LinearMap.ker f) +
        Module.finrank K ↥(LinearMap.ker (f ^ i)) := by
    intro i hi
    let φ : ↥(LinearMap.ker (f ^ (i + 1))) →ₗ[K] V :=
      (f ^ i).comp (LinearMap.ker (f ^ (i + 1))).subtype
    have hrange : φ.range = LinearMap.ker f := by
      apply le_antisymm
      · rintro y ⟨x, rfl⟩
        have hx : (f ^ (i + 1)) (x : V) = 0 := x.2
        change f ((f ^ i) x) = 0
        change (f * f ^ i) x = 0
        rw [← pow_succ']
        exact hx
      · intro y hy
        have hy' : y ∈ LinearMap.range (f ^ 3) := by rw [← hker]; exact hy
        obtain ⟨z, hz⟩ := hy'
        refine ⟨⟨(f ^ (3 - i)) z, ?_⟩, ?_⟩
        · change (f ^ (i + 1)) ((f ^ (3 - i)) z) = 0
          change (f ^ (i + 1) * f ^ (3 - i)) z = 0
          rw [← pow_add]
          have : i + 1 + (3 - i) = 4 := by omega
          rw [this, h4]
          rfl
        · change (f ^ i) ((f ^ (3 - i)) z) = y
          change (f ^ i * f ^ (3 - i)) z = y
          rw [← pow_add]
          have : i + (3 - i) = 3 := by omega
          rw [this]; exact hz
    have hkerφ : φ.ker = (LinearMap.ker (f ^ i)).comap
        (LinearMap.ker (f ^ (i + 1))).subtype := by
      ext x
      exact Iff.rfl
    have hdim := LinearMap.finrank_range_add_finrank_ker φ
    rw [hrange, hkerφ] at hdim
    have hfin : Module.finrank K ↥((LinearMap.ker (f ^ i)).comap
        (LinearMap.ker (f ^ (i + 1))).subtype) =
        Module.finrank K ↥(LinearMap.ker (f ^ i)) := by
      have hmap : ((LinearMap.ker (f ^ i)).comap
          (LinearMap.ker (f ^ (i + 1))).subtype).map
          (LinearMap.ker (f ^ (i + 1))).subtype = LinearMap.ker (f ^ i) := by
        rw [Submodule.map_comap_subtype]
        exact inf_eq_right.mpr (hle_i i hi)
      calc Module.finrank K ↥((LinearMap.ker (f ^ i)).comap
              (LinearMap.ker (f ^ (i + 1))).subtype)
          = Module.finrank K ↥(((LinearMap.ker (f ^ i)).comap
              (LinearMap.ker (f ^ (i + 1))).subtype).map
              (LinearMap.ker (f ^ (i + 1))).subtype) :=
            (Submodule.equivSubtypeMap (LinearMap.ker (f ^ (i + 1))) _).finrank_eq
        _ = Module.finrank K ↥(LinearMap.ker (f ^ i)) := by rw [hmap]
    rw [hfin] at hdim
    exact hdim.symm
  have h3 := hrec 3 (by norm_num)
  have h2 := hrec 2 (by norm_num)
  have h1 := hrec 1 (by norm_num)
  have h0 := hrec 0 (by norm_num)
  have hker0 : Module.finrank K ↥(LinearMap.ker (f ^ 0)) = 0 := by
    rw [pow_zero]
    change Module.finrank K ↥(LinearMap.ker (LinearMap.id : V →ₗ[K] V)) = 0
    rw [LinearMap.ker_id]; simp
  have hker4 : Module.finrank K ↥(LinearMap.ker (f ^ 4)) = Module.finrank K V := by
    rw [h4, LinearMap.ker_zero]; simp
  have hker1 : Module.finrank K ↥(LinearMap.ker (f ^ 1)) =
      Module.finrank K ↥(LinearMap.ker f) := by rw [pow_one]
  have hker2 : Module.finrank K ↥(LinearMap.ker (f ^ 2)) =
      2 * Module.finrank K ↥(LinearMap.ker f) := by
    rw [h1, hker1]; ring
  have hker3 : Module.finrank K ↥(LinearMap.ker (f ^ 3)) =
      3 * Module.finrank K ↥(LinearMap.ker f) := by
    rw [h2, hker2]; ring
  rw [← hker4, h3, hker3]; ring

private lemma ggB2c_U4 (V : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ)
    (hPhi5 : Polynomial.aeval V (cyclotomic 5 ℤ) = 0) :
    (V - 1) ^ 4 =
      -(5 * (1 + 2 * (V - 1) + 2 * (V - 1) ^ 2 + (V - 1) ^ 3)) := by
  set U : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ := V - 1 with hU
  have hVeq : V = U + 1 := by rw [hU, sub_add_cancel]
  have hpoly : (X + 1 : ℤ[X]) ^ 4 + (X + 1) ^ 3 + (X + 1) ^ 2 + (X + 1) + 1 =
      X ^ 4 + 5 * (1 + 2 * X + 2 * X ^ 2 + X ^ 3) := by ring
  have h2 : V ^ 4 + V ^ 3 + V ^ 2 + V + 1 = 0 := by
    have h := hPhi5
    rw [ggB2c_cyclotomic_five_int] at h
    simpa [Polynomial.aeval_X] using h
  rw [hVeq] at h2
  have hid : (U + 1) ^ 4 + (U + 1) ^ 3 + (U + 1) ^ 2 + (U + 1) + 1 =
      U ^ 4 + 5 * (1 + 2 * U + 2 * U ^ 2 + U ^ 3) := by
    have := congrArg (Polynomial.aeval U) hpoly
    simpa [Polynomial.aeval_X, map_ofNat, map_natCast] using this
  rw [hid] at h2
  have : U ^ 4 = -(5 * (1 + 2 * U + 2 * U ^ 2 + U ^ 3)) := by
    rw [eq_neg_iff_add_eq_zero]; exact h2
  simpa [← hU] using this

private lemma ggB2c_toLin'_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (ZMod 5)) (k : ℕ) :
    (Matrix.toLin' M) ^ k = Matrix.toLin' (M ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Matrix.toLin'_one]; rfl
  | succ k ih =>
    rw [pow_succ, ih]
    change Matrix.toLin' (M ^ k) ∘ₗ Matrix.toLin' M = Matrix.toLin' (M ^ (k + 1))
    rw [← Matrix.toLin'_mul, ← pow_succ]

private theorem ggB2c_finrank_ker_le_one
    {W : Type*} [AddCommGroup W] [Module (ZMod 5) W] [Module.Finite (ZMod 5) W]
    (f : Module.End (ZMod 5) W) (hf : f ^ 4 = 0)
    (hker : LinearMap.ker f ≤ LinearMap.range (f ^ 3))
    (hdim : Module.finrank (ZMod 5) W ≤ 4) :
    Module.finrank (ZMod 5) (LinearMap.ker f) ≤ 1 := by
  have hker_eq : LinearMap.ker f = LinearMap.range (f ^ 3) := by
    refine le_antisymm hker ?_
    rintro y ⟨x, rfl⟩
    change (f ^ 3) x ∈ LinearMap.ker f
    rw [LinearMap.mem_ker]
    change (f * f ^ 3) x = 0
    rw [← pow_succ', hf]
    rfl
  have h := ggB2c_finrank_eq_four_mul_finrank_ker f hf hker_eq
  omega

private lemma ggB2c_orderOf_sq_neg_one {l : ZMod 5} (hl : l ^ 2 = -1) : orderOf l = 4 := by
  have hl4 : l ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hl]; decide
  rw [orderOf_eq_iff (by norm_num : 0 < 4)]
  refine ⟨hl4, ?_⟩
  intro m hm hlt
  interval_cases m
  · intro h
    rw [pow_one] at h
    rw [h] at hl
    exact absurd hl (by decide)
  · intro h
    rw [hl] at h
    exact absurd h (by decide)
  · intro h
    have h6 : l ^ 6 = 1 := by rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, h]; decide
    have h6' : l ^ 6 = -1 := by rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, hl]; decide
    rw [h6'] at h6
    exact absurd h6 (by decide)

private lemma ggB2c_card_eigenspace_le (w : WeylGroup .E8) (hw : ExcLangShape .E8 4 w)
    {l : ZMod 5} (hl : l ^ 2 = -1) :
    Nat.card {z : Fin Tag.E8.rank → ZMod 5 //
      (modMat 5 (weylMatrix w))ᵀ *ᵥ z = l • z} ≤ 5 ^ 4 := by
  have hchar : (weylMatrix w).charpoly = (cyclotomic 4 ℤ) ^ 4 := (ggB2c_shape_data w hw).2
  have hord : orderOf (l.val : ZMod 5) = 4 := by
    rw [ZMod.natCast_zmod_val]
    exact ggB2c_orderOf_sq_neg_one hl
  have hcard := card_eigenspace_le_of_charpoly (τ := .E8) (p := 5) (by norm_num) (d := 4) (m := 4)
    (M := weylMatrix w) hchar (q := l.val) hord
  have heq : Nat.card {z : Fin Tag.E8.rank → ZMod 5 //
        (modMat 5 (weylMatrix w))ᵀ *ᵥ z = l • z}
      = Nat.card {z : Fin Tag.E8.rank → ZMod 5 //
          (modMat 5 (weylMatrix w))ᵀ *ᵥ z = (l.val : ZMod 5) • z} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun z => ?_)
    rw [ZMod.natCast_zmod_val]
  rw [heq]; exact hcard

private lemma ggB2c_card_ker_le (W : Type*) [AddCommGroup W] [Module (ZMod 5) W]
    (f : Module.End (ZMod 5) W) [Module.Finite (ZMod 5) ↥(LinearMap.ker f)]
    (hfin : Module.finrank (ZMod 5) (LinearMap.ker f) ≤ 1) :
    Nat.card ↥(LinearMap.ker f) ≤ 5 ^ 2 := by
  have hpow : 5 ^ Module.finrank (ZMod 5) (LinearMap.ker f) =
      Nat.card ↥(LinearMap.ker f) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 5), Nat.card_zmod]
  rw [← hpow]
  calc 5 ^ Module.finrank (ZMod 5) (LinearMap.ker f) ≤ 5 ^ 1 :=
        Nat.pow_le_pow_right (by norm_num) hfin
    _ ≤ 5 ^ 2 := by norm_num

private abbrev ggB2c_mod {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (Fin n) (ZMod 5) := M.map (Int.castRingHom (ZMod 5))

private lemma ggB2c_map_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → ℤ) :
    (ggB2c_mod M) *ᵥ (fun i => (x i : ZMod 5)) = fun i => ((M *ᵥ x) i : ZMod 5) := by
  ext i
  simp only [ggB2c_mod, Matrix.map_apply, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Int.cast_sum, Int.cast_mul]
  rfl

private lemma ggB2c_map_U4 {n : ℕ} (U E : Matrix (Fin n) (Fin n) ℤ)
    (hU4 : U ^ 4 = -(5 * E)) : (ggB2c_mod U) ^ 4 = 0 := by
  have h5 : ((5 : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom (ZMod 5))) = 0 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.ofNat_apply, hij] <;> decide
  change (U.map (Int.castRingHom (ZMod 5))) ^ 4 = 0
  rw [← Matrix.map_pow, hU4]
  have hmap : ((-(5 * E)).map (Int.castRingHom (ZMod 5))) = 0 := by
    ext i j
    rw [Matrix.map_apply, Matrix.neg_apply, Matrix.zero_apply]
    have h5c : (Int.castRingHom (ZMod 5)) (5 : ℤ) = 0 := by decide
    have hE : ((5 * E : Matrix (Fin n) (Fin n) ℤ) i j) = 5 * E i j := by
      rw [Matrix.mul_apply]
      simp only [Matrix.ofNat_apply, Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul]
      rw [Finset.sum_ite_eq]; simp
    rw [hE, map_neg, map_mul, h5c, zero_mul]; exact neg_zero
  rw [hmap]

private lemma ggB2c_Einv_spec_gen {n : ℕ} (U E : Matrix (Fin n) (Fin n) ℤ)
    (hU4 : U ^ 4 = -(5 * E))
    (hE : E = 1 + 2 * U + 2 * U ^ 2 + U ^ 3) :
    ∃ Einv : Matrix (Fin n) (Fin n) (ZMod 5),
      Einv * ggB2c_mod E = 1 ∧
        Einv * (ggB2c_mod U) ^ 3 = (ggB2c_mod U) ^ 3 * Einv := by
  let u : Matrix (Fin n) (Fin n) (ZMod 5) := ggB2c_mod U
  let q : (ZMod 5)[X] := 2 * X + 2 * X ^ 2 + X ^ 3
  let p : (ZMod 5)[X] := 1 - q + q ^ 2 - q ^ 3
  let ν : Matrix (Fin n) (Fin n) (ZMod 5) := Polynomial.aeval u q
  have hu4 : u ^ 4 = 0 := ggB2c_map_U4 U E hU4
  have hq4 : q ^ 4 = (X : (ZMod 5)[X]) ^ 4 * (2 + 2 * X + X ^ 2) ^ 4 := by
    have hq : q = X * (2 + 2 * X + X ^ 2) := by simp [q]; ring
    rw [hq, mul_pow]
  have hν4 : ν ^ 4 = 0 := by
    change (Polynomial.aeval u q) ^ 4 = 0
    rw [← map_pow, hq4]
    simp only [map_mul, map_pow, Polynomial.aeval_X]
    rw [hu4, zero_mul]
  have hEmod : ggB2c_mod E = 1 + ν := by
    have hmap := ggB2c_aeval_mapMatrix (Int.castRingHom (ZMod 5)) U
      (1 + 2 * X + 2 * X ^ 2 + X ^ 3 : ℤ[X])
    have h1 : Polynomial.aeval U (1 + 2 * X + 2 * X ^ 2 + X ^ 3 : ℤ[X]) = E := by
      rw [hE]; simp [Polynomial.aeval_X, map_ofNat, map_natCast]
    have h2 : (1 + 2 * X + 2 * X ^ 2 + X ^ 3 : ℤ[X]).map
        (Int.castRingHom (ZMod 5)) = 1 + q := by
      simp [q]; ring
    rw [h1, h2] at hmap
    have h3 : Polynomial.aeval u (1 + q) = 1 + ν := by
      simp [ν, Polynomial.aeval_X]
    rw [show U.map (Int.castRingHom (ZMod 5)) = u from rfl, h3] at hmap
    exact hmap.symm
  have hp1q : p * (1 + q) = 1 - q ^ 4 := by
    simp only [p]; ring
  have h1 : Polynomial.aeval u p * (1 + ν) = 1 := by
    calc Polynomial.aeval u p * (1 + ν) = 1 - ν ^ 4 := by
          have h := congrArg (Polynomial.aeval u) hp1q
          simp only [Polynomial.aeval_mul, Polynomial.aeval_add, Polynomial.aeval_sub,
            Polynomial.aeval_one, Polynomial.aeval_X, map_pow] at h
          exact h
      _ = 1 - 0 := by rw [hν4]
      _ = 1 := by abel
  have hcomm : Polynomial.aeval u p * (ggB2c_mod U) ^ 3 =
      (ggB2c_mod U) ^ 3 * Polynomial.aeval u p := by
    have hpX : p * X ^ 3 = X ^ 3 * p := by ring
    have h := congrArg (Polynomial.aeval u) hpX
    simpa [map_mul, map_pow, Polynomial.aeval_X, u] using h
  exact ⟨Polynomial.aeval u p, by rw [hEmod]; exact h1, by simpa [u] using hcomm⟩

private lemma ggB2c_ker_map_le_range_cube {n : ℕ}
    (U E : Matrix (Fin n) (Fin n) ℤ)
    (Einv : Matrix (Fin n) (Fin n) (ZMod 5))
    (hU4 : U ^ 4 = -(5 * E))
    (hinv : Einv * ggB2c_mod E = 1)
    (hcomm : Einv * (ggB2c_mod U) ^ 3 = (ggB2c_mod U) ^ 3 * Einv) :
    ∀ x : Fin n → ZMod 5, (ggB2c_mod U) *ᵥ x = 0 →
      ∃ y : Fin n → ZMod 5, ((ggB2c_mod U) ^ 3) *ᵥ y = x := by
  intro x hx
  let x' : Fin n → ℤ := fun i => (x i).val
  have hx' : (fun i => (x' i : ZMod 5)) = x := by
    funext i; exact ZMod.natCast_zmod_val (x i)
  have hzero : (fun i => ((U *ᵥ x') i : ZMod 5)) = 0 := by
    rw [← ggB2c_map_mulVec U x', hx']; exact hx
  have hdvd : ∀ i, (5 : ℤ) ∣ (U *ᵥ x') i := fun i =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd ((U *ᵥ x') i) 5).1 (by
      have := congrFun hzero i; simpa using this)
  choose z hz using hdvd
  have hz' : U *ᵥ x' = (5 : ℤ) • z := funext hz
  have hsmul : (5 * E : Matrix (Fin n) (Fin n) ℤ) = (5 : ℤ) • E := by
    rw [show (5 : Matrix (Fin n) (Fin n) ℤ) = (5 : ℤ) •
      (1 : Matrix (Fin n) (Fin n) ℤ) by
      ext i j
      simp only [Matrix.ofNat_apply, Matrix.smul_apply, Matrix.one_apply]
      by_cases h : i = j <;> simp [h]]
    rw [Matrix.smul_mul, Matrix.one_mul]
  have h5 : (5 : ℤ) • ((U ^ 3) *ᵥ z) = -((5 : ℤ) • (E *ᵥ x')) := by
    calc (5 : ℤ) • ((U ^ 3) *ᵥ z) = (U ^ 3) *ᵥ ((5 : ℤ) • z) := by
          rw [Matrix.mulVec_smul]
      _ = (U ^ 3) *ᵥ (U *ᵥ x') := by rw [← hz']
      _ = (U ^ 3 * U) *ᵥ x' := by rw [Matrix.mulVec_mulVec]
      _ = U ^ 4 *ᵥ x' := rfl
      _ = (-(5 * E)) *ᵥ x' := by rw [hU4]
      _ = -((5 : ℤ) • (E *ᵥ x')) := by
            rw [Matrix.neg_mulVec, hsmul, Matrix.smul_mulVec]
  have hcancel : (U ^ 3) *ᵥ z = -(E *ᵥ x') := by
    have h5' : (5 : ℤ) • ((U ^ 3) *ᵥ z) = (5 : ℤ) • (-(E *ᵥ x')) := by
      rw [h5, ← smul_neg]
    ext i
    have := congrFun h5' i
    simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) this
  let zbar : Fin n → ZMod 5 := fun i => (z i : ZMod 5)
  have hred : ((ggB2c_mod U) ^ 3) *ᵥ zbar = -((ggB2c_mod E) *ᵥ x) := by
    have h := congrArg (fun w : Fin n → ℤ => fun i => (w i : ZMod 5)) hcancel
    have hL : (fun i => ((U ^ 3 *ᵥ z) i : ZMod 5)) = ((ggB2c_mod U) ^ 3) *ᵥ zbar := by
      rw [show ((ggB2c_mod U) ^ 3) = ggB2c_mod (U ^ 3) from by
            simp only [ggB2c_mod, Matrix.map_pow],
        ggB2c_map_mulVec (U ^ 3) z]
    have hR : (fun i => ((-(E *ᵥ x')) i : ZMod 5)) = -((ggB2c_mod E) *ᵥ x) := by
      rw [show (ggB2c_mod E) *ᵥ x = (ggB2c_mod E) *ᵥ (fun i => (x' i : ZMod 5)) by
            rw [hx'],
        ggB2c_map_mulVec E x']
      funext i
      simp only [Pi.neg_apply]
      exact Int.cast_neg _
    rw [hL, hR] at h
    exact h
  have hEx : Einv *ᵥ ((ggB2c_mod E) *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hcube : ((ggB2c_mod U) ^ 3) *ᵥ (Einv *ᵥ zbar) = -x := by
    calc ((ggB2c_mod U) ^ 3) *ᵥ (Einv *ᵥ zbar)
        = (((ggB2c_mod U) ^ 3) * Einv) *ᵥ zbar := by rw [Matrix.mulVec_mulVec]
      _ = (Einv * (ggB2c_mod U) ^ 3) *ᵥ zbar := by rw [hcomm]
      _ = Einv *ᵥ (((ggB2c_mod U) ^ 3) *ᵥ zbar) := by rw [Matrix.mulVec_mulVec]
      _ = Einv *ᵥ (-((ggB2c_mod E) *ᵥ x)) := by rw [hred]
      _ = -(Einv *ᵥ ((ggB2c_mod E) *ᵥ x)) := Matrix.mulVec_neg ((ggB2c_mod E) *ᵥ x) Einv
      _ = -x := by rw [hEx]
  refine ⟨-(Einv *ᵥ zbar), ?_⟩
  calc ((ggB2c_mod U) ^ 3) *ᵥ (-(Einv *ᵥ zbar))
      = -(((ggB2c_mod U) ^ 3) *ᵥ (Einv *ᵥ zbar)) :=
        Matrix.mulVec_neg (Einv *ᵥ zbar) ((ggB2c_mod U) ^ 3)
    _ = -(-x) := by rw [hcube]
    _ = x := neg_neg x

private lemma ggB2c_proj_mem_gen {n : ℕ} (Nmat : Matrix (Fin n) (Fin n) (ZMod 5))
    {l : ZMod 5} (hl : l ^ 2 = -1) (hNmat2 : Nmat ^ 2 = -1) :
    (Nmat - l • (1 : Matrix (Fin n) (Fin n) (ZMod 5))) *
      (((2 * l)⁻¹) • (Nmat + l • (1 : Matrix (Fin n) (Fin n) (ZMod 5)))) = 0 := by
  have h1 : Nmat * (l • 1) = l • Nmat := by rw [Matrix.mul_smul, Matrix.mul_one]
  have h2 : (l • 1) * Nmat = l • Nmat := by rw [Matrix.smul_mul, Matrix.one_mul]
  have h3 : (l • (1 : Matrix (Fin n) (Fin n) (ZMod 5))) *
        (l • (1 : Matrix (Fin n) (Fin n) (ZMod 5))) =
        (l * l) • (1 : Matrix (Fin n) (Fin n) (ZMod 5)) := by
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul]
  have hll : l * l = -1 := by rw [← pow_two l]; exact hl
  have h4 : (Nmat - l • 1) * (Nmat + l • 1) = Nmat * Nmat - (l • 1) * (l • 1) := by
    rw [mul_add, sub_mul, sub_mul, h1, h2]
    abel
  calc (Nmat - l • 1) * (((2 * l)⁻¹) • (Nmat + l • 1))
      = ((2 * l)⁻¹) • ((Nmat - l • 1) * (Nmat + l • 1)) := by rw [Matrix.mul_smul]
    _ = ((2 * l)⁻¹) • (Nmat * Nmat - (l • 1) * (l • 1)) := by rw [h4]
    _ = ((2 * l)⁻¹) • (Nmat * Nmat - (l * l) • 1) := by rw [h3]
    _ = ((2 * l)⁻¹) • ((-1 : Matrix (Fin n) (Fin n) (ZMod 5)) - (l * l) • 1) := by
          rw [← pow_two Nmat, hNmat2]
    _ = 0 := by
      rw [hll]
      have hneg : (-1 : ZMod 5) • (1 : Matrix (Fin n) (Fin n) (ZMod 5)) = -1 := by
        rw [Matrix.smul_one_eq_diagonal]
        rw [show (1 : Matrix (Fin n) (Fin n) (ZMod 5)) =
            Matrix.diagonal (fun _ => (1 : ZMod 5)) from Matrix.diagonal_one.symm]
        exact (Matrix.diagonal_neg (fun _ => (1 : ZMod 5))).symm
      rw [hneg, sub_self, smul_zero]

private lemma ggB2c_proj_id_gen {n : ℕ} (Nmat : Matrix (Fin n) (Fin n) (ZMod 5))
    {l : ZMod 5} (hl : l ^ 2 = -1) (z : Fin n → ZMod 5)
    (hz : (Nmat - l • (1 : Matrix (Fin n) (Fin n) (ZMod 5))) *ᵥ z = 0) :
    (((2 * l)⁻¹) • (Nmat + l • (1 : Matrix (Fin n) (Fin n) (ZMod 5)))) *ᵥ z = z := by
  have hz' : Nmat *ᵥ z = l • z := by
    have h := hz
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h
  have hl0 : l ≠ 0 := by
    intro h
    rw [h] at hl
    exact absurd hl (by decide)
  have h2l : (2 * l : ZMod 5) ≠ 0 := mul_ne_zero (by decide) hl0
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hz']
  rw [show l • z + l • z = (2 * l) • z by module, smul_smul, inv_mul_cancel₀ h2l, one_smul]

private lemma ggB2c_proj_comm_gen {n : ℕ} (Nmat : Matrix (Fin n) (Fin n) (ZMod 5))
    (Umat : Matrix (Fin n) (Fin n) (ZMod 5)) {l : ZMod 5}
    (hNtU : Nmat * Umat = Umat * Nmat) :
    (((2 * l)⁻¹) • (Nmat + l • (1 : Matrix (Fin n) (Fin n) (ZMod 5)))) * Umat =
      Umat * (((2 * l)⁻¹) • (Nmat + l • (1 : Matrix (Fin n) (Fin n) (ZMod 5)))) := by
  have h1 : (Nmat + l • 1) * Umat = Nmat * Umat + l • Umat := by
    rw [add_mul, Matrix.smul_mul, Matrix.one_mul]
  have h2 : Umat * (Nmat + l • 1) = Umat * Nmat + l • Umat := by
    rw [mul_add, Matrix.mul_smul, Matrix.mul_one]
  calc (((2 * l)⁻¹) • (Nmat + l • 1)) * Umat
      = ((2 * l)⁻¹) • ((Nmat + l • 1) * Umat) := by rw [Matrix.smul_mul]
    _ = ((2 * l)⁻¹) • (Nmat * Umat + l • Umat) := by rw [h1]
    _ = ((2 * l)⁻¹) • (Umat * Nmat + l • Umat) := by rw [hNtU]
    _ = ((2 * l)⁻¹) • (Umat * (Nmat + l • 1)) := by rw [h2]
    _ = Umat * (((2 * l)⁻¹) • (Nmat + l • 1)) := by rw [Matrix.mul_smul]

private lemma ggB2c_fl_ker_le_range_gen {n : ℕ}
    (Nmat Umat : Matrix (Fin n) (Fin n) (ZMod 5))
    (Ut : Module.End (ZMod 5) (Fin n → ZMod 5))
    (Vl : Submodule (ZMod 5) (Fin n → ZMod 5))
    {l : ZMod 5} (hl : l ^ 2 = -1) (hNmat2 : Nmat ^ 2 = -1)
    (hVl : Vl = LinearMap.ker (Matrix.toLin' (Nmat - l • 1)))
    (hUt : Ut = Matrix.toLin' Umat)
    (hNtU : Nmat * Umat = Umat * Nmat)
    (hUv : ∀ x ∈ Vl, Ut x ∈ Vl)
    (U E : Matrix (Fin n) (Fin n) ℤ)
    (Einv : Matrix (Fin n) (Fin n) (ZMod 5))
    (hU4 : U ^ 4 = -(5 * E)) (hinv : Einv * ggB2c_mod E = 1)
    (hcomm : Einv * (ggB2c_mod U) ^ 3 = (ggB2c_mod U) ^ 3 * Einv)
    (hUmat : Umat = ggB2c_mod U) :
    LinearMap.ker (Ut.restrict hUv) ≤ LinearMap.range ((Ut.restrict hUv) ^ 3) := by
  have hPmatVl := ggB2c_proj_mem_gen Nmat hl hNmat2
  intro x hx
  have hUtx : Ut ((x : ↥Vl) : Fin n → ZMod 5) = 0 := by
    have h := hx
    rw [LinearMap.mem_ker] at h
    exact congrArg Subtype.val h
  have hUtx' : Umat *ᵥ ((x : ↥Vl) : Fin n → ZMod 5) = 0 := by
    have h := hUtx
    rw [hUt, Matrix.toLin'_apply] at h
    exact h
  obtain ⟨y, hy⟩ := ggB2c_ker_map_le_range_cube U E Einv hU4 hinv hcomm
    ((x : ↥Vl) : Fin n → ZMod 5) (by rw [← hUmat]; exact hUtx')
  have hy' : (Ut ^ 3) y = ((x : ↥Vl) : Fin n → ZMod 5) := by
    rw [hUt, hUmat, ggB2c_toLin'_pow, Matrix.toLin'_apply]
    exact hy
  set Pmat : Matrix (Fin n) (Fin n) (ZMod 5) :=
    ((2 * l)⁻¹) • (Nmat + l • (1 : Matrix (Fin n) (Fin n) (ZMod 5))) with hPmat
  have hPcomm : Pmat * Umat = Umat * Pmat := by
    rw [hPmat]; exact ggB2c_proj_comm_gen Nmat Umat hNtU
  have hπVl : ∀ z, Matrix.toLin' Pmat z ∈ Vl := by
    intro z
    rw [hVl, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, hPmat, hPmatVl, Matrix.zero_mulVec]
  have hπid : ∀ z ∈ Vl, Matrix.toLin' Pmat z = z := by
    intro z hz
    rw [hVl, LinearMap.mem_ker, Matrix.toLin'_apply] at hz
    rw [Matrix.toLin'_apply, hPmat]
    exact ggB2c_proj_id_gen Nmat hl z hz
  have hπUt : Matrix.toLin' Pmat * Ut = Ut * Matrix.toLin' Pmat := by
    rw [hUt, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hPcomm]
  have hπUt3 : Matrix.toLin' Pmat * Ut ^ 3 = Ut ^ 3 * Matrix.toLin' Pmat :=
    (Commute.pow_right (show Commute (Matrix.toLin' Pmat) Ut from hπUt) 3).eq
  have hrestr : ∀ (m : ℕ) (z : ↥Vl),
      (((Ut.restrict hUv) ^ m) z : Fin n → ZMod 5) =
        (Ut ^ m) (z : Fin n → ZMod 5) := by
    intro m
    induction m with
    | zero => intro z; rfl
    | succ m ih =>
      intro z
      rw [pow_succ]
      change (((Ut.restrict hUv) ^ m) ((Ut.restrict hUv) z) : Fin n → ZMod 5) = _
      rw [ih ((Ut.restrict hUv) z), pow_succ]
      rfl
  refine ⟨⟨Matrix.toLin' Pmat y, hπVl y⟩, ?_⟩
  apply Subtype.ext
  change (((Ut.restrict hUv) ^ 3) ⟨Matrix.toLin' Pmat y, hπVl y⟩ :
    Fin n → ZMod 5) = ((x : ↥Vl) : Fin n → ZMod 5)
  rw [hrestr]
  calc (Ut ^ 3) ((Matrix.toLin' Pmat) y) = (Ut ^ 3 * Matrix.toLin' Pmat) y := rfl
    _ = (Matrix.toLin' Pmat * Ut ^ 3) y := by rw [hπUt3]
    _ = Matrix.toLin' Pmat ((Ut ^ 3) y) := rfl
    _ = Matrix.toLin' Pmat ((x : ↥Vl) : Fin n → ZMod 5) := by rw [hy']
    _ = ((x : ↥Vl) : Fin n → ZMod 5) := hπid _ (x : ↥Vl).2

private lemma ggB2c_hfl4_gen {n : ℕ}
    (Ut : Module.End (ZMod 5) (Fin n → ZMod 5))
    (Vl : Submodule (ZMod 5) (Fin n → ZMod 5))
    (Umat : Matrix (Fin n) (Fin n) (ZMod 5))
    (U E : Matrix (Fin n) (Fin n) ℤ)
    (hUt : Ut = Matrix.toLin' Umat) (hUmat : Umat = ggB2c_mod U)
    (hU4 : U ^ 4 = -(5 * E)) (hUv : ∀ x ∈ Vl, Ut x ∈ Vl) :
    (Ut.restrict hUv) ^ 4 = 0 := by
  have hrestr : ∀ (m : ℕ) (z : ↥Vl),
      (((Ut.restrict hUv) ^ m) z : Fin n → ZMod 5) =
        (Ut ^ m) (z : Fin n → ZMod 5) := by
    intro m
    induction m with
    | zero => intro z; rfl
    | succ m ih =>
      intro z
      rw [pow_succ]
      change (((Ut.restrict hUv) ^ m) ((Ut.restrict hUv) z) : Fin n → ZMod 5) = _
      rw [ih ((Ut.restrict hUv) z), pow_succ]
      rfl
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [hrestr 4 x, hUt, ggB2c_toLin'_pow, hUmat, ggB2c_map_U4 U E hU4]
  simp

private lemma ggB2c_hUv_gen {n : ℕ} {l : ZMod 5}
    (Nmat Umat : Matrix (Fin n) (Fin n) (ZMod 5))
    (Ut : Module.End (ZMod 5) (Fin n → ZMod 5))
    (Vl : Submodule (ZMod 5) (Fin n → ZMod 5))
    (hNtU : Nmat * Umat = Umat * Nmat)
    (hUt : Ut = Matrix.toLin' Umat)
    (hVl : Vl = LinearMap.ker (Matrix.toLin' (Nmat - l • 1))) :
    ∀ x ∈ Vl, Ut x ∈ Vl := by
  intro x hx
  rw [hVl, LinearMap.mem_ker, Matrix.toLin'_apply] at hx ⊢
  rw [hUt, Matrix.toLin'_apply]
  have hsub : (Nmat - l • 1) * Umat = Umat * (Nmat - l • 1) := by
    rw [sub_mul, mul_sub, hNtU, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one]
  rw [Matrix.mulVec_mulVec, hsub, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

private lemma ggB2c_ker_card_gen {W : Type*} [AddCommGroup W] [Module (ZMod 5) W]
    (Vl : Submodule (ZMod 5) W) (Ut : Module.End (ZMod 5) W)
    (hUv : ∀ x ∈ Vl, Ut x ∈ Vl) (P : W → Prop)
    (hP : ∀ z, P z ↔ z ∈ Vl ∧ Ut z = 0) :
    Nat.card ↥(LinearMap.ker (Ut.restrict hUv)) = Nat.card {z : W // P z} := by
  have hFix1 : Nat.card ↥(LinearMap.ker (Ut.restrict hUv)) =
      Nat.card {x : ↥Vl // Ut x = 0} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun x => ?_)
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; apply Subtype.ext; exact h
  have hFix2 : Nat.card {x : ↥Vl // Ut x = 0} =
      Nat.card {z : W // z ∈ Vl ∧ Ut z = 0} := by
    apply Nat.card_congr
    exact (Equiv.subtypeSubtypeEquivSubtypeExists (fun z => z ∈ Vl)
      (fun x => Ut x = 0)).trans
      (Equiv.subtypeEquivRight (fun a => by simp [exists_prop]))
  have hFix3 : Nat.card {z : W // z ∈ Vl ∧ Ut z = 0} = Nat.card {z : W // P z} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun z => ?_)
    exact (hP z).symm
  rw [hFix1, hFix2, hFix3]

private theorem ggB2c_rootMultiplicity_pow {R : Type*} [CommRing R] [IsDomain R]
    (P : R[X]) (hP : P ≠ 0) (a : R) (m : ℕ) :
    (P ^ m).rootMultiplicity a = m * P.rootMultiplicity a := by
  induction m with
  | zero => simpa using Polynomial.rootMultiplicity_C (1 : R) a
  | succ n ih =>
      rw [pow_succ, Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hP) hP), ih,
        Nat.succ_mul]

private theorem ggB2c_charpoly_modMat_transpose {τ : Tag} (p : ℕ)
    (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) :
    ((modMat p M)ᵀ).charpoly = (M.charpoly).map (Int.castRingHom (ZMod p)) := by
  rw [Matrix.charpoly_transpose]
  simpa only [modMat] using Matrix.charpoly_map M (Int.castRingHom (ZMod p))

private theorem ggB2c_cyclotomic_rootMultiplicity_le_one {p d q : ℕ} (hp : p.Prime)
    (hq : orderOf (q : ZMod p) = d) :
    (cyclotomic d (ZMod p)).rootMultiplicity (q : ZMod p) ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne d 0 with rfl | hd
  · rw [Polynomial.cyclotomic_zero, ← Polynomial.C_1, Polynomial.rootMultiplicity_C]
    exact Nat.zero_le 1
  · have hd0 : 0 < d := Nat.pos_of_ne_zero hd
    have hpr : IsPrimitiveRoot (q : ZMod p) d := IsPrimitiveRoot.iff_orderOf.mpr hq
    have hq0 : (q : ZMod p) ≠ 0 := hpr.ne_zero hd
    have hdvd : d ∣ p - 1 := by
      rw [← hq]
      exact ZMod.orderOf_dvd_card_sub_one hq0
    have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
    have hpd : ¬ p ∣ d := by
      intro h
      have := Nat.le_of_dvd hd0 h
      have := Nat.le_of_dvd hp1 hdvd
      omega
    have hNe : NeZero (d : ZMod p) := ⟨fun h => hpd ((ZMod.natCast_eq_zero_iff d p).1 h)⟩
    haveI : NeZero (d : ZMod p) := hNe
    have hsep := Polynomial.separable_cyclotomic d (ZMod p)
    have hroot : IsRoot (cyclotomic d (ZMod p)) (q : ZMod p) :=
      Polynomial.isRoot_cyclotomic_iff.mpr hpr
    exact Polynomial.rootMultiplicity_le_one_of_separable hsep (q : ZMod p)

private lemma ggB2c_hdim_gen {K : Type*} [Field K] {n : ℕ}
    (Nmat : Matrix (Fin n) (Fin n) K) (l : K)
    (hroot : ((Nmat - l • 1).charpoly).rootMultiplicity 0 ≤ 4)
    (Vl : Submodule K (Fin n → K))
    (hVl : Vl = LinearMap.ker (Matrix.toLin' (Nmat - l • 1))) :
    Module.finrank K ↥Vl ≤ 4 := by
  have h : Module.finrank K (LinearMap.ker (Matrix.toLin' (Nmat - l • 1))) ≤
      ((Nmat - l • 1).charpoly).rootMultiplicity 0 := by
    have h' := LinearMap.finrank_eigenspace_le (K := K) (M := Fin n → K)
      (φ := Matrix.toLin' (Nmat - l • 1)) (μ := 0)
    rw [Module.End.eigenspace_zero] at h'
    rw [Matrix.charpoly_toLin'] at h'
    exact h'
  rw [hVl]
  exact le_trans h hroot

private lemma ggB2c_finrank_ker_le_one_sub {W : Type*} [AddCommGroup W]
    [Module (ZMod 5) W] (Vl : Submodule (ZMod 5) W) [Module.Finite (ZMod 5) ↥Vl]
    (f : Module.End (ZMod 5) ↥Vl) (hf : f ^ 4 = 0)
    (hker : LinearMap.ker f ≤ LinearMap.range (f ^ 3))
    (hdim : Module.finrank (ZMod 5) ↥Vl ≤ 4) :
    Module.finrank (ZMod 5) (LinearMap.ker f) ≤ 1 :=
  ggB2c_finrank_ker_le_one f hf hker hdim

private lemma ggB2c_card_ker_le_sub {W : Type*} [AddCommGroup W] [Module (ZMod 5) W]
    (Vl : Submodule (ZMod 5) W) [Module.Finite (ZMod 5) ↥Vl]
    (f : Module.End (ZMod 5) ↥Vl) [Module.Finite (ZMod 5) ↥(LinearMap.ker f)]
    (hfin : Module.finrank (ZMod 5) (LinearMap.ker f) ≤ 1) :
    Nat.card ↥(LinearMap.ker f) ≤ 5 ^ 2 :=
  ggB2c_card_ker_le ↥Vl f hfin

private lemma ggB2c_fix_card_le_gen {n : ℕ}
    (Nmat Umat : Matrix (Fin n) (Fin n) (ZMod 5))
    (U E : Matrix (Fin n) (Fin n) ℤ) {l : ZMod 5} (hl : l ^ 2 = -1)
    (hNmat2 : Nmat ^ 2 = -1) (hNtU : Nmat * Umat = Umat * Nmat)
    (hUmat : Umat = ggB2c_mod U)
    (hU4 : U ^ 4 = -(5 * E)) (hE : E = 1 + 2 * U + 2 * U ^ 2 + U ^ 3)
    (hcard : Nat.card {z : Fin n → ZMod 5 // Nmat *ᵥ z = l • z} ≤ 5 ^ 4)
    (hroot : ((Nmat - l • 1).charpoly).rootMultiplicity 0 ≤ 4) :
    Nat.card {z : Fin n → ZMod 5 // Nmat *ᵥ z = l • z ∧ Umat *ᵥ z = 0} ≤ 5 ^ 2 := by
  obtain ⟨Ut, hUt⟩ : ∃ Ut : Module.End (ZMod 5) (Fin n → ZMod 5),
      Ut = Matrix.toLin' Umat := ⟨_, rfl⟩
  obtain ⟨Vl, hVl⟩ : ∃ Vl : Submodule (ZMod 5) (Fin n → ZMod 5),
      Vl = LinearMap.ker (Matrix.toLin' (Nmat - l • 1)) := ⟨_, rfl⟩
  let modAmb : Module (ZMod 5) (Fin n → ZMod 5) := inferInstance
  have hUv : ∀ x ∈ Vl, Ut x ∈ Vl := ggB2c_hUv_gen Nmat Umat Ut Vl hNtU hUt hVl
  obtain ⟨Einv, hinv, hcomm⟩ := ggB2c_Einv_spec_gen U E hU4 hE
  have hker := ggB2c_fl_ker_le_range_gen Nmat Umat Ut Vl hl hNmat2 hVl hUt hNtU hUv U E
    Einv hU4 hinv hcomm hUmat
  have hfl4 := ggB2c_hfl4_gen Ut Vl Umat U E hUt hUmat hU4 hUv
  have hdim := ggB2c_hdim_gen Nmat l hroot Vl hVl
  have hFinVl : Module.Finite (ZMod 5) ↥Vl :=
    Module.Finite.of_injective (Submodule.subtype Vl) Subtype.coe_injective
  have hfin : Module.finrank (ZMod 5) (LinearMap.ker (Ut.restrict hUv)) ≤ 1 :=
    @ggB2c_finrank_ker_le_one_sub (Fin n → ZMod 5) _ modAmb Vl hFinVl
      (Ut.restrict hUv) hfl4 hker hdim
  have hFinKer : Module.Finite (ZMod 5) ↥(LinearMap.ker (Ut.restrict hUv)) :=
    Module.Finite.of_injective (Submodule.subtype (LinearMap.ker (Ut.restrict hUv)))
      Subtype.coe_injective
  have hmain : Nat.card ↥(LinearMap.ker (Ut.restrict hUv)) ≤ 5 ^ 2 :=
    @ggB2c_card_ker_le_sub (Fin n → ZMod 5) _ modAmb Vl hFinVl
      (Ut.restrict hUv) hFinKer hfin
  have hiff : ∀ z : Fin n → ZMod 5,
      (z ∈ Vl ∧ Ut z = 0) ↔ (Nmat *ᵥ z = l • z ∧ Umat *ᵥ z = 0) := by
    intro z
    rw [hVl, LinearMap.mem_ker, Matrix.toLin'_apply, hUt, Matrix.toLin'_apply,
      Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
  have heq := @ggB2c_ker_card_gen (Fin n → ZMod 5) _ modAmb Vl Ut hUv
    (fun z => Nmat *ᵥ z = l • z ∧ Umat *ᵥ z = 0) (fun z => (hiff z).symm)
  rw [← heq]
  exact hmain

private lemma ggB2c_hroot_of_charpoly {n : ℕ} {l : ZMod 5} (hl : l ^ 2 = -1)
    (Nmat : Matrix (Fin n) (Fin n) (ZMod 5))
    (hchar : Nmat.charpoly = (cyclotomic 4 (ZMod 5)) ^ 4) :
    ((Nmat - l • 1).charpoly).rootMultiplicity 0 ≤ 4 := by
  have hscalar : l • (1 : Matrix (Fin n) (Fin n) (ZMod 5)) = Matrix.scalar (Fin n) l := by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hlr : (cyclotomic 4 (ZMod 5)).rootMultiplicity l ≤ 1 := by
    have hq : orderOf (l.val : ZMod 5) = 4 := by
      rw [ZMod.natCast_zmod_val]; exact ggB2c_orderOf_sq_neg_one hl
    have h := ggB2c_cyclotomic_rootMultiplicity_le_one (p := 5) (d := 4) (q := l.val)
      (by norm_num) hq
    simpa [ZMod.natCast_zmod_val] using h
  have hcomp : (((cyclotomic 4 (ZMod 5)) ^ 4).comp (X + C l)).rootMultiplicity 0 =
      ((cyclotomic 4 (ZMod 5)) ^ 4).rootMultiplicity l := by
    have h := Polynomial.rootMultiplicity_comp_C_mul_X_add_C ((cyclotomic 4 (ZMod 5)) ^ 4)
      (1 : ZMod 5) l 0 (isUnit_one)
    simpa using h
  have hpow : ((cyclotomic 4 (ZMod 5)) ^ 4).rootMultiplicity l =
      4 * (cyclotomic 4 (ZMod 5)).rootMultiplicity l :=
    ggB2c_rootMultiplicity_pow (cyclotomic 4 (ZMod 5))
      (Polynomial.cyclotomic.monic 4 (ZMod 5)).ne_zero l 4
  rw [hscalar, Matrix.charpoly_sub_scalar, hchar, hcomp, hpow]
  nlinarith [hlr]

theorem card_fixed_eigenspace_le_of_commute_order_five
    {w v : WeylGroup .E8} (hw : ExcLangShape .E8 4 w) (hvw : v * w = w * v)
    (hv : orderOf v = 5) {l : ZMod 5} (hl : l ^ 2 = -1) :
    Nat.card {z : Fin Tag.E8.rank → ZMod 5 //
      (modMat 5 (weylMatrix w)).transpose *ᵥ z = l • z ∧
        (modMat 5 (weylMatrix v)).transpose *ᵥ z = z} ≤ 5 ^ 2 := by
  have hphi : Polynomial.aeval ((weylMatrix v)ᵀ) (cyclotomic 5 ℤ) = 0 :=
    ggB2c_Phi5_eq_zero_int (ggB2c_transpose_comm w v hvw) (ggB2c_transpose_sq w hw)
      (ggB2c_transpose_pow_five v hv) (ggB2c_transpose_ne_one v hv)
  set U : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ := (weylMatrix v)ᵀ - 1 with hU
  have hU4 : U ^ 4 = -(5 * (1 + 2 * U + 2 * U ^ 2 + U ^ 3)) := by
    rw [hU]; exact ggB2c_U4 ((weylMatrix v)ᵀ) hphi
  have hmodU : modMat 5 U = (modMat 5 (weylMatrix v))ᵀ - 1 := by
    rw [hU]; simp [modMat, Matrix.map_sub, Matrix.map_one, Matrix.transpose_map]
  have hNmat2 : ((modMat 5 (weylMatrix w))ᵀ) ^ 2 = -1 := by
    rw [modMat, ← Matrix.transpose_map, ← Matrix.map_pow, ggB2c_transpose_sq w hw]
    ext i j
    by_cases hij : i = j
    · simp [Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply, hij, map_neg, map_one]
      decide
    · simp [Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply, hij, map_neg, map_one]
      decide
  have hcommN : (modMat 5 (weylMatrix w))ᵀ * (modMat 5 (weylMatrix v))ᵀ =
      (modMat 5 (weylMatrix v))ᵀ * (modMat 5 (weylMatrix w))ᵀ := by
    have h := congrArg (fun M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ => modMat 5 M)
      (ggB2c_transpose_comm w v hvw)
    simp only [modMat, Matrix.map_mul, Matrix.transpose_map] at h
    exact h
  have hNtU : (modMat 5 (weylMatrix w))ᵀ * (modMat 5 U) =
      (modMat 5 U) * (modMat 5 (weylMatrix w))ᵀ := by
    rw [hmodU, mul_sub, sub_mul, Matrix.mul_one, Matrix.one_mul, hcommN]
  have hchar : ((modMat 5 (weylMatrix w))ᵀ).charpoly = (cyclotomic 4 (ZMod 5)) ^ 4 := by
    rw [ggB2c_charpoly_modMat_transpose 5 (weylMatrix w), (ggB2c_shape_data w hw).2,
      Polynomial.map_pow, Polynomial.map_cyclotomic_int]
  have hcard := ggB2c_card_eigenspace_le w hw hl
  have hroot := ggB2c_hroot_of_charpoly hl ((modMat 5 (weylMatrix w))ᵀ) hchar
  have hmain := ggB2c_fix_card_le_gen (n := Tag.E8.rank)
    ((modMat 5 (weylMatrix w))ᵀ) (modMat 5 U) U (1 + 2 * U + 2 * U ^ 2 + U ^ 3)
    hl hNmat2 hNtU rfl hU4 rfl hcard hroot
  rw [show Nat.card {z : Fin Tag.E8.rank → ZMod 5 //
      (modMat 5 (weylMatrix w)).transpose *ᵥ z = l • z ∧
        (modMat 5 (weylMatrix v)).transpose *ᵥ z = z} =
      Nat.card {z : Fin Tag.E8.rank → ZMod 5 //
        (modMat 5 (weylMatrix w))ᵀ *ᵥ z = l • z ∧ (modMat 5 U) *ᵥ z = 0} from by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun z => ?_)
    rw [hmodU, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]]
  exact hmain

end FixedSpace

section NormalizerTorsion

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.ExcMaxToral Polynomial
open scoped Matrix

private abbrev ggB2d_weylQuotient (τ : Tag) (L : Type) [Field L] :
    Type :=
  monomialSubgroup τ L ⧸ (torusGroup τ L).subgroupOf (monomialSubgroup τ L)

private lemma ggB2d_exists_unit_pow_eq {L : Type} [Field L] [IsAlgClosed L]
    (u : Lˣ) {N : ℕ} (hN : 0 < N) : ∃ v : Lˣ, v ^ N = u := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : L) hN
  have hz0 : z ≠ 0 := by
    intro h0
    apply u.ne_zero
    rw [← hz, h0, zero_pow hN.ne']
  exact ⟨Units.mk0 z hz0, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hz)⟩

private lemma ggB2d_torusGroup_divisible {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {N : ℕ} (hN : 0 < N) {t : ModGL τ L} (ht : t ∈ torusGroup τ L) :
    ∃ s ∈ torusGroup τ L, s ^ N = t := by
  have hrange : torusGroup τ L ≤ (rootDiagUnitHom τ L).range := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, u⟩, rfl⟩
    exact ⟨_, (torusElt_eq_rootDiagUnit i u).symm⟩
  obtain ⟨a, ha⟩ := hrange ht
  choose b hb using fun i => ggB2d_exists_unit_pow_eq (a i) hN
  refine ⟨rootDiagUnitHom τ L b, rootDiagUnit_mem_torusGroup b, ?_⟩
  have hbN : b ^ N = a := funext fun i => by rw [Pi.pow_apply, hb i]
  rw [← map_pow, hbN, ha]

private lemma ggB2d_familyKernel_eq_empty {τ : Tag} {L : Type} [Field L]
    (A : Subgroup (Fin τ.rank → Lˣ))
    (hroot : ∀ α : Fin τ.rank → ℤ, IsRoot τ α → ∃ a ∈ A, rootChar a α ≠ 1) :
    CFSG.HardMathSupport.Timmesfeld.Torality.familyKernel
      (fun x : A => (x : Fin τ.rank → Lˣ)) = ∅ := by
  ext α
  constructor
  · intro hα
    obtain ⟨hαr, hα1⟩ := hα
    obtain ⟨a, ha, hne⟩ := hroot α hαr
    exact absurd (hα1 ⟨a, ha⟩) hne
  · intro h
    exact h.elim

private lemma ggB2d_familyGroup_eq_torusGroup {τ : Tag} {L : Type} [Field L]
    (A : Subgroup (Fin τ.rank → Lˣ))
    (hroot : ∀ α : Fin τ.rank → ℤ, IsRoot τ α → ∃ a ∈ A, rootChar a α ≠ 1) :
    CFSG.HardMathSupport.Timmesfeld.Torality.familyGroup (K := L)
      (fun x : A => (x : Fin τ.rank → Lˣ)) = torusGroup τ L := by
  unfold CFSG.HardMathSupport.Timmesfeld.Torality.familyGroup
  rw [ggB2d_familyKernel_eq_empty A hroot]
  simp [rootSpan]

private lemma ggB2d_rootDiagUnitHom_map_le_torusGroup {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L]
    (A : Subgroup (Fin τ.rank → Lˣ)) :
    A.map (rootDiagUnitHom τ L) ≤ torusGroup τ L := by
  rw [Subgroup.map_le_iff_le_comap]
  intro a _
  exact rootDiagUnit_mem_torusGroup a

private lemma ggB2d_conj_inv_mem {τ : Tag} {L : Type} [Field L]
    {A : Subgroup (Fin τ.rank → Lˣ)} {n : ModGL τ L} (hA : Finite A)
    (hnA : ∀ a ∈ A, n * rootDiagUnit τ a * n⁻¹ ∈ A.map (rootDiagUnitHom τ L)) :
    ∀ s ∈ A.map (rootDiagUnitHom τ L), n⁻¹ * s * n ∈ A.map (rootDiagUnitHom τ L) := by
  have hSfin : Finite (A.map (rootDiagUnitHom τ L)) := by
    refine Finite.of_surjective (fun x : A =>
      (⟨rootDiagUnitHom τ L x.1, Subgroup.mem_map_of_mem (rootDiagUnitHom τ L) x.2⟩ :
        A.map (rootDiagUnitHom τ L))) ?_
    rintro ⟨s, hs⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hs
    exact ⟨⟨a, ha⟩, Subtype.ext rfl⟩
  have hfwd : ∀ s ∈ A.map (rootDiagUnitHom τ L),
      n * s * n⁻¹ ∈ A.map (rootDiagUnitHom τ L) := by
    intro s hs
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hs
    exact hnA a ha
  haveI : Finite (A.map (rootDiagUnitHom τ L)) := hSfin
  have hinj : Function.Injective fun s : A.map (rootDiagUnitHom τ L) =>
      (⟨n * s.1 * n⁻¹, hfwd s.1 s.2⟩ : A.map (rootDiagUnitHom τ L)) := by
    intro s t h
    apply Subtype.ext
    exact mul_left_cancel (mul_right_cancel (congrArg Subtype.val h))
  have hsurj := (Finite.injective_iff_surjective).1 hinj
  intro s hs
  obtain ⟨t, ht⟩ := hsurj ⟨s, hs⟩
  have hst : n * t.1 * n⁻¹ = s := congrArg Subtype.val ht
  have heq : n⁻¹ * s * n = t.1 := by rw [← hst]; group
  rw [heq]
  exact t.2

private lemma ggB2d_familyCentralizer_le_monomialSubgroup {τ : Tag} {L : Type} [Field L]
    (A : Subgroup (Fin τ.rank → Lˣ))
    (hroot : ∀ α : Fin τ.rank → ℤ, IsRoot τ α → ∃ a ∈ A, rootChar a α ≠ 1) :
    CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer τ L
      (fun x : A => (x : Fin τ.rank → Lˣ)) ≤ monomialSubgroup τ L := by
  intro g hg
  obtain ⟨w, _, m, hm, hmul⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer_le_mul τ L
      (fun x : A => (x : Fin τ.rank → Lˣ)) hg
  rw [ggB2d_familyGroup_eq_torusGroup A hroot] at hm
  rw [hmul]
  exact mul_mem (torusGroup_le_monomialSubgroup hm) (canonicalRep_mem_monomialSubgroup L w)

private lemma ggB2d_monomialSubgroup_quotient_finite {τ : Tag} {L : Type} [Field L] :
    Finite (ggB2d_weylQuotient τ L) := by
  let f : WeylGroup τ → ggB2d_weylQuotient τ L := fun w =>
    QuotientGroup.mk (⟨canonicalRep (coxeterSystem τ) L w,
      canonicalRep_mem_monomialSubgroup L w⟩ : monomialSubgroup τ L)
  refine Finite.of_surjective f ?_
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨w, k, hk, hgk⟩ := monomialSubgroup_le_torusWeylCosets g.2
  refine ⟨w, ?_⟩
  have hkM : k ∈ monomialSubgroup τ L := torusGroup_le_monomialSubgroup hk
  have hg_eq : g = (⟨k, hkM⟩ : monomialSubgroup τ L) *
      ⟨canonicalRep (coxeterSystem τ) L w, canonicalRep_mem_monomialSubgroup L w⟩ :=
    Subtype.ext hgk
  rw [hg_eq, QuotientGroup.mk_mul]
  have hk1 : (QuotientGroup.mk (⟨k, hkM⟩ : monomialSubgroup τ L) :
      ggB2d_weylQuotient τ L) = 1 := by
    rw [QuotientGroup.eq_one_iff]
    exact hk
  rw [hk1, one_mul]

private lemma ggB2d_conj_le_torusGroup {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (A : Subgroup (Fin τ.rank → Lˣ)) (hA : Finite A)
    (hroot : ∀ α : Fin τ.rank → ℤ, IsRoot τ α → ∃ a ∈ A, rootChar a α ≠ 1)
    {n : ModGL τ L} (hn : n ∈ adjointGroup τ L)
    (hnA : ∀ a ∈ A, n * rootDiagUnit τ a * n⁻¹ ∈ A.map (rootDiagUnitHom τ L)) :
    ∀ t ∈ torusGroup τ L, n * t * n⁻¹ ∈ torusGroup τ L := by
  classical
  let a : A → Fin τ.rank → Lˣ := fun x => x.1
  have hSle : A.map (rootDiagUnitHom τ L) ≤ torusGroup τ L :=
    ggB2d_rootDiagUnitHom_map_le_torusGroup A
  have hback : ∀ s ∈ A.map (rootDiagUnitHom τ L),
      n⁻¹ * s * n ∈ A.map (rootDiagUnitHom τ L) := ggB2d_conj_inv_mem hA hnA
  have hCmono : CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer τ L a ≤
      monomialSubgroup τ L := ggB2d_familyCentralizer_le_monomialSubgroup A hroot
  have hkey : ∀ t ∈ torusGroup τ L,
      n * t * n⁻¹ ∈ CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer τ L a := by
    intro t ht
    rw [CFSG.HardMathSupport.Timmesfeld.Torality.mem_familyCentralizer]
    refine ⟨mul_mem (mul_mem hn ((torusGroup_le_borelGroup.trans
      borelGroup_le_adjointGroup') ht)) (inv_mem hn), ?_⟩
    intro x
    set d : ModGL τ L := rootDiagUnit τ (a x) with hd
    have hdS : d ∈ A.map (rootDiagUnitHom τ L) := by
      rw [hd]
      exact Subgroup.mem_map.2 ⟨x.1, x.2, rfl⟩
    have heS : n⁻¹ * d * n ∈ A.map (rootDiagUnitHom τ L) := hback d hdS
    have heT : n⁻¹ * d * n ∈ torusGroup τ L := hSle heS
    have hcomm : t * (n⁻¹ * d * n) = (n⁻¹ * d * n) * t := by
      obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
      exact rootDiagUnit_mul_comm_of_mem_torusGroup b heT
    have hdg : d * (n * t * n⁻¹) = (n * t * n⁻¹) * d := by
      calc d * (n * t * n⁻¹) = n * (n⁻¹ * d * n) * t * n⁻¹ := by group
        _ = n * ((n⁻¹ * d * n) * t) * n⁻¹ := by group
        _ = n * (t * (n⁻¹ * d * n)) * n⁻¹ := by rw [hcomm]
        _ = n * t * (n⁻¹ * d * n) * n⁻¹ := by group
        _ = (n * t * n⁻¹) * d := by group
    calc d * (n * t * n⁻¹) * d⁻¹ = (n * t * n⁻¹) * d * d⁻¹ := by rw [hdg]
      _ = n * t * n⁻¹ := by group
  intro t ht
  haveI : Finite (ggB2d_weylQuotient τ L) := ggB2d_monomialSubgroup_quotient_finite
  haveI : Nonempty (ggB2d_weylQuotient τ L) := ⟨1⟩
  obtain ⟨s, hs, hspow⟩ := ggB2d_torusGroup_divisible (N := Nat.card (ggB2d_weylQuotient τ L))
    Nat.card_pos ht
  have hsC : n * s * n⁻¹ ∈
      CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer τ L a := hkey s hs
  have hsM : n * s * n⁻¹ ∈ monomialSubgroup τ L := hCmono hsC
  have hq : ((⟨n * s * n⁻¹, hsM⟩ : monomialSubgroup τ L) :
      ggB2d_weylQuotient τ L) ^ Nat.card (ggB2d_weylQuotient τ L) = 1 := pow_card_eq_one'
  have hqmem : (⟨n * s * n⁻¹, hsM⟩ : monomialSubgroup τ L) ^
      Nat.card (ggB2d_weylQuotient τ L) ∈
      (torusGroup τ L).subgroupOf (monomialSubgroup τ L) :=
    (QuotientGroup.eq_one_iff _).1 hq
  have hpowT : (n * s * n⁻¹) ^ Nat.card (ggB2d_weylQuotient τ L) ∈ torusGroup τ L := by
    have hmem := hqmem
    rw [Subgroup.mem_subgroupOf] at hmem
    simpa using hmem
  have hx : (n * s * n⁻¹) ^ Nat.card (ggB2d_weylQuotient τ L) = n * t * n⁻¹ := by
    rw [conj_pow, hspow]
  rw [hx] at hpowT
  exact hpowT

theorem mem_normalizer_torusGroup_of_normalizes_torsion
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (A : Subgroup (Fin τ.rank → Lˣ)) (hA : Finite A)
    (hroot : ∀ α : Fin τ.rank → ℤ, IsRoot τ α → ∃ a ∈ A, rootChar a α ≠ 1)
    {n : ModGL τ L} (hn : n ∈ adjointGroup τ L)
    (hnA : ∀ a ∈ A, n * rootDiagUnit τ a * n⁻¹ ∈ A.map (rootDiagUnitHom τ L)) :
    n ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) := by
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨?_, ?_⟩
  · exact ggB2d_conj_le_torusGroup A hA hroot hn hnA x
  · intro hx
    have hback := ggB2d_conj_inv_mem hA hnA
    have hnA' : ∀ a ∈ A, n⁻¹ * rootDiagUnit τ a * (n⁻¹)⁻¹ ∈ A.map (rootDiagUnitHom τ L) :=
      fun a ha => by
        simpa using hback (rootDiagUnit τ a) (Subgroup.mem_map_of_mem (rootDiagUnitHom τ L) ha)
    have hx' : n⁻¹ * (n * x * n⁻¹) * n ∈ torusGroup τ L :=
      ggB2d_conj_le_torusGroup A hA hroot (inv_mem hn) hnA' (n * x * n⁻¹) hx
    have hxx : n⁻¹ * (n * x * n⁻¹) * n = x := by group
    rwa [hxx] at hx'

end NormalizerTorsion

section TorsionCoordinates

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.ExcMaxToral Polynomial
open scoped Matrix

private lemma ggB2e_cast_exponent {τ : Tag} (α : Fin τ.rank → ℤ) (z : Fin τ.rank → ZMod 5) :
    ((∑ i, ((z i).val : ℤ) * α i : ℤ) : ZMod 5) = ∑ i, (α i : ZMod 5) * z i := by
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ZMod.natCast_zmod_val]
  ring

theorem exists_tuple_torsion_rootChar_ne_one
    {K : Type} [Field K] [Finite K] [CharP K 2] {τ : Tag}
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (α : Fin τ.rank → ℤ) (z : Fin τ.rank → ZMod 5)
    (hz : (modMat 5 M).transpose *ᵥ z = (Nat.card K : ZMod 5) • z)
    (hα : ∑ i, (α i : ZMod 5) * z i ≠ 0) :
    ∃ a ∈ fixedCharTuples M Fr, (∀ i, a i ^ 5 = 1) ∧ rootChar a α ≠ 1 := by
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_units (L := AlgebraicClosure K) (ℓ := 2)
    Nat.prime_two (p := 5) (by norm_num) (by norm_num)
  have ha : expTuple ζ z ∈ fixedCharTuples M Fr :=
    (expTuple_mem_fixedCharTuples_iff (q := Nat.card K) hζ M Fr hFr z).2 hz
  refine ⟨expTuple ζ z, ha, ?_⟩
  refine ⟨?_, ?_⟩
  · intro i
    show (ζ ^ (z i).val) ^ 5 = 1
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · intro h1
    have hdvd : (5 : ℤ) ∣ ∑ i, ((z i).val : ℤ) * α i := by
      rw [rootChar_expTuple z α] at h1
      exact (hζ.zpow_eq_one_iff_dvd _).1 h1
    have hzero : ((∑ i, ((z i).val : ℤ) * α i : ℤ) : ZMod 5) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).2 hdvd
    rw [ggB2e_cast_exponent α z] at hzero
    exact hα hzero

end TorsionCoordinates

section ContradictionStep

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.ExcMaxToral Polynomial
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
open scoped Matrix

private theorem ggB2g_entrywiseHom_baseChangeGL_fixed
    {K L : Type} [Field K] [Finite K]
    [Field L] (ι : K →+* L) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) {τ : Tag}
    (y : ModGL τ K) :
    Units.map (entrywiseHom Fr) (baseChangeGL ι y) = baseChangeGL ι y := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hpow : ∀ c : K, c ^ Nat.card K = c := fun c => by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have hcomp : Fr.comp ι = ι := by
    ext c
    rw [RingHom.comp_apply, hFr, ← map_pow, hpow]
  rw [units_map_entrywiseHom_eq_baseChangeGL Fr (baseChangeGL ι y),
    baseChangeGL_baseChangeGL ι Fr y, hcomp]

private theorem ggB2g_Phi_rho
    {K : Type} [Field K] [Finite K]
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (D : LangDatum .E8 (AlgebraicClosure K)) (hΦ : D.Φ = Units.map (entrywiseHom Fr))
    (x : ModGL .E8 K) :
    Units.map (entrywiseHom Fr)
        (D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * D.g0) =
      D.n⁻¹ * (D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * D.g0) * D.n := by
  have key : D.Φ (D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * D.g0) =
      D.n⁻¹ * (D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * D.g0) * D.n := by
    have hbc : D.Φ (baseChangeGL (algebraMap K (AlgebraicClosure K)) x) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) x := by
      rw [hΦ]
      exact ggB2g_entrywiseHom_baseChangeGL_fixed (algebraMap K (AlgebraicClosure K)) Fr hFr x
    rw [map_mul, map_mul, map_inv, D.lang, hbc]
    group
  simpa only [hΦ] using key

theorem excFiveFour_le_of_toral_normal_subgroup
    {K : Type} [Field K] [Finite K] [CharP K 2] (hq : orderOf (Nat.card K : ZMod 5) = 4)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (D : LangDatum .E8 (AlgebraicClosure K)) (hΦ : D.Φ = Units.map (entrywiseHom Fr))
    (w : WeylGroup .E8) (hn : D.n = canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) w)
    (hshape : ExcLangShape .E8 4 w)
    (hN8 : ∀ l : ZMod 5, l ^ 2 = -1 → ∀ α : Fin Tag.E8.rank → ℤ, IsRoot .E8 α →
      ∃ z : Fin Tag.E8.rank → ZMod 5,
        (modMat 5 (weylMatrix w)).transpose *ᵥ z = l • z ∧ ∑ i, (α i : ZMod 5) * z i ≠ 0)
    (P Q E : Subgroup (adjointGroup .E8 K)) (hQP : Q ≤ P) (hEP : E ≤ P)
    (hQn : ∀ y ∈ P, ∀ x ∈ Q, y * x * y⁻¹ ∈ Q) (hPQ : Nat.card P ≤ 5 * Nat.card Q)
    (hE : IsElemAbelian 5 E) (hEcard : 5 ^ 4 ≤ Nat.card E)
    (hQtor : ∀ x ∈ Q, D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) *
      D.g0 ∈ D.torus)
    (hT5 : ∀ t ∈ D.torus, t ^ 5 = 1 → ∃ x ∈ Q,
      D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) * D.g0 = t) :
    E ≤ Q := by
  classical
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  let rho : adjointGroup .E8 K →* ModGL .E8 (AlgebraicClosure K) :=
    (MulAut.conj D.g0⁻¹).toMonoidHom.comp
      ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup .E8 K).subtype)
  have hrho_apply : ∀ x : adjointGroup .E8 K,
      rho x = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) *
        D.g0 := by
    intro x
    simp [rho, MulAut.conj_apply]
  have hrho_mem : ∀ x : adjointGroup .E8 K, rho x ∈ adjointGroup .E8 (AlgebraicClosure K) := by
    intro x
    rw [hrho_apply]
    exact mul_mem (mul_mem (inv_mem D.g0_mem)
      (baseChangeGL_mem_adjointGroup (algebraMap K (AlgebraicClosure K)) x.2)) D.g0_mem
  have hrho_inj : Function.Injective rho := by
    intro x y hxy
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
    have h := congrArg (fun z => D.g0 * z * D.g0⁻¹) hxy
    simpa [hrho_apply] using h
  let B : Subgroup (Fin (Tag.E8).rank → (AlgebraicClosure K)ˣ) :=
    { carrier := {a | ∀ i, a i ^ 5 = 1}
      mul_mem' := fun {a b} ha hb i => by
        rw [Pi.mul_apply, mul_pow, ha i, hb i, one_mul]
      one_mem' := fun i => by simp
      inv_mem' := fun {a} ha i => by
        rw [Pi.inv_apply, inv_pow, ha i, inv_one] }
  let A : Subgroup (Fin (Tag.E8).rank → (AlgebraicClosure K)ˣ) :=
    fixedCharTuples (weylMatrix w) Fr ⊓ B
  have hqr : (Nat.card K : ZMod 5) ^ 2 = -1 := by
    have h4 : (Nat.card K : ZMod 5) ^ 4 = 1 := by
      rw [← hq]; exact pow_orderOf_eq_one _
    have h2 : (Nat.card K : ZMod 5) ^ 2 ≠ 1 := by
      intro h
      have hdvd : orderOf (Nat.card K : ZMod 5) ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]; exact h
      rw [hq] at hdvd
      omega
    have hprod : ((Nat.card K : ZMod 5) ^ 2 - 1) * ((Nat.card K : ZMod 5) ^ 2 + 1) = 0 := by
      have h : ((Nat.card K : ZMod 5) ^ 2 - 1) * ((Nat.card K : ZMod 5) ^ 2 + 1) =
          (Nat.card K : ZMod 5) ^ 4 - 1 := by ring
      rw [h, h4, sub_self]
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd (sub_eq_zero.mp h) h2
    · exact eq_neg_of_add_eq_zero_left h
  have hroot : ∀ α : Fin (Tag.E8).rank → ℤ, IsRoot .E8 α → ∃ a ∈ A, rootChar a α ≠ 1 := by
    intro α hα
    obtain ⟨z, hz, hpair⟩ := hN8 (Nat.card K : ZMod 5) hqr α hα
    obtain ⟨a, ha, ha5, hchar⟩ :=
      exists_tuple_torsion_rootChar_ne_one Fr hFr (weylMatrix w) α z hz hpair
    exact ⟨a, Subgroup.mem_inf.mpr ⟨ha, fun i => ha5 i⟩, hchar⟩
  have hD : D.torus =
      (fixedCharTuples (weylMatrix w) Fr).map (rootDiagUnitHom .E8 (AlgebraicClosure K)) := by
    have hM : ∀ u, w • u = (weylMatrix w) *ᵥ u := fun u => (weylMatrix_mulVec w u).symm
    show twistedTorusOf D.n D.Φ = _
    rw [hΦ, hn]
    ext x
    constructor
    · intro hx
      obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorus.1 hx).1
      refine ⟨a, ?_, rfl⟩
      rw [← twistedFixedTuples_eq_fixedCharTuples hM Fr]
      exact mem_twistedFixedTuples_iff_conj.2 (mem_twistedTorus.1 hx).2
    · rintro ⟨a, ha, rfl⟩
      rw [← twistedFixedTuples_eq_fixedCharTuples hM Fr] at ha
      exact mem_twistedTorus.2 ⟨rootDiagUnit_mem_torusGroup a,
        mem_twistedFixedTuples_iff_conj.1 ha⟩
  have hAfin : Finite A := by
    have hfin : Finite {a : fixedCharTuples (weylMatrix w) Fr //
        ∀ i, (a : Fin (Tag.E8).rank → (AlgebraicClosure K)ˣ) i ^ 5 = 1} := by
      refine Nat.finite_of_card_ne_zero ?_
      rw [natCard_fixedTorsion (weylMatrix w) Fr Nat.prime_two hFr (p := 5)
        (by norm_num) (by norm_num : 5 ≠ 2)]
      exact Nat.card_ne_zero.mpr ⟨⟨0, by simp⟩, inferInstance⟩
    exact hfin.of_injective (fun x : A => (⟨⟨x.1, x.2.1⟩, x.2.2⟩ :
      {a : fixedCharTuples (weylMatrix w) Fr //
        ∀ i, (a : Fin (Tag.E8).rank → (AlgebraicClosure K)ˣ) i ^ 5 = 1}))
      (fun x _ h => Subtype.ext
        (congrArg (fun z => (z.1.1 : Fin (Tag.E8).rank → (AlgebraicClosure K)ˣ)) h))
  by_contra hnot
  have hnot' : ¬ (E : Set (adjointGroup .E8 K)) ⊆ (Q : Set (adjointGroup .E8 K)) := hnot
  obtain ⟨y, hyE, hyQ⟩ := Set.not_subset.mp hnot'
  have hyP : y ∈ P := hEP hyE
  have hy5 : y ^ 5 = 1 := hE.2 y hyE
  have hnA : ∀ a ∈ A, rho y * rootDiagUnit .E8 a * (rho y)⁻¹ ∈
      A.map (rootDiagUnitHom .E8 (AlgebraicClosure K)) := by
    intro a ha
    have hda_tor : rootDiagUnit .E8 a ∈ D.torus := by
      rw [hD]; exact Subgroup.mem_map.mpr ⟨a, ha.1, rfl⟩
    have hda5 : (rootDiagUnit .E8 a) ^ 5 = 1 := by
      have h := (rootDiagUnitHom .E8 (AlgebraicClosure K)).map_pow a 5
      rw [show a ^ 5 = 1 from funext (fun i => ha.2 i), map_one] at h
      exact h.symm
    obtain ⟨x, hxQ, hxeq⟩ := hT5 (rootDiagUnit .E8 a) hda_tor hda5
    let z : adjointGroup .E8 K := y * x * y⁻¹
    have hzQ : z ∈ Q := hQn y hyP x hxQ
    have hx5 : x ^ 5 = 1 := by
      apply hrho_inj
      rw [map_pow, map_one, hrho_apply x, hxeq, hda5]
    have hz5 : z ^ 5 = 1 := by
      have h : z = (MulAut.conj y) x := rfl
      rw [h, ← map_pow, hx5, map_one]
    have hconj5 : (rho z) ^ 5 = 1 := by
      rw [← map_pow, hz5, map_one]
    have hconj_tor : rho z ∈ D.torus := by
      rw [hrho_apply z]; exact hQtor z hzQ
    rw [hD] at hconj_tor
    obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.mp hconj_tor
    have hb5_eq : b ^ 5 = 1 := by
      have h := (rootDiagUnitHom .E8 (AlgebraicClosure K)).map_pow b 5
      rw [hbeq, hconj5] at h
      exact rootDiagUnit_injective
        (h.trans (map_one (rootDiagUnitHom .E8 (AlgebraicClosure K))).symm)
    have hb5 : ∀ i, b i ^ 5 = 1 := fun i => congrFun hb5_eq i
    have hconj : rho z = rho y * rootDiagUnit .E8 a * (rho y)⁻¹ := by
      have h1 : rho z = rho y * rho x * (rho y)⁻¹ := by
        show rho (y * x * y⁻¹) = _
        rw [map_mul, map_mul, map_inv]
      rw [h1, hrho_apply x, hxeq]
    rw [← hconj]
    exact Subgroup.mem_map.mpr ⟨b, Subgroup.mem_inf.mpr ⟨hb, hb5⟩, hbeq⟩
  have hN : rho y ∈ Subgroup.normalizer
      (torusGroup .E8 (AlgebraicClosure K) : Set (ModGL .E8 (AlgebraicClosure K))) :=
    mem_normalizer_torusGroup_of_normalizes_torsion (τ := .E8) (L := AlgebraicClosure K)
      A hAfin hroot (hrho_mem y) hnA
  obtain ⟨v, hv⟩ :=
    CFSG.RankThree.PartOne.K133H.exists_conj_eq_canonicalRep_of_mem_normalizer
      (V := (torusGroup .E8 (AlgebraicClosure K) : Set (ModGL .E8 (AlgebraicClosure K))))
      (fun _ hx => hx) (Subgroup.mem_inf.mpr ⟨hrho_mem y, hN⟩)
  have hfamK : CFSG.RankThree.PartOne.KE8F.famKernel
      (Set.univ : Set (Fin (Tag.E8).rank → (AlgebraicClosure K)ˣ)) = ∅ := by
    ext α
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hαroot, hαall⟩
    have hne : α ≠ 0 := hαroot.ne_zero
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    obtain ⟨p, hpge, hpprime⟩ :=
      Nat.exists_infinite_primes (max (α i).natAbs 2 + 1)
    have hp2 : p ≠ 2 := by
      intro hp
      have h2 := le_max_right (α i).natAbs 2
      rw [hp] at hpge
      omega
    obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_units (L := AlgebraicClosure K)
      Nat.prime_two hpprime hp2
    have h1 : ζ ^ (α i) = 1 := by
      rw [← CFSG.StandardType.ExcSplitL.rootChar_mulSingle i ζ α]
      exact hαall (Pi.mulSingle i ζ) (Set.mem_univ _)
    have hdvd : (p : ℤ) ∣ α i := (hζ.zpow_eq_one_iff_dvd (α i)).mp h1
    have hdvd' : p ∣ (α i).natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hdvd
      simpa using this
    have hpos : 0 < (α i).natAbs := Int.natAbs_pos.mpr hi
    have habs : (α i).natAbs < p := by
      have h2 := le_max_left (α i).natAbs 2
      omega
    have := Nat.le_of_dvd hpos hdvd'
    omega
  have hmono : rho y ∈ monomialSubgroup .E8 (AlgebraicClosure K) := by
    set nv := canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) v with hnv
    have hg'mem : nv⁻¹ * rho y ∈ adjointGroup .E8 (AlgebraicClosure K) :=
      mul_mem (inv_mem (canonicalRep_mem_adjointGroup (coxeterSystem .E8) (AlgebraicClosure K) v))
        (hrho_mem y)
    have hcomm : ∀ a ∈ (Set.univ : Set (Fin (Tag.E8).rank → (AlgebraicClosure K)ˣ)),
        rootDiagUnit .E8 a * (nv⁻¹ * rho y) * (rootDiagUnit .E8 a)⁻¹ = nv⁻¹ * rho y := by
      intro a _
      have h1 : rho y * rootDiagUnit .E8 a * (rho y)⁻¹ =
          nv * rootDiagUnit .E8 a * nv⁻¹ :=
        hv (rootDiagUnit .E8 a) (rootDiagUnit_mem_torusGroup a)
      have h2 : (nv⁻¹ * rho y) * rootDiagUnit .E8 a * (nv⁻¹ * rho y)⁻¹ =
          rootDiagUnit .E8 a := by
        rw [show (nv⁻¹ * rho y) * rootDiagUnit .E8 a * (nv⁻¹ * rho y)⁻¹ =
            nv⁻¹ * (rho y * rootDiagUnit .E8 a * (rho y)⁻¹) * nv from by group]
        rw [h1]; group
      have hcd : rootDiagUnit .E8 a * (nv⁻¹ * rho y) =
          (nv⁻¹ * rho y) * rootDiagUnit .E8 a :=
        ((mul_inv_eq_iff_eq_mul).mp h2).symm
      rw [hcd, mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨w'', -, h, hh, u, hu, vv, hvv, hg'eq⟩ :=
      CFSG.RankThree.PartOne.KE8F.fam_factor
        (Set.univ : Set (Fin (Tag.E8).rank → (AlgebraicClosure K)ˣ)) hg'mem hcomm
    have hu1 : u = 1 := by
      have hu' : u ∈ rootSpan .E8 (AlgebraicClosure K) (∅ : Set (Fin (Tag.E8).rank → ℤ)) := by
        rwa [hfamK, Set.empty_inter] at hu
      have : u ∈ (⊥ : Subgroup (ModGL .E8 (AlgebraicClosure K))) := by
        simpa [rootSpan] using hu'
      exact Subgroup.mem_bot.mp this
    have hv1 : vv = 1 := by
      have hv' : vv ∈ rootSpan .E8 (AlgebraicClosure K) (∅ : Set (Fin (Tag.E8).rank → ℤ)) := by
        rwa [hfamK, Set.empty_inter] at hvv
      have : vv ∈ (⊥ : Subgroup (ModGL .E8 (AlgebraicClosure K))) := by
        simpa [rootSpan] using hv'
      exact Subgroup.mem_bot.mp this
    have hg'eq' : nv⁻¹ * rho y = h * canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) w'' := by
      rw [hg'eq, hu1, hv1]; group
    have hdecomp : rho y = nv * h * canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) w'' := by
      have h := congrArg (fun z => nv * z) hg'eq'
      simpa [mul_assoc] using h
    rw [hdecomp]
    exact mul_mem (mul_mem (canonicalRep_mem_monomialSubgroup (AlgebraicClosure K) v)
      (torusGroup_le_monomialSubgroup hh))
      (canonicalRep_mem_monomialSubgroup (AlgebraicClosure K) w'')
  have hxN : rho y ∈ NFix (canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) w) Fr := by
    refine mem_NFix.mpr ⟨hmono, ?_⟩
    have hfix : Units.map (entrywiseHom Fr) (rho y) = D.n⁻¹ * rho y * D.n := by
      have h := ggB2g_Phi_rho Fr hFr D hΦ (y : ModGL .E8 K)
      rw [← hrho_apply y] at h
      exact h
    rw [negPhi_apply, ← hn, hfix]
    group
  let v₂ : WeylGroup .E8 :=
    NFixToWeyl (canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) w) Fr ⟨rho y, hxN⟩
  have hv₂comm : v₂ * w = w * v₂ := by
    have h := NFixToWeyl_mem_centralizer Fr w ⟨rho y, hxN⟩
    exact (Subgroup.mem_centralizer_iff.mp h w (Set.mem_singleton w)).symm
  have htoreq : twistedTorusOf (canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) w)
      (Units.map (entrywiseHom Fr)) = D.torus := by
    rw [← hn, ← hΦ]; rfl
  have hv₂ker : v₂ = 1 ↔ rho y ∈ D.torus := by
    show NFixToWeyl (canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) w) Fr
      ⟨rho y, hxN⟩ = 1 ↔ rho y ∈ D.torus
    rw [← MonoidHom.mem_ker, NFixToWeyl_ker, Subgroup.mem_subgroupOf, htoreq]
  have hv₂ne : v₂ ≠ 1 := by
    intro h1
    have hmem : rho y ∈ D.torus := hv₂ker.mp h1
    have h5 : (rho y) ^ 5 = 1 := by rw [← map_pow, hy5, map_one]
    obtain ⟨x', hx'Q, hx'eq⟩ := hT5 (rho y) hmem h5
    have hrhoeq : rho x' = rho y := by rw [hrho_apply x', hx'eq]
    exact hyQ (hrho_inj hrhoeq ▸ hx'Q)
  have hv₂pow : v₂ ^ 5 = 1 := by
    have hx5 : (⟨rho y, hxN⟩ : NFix (canonicalRep (coxeterSystem .E8)
        (AlgebraicClosure K) w) Fr) ^ 5 = 1 := by
      apply Subtype.ext
      show (rho y) ^ 5 = 1
      rw [← map_pow, hy5, map_one]
    dsimp only [v₂]
    rw [← map_pow, hx5, map_one]
  have hv₂ord : orderOf v₂ = 5 := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact orderOf_eq_prime hv₂pow hv₂ne
  have hv₂action : ∀ z ∈ torusGroup .E8 (AlgebraicClosure K),
      rho y * z * (rho y)⁻¹ =
        canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) v₂ * z *
          (canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) v₂)⁻¹ := by
    intro z hz
    obtain ⟨u, k, hk, hxk⟩ := monomialSubgroup_le_torusWeylCosets hmono
    have hmaps : MapsRootLines (rho y) u := by
      rw [hxk]
      simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep u)
    have hv₂eq : v₂ = u := NFixToWeyl_eq hmaps
    rw [hv₂eq, hxk]
    have hz' : canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) u * z *
        (canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) u)⁻¹ ∈
        torusGroup .E8 (AlgebraicClosure K) :=
      (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer u) z).1 hz
    calc (k * canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) u) * z *
          (k * canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) u)⁻¹
        = k * (canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) u * z *
            (canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) u)⁻¹) * k⁻¹ := by group
      _ = canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) u * z *
            (canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) u)⁻¹ := by
          rw [torusGroup_mul_comm hk hz']; group
  have hcard_inf : 5 ^ 3 ≤ Nat.card ↥(E ⊓ Q) := by
    have hEPcard : Nat.card E ≤ Nat.card P :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hEP)
        (fun a b h => Subtype.ext (congrArg (fun x : P => (x : adjointGroup .E8 K)) h))
    have hQpos : 0 < Nat.card Q := by
      have h : 5 ^ 4 ≤ 5 * Nat.card Q := le_trans hEcard (le_trans hEPcard hPQ)
      have h53 : 5 ^ 3 ≤ Nat.card Q := by
        have h' : 5 * 5 ^ 3 ≤ 5 * Nat.card Q := by
          simpa [show 5 ^ 4 = 5 * 5 ^ 3 by norm_num] using h
        exact Nat.le_of_mul_le_mul_left h' (by norm_num)
      omega
    have hPpos : 0 < Nat.card P :=
      lt_of_lt_of_le (by norm_num : 0 < 5 ^ 4) (le_trans hEcard hEPcard)
    have hPne : Q.relIndex P ≠ 0 := by
      have h2 := Subgroup.relIndex_mul_card (H := Q) (K := P)
      rw [inf_eq_left.mpr hQP] at h2
      intro h0
      rw [h0, zero_mul] at h2
      omega
    have hrel : (E ⊓ Q).relIndex E ≤ 5 := by
      rw [Subgroup.inf_relIndex_left]
      refine le_trans (Subgroup.relIndex_le_of_le_right hEP hPne) ?_
      have h2 := Subgroup.relIndex_mul_card (H := Q) (K := P)
      rw [inf_eq_left.mpr hQP] at h2
      exact Nat.le_of_mul_le_mul_right (h2 ▸ hPQ) hQpos
    have h1 : (E ⊓ Q).relIndex E * Nat.card ↥(E ⊓ Q) = Nat.card E := by
      have := Subgroup.relIndex_mul_card (H := E ⊓ Q) (K := E)
      simpa [inf_assoc, inf_left_comm, inf_comm, inf_idem] using this
    have h2 : 5 ^ 4 ≤ (E ⊓ Q).relIndex E * Nat.card ↥(E ⊓ Q) := by
      rw [h1]; exact hEcard
    have h3 : 5 ^ 4 ≤ 5 * Nat.card ↥(E ⊓ Q) :=
      le_trans h2 (Nat.mul_le_mul_right _ hrel)
    have h4 : 5 * 5 ^ 3 ≤ 5 * Nat.card ↥(E ⊓ Q) := by
      simpa [show 5 ^ 4 = 5 * 5 ^ 3 by norm_num] using h3
    exact Nat.le_of_mul_le_mul_left h4 (by norm_num)
  have hle : Nat.card ↥(E ⊓ Q) ≤ 5 ^ 2 := by
    obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_units (L := AlgebraicClosure K)
      Nat.prime_two (by norm_num) (by norm_num : 5 ≠ 2)
    have hZle : Nat.card {z : Fin (Tag.E8).rank → ZMod 5 //
        (modMat 5 (weylMatrix w)).transpose *ᵥ z = (Nat.card K : ZMod 5) • z ∧
          (modMat 5 (weylMatrix v₂)).transpose *ᵥ z = z} ≤ 5 ^ 2 :=
      card_fixed_eigenspace_le_of_commute_order_five hshape hv₂comm hv₂ord hqr
    have hex : ∀ x : ↥(E ⊓ Q), ∃ z : Fin (Tag.E8).rank → ZMod 5,
        (modMat 5 (weylMatrix w)).transpose *ᵥ z = (Nat.card K : ZMod 5) • z ∧
        (modMat 5 (weylMatrix v₂)).transpose *ᵥ z = z ∧
        rootDiagUnit .E8 (expTuple ζ z) = rho x.1 := by
      intro x
      have hxT : rho x.1 ∈ D.torus := hQtor x.1 x.2.2
      have hx5 : (rho x.1) ^ 5 = 1 := by rw [← map_pow, hE.2 x.1 x.2.1, map_one]
      obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp (hD ▸ hxT)
      have haeq' : rootDiagUnit .E8 a = rho x.1 := haeq
      have ha5 : ∀ i, a i ^ 5 = 1 := by
        have ha5eq : a ^ 5 = 1 := by
          have h := (rootDiagUnitHom .E8 (AlgebraicClosure K)).map_pow a 5
          rw [haeq, hx5] at h
          exact rootDiagUnit_injective
            (h.trans (map_one (rootDiagUnitHom .E8 (AlgebraicClosure K))).symm)
        intro i; exact congrFun ha5eq i
      have hζL : IsPrimitiveRoot (ζ : AlgebraicClosure K) 5 :=
        IsPrimitiveRoot.coe_units_iff.mpr hζ
      choose k hk hk' using fun i => hζL.eq_pow_of_pow_eq_one (by
        have := congrArg (fun x : (AlgebraicClosure K)ˣ => (x : AlgebraicClosure K)) (ha5 i)
        simpa using this)
      let z : Fin (Tag.E8).rank → ZMod 5 := fun i => (k i : ZMod 5)
      have hz : expTuple ζ z = a := funext fun i => by
        apply Units.ext
        show ((ζ : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) ^ ((k i : ZMod 5)).val =
          (a i : AlgebraicClosure K)
        rw [ZMod.val_natCast_of_lt (hk i)]
        exact hk' i
      refine ⟨z, ?_, ?_, ?_⟩
      · exact (expTuple_mem_fixedCharTuples_iff (p := 5) hζ (weylMatrix w) Fr hFr z).mp
          (by rw [hz]; exact ha)
      · have hcommE : y * x.1 = x.1 * y := by
          haveI : IsMulCommutative ↥E := hE.1
          letI : CommMagma ↥E := IsMulCommutative.instCommMagma
          exact congrArg (fun w : ↥E => (w : adjointGroup .E8 K))
            (mul_comm (⟨y, hyE⟩ : ↥E) (⟨x.1, x.2.1⟩ : ↥E))
        have hcommxy : rho y * rho x.1 * (rho y)⁻¹ = rho x.1 := by
          have h : rho y * rho x.1 = rho x.1 * rho y := by
            rw [← map_mul, ← map_mul, hcommE]
          rw [h]; group
        have haction := hv₂action (rho x.1)
          (by rw [← haeq']; exact rootDiagUnit_mem_torusGroup a)
        have hwt : weylTuple v₂ a = a := by
          apply rootDiagUnit_injective (τ := .E8) (K := AlgebraicClosure K)
          rw [← canonicalRep_conj_rootDiagUnit v₂ a, haeq', ← haction, hcommxy]
        have hfixT : a ∈ fixedCharTuples (weylMatrix v₂) (RingHom.id (AlgebraicClosure K)) := by
          rw [mem_fixedCharTuples_iff]
          intro u
          show rootChar a ((weylMatrix v₂) *ᵥ u) =
            Units.map (RingHom.id (AlgebraicClosure K)).toMonoidHom (rootChar a u)
          rw [weylMatrix_mulVec]
          have h := rootChar_weylTuple v₂ a (v₂ • u)
          rw [hwt] at h
          rw [inv_smul_smul] at h
          simpa using h
        have hzfix := (expTuple_mem_fixedCharTuples_iff (p := 5) hζ (weylMatrix v₂)
          (RingHom.id (AlgebraicClosure K)) (q := 1) (fun c => by simp) z).mp
          (by rw [hz]; exact hfixT)
        simpa using hzfix
      · rw [hz, haeq']
    let f : ↥(E ⊓ Q) → {z : Fin (Tag.E8).rank → ZMod 5 //
        (modMat 5 (weylMatrix w)).transpose *ᵥ z = (Nat.card K : ZMod 5) • z ∧
          (modMat 5 (weylMatrix v₂)).transpose *ᵥ z = z} := fun x =>
      ⟨Classical.choose (hex x), (Classical.choose_spec (hex x)).1,
        (Classical.choose_spec (hex x)).2.1⟩
    have hf_inj : Function.Injective f := by
      intro x x' h
      have hz : (Classical.choose (hex x)) = Classical.choose (hex x') :=
        congrArg Subtype.val h
      have hx1 := (Classical.choose_spec (hex x)).2.2
      have hx2 := (Classical.choose_spec (hex x')).2.2
      apply Subtype.ext
      apply hrho_inj
      rw [← hx1, ← hx2, hz]
    exact le_trans (Nat.card_le_card_of_injective f hf_inj) hZle
  omega

end ContradictionStep

section Assembly

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.ExcMaxToral Polynomial
open scoped Matrix

private theorem ggB2f_weylMatrix_eq_of_mulVec {τ : Tag} {w : WeylGroup τ}
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hM : ∀ u, w • u = M *ᵥ u) :
    M = weylMatrix w := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [← hM (Pi.single j 1), weylMatrix_mulVec]

private theorem ggB2f_entrywiseHom_baseChangeGL_fixed
    {K L : Type} [Field K] [Finite K] [Field L] (ι : K →+* L) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {τ : Tag} (y : ModGL τ K) :
    Units.map (entrywiseHom Fr) (baseChangeGL ι y) = baseChangeGL ι y := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hpow : ∀ c : K, c ^ Nat.card K = c := fun c => by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have hcomp : Fr.comp ι = ι := by
    ext c
    rw [RingHom.comp_apply, hFr, ← map_pow, hpow]
  rw [units_map_entrywiseHom_eq_baseChangeGL Fr (baseChangeGL ι y),
    baseChangeGL_baseChangeGL ι Fr y, hcomp]

theorem excFiveFourToral
    (K : Type) [Field K] : ExcFiveFourToral K := by
  intro hfin hchar hq E hE hEcard
  classical
  haveI : Finite K := hfin
  haveI : CharP K 2 := hchar
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨w, hshape, hN8⟩ := exists_regular_weyl_E8_four_pairing_ne_zero
  obtain ⟨hw4, M₀, hM₀, hchar₀⟩ := hshape.2.2 ⟨rfl, Or.inr (Or.inl rfl)⟩
  have hMweyl : M₀ = weylMatrix w := ggB2f_weylMatrix_eq_of_mulVec hM₀
  have hchar : (weylMatrix w).charpoly = (cyclotomic 4 ℤ) ^ 4 := by
    rw [← hMweyl]; exact hchar₀
  have hM : ∀ u : Fin Tag.E8.rank → ℤ, w • u = weylMatrix w *ᵥ u :=
    fun u => (weylMatrix_mulVec w u).symm
  have hn0 : (4 : ℕ) ≠ 0 := by norm_num
  have hw4' : w ^ 4 = 1 := by rw [← hw4]; exact pow_orderOf_eq_one w
  have hpow : (weylMatrix w) ^ 4 = 1 := by rw [← weylMatrix_pow, hw4', weylMatrix_one]
  have hqK : Nat.card K ≠ 1 := (Finite.one_lt_card (α := K)).ne'
  have hev : (weylMatrix w).charpoly.eval (Nat.card K : ℤ) ≠ 0 := by
    rw [hchar, eval_pow]
    refine pow_ne_zero 4 fun h => ?_
    have hlt := Polynomial.sub_one_lt_natAbs_cyclotomic_eval (n := 4) (q := Nat.card K)
      (by norm_num) hqK
    rw [h, Int.natAbs_zero] at hlt
    omega
  have hord : (Nat.card (adjointGroup .E8 K)).factorization 5 ≤
      (((weylMatrix w).charpoly.eval (Nat.card K : ℤ)).natAbs).factorization 5 + 1 := by
    rw [hchar]
    exact le_of_eq (factorization_card_adjointGroup_E8_five_four (K := K) hq)
  obtain ⟨Fr, hFr, g0, hg0C, hg0lang, hconj⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_langFrame_untwisted 1
      (Or.inr (Or.inr ⟨rfl, rfl⟩)) K Nat.prime_five (by norm_num) w hM hn0 hpow hev hord
  haveI : Finite (ModGL .E8 K) := finite_modGL
  haveI : Finite (adjointGroup .E8 K) := inferInstance
  have hE5 : IsPGroup 5 ↥E := fun g => ⟨1, by
    apply Subtype.ext
    have h := hE.2 (g : adjointGroup .E8 K) g.2
    simpa using h⟩
  obtain ⟨P, hEP⟩ := IsPGroup.exists_le_sylow (p := 5) hE5
  have hPexp : Nat.card (P : Subgroup (adjointGroup .E8 K)) =
      5 ^ (Nat.card (adjointGroup .E8 K)).factorization 5 := by
    have h := Sylow.card_eq_multiplicity P
    simpa using h
  obtain ⟨c, Q, hQP, hPle, hQconj⟩ :=
    hconj (P : Subgroup (adjointGroup .E8 K)) P.isPGroup'
  let bc : adjointGroup .E8 K →* ModGL .E8 (AlgebraicClosure K) :=
    (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup .E8 K).subtype
  have hbcC : bc c ∈ adjointGroup .E8 (AlgebraicClosure K) :=
    baseChangeGL_mem_adjointGroup (f := algebraMap K (AlgebraicClosure K)) c.2
  have hfix : Units.map (entrywiseHom Fr) (bc c) = bc c :=
    ggB2f_entrywiseHom_baseChangeGL_fixed (algebraMap K (AlgebraicClosure K)) Fr hFr
      (c : ModGL .E8 K)
  let D : LangDatum .E8 (AlgebraicClosure K) :=
    { Φ := Units.map (entrywiseHom Fr)
      q := Nat.card K
      n := canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) w
      g0 := (bc c)⁻¹ * g0
      steinberg := ⟨Fr, hFr, 1, Or.inl rfl, fun g => by simp⟩
      n_weyl := ⟨w, rfl⟩
      g0_mem := mul_mem (inv_mem hbcC) hg0C
      lang := by rw [map_mul, map_inv, hfix, hg0lang]; group }
  have hQtor : ∀ x ∈ Q, D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL .E8 K) * D.g0 ∈ D.torus := by
    intro x hx
    obtain ⟨y, hyT, hyeq⟩ := Subgroup.mem_map.1 (hQconj x hx)
    have hgoal : D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL .E8 K) * D.g0 = y := by
      change ((bc c)⁻¹ * g0)⁻¹ * bc x * ((bc c)⁻¹ * g0) = y
      calc ((bc c)⁻¹ * g0)⁻¹ * bc x * ((bc c)⁻¹ * g0)
          = g0⁻¹ * (bc c * bc x * (bc c)⁻¹) * g0 := by group
        _ = g0⁻¹ * bc (c * x * c⁻¹ : adjointGroup .E8 K) * g0 := by
              congr 1
              rw [map_mul, map_mul, map_inv]
        _ = y := by
              change g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                ((c * x * c⁻¹ : adjointGroup .E8 K) : ModGL .E8 K) * g0 = y
              rw [← hyeq]
              change g0⁻¹ * (g0 * y * g0⁻¹) * g0 = y
              group
    rw [hgoal]; exact hyT
  have hQn : ∀ y ∈ (P : Subgroup (adjointGroup .E8 K)), ∀ x ∈ Q, y * x * y⁻¹ ∈ Q := by
    let P₀ : Subgroup (adjointGroup .E8 K) := (P : Subgroup (adjointGroup .E8 K))
    let Qp : Subgroup ↥P₀ := Q.subgroupOf P₀
    have hQpcard : Nat.card ↥Qp = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    have hidx_le : Qp.index ≤ 5 := by
      have h1 : Nat.card Q * Qp.index = Nat.card ↥P₀ := by
        rw [← hQpcard]; exact Subgroup.card_mul_index Qp
      have h2 : Nat.card Q * Qp.index ≤ Nat.card Q * 5 := by
        rw [h1, mul_comm (Nat.card Q) 5]
        exact hPle
      exact Nat.le_of_mul_le_mul_left h2 hQpos
    have hidx_dvd : Qp.index ∣ 5 ^ (Nat.card (adjointGroup .E8 K)).factorization 5 := by
      rw [← hPexp]
      exact ⟨Nat.card ↥Qp, by rw [mul_comm]; exact (Subgroup.card_mul_index Qp).symm⟩
    have hidx_cases : Qp.index = 1 ∨ Qp.index = 5 := by
      obtain ⟨j, hjle, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hidx_dvd
      have hj : j ≤ 1 :=
        (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).1 (by rw [← hjeq]; exact hidx_le)
      interval_cases j
      · left; simpa using hjeq
      · right; simpa using hjeq
    have hQpNormal : Qp.Normal := by
      rcases hidx_cases with h1 | h5
      · exact Subgroup.normal_of_index_eq_one h1
      · refine Subgroup.normal_of_index_eq_minFac_card ?_
        have hminfac : (Nat.card ↥P₀).minFac = 5 := by
          have hne1 : Nat.card ↥P₀ ≠ 1 := by
            have hle : Nat.card ↥E ≤ Nat.card ↥P₀ := Subgroup.card_le_of_le hEP
            have h54 : 5 ^ 4 ≤ Nat.card ↥P₀ := le_trans hEcard hle
            intro h; rw [h] at h54; norm_num at h54
          have hd : (Nat.card ↥P₀).minFac ∣
              5 ^ (Nat.card (adjointGroup .E8 K)).factorization 5 := by
            rw [← hPexp]; exact Nat.minFac_dvd _
          exact (Nat.prime_dvd_prime_iff_eq (Nat.minFac_prime hne1) Nat.prime_five).1
            (Nat.Prime.dvd_of_dvd_pow (Nat.minFac_prime hne1) hd)
        rw [h5, hminfac]
    intro y hy x hx
    have hmem : (⟨y, hy⟩ : ↥P₀) * (⟨x, hQP hx⟩ : ↥P₀) * (⟨y, hy⟩ : ↥P₀)⁻¹ ∈ Qp :=
      hQpNormal.conj_mem (⟨x, hQP hx⟩ : ↥P₀) hx (⟨y, hy⟩ : ↥P₀)
    exact Subgroup.mem_subgroupOf.1 hmem
  haveI : Finite ↥D.torus := by
    have h := CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.finite_twistedTorusOf_gen
      (K := K) (L := AlgebraicClosure K) (τ := .E8) Fr w (M := weylMatrix w) hM hFr hn0 hpow
    simpa only [LangDatum.torus] using h
  have hTne0 : Nat.card ↥D.torus ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1, one_mem _⟩, inferInstance⟩
  have hQ5 : IsPGroup 5 ↥Q := by
    intro g
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨(g : adjointGroup .E8 K), hQP g.2⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    simpa using congrArg Subtype.val hk
  let ρ : adjointGroup .E8 K →* ModGL .E8 (AlgebraicClosure K) :=
    (MulAut.conj D.g0⁻¹).toMonoidHom.comp bc
  have hρ_apply : ∀ x : adjointGroup .E8 K, ρ x =
      D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) * D.g0 := by
    intro x
    change D.g0⁻¹ * bc x * (D.g0⁻¹)⁻¹ =
      D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) * D.g0
    rw [inv_inv]
    rfl
  have hρinj : Function.Injective ρ := by
    have h1 : Function.Injective (bc : adjointGroup .E8 K → ModGL .E8 (AlgebraicClosure K)) :=
      (baseChangeGL_injective (algebraMap K (AlgebraicClosure K))).comp
        (Subgroup.subtype_injective _)
    exact (MulAut.conj D.g0⁻¹).injective.comp h1
  let S : Subgroup (ModGL .E8 (AlgebraicClosure K)) := Q.map ρ
  have hScard : Nat.card ↥S = Nat.card ↥Q := Subgroup.card_map_of_injective hρinj
  have hST : S ≤ D.torus := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
    rw [hρ_apply x]
    exact hQtor x hx
  have hS5 : IsPGroup 5 ↥S := hQ5.map ρ
  have hTcard : Nat.card ↥D.torus =
      ((weylMatrix w).charpoly.eval (Nat.card K : ℤ)).natAbs := by
    have h := CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.card_twistedTorusOf_gen
      (K := K) (L := AlgebraicClosure K) (τ := .E8) Fr w (M := weylMatrix w) hM hFr hn0 hpow
    simpa only [LangDatum.torus] using h
  have hCi : (Nat.card (adjointGroup .E8 K)).factorization 5 =
      (Nat.card ↥D.torus).factorization 5 + 1 := by
    rw [hTcard, hchar]
    exact factorization_card_adjointGroup_E8_five_four (K := K) hq
  have hSsub_card : Nat.card ↥(S.subgroupOf D.torus) = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hST).toEquiv
  have hQdvd : Nat.card ↥Q ∣ Nat.card ↥D.torus := by
    rw [← hScard, ← hSsub_card]
    exact Subgroup.card_subgroup_dvd_card (S.subgroupOf D.torus)
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hQ5
  have h5ale : 5 ^ (Nat.card ↥D.torus).factorization 5 ≤ Nat.card ↥Q := by
    have h := hPle
    rw [hPexp, hCi] at h
    rw [pow_succ] at h
    rw [mul_comm 5 (Nat.card ↥Q)] at h
    exact Nat.le_of_mul_le_mul_right h (by norm_num)
  have hr_le : r ≤ (Nat.card ↥D.torus).factorization 5 := by
    have hdvd : 5 ^ r ∣ Nat.card ↥D.torus := by rw [← hr]; exact hQdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five hTne0).1 hdvd
  have ha_le_r : (Nat.card ↥D.torus).factorization 5 ≤ r :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).1 (by rw [← hr]; exact h5ale)
  have hQcard : Nat.card ↥Q = 5 ^ (Nat.card ↥D.torus).factorization 5 := by
    rw [hr]; congr 1; omega
  have hT5 : ∀ t ∈ D.torus, t ^ 5 = 1 → ∃ x ∈ Q,
      D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) * D.g0 = t := by
    intro t htT ht5
    haveI : IsMulCommutative ↥D.torus :=
      CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.isMulCommutative_twistedTorusOf_gen
        (L := AlgebraicClosure K) (τ := .E8) Fr w (M := weylMatrix w) hM
    let tt : ↥D.torus := ⟨t, htT⟩
    have htt5 : tt ^ 5 = 1 := Subtype.ext (by simpa using ht5)
    have hSsub_p : IsPGroup 5 ↥(S.subgroupOf D.torus) := hS5.comap_subtype
    have hKsub_p : IsPGroup 5 ↥(Subgroup.zpowers tt) := by
      intro g
      refine ⟨1, ?_⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
      apply Subtype.ext
      rw [pow_one]
      change (g : ↥D.torus) ^ 5 = 1
      rw [show (g : ↥D.torus) = tt ^ k from hk.symm, ← zpow_natCast, ← zpow_mul, mul_comm,
        zpow_mul, zpow_natCast, htt5, one_zpow]
    have hsup_p : IsPGroup 5 ↥(S.subgroupOf D.torus ⊔ Subgroup.zpowers tt) :=
      hSsub_p.to_sup_of_normal_right hKsub_p
    obtain ⟨s, hs⟩ := IsPGroup.iff_card.mp hsup_p
    have hsup_dvd : Nat.card ↥(S.subgroupOf D.torus ⊔ Subgroup.zpowers tt) ∣
        Nat.card ↥D.torus := Subgroup.card_subgroup_dvd_card _
    have hs_le : s ≤ (Nat.card ↥D.torus).factorization 5 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five hTne0).1 (by rw [← hs]; exact hsup_dvd)
    have hge : 5 ^ (Nat.card ↥D.torus).factorization 5 ≤ 5 ^ s := by
      rw [← hs]
      calc 5 ^ (Nat.card ↥D.torus).factorization 5 = Nat.card ↥S := by rw [hScard, hQcard]
        _ = Nat.card ↥(S.subgroupOf D.torus) := hSsub_card.symm
        _ ≤ Nat.card ↥(S.subgroupOf D.torus ⊔ Subgroup.zpowers tt) :=
              Subgroup.card_le_of_le le_sup_left
    have hs_eq : s = (Nat.card ↥D.torus).factorization 5 :=
      le_antisymm hs_le ((Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).1 hge)
    have hcard_eq : Nat.card ↥(S.subgroupOf D.torus ⊔ Subgroup.zpowers tt) =
        Nat.card ↥(S.subgroupOf D.torus) := by
      rw [hs, hs_eq, hSsub_card, hScard, hQcard]
    have hsup_eq : S.subgroupOf D.torus ⊔ Subgroup.zpowers tt = S.subgroupOf D.torus := by
      have h := Subgroup.eq_of_le_of_card_ge (H := S.subgroupOf D.torus)
        (K := S.subgroupOf D.torus ⊔ Subgroup.zpowers tt) le_sup_left (le_of_eq hcard_eq)
      exact h.symm
    have htt_mem : tt ∈ S.subgroupOf D.torus := by
      rw [← hsup_eq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.2 ⟨1, zpow_one tt⟩)
    have hmemS : (tt : ModGL .E8 (AlgebraicClosure K)) ∈ S :=
      Subgroup.mem_subgroupOf.1 htt_mem
    obtain ⟨x, hx, hxρ⟩ := Subgroup.mem_map.1 hmemS
    exact ⟨x, hx, by rw [← hρ_apply x]; exact hxρ⟩
  have hEsubQ : E ≤ Q :=
    excFiveFour_le_of_toral_normal_subgroup (K := K) hq Fr hFr D rfl w rfl hshape hN8
      (P : Subgroup (adjointGroup .E8 K)) Q E hQP hEP hQn hPle hE hEcard hQtor hT5
  refine ⟨Fr, hFr, D, rfl, rfl, ⟨w, rfl, hshape⟩, ?_⟩
  intro x hx
  exact hQtor x (hEsubQ hx)

end Assembly

section Unconditional

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem adjointMaxElemToral
    (τ : Tag) (K : Type) [Field K] (p : ℕ) : AdjointMaxElemToral τ K p :=
  adjointMaxElemToral_of_fiveFourToral τ K p (excFiveFourToral K)

end Unconditional

end CFSG.StandardType.ExcMaxToral

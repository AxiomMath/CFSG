module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.LinearAlgebra.Eigenspace.Zero

public section

namespace CFSG.StandardType.TableCRes

open Polynomial
open scoped Matrix

section CyclotomicList

theorem exists_cyclotomic_list {N : ℕ} (hN : 0 < N) :
    ∀ (n : ℕ) (P : ℤ[X]), P.Monic → P.natDegree = n →
      (∀ z : ℂ, aeval z P = 0 → z ^ N = 1) →
      ∃ l : List ℕ, (∀ d ∈ l, 0 < d) ∧ P = (l.map fun d => cyclotomic d ℤ).prod := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P hP hdeg hroots
    by_cases h0 : P.natDegree = 0
    · exact ⟨[], by simp, by simpa using eq_one_of_monic_natDegree_zero hP h0⟩
    · have hdegpos : 0 < (P.map (Int.castRingHom ℂ)).degree := by
        rw [degree_map_eq_of_injective (RingHom.injective_int _)]
        exact natDegree_pos_iff_degree_pos.1 (Nat.pos_of_ne_zero h0)
      obtain ⟨z, hz⟩ := Complex.exists_root hdegpos
      have hz' : aeval z P = 0 := by
        rw [aeval_def, eval₂_eq_eval_map]
        exact hz
      have hzN : z ^ N = 1 := hroots z hz'
      have hprim : IsPrimitiveRoot z (orderOf z) := IsPrimitiveRoot.orderOf z
      have hdpos : 0 < orderOf z :=
        orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨N, hN, hzN⟩)
      have hΦ : cyclotomic (orderOf z) ℤ = minpoly ℤ z := cyclotomic_eq_minpoly hprim hdpos
      have hdvd : cyclotomic (orderOf z) ℤ ∣ P := by
        rw [hΦ]
        exact minpoly.isIntegrallyClosed_dvd (hprim.isIntegral hdpos) hz'
      obtain ⟨Q, hQ⟩ := hdvd
      have hQm : Q.Monic := (cyclotomic.monic _ ℤ).of_mul_monic_left (hQ ▸ hP)
      have hQdeg : Q.natDegree < n := by
        have h1 : P.natDegree = (cyclotomic (orderOf z) ℤ).natDegree + Q.natDegree := by
          rw [hQ]
          exact natDegree_mul (cyclotomic_ne_zero _ _) hQm.ne_zero
        rw [natDegree_cyclotomic] at h1
        have := Nat.totient_pos.2 hdpos
        omega
      obtain ⟨l, hl0, hl⟩ := ih Q.natDegree hQdeg Q hQm rfl
        (fun w hw => hroots w (by rw [hQ, map_mul, hw, mul_zero]))
      refine ⟨orderOf z :: l, ?_, ?_⟩
      · intro d hd
        rcases List.mem_cons.1 hd with rfl | hd
        · exact hdpos
        · exact hl0 d hd
      · rw [hQ, hl, List.map_cons, List.prod_cons]

theorem natDegree_prod_cyclotomic (l : List ℕ) :
    ((l.map fun d => cyclotomic d ℤ).prod).natDegree = (l.map Nat.totient).sum := by
  induction l with
  | nil => simp
  | cons d l ih =>
    rw [List.map_cons, List.prod_cons, natDegree_mul (cyclotomic_ne_zero _ _), ih,
      natDegree_cyclotomic, List.map_cons, List.sum_cons]
    exact List.prod_ne_zero (by simp [cyclotomic_ne_zero])

theorem pow_count_dvd_prod_cyclotomic (c : ℕ) (l : List ℕ) :
    cyclotomic c ℤ ^ l.count c ∣ (l.map fun d => cyclotomic d ℤ).prod := by
  induction l with
  | nil => simp
  | cons d l ih =>
    rw [List.map_cons, List.prod_cons, List.count_cons]
    by_cases hdc : d = c
    · subst hdc
      simp only [beq_self_eq_true, if_true, pow_succ, mul_comm (cyclotomic d ℤ ^ _)]
      exact mul_dvd_mul_left _ ih
    · simp only [beq_iff_eq, hdc, if_false, add_zero]
      exact ih.mul_left _

end CyclotomicList

section ModP

variable {p : ℕ} [hp : Fact p.Prime]

theorem rootMultiplicity_cyclotomic_modp {q : ZMod p} {c d : ℕ} (hp7 : 7 ≤ p)
    (hcφ : Nat.totient c = 2) (hcp : ¬ p ∣ c) (hq : orderOf q = c) (hd : 0 < d)
    (hd8 : Nat.totient d ≤ 8) :
    rootMultiplicity q (cyclotomic d (ZMod p)) = if d = c then 1 else 0 := by
  obtain ⟨k, m, hpm, hdm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' p hp.out.one_lt.ne'
  have : NeZero (m : ZMod p) := ⟨by rwa [Ne, ZMod.natCast_eq_zero_iff]⟩
  have : NeZero (c : ZMod p) := ⟨by rwa [Ne, ZMod.natCast_eq_zero_iff]⟩
  have hroot : IsRoot (cyclotomic d (ZMod p)) q ↔ IsPrimitiveRoot q m := by
    rw [hdm]
    exact isRoot_cyclotomic_prime_pow_mul_iff_of_charP
  by_cases hdc : d = c
  · subst hdc
    have hr : IsRoot (cyclotomic d (ZMod p)) q :=
      isRoot_cyclotomic_iff.2 (hq ▸ IsPrimitiveRoot.orderOf q)
    have h1 : 0 < rootMultiplicity q (cyclotomic d (ZMod p)) :=
      (rootMultiplicity_pos (cyclotomic_ne_zero d _)).2 hr
    have h2 := rootMultiplicity_le_one_of_separable (separable_cyclotomic d (ZMod p)) q
    rw [if_pos rfl]
    omega
  · rw [if_neg hdc]
    refine rootMultiplicity_eq_zero fun hr => hdc ?_
    have hmc : m = c := by
      have := (hroot.1 hr).eq_orderOf
      rw [hq] at this
      exact this
    subst hmc
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using hdm
    · exfalso
      have hcop : Nat.Coprime (p ^ k) m :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpm)
      have h1 : Nat.totient d = Nat.totient (p ^ k) * 2 := by
        rw [hdm, Nat.totient_mul hcop, hcφ]
      rw [Nat.totient_prime_pow hp.out hk] at h1
      have h2 : p ^ (k - 1) ≥ 1 := Nat.one_le_pow _ _ hp.out.pos
      have h3 : p ^ (k - 1) * (p - 1) ≥ 6 := by nlinarith [Nat.sub_le_sub_right hp7 1]
      omega

theorem rootMultiplicity_prod_cyclotomic {q : ZMod p} {c : ℕ} (hp7 : 7 ≤ p)
    (hcφ : Nat.totient c = 2) (hcp : ¬ p ∣ c) (hq : orderOf q = c) :
    ∀ l : List ℕ, (∀ d ∈ l, 0 < d) → (l.map Nat.totient).sum ≤ 8 →
      rootMultiplicity q ((l.map fun d => cyclotomic d (ZMod p)).prod) = l.count c := by
  intro l
  induction l with
  | nil => intros; simp
  | cons d l ih =>
    intro hpos hsum
    rw [List.map_cons, List.sum_cons] at hsum
    have hpos' : ∀ x ∈ l, 0 < x := fun x hx => hpos x (List.mem_cons_of_mem _ hx)
    have hne : ((l.map fun d => cyclotomic d (ZMod p)).prod) ≠ 0 :=
      List.prod_ne_zero (by simp [cyclotomic_ne_zero])
    rw [List.map_cons, List.prod_cons,
      rootMultiplicity_mul (mul_ne_zero (cyclotomic_ne_zero _ _) hne),
      ih hpos' (by omega), rootMultiplicity_cyclotomic_modp hp7 hcφ hcp hq (hpos d (by simp))
        (by omega), List.count_cons]
    by_cases hdc : d = c
    · simp [hdc]
      omega
    · simp [hdc]

end ModP

section Main

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem pow_eq_one_of_aeval_charpoly (R : Matrix ι ι ℤ) {N : ℕ} (hR : R ^ N = 1)
    (z : ℂ) (hz : aeval z R.charpoly = 0) : z ^ N = 1 := by
  set M : Matrix ι ι ℂ := R.map (Int.castRingHom ℂ) with hM
  have hMN : M ^ N = 1 := by
    have h := map_pow ((Int.castRingHom ℂ).mapMatrix : Matrix ι ι ℤ →+* _) R N
    rw [hR, map_one] at h
    exact h.symm
  have hroot : M.charpoly.IsRoot z := by
    rw [hM, Matrix.charpoly_map]
    simpa [IsRoot, aeval_def, eval₂_eq_eval_map] using hz
  have hz_spec : z ∈ spectrum ℂ M := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  have h1 : z ^ N ∈ spectrum ℂ (M ^ N) := spectrum.pow_mem_pow M N hz_spec
  rw [hMN, spectrum.one_eq] at h1
  exact h1

theorem cyclotomic_aeval_eq_zero {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) {c : ℕ}
    (hc : c = 3 ∨ c = 6) {q : ZMod p} (hq : orderOf q = c) (hι : Fintype.card ι = 8)
    (R : Matrix ι ι ℤ) {N : ℕ} (hN : 0 < N) (hR : R ^ N = 1)
    (hdim : 4 ≤ Module.finrank (ZMod p)
      (Module.End.eigenspace (Matrix.mulVecLin ((R.map (Int.castRingHom (ZMod p)))ᵀ)) q)) :
    aeval R (cyclotomic c ℤ) = 0 := by
  classical
  have hcφ : Nat.totient c = 2 := by rcases hc with rfl | rfl <;> decide
  have hcp : ¬ p ∣ c := by
    intro h
    have := Nat.le_of_dvd (by rcases hc with rfl | rfl <;> norm_num) h
    rcases hc with rfl | rfl <;> omega
  have hdeg8 : R.charpoly.natDegree = 8 := by
    rw [Matrix.charpoly_natDegree_eq_dim, hι]
  obtain ⟨l, hl0, hl⟩ := exists_cyclotomic_list hN 8 R.charpoly (Matrix.charpoly_monic R) hdeg8
    (fun z hz => pow_eq_one_of_aeval_charpoly R hR z hz)
  have hdegl : (l.map Nat.totient).sum = 8 := by
    rw [← natDegree_prod_cyclotomic, ← hl, hdeg8]
  have hmodp : (R.map (Int.castRingHom (ZMod p))).charpoly =
      (l.map fun d => cyclotomic d (ZMod p)).prod := by
    rw [Matrix.charpoly_map, hl, Polynomial.map_list_prod]
    simp [List.map_map, Function.comp_def, map_cyclotomic]
  have hmult : 4 ≤ rootMultiplicity q (R.map (Int.castRingHom (ZMod p))).charpoly := by
    refine hdim.trans ?_
    have := LinearMap.finrank_eigenspace_le
      (Matrix.mulVecLin ((R.map (Int.castRingHom (ZMod p)))ᵀ)) q
    rwa [Matrix.charpoly_mulVecLin, Matrix.charpoly_transpose] at this
  rw [hmodp, rootMultiplicity_prod_cyclotomic hp7 hcφ hcp hq l hl0 (by omega)] at hmult
  have hdvd : cyclotomic c ℤ ^ 4 ∣ R.charpoly := by
    rw [hl]
    exact (pow_dvd_pow _ hmult).trans (pow_count_dvd_prod_cyclotomic c l)
  have hχ : R.charpoly = cyclotomic c ℤ ^ 4 := by
    refine eq_of_monic_of_dvd_of_natDegree_le ((cyclotomic.monic c ℤ).pow 4)
      (Matrix.charpoly_monic R) hdvd ?_
    rw [natDegree_pow, natDegree_cyclotomic, hcφ, hdeg8]
  set Rq : Matrix ι ι ℚ := R.map (Int.castRingHom ℚ) with hRq
  have hRqN : Rq ^ N = 1 := by
    have h := map_pow ((Int.castRingHom ℚ).mapMatrix : Matrix ι ι ℤ →+* _) R N
    rw [hR, map_one] at h
    exact h.symm
  have hm1 : minpoly ℚ Rq ∣ X ^ N - 1 :=
    minpoly.dvd ℚ Rq (by simp [hRqN, map_sub, map_pow, aeval_X])
  have hm2 : minpoly ℚ Rq ∣ cyclotomic c ℚ ^ 4 := by
    have := Matrix.minpoly_dvd_charpoly Rq
    rwa [hRq, Matrix.charpoly_map, hχ, Polynomial.map_pow, map_cyclotomic] at this
  have hc0 : 0 < c := by rcases hc with rfl | rfl <;> norm_num
  have hirr : Irreducible (cyclotomic c ℚ) := cyclotomic.irreducible_rat hc0
  obtain ⟨i, hi4, hassoc⟩ := (dvd_prime_pow hirr.prime 4).1 hm2
  have hmin : minpoly ℚ Rq = cyclotomic c ℚ ^ i :=
    eq_of_monic_of_associated (minpoly.monic (Matrix.isIntegral Rq)) ((cyclotomic.monic c ℚ).pow i)
      hassoc
  have hi1 : i = 1 := by
    rcases Nat.lt_or_ge i 2 with h | h
    · interval_cases i
      · exfalso
        have := minpoly.aeval ℚ Rq
        rw [hmin, pow_zero, map_one] at this
        exact one_ne_zero this
      · rfl
    · exfalso
      have hsq : Squarefree (X ^ N - 1 : ℚ[X]) := by
        have := (separable_X_pow_sub_C (1 : ℚ) (Nat.pos_iff_ne_zero.1 hN |> fun h => by
          exact_mod_cast h) one_ne_zero).squarefree
        simpa using this
      have hdv : cyclotomic c ℚ * cyclotomic c ℚ ∣ X ^ N - 1 := by
        have h2 : cyclotomic c ℚ ^ 2 ∣ cyclotomic c ℚ ^ i := pow_dvd_pow _ h
        rw [← hmin, sq] at h2
        exact h2.trans hm1
      exact hirr.not_isUnit (hsq _ hdv)
  have hphi : aeval Rq (cyclotomic c ℚ) = 0 := by
    have := minpoly.aeval ℚ Rq
    rwa [hmin, hi1, pow_one] at this
  have hphiZ : aeval Rq (cyclotomic c ℤ) = 0 := by
    have h1 : aeval Rq ((cyclotomic c ℤ).map (algebraMap ℤ ℚ)) = 0 := by
      rw [algebraMap_int_eq, map_cyclotomic_int]
      exact hphi
    rwa [aeval_map_algebraMap] at h1
  have hinj : Function.Injective (fun A : Matrix ι ι ℤ => A.map (Int.castRingHom ℚ)) :=
    Matrix.map_injective (RingHom.injective_int _)
  apply hinj
  have hmap : (aeval R (cyclotomic c ℤ)).map (Int.castRingHom ℚ) = aeval Rq (cyclotomic c ℤ) := by
    have := Polynomial.aeval_algHom_apply
      (AlgHom.mapMatrix (Int.castRingHom ℚ).toIntAlgHom) R (cyclotomic c ℤ)
    exact this.symm
  beta_reduce
  rw [hmap, hphiZ]
  ext i j
  simp

end Main

end CFSG.StandardType.TableCRes

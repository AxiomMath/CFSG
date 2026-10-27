module

public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoTailProofParab
import CFSG.RankThree.PartTwo.Sec16.KSL3TwoTailProofSU3

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace ProofKS1623Parab

open CFSG
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.SteinbergBR.BlockPar
open Matrix

variable {F : Type} [Field F]

@[expose] def IsDiag (t : SpecialLinearGroup (Fin 3) F) : Prop :=
  ∀ i j, i ≠ j → t.val i j = 0

theorem eq_diagonal_of_isDiag {t : SpecialLinearGroup (Fin 3) F} (ht : IsDiag t) :
    t.val = diagonal fun i => t.val i i := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq]
  · rw [diagonal_apply_ne _ hij, ht i j hij]

theorem isDiag_of_val_eq {t : SpecialLinearGroup (Fin 3) F} {d : Fin 3 → F}
    (h : t.val = diagonal d) : IsDiag t := fun i j hij => by
  rw [h, diagonal_apply_ne _ hij]

theorem isDiag_one : IsDiag (1 : SpecialLinearGroup (Fin 3) F) :=
  isDiag_of_val_eq (d := fun _ => 1) (by rw [diagonal_one]; rfl)

theorem isDiag_mul {s t : SpecialLinearGroup (Fin 3) F} (hs : IsDiag s) (ht : IsDiag t) :
    IsDiag (s * t) :=
  isDiag_of_val_eq (d := fun i => s.val i i * t.val i i) (by
    rw [show (s * t).val = s.val * t.val from rfl, eq_diagonal_of_isDiag hs,
      eq_diagonal_of_isDiag ht, diagonal_mul_diagonal]
    simp)

theorem mul_val_diag {s t : SpecialLinearGroup (Fin 3) F} (hs : IsDiag s) (ht : IsDiag t)
    (i : Fin 3) : (s * t).val i i = s.val i i * t.val i i := by
  rw [show (s * t).val = s.val * t.val from rfl, eq_diagonal_of_isDiag hs,
    eq_diagonal_of_isDiag ht, diagonal_mul_diagonal]
  simp

theorem isDiag_pow {t : SpecialLinearGroup (Fin 3) F} (ht : IsDiag t) (k : ℕ) :
    IsDiag (t ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact isDiag_one
  | succ k ih => rw [pow_succ]; exact isDiag_mul ih ht

theorem pow_val_diag {t : SpecialLinearGroup (Fin 3) F} (ht : IsDiag t) (k : ℕ) (i : Fin 3) :
    (t ^ k).val i i = t.val i i ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_val_diag (isDiag_pow ht k) ht, ih, pow_succ]

theorem isDiag_scalarElement (c : Fˣ) (hc : c ^ 3 = 1) :
    IsDiag (scalarElement (n := 3) c hc) :=
  isDiag_of_val_eq (d := fun _ => (c : F)) (by rw [coe_scalarElement, scalar_apply])

@[expose] def diagTwo (τ : F) (hτ : τ ^ 3 = 1) : SpecialLinearGroup (Fin 2) F :=
  ⟨diagonal ![τ, τ ^ 2], by
    rw [det_diagonal, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [← pow_succ', hτ]⟩

@[expose] def dZero (τ : F) (hτ : τ ^ 3 = 1) : SpecialLinearGroup (Fin 3) F :=
  lev F (diagTwo τ hτ)

theorem dZero_val (τ : F) (hτ : τ ^ 3 = 1) :
    (dZero τ hτ).val = diagonal ![τ, τ ^ 2, 1] := by
  rw [dZero, lev_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levMat, diagTwo]

theorem proj_dZero_mem_leviP (τ : F) (hτ : τ ^ 3 = 1) :
    proj 3 F (dZero τ hτ) ∈ leviP F :=
  ⟨diagTwo τ hτ, rfl⟩

theorem dZero_entries_ne {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {i j : Fin 3} (hij : i ≠ j) :
    (![τ, τ ^ 2, 1] : Fin 3 → F) i ≠ ![τ, τ ^ 2, 1] j := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have h12 : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    have : τ * τ = τ * 1 := by rw [← sq, ← h, mul_one]
    exact mul_left_cancel₀ hτ0 this
  have h2 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ ^ 3 * (τ ^ 2)⁻¹ := by field_simp
      _ = 1 := by rw [hτ, h, inv_one, one_mul]
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
       first
        | exact h12
        | exact h12.symm
        | exact hτ1
        | exact Ne.symm hτ1
        | exact h2
        | exact Ne.symm h2)

theorem pow_three_isDiag {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {h : SpecialLinearGroup (Fin 3) F}
    (hc : proj 3 F (dZero τ hτ) * proj 3 F h = proj 3 F h * proj 3 F (dZero τ hτ)) :
    IsDiag (h ^ 3) := by
  set D := dZero τ hτ with hD
  have hz : h * D * h⁻¹ * D⁻¹ ∈ scalars 3 F := by
    rw [← proj_eq_one_iff, map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
    group
  set z := h * D * h⁻¹ * D⁻¹ with hzdef
  have hzc : ∀ y : SpecialLinearGroup (Fin 3) F, z * y = y * z := fun y =>
    (Subgroup.mem_center_iff.mp ((scalars_eq_center 3 F) ▸ hz) y).symm
  have hz3 : z ^ 3 = 1 := by
    obtain ⟨c, hc3, hzc'⟩ := mem_scalars.mp hz
    apply Subtype.ext
    rw [show (z ^ 3).val = z.val ^ 3 from rfl, hzc', ← map_pow, ← Units.val_pow_eq_pow_val, hc3,
      Units.val_one, map_one]
    rfl
  have hhD : h * D = z * D * h := by
    rw [hzdef]
    group
  have hk : ∀ k : ℕ, h ^ k * D = z ^ k * D * h ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc h ^ (k + 1) * D = h ^ k * (h * D) := by rw [pow_succ, mul_assoc]
        _ = h ^ k * (z * D * h) := by rw [hhD]
        _ = z * (h ^ k * D) * h := by
          rw [← mul_assoc, ← mul_assoc, ← hzc (h ^ k)]
          group
        _ = z * (z ^ k * D * h ^ k) * h := by rw [ih]
        _ = z ^ (k + 1) * D * h ^ (k + 1) := by
          rw [pow_succ, pow_succ, ← hzc (z ^ k)]
          group
  have h3 := hk 3
  rw [hz3, one_mul] at h3
  have hmat : (h ^ 3).val * diagonal ![τ, τ ^ 2, 1] = diagonal ![τ, τ ^ 2, 1] * (h ^ 3).val := by
    have := congrArg Subtype.val h3
    rw [show (h ^ 3 * D).val = (h ^ 3).val * D.val from rfl,
      show (D * h ^ 3).val = D.val * (h ^ 3).val from rfl, hD, dZero_val] at this
    exact this
  intro i j hij
  exact Sec4.entry_eq_zero_of_commute_diagonal hmat (dZero_entries_ne hτ hτ1 hij)

theorem scalarElement_commute (c : Fˣ) (hc : c ^ 3 = 1) (y : SpecialLinearGroup (Fin 3) F) :
    Commute (scalarElement (n := 3) c hc) y :=
  (Subgroup.mem_center_iff.mp ((scalars_eq_center 3 F) ▸ scalarElement_mem_scalars c hc) y).symm

theorem three_dvd_two_mul_sq_add_one {p : ℕ} (hp3 : Nat.Coprime 3 p) : 3 ∣ 2 * p ^ 2 + 1 := by
  have hp : p % 3 = 1 ∨ p % 3 = 2 := by
    have h0 : p % 3 ≠ 0 := by
      intro h0
      have : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
      have := Nat.Coprime.coprime_dvd_right this hp3
      norm_num at this
    omega
  have hsq : p ^ 2 % 3 = (p % 3) ^ 2 % 3 := Nat.pow_mod p 2 3
  rcases hp with h | h <;> rw [h] at hsq <;> norm_num at hsq <;> omega

theorem exists_diag_rep {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {p : ℕ} (hp1 : 1 < p)
    (hp3 : Nat.Coprime 3 p) {x : projectiveSL 3 F} (hxp : x ^ p = 1)
    (hxc : proj 3 F (dZero τ hτ) * x = x * proj 3 F (dZero τ hτ)) :
    ∃ t : SpecialLinearGroup (Fin 3) F, IsDiag t ∧ t ^ p = 1 ∧ proj 3 F t = x := by
  obtain ⟨h, rfl⟩ := proj_surjective 3 F x
  have hd := pow_three_isDiag hτ hτ1 hxc
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hp3 hp1
  set t0 := (h ^ 3) ^ k with ht0
  have ht0d : IsDiag t0 := isDiag_pow hd k
  have hx : proj 3 F t0 = proj 3 F h := by
    rw [ht0, map_pow, map_pow, ← pow_mul]
    have : 3 * k = p * (3 * k / p) + 1 := by have := Nat.div_add_mod (3 * k) p; omega
    rw [this, pow_succ, pow_mul, hxp, one_pow, one_mul]
  have hsc : t0 ^ p ∈ scalars 3 F := by
    rw [← proj_eq_one_iff, map_pow, hx, hxp]
  obtain ⟨c, hc3, hct⟩ := mem_scalars.mp hsc
  set ν : Fˣ := c ^ (2 * p) with hν
  have hν3 : ν ^ 3 = 1 := by rw [hν, ← pow_mul, mul_comm, pow_mul, hc3, one_pow]
  refine ⟨scalarElement ν hν3 * t0, isDiag_mul (isDiag_scalarElement ν hν3) ht0d, ?_, ?_⟩
  · rw [(scalarElement_commute ν hν3 t0).mul_pow]
    apply Subtype.ext
    rw [show (scalarElement ν hν3 ^ p * t0 ^ p).val =
        (scalarElement ν hν3).val ^ p * (t0 ^ p).val from rfl, hct, coe_scalarElement,
      ← map_pow, ← map_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, hν, ← pow_mul,
      ← pow_succ]
    obtain ⟨r, hr⟩ := three_dvd_two_mul_sq_add_one hp3
    rw [show 2 * p * p + 1 = 2 * p ^ 2 + 1 by ring, hr, pow_mul, hc3, one_pow, Units.val_one,
      map_one]
    rfl
  · rw [map_mul, (proj_eq_one_iff).mpr (scalarElement_mem_scalars ν hν3), one_mul, hx]

theorem proj_mem_leviP_of_isDiag {t : SpecialLinearGroup (Fin 3) F} (ht : IsDiag t)
    (h22 : t.val 2 2 = 1) : proj 3 F t ∈ leviP F := by
  have hdet : t.val 0 0 * t.val 1 1 = 1 := by
    have h1 := t.prop
    rw [eq_diagonal_of_isDiag ht, det_diagonal, Fin.prod_univ_three, h22, mul_one] at h1
    exact h1
  refine ⟨⟨diagonal ![t.val 0 0, t.val 1 1], by
    rw [det_diagonal, Fin.prod_univ_two]
    simpa using hdet⟩, ?_⟩
  change proj 3 F (lev F _) = proj 3 F t
  congr 1
  apply Subtype.ext
  show levMat (diagonal ![t.val 0 0, t.val 1 1]) = t.val
  rw [eq_diagonal_of_isDiag ht]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levMat, h22]

theorem exists_le_leviP [Finite F] {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {P : Subgroup (projectiveSL 3 F)}
    (hPC : P ≤ Subgroup.centralizer ({proj 3 F (dZero τ hτ)} : Set (projectiveSL 3 F)))
    (hPel : CFSG.Assembly.IsElemAbelian p P) (hPc : Nat.card P = p ^ 2) :
    ∃ X : Subgroup (projectiveSL 3 F), X ≤ P ∧ Nat.card X = p ∧ X ≤ leviP F := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).mpr (by omega)
  have hrep : ∀ x : P, ∃ t : SpecialLinearGroup (Fin 3) F,
      IsDiag t ∧ t ^ p = 1 ∧ proj 3 F t = x := fun x =>
    exists_diag_rep hτ hτ1 hp.one_lt hcop (hPel.2 x x.2)
      (Subgroup.mem_centralizer_singleton_iff.mp (hPC x.2)).symm
  by_contra hno
  have hno' : ∀ x ∈ P, x ≠ 1 → x ∉ leviP F := by
    intro x hx hx1 hxl
    apply hno
    refine ⟨Subgroup.zpowers x, Subgroup.zpowers_le.mpr hx, ?_, Subgroup.zpowers_le.mpr hxl⟩
    rw [Nat.card_zpowers, orderOf_eq_prime (hPel.2 x hx) hx1]
  choose rep hrepd hrepp hrepx using hrep
  set f : P → F := fun x => (rep x).val 2 2 with hfdef
  have hf : Function.Injective f := by
    intro x y hxy
    set s := rep x * rep y ^ (p - 1) with hsdef
    have hsd : IsDiag s := isDiag_mul (hrepd x) (isDiag_pow (hrepd y) _)
    have hyinv : (y : projectiveSL 3 F) ^ (p - 1) = (y : projectiveSL 3 F)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hp.one_le, hPel.2 y y.2]
    have hsproj : proj 3 F s = x * (y : projectiveSL 3 F)⁻¹ := by
      rw [hsdef, map_mul, map_pow, hrepx, hrepx, hyinv]
    have hs22 : s.val 2 2 = 1 := by
      rw [hsdef, mul_val_diag (hrepd x) (isDiag_pow (hrepd y) _),
        pow_val_diag (hrepd y)]
      have h1 : (rep x).val 2 2 = (rep y).val 2 2 := hxy
      rw [h1, ← pow_succ', Nat.sub_add_cancel hp.one_le, ← pow_val_diag (hrepd y), hrepp]
      rfl
    have hmem : x * (y : projectiveSL 3 F)⁻¹ ∈ P := mul_mem x.2 (inv_mem y.2)
    by_contra hne
    have hne' : x * (y : projectiveSL 3 F)⁻¹ ≠ 1 := by
      intro h1
      apply hne
      exact Subtype.ext (mul_inv_eq_one.mp h1)
    exact hno' _ hmem hne' (hsproj ▸ proj_mem_leviP_of_isDiag hsd hs22)
  set S : Finset F := (Polynomial.nthRoots p (1 : F)).toFinset with hS
  have hfS : ∀ x, f x ∈ S := by
    intro x
    rw [hS, Multiset.mem_toFinset, Polynomial.mem_nthRoots hp.pos]
    rw [hfdef]
    simp only
    rw [← pow_val_diag (hrepd x), hrepp]
    rfl
  have hcard : Nat.card P ≤ p := by
    have h1 : Nat.card P ≤ Nat.card S :=
      Nat.card_le_card_of_injective (fun x => (⟨f x, hfS x⟩ : S)) (fun x y hxy => hf
        (congrArg Subtype.val hxy))
    have h2 : Nat.card S = S.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    have h3 : S.card ≤ p := by
      rw [hS]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots p (1 : F))
    omega
  rw [hPc] at hcard
  have hp1 := hp.one_lt
  nlinarith

theorem pow_three_ne_of_not_nine_dvd [Finite F] (h9 : ¬ 9 ∣ Nat.card F - 1) {c : F}
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (r : F) : r ^ 3 ≠ c := by
  intro hr
  have := Fintype.ofFinite F
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hr
    rw [← hr, zero_pow (by norm_num)] at hc3
    exact zero_ne_one hc3
  have h9r : r ^ 9 = 1 := by
    rw [show 9 = 3 * 3 by rfl, pow_mul, hr, hc3]
  have hq : r ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one r hr0
  rw [← Nat.card_eq_fintype_card] at hq
  have hg : r ^ Nat.gcd 9 (Nat.card F - 1) = 1 := pow_gcd_eq_one.mpr ⟨h9r, hq⟩
  have hgd : Nat.gcd 9 (Nat.card F - 1) ∣ 3 := by
    have hd : Nat.gcd 9 (Nat.card F - 1) ∣ 9 := Nat.gcd_dvd_left _ _
    have hne : Nat.gcd 9 (Nat.card F - 1) ≠ 9 := fun he =>
      h9 (he ▸ Nat.gcd_dvd_right 9 (Nat.card F - 1))
    have hdiv : Nat.gcd 9 (Nat.card F - 1) ∈ Nat.divisors 9 := by
      rw [Nat.mem_divisors]; exact ⟨hd, by norm_num⟩
    have h9d : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [h9d] at hdiv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
    rcases hdiv with h1 | h1 | h1
    · rw [h1]; exact one_dvd 3
    · rw [h1]
    · exact absurd h1 hne
  obtain ⟨k, hk⟩ := hgd
  have h3r : r ^ 3 = 1 := by rw [hk, pow_mul, hg, one_pow]
  exact hc1 (hr ▸ h3r)

theorem exists_conj_dZero [Finite F] [CharP F 2] (hq1 : Nat.card F % 3 = 1)
    (hq9 : ¬ 9 ∣ Nat.card F - 1) {b : projectiveSL 3 F} (hb : orderOf b = 3) :
    ∃ (τ : F) (hτ : τ ^ 3 = 1), τ ≠ 1 ∧ ∃ g : SpecialLinearGroup (Fin 3) F,
      b = proj 3 F g * proj 3 F (dZero τ hτ) * (proj 3 F g)⁻¹ := by
  have := Fintype.ofFinite F
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h3 : (3 : F) ≠ 0 := by
    intro h3
    have : (1 : F) = 0 := by linear_combination h3 - h2
    exact one_ne_zero this
  obtain ⟨u, hu⟩ : ∃ u : Fˣ, orderOf u = 3 := by
    refine exists_prime_orderOf_dvd_card' 3 ?_
    rw [Nat.card_units]
    have h1 : 1 ≤ Nat.card F := Nat.card_pos
    omega
  set τ : F := (u : F) with hτdef
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτdef, ← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have hτ1 : τ ≠ 1 := by
    intro h1
    have : u = 1 := Units.ext h1
    rw [this, orderOf_one] at hu
    norm_num at hu
  have hτ0 : τ ≠ 0 := by
    rintro h0
    rw [h0] at hτ3
    norm_num at hτ3
  refine ⟨τ, hτ3, hτ1, ?_⟩
  obtain ⟨B, rfl⟩ := proj_surjective 3 F b
  have hb3 : proj 3 F (B ^ 3) = 1 := by
    have h1 := pow_orderOf_eq_one (proj 3 F B)
    rw [hb] at h1
    rw [map_pow, h1]
  rw [proj_eq_one_iff] at hb3
  obtain ⟨c, hc3, hBc⟩ := mem_scalars.mp hb3
  have hc1 : (c : F) = 1 := by
    by_contra hc1
    have hc3' : (c : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
    have hM : B.val ^ 3 = (c : F) • 1 := by
      rw [show B.val ^ 3 = (B ^ 3).val from rfl, hBc, scalar_apply, smul_one_eq_diagonal]
    have hdet := ProofKS1623SU3.det_eq_of_pow_three_eq_smul B.val (c : F) hM
      (pow_three_ne_of_not_nine_dvd hq9 hc3' hc1)
    rw [B.prop] at hdet
    exact hc1 hdet.symm
  have hB3 : B.val ^ 3 = 1 := by
    rw [show B.val ^ 3 = (B ^ 3).val from rfl, hBc, hc1, map_one]
  have hb1 : proj 3 F B ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hb
    norm_num at hb
  have hBs : ∀ a : F, B.val ≠ a • 1 := by
    intro a ha
    apply hb1
    rw [proj_eq_one_iff, mem_scalars]
    have ha0 : a ≠ 0 := by
      rintro rfl
      have := B.prop
      rw [ha, zero_smul, det_zero] at this
      exact zero_ne_one this
    refine ⟨Units.mk0 a ha0, ?_, ?_⟩
    · apply Units.ext
      have := B.prop
      rw [ha, det_smul, det_one, mul_one, Fintype.card_fin] at this
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, this, Units.val_one]
    · rw [ha, Units.val_mk0, scalar_apply, smul_one_eq_diagonal]
  obtain ⟨g0, j, hg0, hform⟩ := Sec4.exists_normal_form hτ3 hτ1 h3 hB3 hBs
  have hg0det : g0.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det g0).mp hg0).ne_zero
  have hdetD : ∀ {D : Matrix (Fin 3) (Fin 3) F}, (τ ^ (j : ℕ) • B.val) * g0 = g0 * D →
      D.det = 1 := by
    intro D hD
    have h1 := congrArg Matrix.det hD
    rw [det_mul, det_mul, det_smul, B.prop, Fintype.card_fin, mul_one, ← pow_mul,
      mul_comm (j : ℕ) 3, pow_mul, hτ3, one_pow, one_mul] at h1
    exact (mul_right_eq_self₀.1 h1.symm).resolve_right hg0det
  rcases hform with hD | hD | hD
  swap
  · exfalso
    have h1 := hdetD hD
    rw [det_diagonal, Fin.prod_univ_three] at h1
    simp at h1
    exact hτ1 h1
  swap
  · exfalso
    have h1 := hdetD hD
    rw [det_diagonal, Fin.prod_univ_three] at h1
    change τ ^ 2 * 1 * 1 = 1 at h1
    rw [mul_one, mul_one] at h1
    exact hτ1 (by linear_combination hτ3 - τ * h1)
  set δ := g0.det with hδ
  set g1 : Matrix (Fin 3) (Fin 3) F := g0 * diagonal ![δ⁻¹, 1, 1] with hg1
  have hg1det : g1.det = 1 := by
    rw [hg1, det_mul, det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, mul_one]
    exact mul_inv_cancel₀ hg0det
  set G1 : SpecialLinearGroup (Fin 3) F := ⟨g1, hg1det⟩ with hG1
  have hτj : (τ ^ (j : ℕ)) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hτ3, one_pow]
  have hτj0 : τ ^ (j : ℕ) ≠ 0 := pow_ne_zero _ hτ0
  set z : Fˣ := (Units.mk0 (τ ^ (j : ℕ)) hτj0)⁻¹ with hz
  have hz3 : z ^ 3 = 1 := by
    rw [hz, inv_pow, inv_eq_one]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτj, Units.val_one]
  have hBG : B * G1 = G1 * (scalarElement z hz3 * dZero τ hτ3) := by
    apply Subtype.ext
    show B.val * g1 = g1 * (scalar (Fin 3) (z : F) * (dZero τ hτ3).val)
    rw [dZero_val, hg1, scalar_apply, ← smul_one_eq_diagonal]
    have hcomm : diagonal ![δ⁻¹, 1, 1] * diagonal ![τ, τ ^ 2, 1] =
        diagonal ![τ, τ ^ 2, 1] * diagonal ![δ⁻¹, 1, 1] := by
      rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      ring
    have hzτ : (z : F) * τ ^ (j : ℕ) = 1 := by
      rw [hz, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hτj0]
    calc B.val * (g0 * diagonal ![δ⁻¹, 1, 1])
        = ((z : F) * τ ^ (j : ℕ)) • (B.val * g0 * diagonal ![δ⁻¹, 1, 1]) := by
          rw [hzτ, one_smul, Matrix.mul_assoc]
      _ = (z : F) • ((τ ^ (j : ℕ) • B.val) * g0 * diagonal ![δ⁻¹, 1, 1]) := by
          rw [Matrix.smul_mul, Matrix.smul_mul, smul_smul]
      _ = (z : F) • (g0 * diagonal ![τ, τ ^ 2, 1] * diagonal ![δ⁻¹, 1, 1]) := by rw [hD]
      _ = (z : F) • (g0 * (diagonal ![δ⁻¹, 1, 1] * diagonal ![τ, τ ^ 2, 1])) := by
          rw [Matrix.mul_assoc, ← hcomm]
      _ = g0 * diagonal ![δ⁻¹, 1, 1] *
          ((z : F) • (1 : Matrix (Fin 3) (Fin 3) F) * diagonal ![τ, τ ^ 2, 1]) := by
          rw [smul_one_mul, Matrix.mul_smul, Matrix.mul_assoc]
  refine ⟨G1, ?_⟩
  have hB : B = G1 * (scalarElement z hz3 * dZero τ hτ3) * G1⁻¹ := by
    rw [← hBG]
    group
  rw [hB, map_mul, map_mul, map_mul, (proj_eq_one_iff).mpr (scalarElement_mem_scalars z hz3),
    one_mul, map_inv]

end ProofKS1623Parab

end CFSG.RankThree.PartTwo.Sec16

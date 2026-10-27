module

public import CFSG.LocalAnalysis.StandardType.GGL45TALinRecipe
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.RankThree.PartOne.Q1327C.BU5Diag

public section

namespace CFSG.StandardType.GGL45TG.SU

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

variable {n d : ℕ} {K : Type} [Field K]

private theorem pow_pow_eq_self_of_pow_eq {Q : ℕ} {y : K} (hy : y ^ Q = y) (k : ℕ) :
    y ^ Q ^ k = y := by
  induction k with
  | zero => rw [pow_zero, pow_one]
  | succ k ih => rw [pow_succ, pow_mul, ih, hy]

private theorem two_pow_sq_sub_one (n : ℕ) : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
  rw [← Nat.sq_sub_sq, one_pow]

private theorem pow_two_pow_add_one_of_pElt [Finite K] (h : UnitaryFieldData 2 n K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) {u : Kˣ} (hu : GGL45IsPElt p u) :
    u ^ (2 ^ n + 1) = 1 := by
  obtain ⟨k, hk⟩ := hu
  have h1 : orderOf u ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf u ∣ (2 ^ n + 1) * (2 ^ n - 1) := by
    have := orderOf_dvd_natCard u
    rwa [Nat.card_units, h.card, mul_comm 2 n, pow_mul, two_pow_sq_sub_one] at this
  have hndvd : ¬ p ∣ 2 ^ n - 1 := by
    intro hd
    have h3 : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hpq hd
    have h4 : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
      have := Nat.one_le_two_pow (n := n)
      omega
    rw [h4] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  have hcop : Nat.Coprime (orderOf u) (2 ^ n - 1) :=
    Nat.Coprime.coprime_dvd_left h1
      (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd))
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right h2)

theorem exists_unitary_frame [Finite K] (h : UnitaryFieldData 2 n K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : p ∣ n) (hpq : (p : ℤ) ∣ 2 ^ (n / p) + 1) {τ : K ≃+* K}
    (hτ : ∀ a, τ a = a ^ (2 ^ (n / p)) ^ 2) (L : Set (GL (Fin d) K)) (hL : L.Finite)
    (hcomm : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x)
    (hunit : ∀ x ∈ L,
      ((x : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (x : Matrix (Fin d) (Fin d) K) = 1)
    (hpow : ∀ x ∈ L, x ^ p = 1) (hfix : ∀ x ∈ L, Matrix.GeneralLinearGroup.map τ.toRingHom x = x) :
    ∃ P : GL (Fin d) K, Matrix.GeneralLinearGroup.map τ.toRingHom P = P ∧
      (∀ x ∈ L, ((P * x * P⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag) ∧
      ∀ t : Fin d → Kˣ, ∏ i, t i = 1 → (∀ i, GGL45IsPElt p (t i)) →
        P⁻¹ * GGL45TA.diagGL d t * P ∈ LargeEvenSUGroup (Fin d) K (2 ^ n) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set e := n / p with he
  have hn1 : 1 ≤ n := h.one_le
  have hnpe : n = e * p := (Nat.div_mul_cancel hpn).symm
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, zero_mul] at hnpe; omega
    · exact h0
  have hen : e < n := by
    have : e * 3 ≤ e * p := Nat.mul_le_mul_left e hp3
    omega
  have hmq : p ∣ 2 ^ e + 1 := by exact_mod_cast hpq
  set Q := (2 ^ e) ^ 2 with hQ
  have hτk : ∀ k : ℕ, ∀ a : K, (τ ^ k) a = a ^ Q ^ k := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih => intro a; rw [pow_succ', RingAut.mul_apply, ih, hτ, ← pow_mul, ← pow_succ]
  have hτp : τ ^ p = 1 := by
    ext a
    have hQp : Q ^ p = 2 ^ n * 2 ^ n := by
      rw [hQ, ← pow_mul, ← pow_mul, ← pow_add, hnpe]
      congr 1
      ring
    rw [hτk, hQp, pow_mul, ← h.bar_apply, ← h.bar_apply, h.bar_bar]
    rfl
  have hτ1 : τ ≠ 1 := by
    intro h1
    have := Fintype.ofFinite K
    have hQ1 : 1 < Q := Nat.one_lt_pow two_ne_zero (Nat.one_lt_two_pow (by omega))
    have hroot : ∀ a : K, a ^ Q = a := fun a => by rw [← hτ, h1]; rfl
    have hlt : Q < Fintype.card K := by
      rw [← Nat.card_eq_fintype_card, h.card, hQ, ← pow_mul]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hP := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (Polynomial.X ^ Q - Polynomial.X : Polynomial K) (f := id) Function.injective_id
      (fun a => by simp [hroot a])
      (by rw [FiniteField.X_pow_card_sub_X_natDegree_eq K hQ1]; exact hlt)
    have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K hQ1
    rw [hP, Polynomial.natDegree_zero] at hdeg
    omega
  have hord : orderOf τ = p := orderOf_eq_prime hτp hτ1
  set k₀ := FQ.fixF τ with hk₀
  obtain ⟨-, hcard⟩ := FQ.card_fixedPoints_field (m := 2 * n) (by omega) h.card τ
  rw [hord] at hcard
  have hk₀card : Nat.card k₀ = 2 ^ (2 * e) := by
    rw [FQ.card_fixF, hcard, hnpe, ← mul_assoc, Nat.mul_div_cancel _ hp.pos]
  have h₀ : UnitaryFieldData 2 e k₀ := ⟨Nat.prime_two, he1, hk₀card⟩
  obtain ⟨j, hj⟩ := hp.odd_of_ne_two hp2
  have h2n : 2 ^ n = 2 ^ e * Q ^ j := by
    rw [hQ, ← pow_mul, ← pow_mul, ← pow_add, hnpe, hj]
    congr 1
    ring
  have hbar0 : ∀ c : k₀, ((h₀.bar c : k₀) : K) = h.bar (c : K) := by
    intro c
    have hc : (c : K) ^ Q = c := by rw [← hτ]; exact FQ.mem_fixF.mp c.2
    have hy : ((c : K) ^ 2 ^ e) ^ Q = (c : K) ^ 2 ^ e := by
      rw [← pow_mul, mul_comm (2 ^ e) Q, pow_mul, hc]
    rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, SubmonoidClass.coe_pow, h2n,
      pow_mul, pow_pow_eq_self_of_pow_eq hy]
  set ι : GL (Fin d) k₀ →* GL (Fin d) K := Matrix.GeneralLinearGroup.map k₀.subtype with hι
  have hιinj : Function.Injective ι := FQ.glMap_subtype_injective τ
  have hιmat : ∀ A : GL (Fin d) k₀, ((ι A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (A : Matrix (Fin d) (Fin d) k₀).map k₀.subtype := fun A => rfl
  have hcompbar : (⇑h.bar ∘ ⇑k₀.subtype) = (⇑k₀.subtype ∘ ⇑h₀.bar) :=
    funext fun c => (hbar0 c).symm
  have hunitι : ∀ A : GL (Fin d) k₀,
      (((ι A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
          ((ι A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        (((A : Matrix (Fin d) (Fin d) k₀).map h₀.bar)ᵀ * (A : Matrix (Fin d) (Fin d) k₀)).map
          k₀.subtype := by
    intro A
    rw [hιmat, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_map, hcompbar]
  have hU₀ : ∀ A : GL (Fin d) k₀, A ∈ primeFormUnitary h₀ (idGram k₀ d) ↔
      ((A : Matrix (Fin d) (Fin d) k₀).map h₀.bar)ᵀ * (A : Matrix (Fin d) (Fin d) k₀) = 1 := by
    intro A
    rw [mem_primeFormUnitary, idGram, Units.val_one, Matrix.mul_one]
  have hdesc : ∀ x ∈ L, ∃ A : primeFormUnitary h₀ (idGram k₀ d), ι (A : GL (Fin d) k₀) = x := by
    intro x hx
    obtain ⟨A, hA⟩ := FQ.exists_descend τ x (hfix x hx)
    refine ⟨⟨A, (hU₀ A).mpr ?_⟩, hA⟩
    have h1 : (((A : Matrix (Fin d) (Fin d) k₀).map h₀.bar)ᵀ *
        (A : Matrix (Fin d) (Fin d) k₀)).map k₀.subtype =
        (1 : Matrix (Fin d) (Fin d) k₀).map k₀.subtype := by
      rw [← hunitι, Matrix.map_one _ (map_zero _) (map_one _), show ι A = x from hA]
      exact hunit x hx
    exact Matrix.map_injective k₀.subtype.injective h1
  let S₀ : Set (primeFormUnitary h₀ (idGram k₀ d)) := {A | ι (A : GL (Fin d) k₀) ∈ L}
  have hS₀ : S₀.Pairwise Commute := by
    intro A hA B hB _
    apply Subtype.ext
    apply hιinj
    change ι ((A : GL (Fin d) k₀) * B) = ι ((B : GL (Fin d) k₀) * A)
    rw [map_mul, map_mul]
    exact hcomm _ hA _ hB
  set G : Subgroup (primeFormUnitary h₀ (idGram k₀ d)) := Subgroup.closure S₀ with hG
  have hGcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := by
    intro x hx y hy
    have := isMulCommutative_iff.mp (Subgroup.isMulCommutative_closure hS₀) ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hGpow : ∀ x ∈ G, x ^ p = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      apply Subtype.ext
      apply hιinj
      change ι ((x : GL (Fin d) k₀) ^ p) = ι 1
      rw [map_pow, map_one]
      exact hpow _ hx
    | one => exact one_pow p
    | mul x y hx hy ihx ihy =>
      rw [(show Commute x y from hGcomm x hx y hy).mul_pow, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  haveI : Finite k₀ := h₀.finite
  obtain ⟨ζ₀, hζ₀⟩ := TypeA.exists_isPrimitiveRoot (K := k₀) hp (by
    rw [hk₀card, mul_comm, pow_mul, two_pow_sq_sub_one]
    exact Dvd.dvd.mul_right hmq _)
  obtain ⟨P₀, hP₀⟩ := RankThree.PartOne.Q1327C.exists_unitary_conj_diag_m h₀ hζ₀ hmq G hGcomm
    hGpow
  set B : GL (Fin d) k₀ := (P₀ : GL (Fin d) k₀)⁻¹ with hB
  have hBU : B ∈ primeFormUnitary h₀ (idGram k₀ d) := inv_mem P₀.2
  refine ⟨ι B, FQ.glMap_subtype_fixed τ B, fun x hx => ?_, fun t ht htp => ?_⟩
  · obtain ⟨A, hA⟩ := hdesc x hx
    have hAG : A ∈ G :=
      Subgroup.subset_closure (show ι (A : GL (Fin d) k₀) ∈ L by rw [hA]; exact hx)
    have hdiag := hP₀ A hAG
    have hconj : ι B * x * (ι B)⁻¹ =
        ι ((P₀⁻¹ * A * P₀ : primeFormUnitary h₀ (idGram k₀ d)) : GL (Fin d) k₀) := by
      rw [← hA, hB, ← map_inv, ← map_mul, ← map_mul, inv_inv]
      rfl
    rw [hconj, hιmat]
    intro i j hij
    rw [Matrix.map_apply, hdiag hij, map_zero]
  · have hpq1 : p ∣ 2 ^ n + 1 := by
      have h1 := Odd.nat_add_dvd_pow_add_pow (2 ^ e) 1 (hp.odd_of_ne_two hp2)
      rw [one_pow, ← pow_mul, ← hnpe] at h1
      exact hmq.trans h1
    have htq : ∀ i, t i ^ (2 ^ n + 1) = 1 := fun i =>
      pow_two_pow_add_one_of_pElt h hp hp2 hpq1 (htp i)
    have hPunit : (((ι B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
        ((ι B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [hunitι, (hU₀ B).mp hBU, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [InndiagSU.largeEvenSUGroup_eq_gramSU h]
    have hPU : (ι B)⁻¹ ∈ primeFormUnitary h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      refine inv_mem ?_
      rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one]
      exact hPunit
    have hD : GGL45TA.diagGL d t ∈ gramSU h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      rw [mem_gramSU, Units.val_one, Matrix.mul_one, GGL45TA.coe_diagGL]
      refine ⟨?_, by rw [det_diagonal, ← Units.coe_prod, ht, Units.val_one]⟩
      rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
        ← Matrix.diagonal_one]
      congr 1
      funext i
      rw [UnitaryFieldData.bar_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, htq i, Units.val_one]
    have := conj_mem_gramSU h _ hPU hD
    rwa [inv_inv] at this

private def frameExp (p m a b : ℕ) (s : Fin m → ℕ) : Fin (m + 4) → ℕ :=
  Fin.cons a (Fin.cons a (Fin.cons b (Fin.cons ((p - 1) * (a + a + b + ∑ j, s j)) s)))

private theorem frameExp_zero (p m a b : ℕ) (s : Fin m → ℕ) : frameExp p m a b s 0 = a := by
  simp [frameExp]

private theorem frameExp_one (p m a b : ℕ) (s : Fin m → ℕ) :
    frameExp p m a b s (Fin.succ 0) = a := by
  simp [frameExp]

private theorem frameExp_two (p m a b : ℕ) (s : Fin m → ℕ) :
    frameExp p m a b s (Fin.succ (Fin.succ 0)) = b := by
  simp only [frameExp, Fin.cons_succ, Fin.cons_zero]

private theorem frameExp_succ (p m a b : ℕ) (s : Fin m → ℕ) (j : Fin m) :
    frameExp p m a b s j.succ.succ.succ.succ = s j := by
  simp [frameExp]

private theorem sum_frameExp {p : ℕ} (hp : 1 ≤ p) (m a b : ℕ) (s : Fin m → ℕ) :
    ∑ i, frameExp p m a b s i = p * (a + a + b + ∑ j, s j) := by
  obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, (Nat.sub_add_cancel hp).symm⟩
  simp only [frameExp, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Nat.add_sub_cancel]
  ring

theorem false_of_card_E_le [Finite K] (h : UnitaryFieldData 2 n K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpd : p ∣ d) (hd : 3 ≤ d) (hpq : (p : ℤ) ∣ 2 ^ n + 1) {τ : K ≃+* K}
    (hτp : τ ^ p = 1) {L : Type} [Group L] [Finite L]
    {π : LargeEvenSUGroup (Fin d) K (2 ^ n) →* L} (hπ : Function.Surjective π)
    (hker : ∀ g ∈ π.ker, (g : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K) {ψ : MulAut L}
    (hψ : ∀ a b : LargeEvenSUGroup (Fin d) K (2 ^ n),
      (b : GL (Fin d) K) = Matrix.GeneralLinearGroup.map τ.toRingHom a → ψ (π a) = π b)
    {E : Subgroup (MulAut L)} (hE2 : p ^ 2 ≤ Nat.card E)
    (hrk : ∀ R₀ Q : Subgroup L, IsElemAbelian p R₀ → (∀ r ∈ R₀, ψ r = r) → IsPGroup 2 Q →
      Q ≠ ⊥ → (∀ g ∈ Q, ψ g ∈ Q) → R₀ ≤ Subgroup.normalizer (Q : Set L) →
      Nat.card R₀ * p ≤ Nat.card E * p ^ 2 ∧
        (Nat.Coprime p (Nat.card (Subgroup.center L)) → Nat.card R₀ ≤ Nat.card E))
    (hEdp : Nat.card E ≤ p ^ (d / p)) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : CharP K 2 := h.charP
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpq' : p ∣ 2 ^ n + 1 := by exact_mod_cast hpq
  obtain ⟨e, hde⟩ := hpd
  have hdp : d / p = e := by rw [hde, Nat.mul_div_cancel_left e hp.pos]
  rw [hdp] at hEdp
  have he2 : 2 ≤ e := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hE2.trans hEdp)
  have h3e : 3 * e ≤ p * e := Nat.mul_le_mul_right e hp3
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 4 := ⟨d - 4, by omega⟩
  have hpK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card, mul_comm 2 n, pow_mul, two_pow_sq_sub_one]
    exact Dvd.dvd.mul_right hpq' _
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hpK
  have hζ : IsPrimitiveRoot ζ p := IsPrimitiveRoot.iff_orderOf.mpr hζo
  have hζK : IsPrimitiveRoot (ζ : K) p := IsPrimitiveRoot.coe_units_iff.mpr hζ
  have hroot : ∀ u : Kˣ, u ^ p = 1 → u ^ (2 ^ n + 1) = 1 := by
    intro u hu
    obtain ⟨c, hc⟩ := hpq'
    rw [hc, pow_mul, hu, one_pow]
  have hτfix : ∀ u : Kˣ, u ^ p = 1 → τ (u : K) = u := fun u hu =>
    LinModel.fieldAut_fixes_root hp hζK (k := 1) (by rw [pow_one]; exact hτp)
      (by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one])
  have hSU : ∀ g : GL (Fin (m + 4)) K, g ∈ LargeEvenSUGroup (Fin (m + 4)) K (2 ^ n) ↔
      (g : Matrix (Fin (m + 4)) (Fin (m + 4)) K).det = 1 ∧
        ((g : Matrix (Fin (m + 4)) (Fin (m + 4)) K).map h.bar)ᵀ *
          (g : Matrix (Fin (m + 4)) (Fin (m + 4)) K) = 1 := fun g => by
    rw [InndiagSU.largeEvenSUGroup_eq_gramSU h, mem_gramSU, Units.val_one, Matrix.mul_one,
      and_comm]
  set i₁ : Fin (m + 4) := Fin.succ 0 with hi₁
  set i₂ : Fin (m + 4) := Fin.succ (Fin.succ 0) with hi₂
  let D : Subgroup (Fin (m + 4) → Kˣ) :=
    { carrier := {t | (∀ i, t i ^ p = 1) ∧ t 0 = t i₁ ∧ ∏ i, t i = 1}
      mul_mem' := fun {a b} ha hb => ⟨fun i => by
          rw [Pi.mul_apply, mul_pow, ha.1 i, hb.1 i, one_mul],
        by rw [Pi.mul_apply, Pi.mul_apply, ha.2.1, hb.2.1],
        by rw [show (∏ i, (a * b) i) = ∏ i, a i * b i from rfl, Finset.prod_mul_distrib, ha.2.2,
          hb.2.2, one_mul]⟩
      one_mem' := ⟨fun i => one_pow p, rfl, Finset.prod_const_one⟩
      inv_mem' := fun {a} ha => ⟨fun i => by rw [Pi.inv_apply, inv_pow, ha.1 i, inv_one],
        by rw [Pi.inv_apply, Pi.inv_apply, ha.2.1],
        by rw [show (∏ i, a⁻¹ i) = ∏ i, (a i)⁻¹ from rfl, Finset.prod_inv_distrib, ha.2.2,
          inv_one]⟩ }
  have hDSU : ∀ t : D, GGL45TA.diagGL (m + 4) t.1 ∈ LargeEvenSUGroup (Fin (m + 4)) K (2 ^ n) := by
    intro t
    rw [hSU, GGL45TA.coe_diagGL]
    refine ⟨by rw [det_diagonal, ← Units.coe_prod, t.2.2.2, Units.val_one], ?_⟩
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [UnitaryFieldData.bar_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, hroot _ (t.2.1 i),
      Units.val_one]
  let δ : D →* LargeEvenSUGroup (Fin (m + 4)) K (2 ^ n) :=
    ((GGL45TA.diagGL (m + 4)).comp D.subtype).codRestrict _ hDSU
  have hδ : ∀ t : D, ((δ t : LargeEvenSUGroup (Fin (m + 4)) K (2 ^ n)) : GL (Fin (m + 4)) K) =
      GGL45TA.diagGL (m + 4) t.1 := fun t => rfl
  let ρ : D →* L := π.comp δ
  set R := ρ.range with hR
  set v : Fin (m + 4) → K := Pi.single 0 1 + Pi.single i₁ 1 with hv
  have h01 : (0 : Fin (m + 4)) ≠ i₁ := (Fin.succ_ne_zero 0).symm
  have hv0 : v 0 = 1 := by simp [hv, h01]
  have hv1 : v i₁ = 1 := by simp [hv, h01.symm]
  have hvv : v ⬝ᵥ v = 0 := by
    have : v ⬝ᵥ v = 1 + 1 := by
      simp [hv, h01, h01.symm, dotProduct_add, add_dotProduct]
    rw [this, CharTwo.add_self_eq_zero]
  set N : Matrix (Fin (m + 4)) (Fin (m + 4)) K := vecMulVec v v with hN
  have hNN : N * N = 0 := by
    rw [hN, vecMulVec_mul_vecMulVec, hvv, zero_smul]
    ext i j
    simp [vecMulVec_apply]
  have hN2 : N + N = 0 := by
    ext i j
    rw [Matrix.add_apply, CharTwo.add_self_eq_zero, Matrix.zero_apply]
  have hx₁sq : (1 + N) * (1 + N) = 1 := by
    have : (1 + N) * (1 + N) = 1 + (N + N) + N * N := by noncomm_ring
    rw [this, hN2, hNN, add_zero, add_zero]
  let x₁ : GL (Fin (m + 4)) K := ⟨1 + N, 1 + N, hx₁sq, hx₁sq⟩
  have hvσ : ∀ σ : K →+* K, ∀ i, σ (v i) = v i := by
    intro σ i
    simp only [hv, Pi.add_apply, Pi.single_apply]
    split_ifs <;> simp
  have hx₁σ : ∀ σ : K →+* K, (1 + N).map σ = 1 + N := by
    intro σ
    rw [Matrix.map_add σ (map_add σ), Matrix.map_one σ (map_zero σ) (map_one σ)]
    congr 1
    ext i j
    rw [Matrix.map_apply, hN, vecMulVec_apply, map_mul, hvσ, hvσ]
  have hx₁SU : x₁ ∈ LargeEvenSUGroup (Fin (m + 4)) K (2 ^ n) := by
    rw [hSU]
    refine ⟨?_, ?_⟩
    · show (1 + N).det = 1
      rw [hN, Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow, hvv,
        add_zero]
    · show ((1 + N).map h.bar)ᵀ * (1 + N) = 1
      rw [hx₁σ, Matrix.transpose_add, Matrix.transpose_one, hN, Matrix.transpose_vecMulVec, ← hN,
        hx₁sq]
  let y₁ : LargeEvenSUGroup (Fin (m + 4)) K (2 ^ n) := ⟨x₁, hx₁SU⟩
  set g₁ := π y₁ with hg₁
  have hy₁sq : y₁ ^ 2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, sq, Subgroup.coe_one, Units.val_one]
    exact hx₁sq
  have hg₁sq : g₁ ^ 2 = 1 := by rw [hg₁, ← map_pow, hy₁sq, map_one]
  have hg₁ne : g₁ ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := hker y₁ h1
    have h2 := congrArg
      (fun g : GL (Fin (m + 4)) K => (g : Matrix (Fin (m + 4)) (Fin (m + 4)) K) 0 i₁) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_ne _ h01] at h2
    have h3 : ((y₁ : GL (Fin (m + 4)) K) : Matrix (Fin (m + 4)) (Fin (m + 4)) K) 0 i₁ = 1 := by
      show (1 + N) 0 i₁ = 1
      rw [Matrix.add_apply, Matrix.one_apply_ne h01, zero_add, hN, vecMulVec_apply, hv0, hv1,
        mul_one]
    rw [h3] at h2
    exact zero_ne_one h2
  have hψg₁ : ψ g₁ = g₁ := by
    refine hψ y₁ y₁ (Units.ext ?_)
    rw [YS09Field.coe_glMap]
    exact (hx₁σ τ.toRingHom).symm
  set Q := Subgroup.zpowers g₁ with hQ
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, pow_one]; exact orderOf_eq_prime hg₁sq hg₁ne)
  have hQne : Q ≠ ⊥ := fun hb => hg₁ne (Subgroup.zpowers_eq_bot.mp hb)
  have hQψ : ∀ g ∈ Q, ψ g ∈ Q := by
    rintro g ⟨k, rfl⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [map_zpow, hψg₁]⟩
  have hDcomm : ∀ a b : D, a * b = b * a := fun a b => Subtype.ext (mul_comm _ _)
  have hRelem : IsElemAbelian p R := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul, hDcomm]
    · obtain ⟨a, rfl⟩ := hx
      rw [← map_pow]
      have : a ^ p = 1 := Subtype.ext (funext fun i => by
        rw [Subgroup.coe_pow, Pi.pow_apply]; exact a.2.1 i)
      rw [this, map_one]
  have hRψ : ∀ r ∈ R, ψ r = r := by
    rintro _ ⟨a, rfl⟩
    refine hψ (δ a) (δ a) ?_
    rw [hδ, GGL45TA.map_diagGL]
    congr 1
    funext i
    exact Units.ext (hτfix _ (a.2.1 i)).symm
  have hvt : ∀ t : D, ∀ r, v r ≠ 0 → t.1 r = t.1 0 := by
    intro t r hr
    by_cases h0 : r = 0
    · rw [h0]
    · by_cases h1 : r = i₁
      · rw [h1, t.2.2.1]
      · exfalso
        apply hr
        simp [hv, h0, h1]
  have hcommx : ∀ t : D,
      GGL45TA.diagGL (m + 4) t.1 * x₁ = x₁ * GGL45TA.diagGL (m + 4) t.1 := by
    intro t
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, GGL45TA.coe_diagGL]
    show diagonal (fun i => (t.1 i : K)) * (1 + N) = (1 + N) * diagonal (fun i => (t.1 i : K))
    rw [mul_add, add_mul, mul_one, one_mul]
    congr 1
    ext r s
    rw [diagonal_mul, mul_diagonal, hN, vecMulVec_apply]
    by_cases hr : v r = 0
    · rw [hr]; ring
    · by_cases hs : v s = 0
      · rw [hs]; ring
      · rw [hvt t r hr, hvt t s hs]; ring
  have hRnorm : R ≤ Subgroup.normalizer (Q : Set L) := by
    rintro _ ⟨a, rfl⟩
    have hc : Commute (ρ a) g₁ := by
      change π (δ a) * π y₁ = π y₁ * π (δ a)
      rw [← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext (hcommx a))
    have hcg : ∀ k : ℤ, ρ a * g₁ ^ k * (ρ a)⁻¹ = g₁ ^ k := fun k => by
      rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, (hcg k).symm⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have hk' : g₁ ^ k = ρ a * g * (ρ a)⁻¹ := hk
      have h1 : (ρ a)⁻¹ * g₁ ^ k * ρ a = g := by rw [hk']; group
      have h2 : (ρ a)⁻¹ * g₁ ^ k * ρ a = g₁ ^ k := by
        rw [mul_assoc, ← (hc.zpow_right k).eq, ← mul_assoc, inv_mul_cancel, one_mul]
      exact h2.symm.trans h1
  obtain ⟨hrk1, hrk2⟩ := hrk R Q hRelem hRψ hQ2 hQne hQψ hRnorm
  have hζpow : ∀ k : ℕ, (ζ ^ k) ^ p = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hvecD : ∀ (a b : ℕ) (s : Fin m → ℕ), (fun i => ζ ^ frameExp p m a b s i) ∈ D := by
    intro a b s
    refine ⟨fun i => hζpow _, ?_, ?_⟩
    · show ζ ^ frameExp p m a b s 0 = ζ ^ frameExp p m a b s i₁
      rw [frameExp_zero, hi₁, frameExp_one]
    · show ∏ i, ζ ^ frameExp p m a b s i = 1
      rw [Finset.prod_pow_eq_pow_sum, sum_frameExp hp.one_le, pow_mul, hζ.pow_eq_one, one_pow]
  have hvecinj : ∀ (a b a' b' : ℕ) (s s' : Fin m → ℕ), a < p → b < p → (∀ j, s j < p) →
      a' < p → b' < p → (∀ j, s' j < p) →
      (∀ i, ζ ^ frameExp p m a b s i = ζ ^ frameExp p m a' b' s' i) →
        a = a' ∧ b = b' ∧ s = s' := by
    intro a b a' b' s s' ha hb hs ha' hb' hs' hall
    refine ⟨hζ.pow_inj ha ha' ?_, hζ.pow_inj hb hb' ?_,
      funext fun j => hζ.pow_inj (hs j) (hs' j) ?_⟩
    · have := hall 0
      rwa [frameExp_zero, frameExp_zero] at this
    · have := hall (Fin.succ (Fin.succ 0))
      rwa [frameExp_two, frameExp_two] at this
    · have := hall j.succ.succ.succ.succ
      rwa [frameExp_succ, frameExp_succ] at this
  have hkerD : ∀ w : D, ρ w = 1 → ∃ c : Kˣ, ∀ i, w.1 i = c := by
    intro w hw
    obtain ⟨c, hc⟩ := hker (δ w) hw
    refine ⟨c, fun i => Units.ext ?_⟩
    have h3 := congrArg
      (fun g : GL (Fin (m + 4)) K => (g : Matrix (Fin (m + 4)) (Fin (m + 4)) K) i i) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq, hδ,
      GGL45TA.coe_diagGL] at h3
    exact h3.symm
  have hρinj : ∀ t t' : D, ρ t = ρ t' → t.1 i₂ = t'.1 i₂ → t = t' := by
    intro t t' htt h2
    have h1 : ρ (t * t'⁻¹) = 1 := by rw [map_mul, map_inv, htt, mul_inv_cancel]
    obtain ⟨c, hc⟩ := hkerD _ h1
    have hc1 : c = 1 := by
      rw [← hc i₂]
      exact mul_inv_eq_one.mpr h2
    apply Subtype.ext
    funext i
    have := hc i
    rw [hc1] at this
    exact mul_inv_eq_one.mp this
  have hlow1 : p ^ (m + 1) ≤ Nat.card R := by
    let F : Fin p × (Fin m → Fin p) → R := fun x =>
      ⟨ρ ⟨_, hvecD x.1 0 (fun j => x.2 j)⟩, ⟨_, rfl⟩⟩
    have hF : Function.Injective F := by
      rintro ⟨a, s⟩ ⟨a', s'⟩ hFF
      have h1 := hρinj _ _ (congrArg Subtype.val hFF) (by
        show ζ ^ frameExp p m a 0 (fun j => s j) i₂ = ζ ^ frameExp p m a' 0 (fun j => s' j) i₂
        rw [hi₂, frameExp_two, frameExp_two])
      have hall := fun i => congrFun (congrArg Subtype.val h1) i
      obtain ⟨ha, -, hs⟩ := hvecinj a 0 a' 0 (fun j => s j) (fun j => s' j) a.2 hp.pos
        (fun j => (s j).2) a'.2 hp.pos (fun j => (s' j).2) hall
      exact Prod.ext (Fin.ext ha) (funext fun j => Fin.ext (congrFun hs j))
    have := Nat.card_le_card_of_injective F hF
    rwa [Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_fin, ← pow_succ'] at this
  have hw₀D : (fun _ : Fin (m + 4) => ζ) ∈ D := by
    refine ⟨fun _ => hζ.pow_eq_one, rfl, ?_⟩
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hde, pow_mul, hζ.pow_eq_one,
      one_pow]
  let w₀ : D := ⟨_, hw₀D⟩
  have hw₀p : w₀ ^ p = 1 := Subtype.ext (funext fun _ => hζ.pow_eq_one)
  by_cases ha : ρ w₀ = 1
  ·
    by_cases hcop : Nat.Coprime p (Nat.card (Subgroup.center L))
    ·
      have h1 : p ^ (m + 1) ≤ p ^ e := hlow1.trans ((hrk2 hcop).trans hEdp)
      have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
      omega
    ·
      have hdvdZ : p ∣ Nat.card (Subgroup.center L) := by
        by_contra hnd
        exact hcop ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
      obtain ⟨z, hzo⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center L) p hdvdZ
      obtain ⟨y, hy⟩ := hπ (z : L)
      have hperf : Group.IsPerfect (LargeEvenSUGroup (Fin (m + 4)) K (2 ^ n)) :=
        ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := n) h.card_eq_sq (by omega)
          (fun hq => absurd (congrArg Prod.fst hq) (by simp))
      have hkerC : π.ker ≤ Subgroup.center (LargeEvenSUGroup (Fin (m + 4)) K (2 ^ n)) :=
        fun g hg => FQ.scalars_subgroupOf_le_center _ (hker g hg)
      have hconj := RankThree.PartOne.S15K.eq_of_perfect_of_map_eq π hkerC hperf
        (MulAut.conj y).toMonoidHom (MonoidHom.id _) (fun u => by
          rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply, map_mul, map_mul,
            map_inv, hy, (Subgroup.mem_center_iff.mp z.2 (π u)).symm, mul_inv_cancel_right])
      have hycomm : ∀ g ∈ unitarySU 2 n K (m + 4), (y : GL (Fin (m + 4)) K) * g = g * y := by
        intro g hg
        have h1 : (y : GL (Fin (m + 4)) K) * g * (y : GL (Fin (m + 4)) K)⁻¹ = g :=
          congrArg Subtype.val (hconj ⟨g, hg⟩)
        calc (y : GL (Fin (m + 4)) K) * g =
            (y : GL (Fin (m + 4)) K) * g * (y : GL (Fin (m + 4)) K)⁻¹ * y := by group
          _ = g * y := by rw [h1]
      obtain ⟨c, hc⟩ := TableBUE.mem_scalars_of_commute h hp hpq' hycomm
      have hcd : c ^ (m + 4) = 1 := by
        have hdet := ((hSU _).mp y.2).1
        rw [← hc, InndiagSU.det_coe_scalar] at hdet
        exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
      have hce : (c ^ e) ^ p = 1 := by rw [← pow_mul, mul_comm, ← hde, hcd]
      obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p (c ^ e)).mpr hce)
      have hye : y ^ e = δ w₀ ^ j := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_pow, ← hc, hδ, ← map_pow, ← map_pow]
        apply Units.ext
        rw [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, GGL45TA.coe_diagGL]
        congr 1
        funext i
        rw [← hj]
        rfl
      have hze : (z : L) ^ e = 1 := by
        rw [← hy, ← map_pow, hye, map_pow]
        change ρ w₀ ^ j = 1
        rw [ha, one_pow]
      have hpe : p ∣ e := by
        rw [← hzo, ← Subgroup.orderOf_coe]
        exact orderOf_dvd_of_pow_eq_one hze
      have hpe' : p ≤ e := Nat.le_of_dvd (by omega) hpe
      have h1 : p ^ (m + 2) ≤ p ^ (e + 2) := by
        calc p ^ (m + 2) = p ^ (m + 1) * p := pow_succ _ _
          _ ≤ Nat.card R * p := Nat.mul_le_mul_right p hlow1
          _ ≤ Nat.card E * p ^ 2 := hrk1
          _ ≤ p ^ e * p ^ 2 := Nat.mul_le_mul_right _ hEdp
          _ = p ^ (e + 2) := (pow_add _ _ _).symm
      have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
      omega
  ·
    have hord : orderOf (ρ w₀) = p := orderOf_eq_prime (by rw [← map_pow, hw₀p, map_one]) ha
    have hρtriv : ∀ w : D, ρ w = 1 → w = 1 := by
      intro w hw
      obtain ⟨c, hc⟩ := hkerD w hw
      have hcp : c ^ p = 1 := by rw [← hc 0]; exact w.2.1 0
      obtain ⟨k, hk, hck⟩ := hζ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p c).mpr hcp)
      have hw' : w = w₀ ^ k := Subtype.ext (funext fun i => by rw [hc i, ← hck]; rfl)
      rw [hw', map_pow] at hw
      have hpk : p ∣ k := by rw [← hord]; exact orderOf_dvd_of_pow_eq_one hw
      rw [hw', Nat.eq_zero_of_dvd_of_lt hpk hk, pow_zero]
    have hlow2 : p ^ (m + 2) ≤ Nat.card R := by
      let F : Fin p × Fin p × (Fin m → Fin p) → R := fun x =>
        ⟨ρ ⟨_, hvecD x.1 x.2.1 (fun j => x.2.2 j)⟩, ⟨_, rfl⟩⟩
      have hF : Function.Injective F := by
        rintro ⟨a, b, s⟩ ⟨a', b', s'⟩ hFF
        have h1 : ρ ((⟨_, hvecD a b (fun j => s j)⟩ : D) *
            (⟨_, hvecD a' b' (fun j => s' j)⟩ : D)⁻¹) = 1 := by
          rw [map_mul, map_inv, mul_inv_eq_one]
          exact congrArg Subtype.val hFF
        have h2 := mul_inv_eq_one.mp (hρtriv _ h1)
        have hall := fun i => congrFun (congrArg Subtype.val h2) i
        obtain ⟨ha, hb, hs⟩ := hvecinj a b a' b' (fun j => s j) (fun j => s' j) a.2 b.2
          (fun j => (s j).2) a'.2 b'.2 (fun j => (s' j).2) hall
        exact Prod.ext (Fin.ext ha)
          (Prod.ext (Fin.ext hb) (funext fun j => Fin.ext (congrFun hs j)))
      have := Nat.card_le_card_of_injective F hF
      rwa [Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_fin, ← pow_succ',
        ← pow_succ'] at this
    have h1 : p ^ (m + 3) ≤ p ^ (e + 2) := by
      calc p ^ (m + 3) = p ^ (m + 2) * p := pow_succ _ _
        _ ≤ Nat.card R * p := Nat.mul_le_mul_right p hlow2
        _ ≤ Nat.card E * p ^ 2 := hrk1
        _ ≤ p ^ e * p ^ 2 := Nat.mul_le_mul_right _ hEdp
        _ = p ^ (e + 2) := (pow_add _ _ _).symm
    have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
    omega

end CFSG.StandardType.GGL45TG.SU

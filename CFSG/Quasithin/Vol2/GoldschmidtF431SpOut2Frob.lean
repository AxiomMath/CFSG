module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bCent
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpModel
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisAutClass

public section

namespace CFSG.Quasithin.H13.F431

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin.H13.F431.SpModel
  CFSG.QuasithinUnique CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

namespace SpOut2

section Frob

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem frobAut_pow_uElt (k : ℕ) (a b c d : F) :
    (frobAut F ^ k) (uElt a b c d) = uElt (a ^ 2 ^ k) (b ^ 2 ^ k) (c ^ 2 ^ k) (d ^ 2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, frobAut_uElt]
    simp only [← pow_mul, ← pow_succ]

theorem mat_frobAut_pow (k : ℕ) (g : antiSp F) :
    mat ((frobAut F ^ k) g) = (mat g).map fun x => x ^ 2 ^ k := by
  induction k generalizing g with
  | zero => ext i j; simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, mat_frobAut, ih]
    ext i j
    simp only [Matrix.map_apply, ← pow_mul, ← pow_succ]

theorem frobAut_pow_mem_antiUnipotent_iff (k : ℕ) (x : antiSp F) :
    (frobAut F ^ k) x ∈ antiUnipotent F ↔ x ∈ antiUnipotent F := by
  have hsurj : ∀ y : F, ∃ z : F, z ^ 2 ^ k = y := by
    intro y
    have hinj : Function.Injective (iterateFrobenius F 2 k) := (iterateFrobenius F 2 k).injective
    obtain ⟨z, hz⟩ := Finite.injective_iff_surjective.mp hinj y
    exact ⟨z, by simpa [iterateFrobenius_def] using hz⟩
  constructor
  · rintro ⟨a, b, c, d, h⟩
    obtain ⟨a', ha⟩ := hsurj a
    obtain ⟨b', hb⟩ := hsurj b
    obtain ⟨c', hc⟩ := hsurj c
    obtain ⟨d', hd⟩ := hsurj d
    have : (frobAut F ^ k) x = (frobAut F ^ k) (uElt a' b' c' d') := by
      rw [h, frobAut_pow_uElt, ha, hb, hc, hd]
    exact ⟨a', b', c', d', (frobAut F ^ k).injective this⟩
  · rintro ⟨a, b, c, d, rfl⟩
    exact ⟨_, _, _, _, frobAut_pow_uElt k a b c d⟩

theorem frobAut_pow_iRep (k : ℕ) (j : Fin 3) : (frobAut F ^ k) (iRep F j) = iRep F j := by
  fin_cases j
  · show (frobAut F ^ k) (uElt 0 1 0 0) = uElt 0 1 0 0
    rw [frobAut_pow_uElt]
    simp
  · show (frobAut F ^ k) (uElt 0 0 1 0) = uElt 0 0 1 0
    rw [frobAut_pow_uElt]
    simp
  · show (frobAut F ^ k) (uElt 0 1 1 0) = uElt 0 1 1 0
    rw [frobAut_pow_uElt]
    simp

theorem frobAut_pow_card {n : ℕ} (hF : Nat.card F = 2 ^ n) : frobAut F ^ n = 1 := by
  refine MulEquiv.ext fun g => ?_
  apply mat_ext
  rw [mat_frobAut_pow]
  ext i j
  simp only [Matrix.map_apply]
  have : Fintype F := Fintype.ofFinite F
  have h := FiniteField.pow_card (mat g i j)
  rw [← Nat.card_eq_fintype_card, hF] at h
  exact h

theorem frobAut_pow_eq_one_iff {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) (k : ℕ) :
    frobAut F ^ k = 1 ↔ n ∣ k := by
  constructor
  · intro h
    have hr : frobAut F ^ (k % n) = 1 := by
      have e : frobAut F ^ k = (frobAut F ^ n) ^ (k / n) * frobAut F ^ (k % n) := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
      rw [e, frobAut_pow_card hF, one_pow, one_mul] at h
      exact h
    have := conj_mul_frobAut_pow_inj (K := F) hn hF (g := 1) (g' := 1) (k := 0) (k' := k % n)
      hn (Nat.mod_lt _ hn) (by rw [hr, pow_zero])
    exact Nat.dvd_of_mod_eq_zero this.2.symm
  · rintro ⟨c, rfl⟩
    rw [pow_mul, frobAut_pow_card hF, one_pow]

theorem conj_eq_frobAut_pow {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) {g : antiSp F}
    {k : ℕ} (h : MulAut.conj g = frobAut F ^ k) : g = 1 := by
  have hr : frobAut F ^ (k % n) = MulAut.conj g := by
    have e : frobAut F ^ k = (frobAut F ^ n) ^ (k / n) * frobAut F ^ (k % n) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [e, frobAut_pow_card hF, one_pow, one_mul] at h
    exact h.symm
  have := conj_mul_frobAut_pow_inj (K := F) hn hF (g := g) (g' := 1) (k := 0) (k' := k % n)
    hn (Nat.mod_lt _ hn) (by rw [pow_zero, mul_one, hr]; simp)
  exact this.1

section Fields

theorem card_sq_le_of_ne_top {K : Type} [Field K] [Finite K] (k : Subfield K) (hk : k ≠ ⊤) :
    Nat.card k ^ 2 ≤ Nat.card K := by
  have h1 : Nat.card K = Nat.card k ^ Module.finrank k K := Module.natCard_eq_pow_finrank
  have h2 : Module.finrank k K ≠ 1 := by
    intro h
    apply hk
    rw [finrank_eq_one_iff'] at h
    obtain ⟨v, hv, hall⟩ := h
    rw [eq_top_iff]
    intro x _
    obtain ⟨c, hc⟩ := hall x
    obtain ⟨c1, hc1⟩ := hall 1
    have hv' : (v : K) ≠ 0 := hv
    have hc1' : (c1 : K) * v = 1 := hc1
    have hc' : (c : K) * v = x := hc
    have : x = (c : K) * (c1 : K)⁻¹ := by
      have hc10 : (c1 : K) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hc1'
        exact zero_ne_one hc1'
      field_simp
      have : (v : K) = (c1 : K)⁻¹ := by
        field_simp
        linear_combination hc1'
      rw [← hc', this]
      field_simp
    rw [this]
    exact k.mul_mem c.2 (k.inv_mem c1.2)
  have h3 : Module.finrank k K ≠ 0 := Module.finrank_pos.ne'
  have h4 : 2 ≤ Module.finrank k K := by omega
  rw [h1]
  exact Nat.pow_le_pow_right Nat.card_pos h4

omit [Finite F] [CharP F 2] in
theorem card_descentField_frob {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card F = 2 ^ (2 * m)) :
    ∃ σ : F ≃+* F, (∀ x, σ x = x ^ 2 ^ m) ∧ σ ≠ 1 ∧ σ * σ = 1 ∧
      Nat.card (descentField σ) = 2 ^ m := by
  obtain ⟨Fr, hFr, hord, hzp⟩ := exists_frobenius_data (K := F) (by omega) hK
  have hpow : ∀ k : ℕ, ∀ x, (Fr ^ k) x = x ^ 2 ^ k := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, RingAut.mul_apply, hFr, ih, ← pow_mul, pow_succ, mul_comm]
  set σ : F ≃+* F := Fr ^ m with hσdef
  have hσ1 : σ ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  have hσσ : σ * σ = 1 := by
    rw [hσdef, ← pow_add, ← two_mul]
    have := pow_orderOf_eq_one Fr
    rwa [hord] at this
  have haa : fieldAut 2 F σ * fieldAut 2 F σ = 1 := by rw [← map_mul, hσσ, map_one]
  obtain ⟨-, -, hcard, -⟩ := even_symplectic_quadratic_involution_descent (r := 2) (f := 2 * m)
    (by norm_num) (by omega) hK (a := fieldAut 2 F σ) haa 1 σ
    (by change fieldAut 2 F σ = spInner 2 F 1 * fieldAut 2 F σ; rw [map_one, one_mul]) hσ1
  refine ⟨σ, hpow m, hσ1, hσσ, ?_⟩
  rw [hcard]
  congr 1
  omega

omit [Finite F] [CharP F 2] in
theorem exists_fixed_ne {σ : F ≃+* F} {m : ℕ} (hm : 2 ≤ m)
    (hcard : Nat.card (descentField σ) = 2 ^ m) :
    ∃ t : F, σ t = t ∧ t ≠ 0 ∧ t ≠ 1 := by
  by_contra hcon
  have hsub : ∀ t : descentField σ, (t : F) = 0 ∨ (t : F) = 1 := by
    intro t
    by_contra h
    push Not at h
    exact hcon ⟨t, mem_descentField.mp t.2, h.1, h.2⟩
  have hle : Nat.card (descentField σ) ≤ 2 := by
    classical
    have : Function.Injective
        (fun t : descentField σ => if (t : F) = 0 then (0 : Fin 2) else 1) := by
      intro a b hab
      apply Subtype.ext
      rcases hsub a with ha | ha <;> rcases hsub b with hb | hb
      · rw [ha, hb]
      · simp [ha, hb] at hab
      · simp [ha, hb] at hab
      · rw [ha, hb]
    have := Nat.card_le_card_of_injective _ this
    simpa using this
  rw [hcard] at hle
  have : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

end Fields

section Fixed

variable {m : ℕ}

theorem twoPart_fixedSubgroup_frob (hm : 1 ≤ m) (hK : Nat.card F = 2 ^ (2 * m)) :
    twoPart (fixedSubgroup (frobAut F ^ m)) = 2 ^ (4 * m) := by
  obtain ⟨k, hcp, lift, hcard, hinj, hrange⟩ := exists_even_fixed (K := F) hm hK
  have e1 : Nat.card (fixedSubgroup (minorAut F ^ (2 * m))) = Nat.card (antiSp k) := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [frobAut_pow_eq]
  obtain ⟨hU, hS⟩ := card_and_isSylowTwoOf_antiUnipotent (K := k)
  have h2 := hS.card_eq
  unfold twoPart at h2 ⊢
  rw [Subgroup.card_top] at h2
  rw [e1, ← h2, hU, hcard, ← pow_mul, show m * 4 = 4 * m by ring]

theorem card_U0_ge (hm : 1 ≤ m) (hK : Nat.card F = 2 ^ (2 * m)) :
    2 ^ (4 * m) ≤
      Nat.card (antiUnipotent F ⊓ fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F)) := by
  obtain ⟨σ, hσ, -, -, hcard⟩ := card_descentField_frob (F := F) hm hK
  let f : descentField σ × descentField σ × descentField σ × descentField σ →
      ↥(antiUnipotent F ⊓ fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F)) :=
    fun p => ⟨uElt (p.1 : F) (p.2.1 : F) (p.2.2.1 : F) (p.2.2.2 : F), ⟨_, _, _, _, rfl⟩, by
      show (frobAut F ^ m) (uElt (p.1 : F) (p.2.1 : F) (p.2.2.1 : F) (p.2.2.2 : F)) =
        uElt (p.1 : F) (p.2.1 : F) (p.2.2.1 : F) (p.2.2.2 : F)
      rw [frobAut_pow_uElt]
      have h1 : ∀ x : descentField σ, (x : F) ^ 2 ^ m = x := fun x => by
        rw [← hσ, coe_descentField_fixed]
      rw [h1, h1, h1, h1]⟩
  have hf : Function.Injective f := by
    intro p q h
    have := uElt_inj (congrArg Subtype.val h)
    obtain ⟨h1, h2, h3, h4⟩ := this
    exact Prod.ext (Subtype.ext h1) (Prod.ext (Subtype.ext h2)
      (Prod.ext (Subtype.ext h3) (Subtype.ext h4)))
  have := Nat.card_le_card_of_injective f hf
  simp only [Nat.card_prod, hcard] at this
  rw [show 2 ^ (4 * m) = 2 ^ m * (2 ^ m * (2 ^ m * 2 ^ m)) by ring]
  exact this

end Fixed

end Frob

end SpOut2

end CFSG.Quasithin.H13.F431

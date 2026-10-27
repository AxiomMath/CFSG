module

public import CFSG.RankThree.PartTwo.KFacts.K71SU3AutFacts

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open Matrix

section Diagonal

variable {K : Type} [Field K]

theorem offDiag_eq_zero_of_commute_diagonal {M : Matrix (Fin 3) (Fin 3) K} {a : Fin 3 → K}
    (ha : ∀ i j, i ≠ j → a i ≠ a j) (h : M * diagonal a = diagonal a * M) {i j : Fin 3}
    (hij : i ≠ j) : M i j = 0 := by
  have h1 := congrArg (fun X : Matrix (Fin 3) (Fin 3) K => X i j) h
  simp only [mul_diagonal, diagonal_mul] at h1
  have h2 : M i j * (a j - a i) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.mp h3).symm (ha i j hij)

theorem exists_eq_of_mul_diagonal_eq {g : GL (Fin 3) K} {a b : Fin 3 → K}
    (h : (g : Matrix (Fin 3) (Fin 3) K) * diagonal a = diagonal b * g) (j : Fin 3) :
    ∃ i, a j = b i := by
  by_contra hcon
  have hcol : ∀ i, (g : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    intro i
    have h1 := congrArg (fun X : Matrix (Fin 3) (Fin 3) K => X i j) h
    simp only [mul_diagonal, diagonal_mul] at h1
    have h2 : (g : Matrix (Fin 3) (Fin 3) K) i j * (a j - b i) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd ⟨i, sub_eq_zero.mp h3⟩ hcon
  have h1 := congrArg (fun X : Matrix (Fin 3) (Fin 3) K => X j j) (Units.inv_mul g)
  simp only [Matrix.mul_apply, hcol, mul_zero, Finset.sum_const_zero, one_apply_eq] at h1
  exact zero_ne_one h1

theorem eq_or_eq_or_eq_of_mul_diagonal_eq {g : GL (Fin 3) K} {a b : Fin 3 → K}
    (h : (g : Matrix (Fin 3) (Fin 3) K) * diagonal a = diagonal b * g) (j : Fin 3) :
    a j = b 0 ∨ a j = b 1 ∨ a j = b 2 := by
  obtain ⟨i, hi⟩ := exists_eq_of_mul_diagonal_eq h j
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)

theorem vec3_injective {α : Type*} {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ i j : Fin 3, i ≠ j → (![a, b, c] : Fin 3 → α) i ≠ ![a, b, c] j := by
  have hba := hab.symm
  have hca := hac.symm
  have hcb := hbc.symm
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem pow_nine_eq_one_of_diagonal (h : UnitaryFieldData 2 3 K) {g : GL (Fin 3) K}
    (hu : ((g : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * g = 1)
    (hg : ∀ i j, i ≠ j → (g : Matrix (Fin 3) (Fin 3) K) i j = 0) : g ^ 9 = 1 := by
  have hMd : (g : Matrix (Fin 3) (Fin 3) K) =
      diagonal (fun i => (g : Matrix (Fin 3) (Fin 3) K) i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
    · rw [hg i j hij, diagonal_apply_ne _ hij]
  have hentry : ∀ i, (g : Matrix (Fin 3) (Fin 3) K) i i ^ 9 = 1 := by
    intro i
    have h1 := congrArg (fun X : Matrix (Fin 3) (Fin 3) K => X i i) hu
    rw [hMd] at h1
    simp only [diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
      diagonal_apply_eq, one_apply_eq, h.bar_apply] at h1
    calc (g : Matrix (Fin 3) (Fin 3) K) i i ^ 9 =
        (g : Matrix (Fin 3) (Fin 3) K) i i ^ 2 ^ 3 * (g : Matrix (Fin 3) (Fin 3) K) i i := by
          ring
      _ = 1 := h1
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hMd, diagonal_pow, Units.val_one, ← diagonal_one]
  congr 1
  funext i
  exact hentry i

theorem exists_orderOf_eq_nine (h : UnitaryFieldData 2 3 K) : ∃ μ : Kˣ, orderOf μ = 9 := by
  have := h.finite
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcard : Nat.card Kˣ = 63 := by
    rw [Nat.card_units, h.card]
    norm_num
  have hog : orderOf g = 63 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  refine ⟨g ^ 7, ?_⟩
  rw [orderOf_pow_of_dvd (by norm_num) (by rw [hog]; norm_num), hog]

end Diagonal

section Torus

variable {K : Type} [Field K]

theorem eq_bot_of_commute_conj_diagonal (h : UnitaryFieldData 2 3 K) {D : unitarySU 2 3 K 3}
    {d e : Fin 3 → K} (hD : ((D : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d)
    (hde : ∀ i, d i * e i = 1) (hd : ∀ i k, i ≠ k → d k * e i + d i * e k = 1)
    {N : Subgroup (MulAut (unitarySU 2 3 K 3))}
    (hNc : ∀ ν ∈ N, ν * MulAut.conj D = MulAut.conj D * ν) (hN3 : ¬ 3 ∣ Nat.card N)
    (hNn : ∀ ℓ, MulAut.conj D ℓ = ℓ → ∀ ν ∈ N, MulAut.conj ℓ * ν * (MulAut.conj ℓ)⁻¹ ∈ N) :
    N = ⊥ := by
  have := h.finite
  have : CharP K 2 := h.charP
  have hq : 2 < 2 ^ 3 := by norm_num
  have hdist : ∀ i k, i ≠ k → d i ≠ d k := by
    intro i k hik hdd
    have h1 := hd i k hik
    have h2 := hde i
    have h3 := hde k
    rw [hdd] at h1 h2
    rw [h2, h3, CharTwo.add_self_eq_zero] at h1
    exact zero_ne_one h1
  have hfixdiag : ∀ ℓ : unitarySU 2 3 K 3, MulAut.conj D ℓ = ℓ →
      ∀ i j, i ≠ j → ((ℓ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    intro ℓ hℓ i j hij
    have h1 : D * ℓ = ℓ * D := by
      rw [MulAut.conj_apply] at hℓ
      calc D * ℓ = D * ℓ * D⁻¹ * D := by group
        _ = ℓ * D := by rw [hℓ]
    have h2 := congrArg (fun x : unitarySU 2 3 K 3 =>
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h1
    simp only [Subgroup.coe_mul, Units.val_mul, hD] at h2
    exact offDiag_eq_zero_of_commute_diagonal hdist h2.symm hij
  have hfix9 : ∀ ℓ : unitarySU 2 3 K 3, MulAut.conj D ℓ = ℓ → ℓ ^ 9 = 1 := by
    intro ℓ hℓ
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact pow_nine_eq_one_of_diagonal h ((mem_unitarySU_iff h).mp ℓ.2).2 (hfixdiag ℓ hℓ)
  have hcommD : ∀ (ℓ : unitarySU 2 3 K 3) (x : Fin 3 → K),
      ((ℓ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal x → MulAut.conj D ℓ = ℓ := by
    intro ℓ x hx
    have h1 : D * ℓ = ℓ * D := by
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul, hD, hx, diagonal_mul_diagonal, mul_comm]
    rw [MulAut.conj_apply, h1, mul_inv_cancel_right]
  have hkey : ∀ ν ∈ N, ∀ ℓ : unitarySU 2 3 K 3, MulAut.conj D ℓ = ℓ →
      ∃ c : Kˣ, c ^ 3 = 1 ∧
        ((ν ℓ : unitarySU 2 3 K 3) : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c * ℓ := by
    intro ν hν ℓ hℓ
    have hνℓ : MulAut.conj D (ν ℓ) = ν ℓ := apply_apply_eq_of_commute (hNc ν hν) hℓ
    have hfix : MulAut.conj D (ℓ * (ν ℓ)⁻¹) = ℓ * (ν ℓ)⁻¹ := by
      rw [map_mul, map_inv, hℓ, hνℓ]
    have hmem := conj_mul_inv_apply_mem hν (hNn ℓ hℓ)
    have h1 : MulAut.conj (ℓ * (ν ℓ)⁻¹) = 1 := by
      refine eq_one_of_pow_three_pow_eq_one hN3 hmem (k := 2) ?_
      rw [← map_pow, show (3 : ℕ) ^ 2 = 9 by norm_num, hfix9 _ hfix, map_one]
    obtain ⟨c, hc3, hc⟩ := exists_scalar_of_conj_eq_one h hq h1
    refine ⟨c⁻¹, by rw [inv_pow, hc3, inv_one], ?_⟩
    have h2 : (ℓ : GL (Fin 3) K) * ((ν ℓ : unitarySU 2 3 K 3) : GL (Fin 3) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) c := by
      rw [← hc, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [map_inv, ← h2]
    group
  obtain ⟨μ, hμ⟩ := exists_orderOf_eq_nine h
  have hμ9 : μ ^ 9 = 1 := by rw [← hμ]; exact pow_orderOf_eq_one μ
  have hμ9' : μ ^ (2 ^ 3 + 1) = 1 := hμ9
  have hm9 : (μ : K) ^ 9 = 1 := by rw [← Units.val_pow_eq_pow_val, hμ9, Units.val_one]
  have hm3 : (μ : K) ^ 3 ≠ 1 := fun h1 => by
    have h2 : μ ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h1, Units.val_one])
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hμ] at this
    norm_num at this
  have hm0 : (μ : K) ≠ 0 := μ.ne_zero
  have hinv9 : ∀ x : Kˣ, x ^ (2 ^ 3 + 1) = 1 → x⁻¹ ^ (2 ^ 3 + 1) = 1 := fun x hx => by
    rw [inv_pow, hx, inv_one]
  have hℓ₁mem : diag3 μ μ⁻¹ 1 ∈ unitarySU 2 3 K 3 :=
    diag3_mem_unitarySU h hμ9' (hinv9 μ hμ9') (one_pow _) (by group)
  have hℓ₂mem : diag3 μ μ (μ⁻¹ * μ⁻¹) ∈ unitarySU 2 3 K 3 :=
    diag3_mem_unitarySU h hμ9' hμ9' (by rw [mul_pow, hinv9 μ hμ9', one_mul]) (by group)
  set ℓ₁ : unitarySU 2 3 K 3 := ⟨_, hℓ₁mem⟩ with hℓ₁
  set ℓ₂ : unitarySU 2 3 K 3 := ⟨_, hℓ₂mem⟩ with hℓ₂
  have hℓ₁fix : MulAut.conj D ℓ₁ = ℓ₁ := hcommD ℓ₁ _ (coe_diag3 _ _ _)
  have hℓ₂fix : MulAut.conj D ℓ₂ = ℓ₂ := hcommD ℓ₂ _ (coe_diag3 _ _ _)
  rw [eq_bot_iff]
  intro ν hν
  rw [Subgroup.mem_bot]
  obtain ⟨B, δ, rfl⟩ := exists_suConj_mul_suField h hq ν
  have hνn : (suConj h B * suField h δ) ^ Nat.card N = 1 := by
    have h1 := pow_card_eq_one' (G := N) (x := ⟨_, hν⟩)
    exact congrArg Subtype.val h1
  have hδ2 : δ ^ 2 = 1 := sq_eq_one_of_pow_eq_one h hN3
    (pow_eq_one_of_suConj_mul_suField_pow_eq_one h hq hνn)
  have hmat : ∀ (ℓ : unitarySU 2 3 K 3) (x : Fin 3 → K),
      ((ℓ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal x → ∀ c : Kˣ,
      (((suConj h B * suField h δ) ℓ : unitarySU 2 3 K 3) : GL (Fin 3) K) =
        GeneralLinearGroup.scalar (Fin 3) c * ℓ →
      ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal (fun i => δ (x i)) =
        diagonal (fun i => (c : K) * x i) * ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro ℓ x hx c hc
    rw [MulAut.mul_apply, coe_suConj, coe_suField] at hc
    have h1 : (B : GL (Fin 3) K) * glAut δ (ℓ : GL (Fin 3) K) =
        GeneralLinearGroup.scalar (Fin 3) c * (ℓ : GL (Fin 3) K) * (B : GL (Fin 3) K) := by
      rw [← hc, Subgroup.coe_inv, inv_mul_cancel_right]
    have h2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h1
    simp only [Units.val_mul, coe_glAut, hx, diagonal_map (map_zero δ),
      GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_mul_diagonal] at h2
    exact h2
  obtain ⟨c₁, hc₁3, hc₁⟩ := hkey _ hν ℓ₁ hℓ₁fix
  have hmat₁ := hmat ℓ₁ _ (coe_diag3 _ _ _) c₁ hc₁
  have hc₁3' : (c₁ : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc₁3, Units.val_one]
  have hc₁1 : (c₁ : K) = 1 := by
    rcases eq_or_eq_or_eq_of_mul_diagonal_eq hmat₁ 2 with hi | hi | hi <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Units.val_one, map_one,
        Units.val_inv_eq_inv_val] at hi
    · exfalso
      apply hm3
      have h1 : ((c₁ : K) * μ) ^ 3 = 1 := by rw [← hi, one_pow]
      rw [mul_pow, hc₁3', one_mul] at h1
      exact h1
    · exfalso
      apply hm3
      have h1 : (c₁ : K) = μ := by
        calc (c₁ : K) = (c₁ : K) * (μ : K)⁻¹ * μ := by field_simp
          _ = μ := by rw [← hi, one_mul]
      rw [← h1, hc₁3']
    · rw [mul_one] at hi
      exact hi.symm
  have hδμ : δ μ = μ ∨ δ μ = (μ : K)⁻¹ := by
    rcases eq_or_eq_or_eq_of_mul_diagonal_eq hmat₁ 0 with hi | hi | hi <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Units.val_one, Units.val_inv_eq_inv_val, hc₁1,
        one_mul] at hi
    · exact Or.inl hi
    · exact Or.inr hi
    · exfalso
      apply hm3
      have h1 : (μ : K) = 1 := δ.injective (hi.trans (map_one δ).symm)
      rw [h1, one_pow]
  obtain ⟨c₂, hc₂3, hc₂⟩ := hkey _ hν ℓ₂ hℓ₂fix
  have hmat₂ := hmat ℓ₂ _ (coe_diag3 _ _ _) c₂ hc₂
  have hc₂3' : (c₂ : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc₂3, Units.val_one]
  have hδμ' : δ μ = μ := by
    rcases hδμ with h1 | h1
    · exact h1
    · exfalso
      apply hm3
      have h6 : (c₂ : K) * (μ : K) ^ 2 = 1 → (μ : K) ^ 3 = 1 := fun h2 => by
        have h3 : (μ : K) ^ 6 = 1 := by
          have h4 := congrArg (· ^ 3) h2
          simp only [mul_pow, hc₂3', one_mul, one_pow, ← pow_mul] at h4
          exact h4
        have h4 : (μ : K) ^ 9 = (μ : K) ^ 6 * (μ : K) ^ 3 := by ring
        rw [hm9, h3, one_mul] at h4
        exact h4.symm
      rcases eq_or_eq_or_eq_of_mul_diagonal_eq hmat₂ 0 with hi | hi | hi <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, Units.val_mul, Units.val_inv_eq_inv_val,
          h1] at hi
      ·
        exact h6 (by rw [sq, ← mul_assoc, ← hi, inv_mul_cancel₀ hm0])
      · exact h6 (by rw [sq, ← mul_assoc, ← hi, inv_mul_cancel₀ hm0])
      ·
        have h2 : (c₂ : K) = μ := by
          calc (c₂ : K) = (c₂ : K) * ((μ : K)⁻¹ * (μ : K)⁻¹) * ((μ : K) * μ) := by field_simp
            _ = (μ : K)⁻¹ * ((μ : K) * μ) := by rw [← hi]
            _ = μ := by field_simp
        rw [← h2, hc₂3']
  have hδ1 : δ = 1 := by
    rcases eq_one_or_apply_eq_pow_of_sq_eq_one h hδ2 with h1 | h1
    · exact h1
    · exfalso
      apply hm3
      have h2 := h1 μ
      rw [hδμ'] at h2
      have h3 : (μ : K) ^ 2 = 1 := by
        have h4 : (μ : K) ^ 9 = (μ : K) ^ 2 ^ 3 * μ := by ring
        rw [← h2, hm9] at h4
        rw [sq]
        exact h4.symm
      have h4 : (μ : K) ^ 9 = ((μ : K) ^ 2) ^ 4 * μ := by ring
      rw [hm9, h3, one_pow, one_mul] at h4
      rw [← h4, one_pow]
  subst hδ1
  rw [map_one, mul_one]
  rw [map_one, mul_one] at hν
  have hone : ∀ y : K, (1 : K ≃+* K) y = y := fun y => rfl
  simp only [hone, hc₁1, one_mul, Units.val_inv_eq_inv_val, Units.val_one] at hmat₁
  have hμ1 : (μ : K) ≠ 1 := fun h1 => hm3 (by rw [h1, one_pow])
  have hμi : (μ : K) ≠ (μ : K)⁻¹ := fun h1 => hm3 (by
    have h2 : (μ : K) ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [h1]; exact mul_inv_cancel₀ hm0
    have h4 : (μ : K) ^ 9 = ((μ : K) ^ 2) ^ 4 * μ := by ring
    rw [hm9, h2, one_pow, one_mul] at h4
    rw [← h4, one_pow])
  have hi1 : (μ : K)⁻¹ ≠ 1 := fun h1 => hμ1 (by rw [← inv_inv (μ : K), h1, inv_one])
  have hmdist := vec3_injective hμi hμ1 hi1
  have hBoff := fun i j (hij : i ≠ j) => offDiag_eq_zero_of_commute_diagonal hmdist hmat₁ hij
  have hB9 : (B : GL (Fin 3) K) ^ 9 = 1 := pow_nine_eq_one_of_diagonal h B.2 hBoff
  have hB9' : B ^ 9 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hB9)
  refine eq_one_of_pow_three_pow_eq_one hN3 hν (k := 2) ?_
  rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← map_pow, hB9', map_one]

theorem eq_bot_of_commute_conj (h : UnitaryFieldData 2 3 K) {u : unitarySU 2 3 K 3}
    (hu3 : u ^ 3 = 1) (hus : ∀ c : K, ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ c • 1)
    {N : Subgroup (MulAut (unitarySU 2 3 K 3))}
    (hNc : ∀ ν ∈ N, ν * MulAut.conj u = MulAut.conj u * ν) (hN3 : ¬ 3 ∣ Nat.card N)
    (hNn : ∀ ℓ, MulAut.conj u ℓ = ℓ → ∀ ν ∈ N, MulAut.conj ℓ * ν * (MulAut.conj ℓ)⁻¹ ∈ N) :
    N = ⊥ := by
  have hPi : PiField false 2 3 K := ⟨Nat.prime_two, by norm_num, by rw [h.card]; rfl⟩
  have hq3 : ModThree false (2 ^ 3) := by
    show 2 ^ 3 % 3 = 2
    norm_num
  have hu3' : (u : GL (Fin 3) K) ^ 3 = 1 := by
    have := congrArg Subtype.val hu3
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  obtain ⟨g, d, e, hg, hug, hde, hd⟩ := exists_unitary_diagonal hPi hq3 u.2 hu3' hus
  set G₀ : unitaryIsom3 h := ⟨g, (mem_glPi_false h).1 hg⟩ with hG₀
  set D : unitarySU 2 3 K 3 := suConj h G₀⁻¹ u with hDdef
  have hD : ((D : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d := by
    have h1 : (D : GL (Fin 3) K) = g⁻¹ * (u : GL (Fin 3) K) * g := by
      rw [hDdef, coe_suConj]
      simp only [Subgroup.coe_inv, inv_inv, hG₀]
    rw [h1, Units.val_mul, Units.val_mul, mul_assoc, hug, ← mul_assoc, Units.inv_mul,
      Matrix.one_mul]
  have hu : u = suConj h G₀ D := by
    rw [hDdef, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hε : MulAut.conj u = suConj h G₀ * MulAut.conj D * (suConj h G₀)⁻¹ := by
    rw [mul_conj_mul_inv, ← hu]
  exact eq_bot_of_conj hε (fun N₀ hc h3 hn => eq_bot_of_commute_conj_diagonal h hD hde hd hc h3 hn)
    hNc hN3 hNn

end Torus

end CFSG.RankThree.PartTwo.KFacts

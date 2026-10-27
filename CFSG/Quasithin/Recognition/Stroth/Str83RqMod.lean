module

public import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Small

public section

namespace CFSG.Quasithin.Stroth.Rq

open Matrix Polynomial CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups Polynomial

private theorem eq_one_of_mulVec_eq_self {K : Type*} [Field K] [CharP K 2] {g : SL(2, K)}
    {v : Fin 2 → K} (hv : v ≠ 0) (hgv : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v) {m : ℕ}
    (hm : Odd m) (hgm : g ^ m = 1) : g = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set M : Matrix (Fin 2) (Fin 2) K := (g : Matrix (Fin 2) (Fin 2) K) with hMdef
  have hdet : M.det = 1 := g.2
  obtain ⟨p, q, r, s, hM⟩ : ∃ p q r s : K, M = !![p, q; r, s] :=
    ⟨M 0 0, M 0 1, M 1 0, M 1 1, Matrix.eta_fin_two M⟩
  rw [hM, Matrix.det_fin_two_of] at hdet
  have e0 := congrFun hgv 0
  have e1 := congrFun hgv 1
  rw [hM] at e0 e1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e0 e1
  have hbr : (p - 1) * (s - 1) - q * r = 0 := by
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := fun h => hv (funext fun i => by fin_cases i <;> simp [hv0, h])
      have : ((p - 1) * (s - 1) - q * r) * v 1 = 0 := by
        linear_combination (-r) * e0 + (p - 1) * e1
      exact (mul_eq_zero.mp this).resolve_right hv1
    · have : ((p - 1) * (s - 1) - q * r) * v 0 = 0 := by
        linear_combination (s - 1) * e0 - q * e1
      exact (mul_eq_zero.mp this).resolve_right hv0
  have hps : p + s = 0 := by linear_combination -hbr + hdet + h2
  have hgg : g * g = 1 := by
    apply Subtype.ext
    change M * M = 1
    rw [hM, Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination p * hps - hdet - h2
    · linear_combination q * hps
    · linear_combination r * hps
    · linear_combination s * hps - hdet - h2
  obtain ⟨k, rfl⟩ := hm
  have hk : g ^ (2 * k + 1) = g := by rw [pow_succ, pow_mul, sq, hgg, one_pow, one_mul]
  rw [← hk, hgm]

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

private theorem eq_one_of_mulVec_eq_smul (hodd : Odd (Fintype.card F + 1)) {g : SL(2, F)}
    (hg : g ^ (Fintype.card F + 1) = 1) {v : Fin 2 → F} (hv : v ≠ 0) {μ : F}
    (hgv : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v = μ • v) : g = 1 := by
  have hpow : ∀ k : ℕ, ((g ^ k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hgv,
        Matrix.mulVec_smul, ih, smul_smul, pow_succ']
  have hv1 : v = μ ^ (Fintype.card F + 1) • v := by
    rw [← hpow, hg, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hμ1 : μ ^ (Fintype.card F + 1) = 1 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    have hvi := congrFun hv1 i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hvi hi
    have : (μ ^ (Fintype.card F + 1) - 1) * v i = 0 := by linear_combination -hvi
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hi)
  have hμ : μ = 1 := by
    rw [pow_succ, FiniteField.pow_card] at hμ1
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have : (μ - 1) * (μ - 1) = 0 := by linear_combination hμ1 + (1 - μ) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp this)
  subst hμ
  exact eq_one_of_mulVec_eq_self hv (by rw [hgv, one_smul]) hodd hg

private theorem exists_eigen_of_det_eq_zero {K : Type*} [Field K]
    {g X k : Matrix (Fin 2) (Fin 2) K} (hX : X ≠ 0) (hdet : X.det = 0) (hgX : g * X = X * k) :
    ∃ v : Fin 2 → K, v ≠ 0 ∧ ∃ μ : K, g *ᵥ v = μ • v := by
  obtain ⟨e, he⟩ : ∃ e : Fin 2 → K, X *ᵥ e ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hX
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one] using this
  set f := k *ᵥ e with hf
  set c := X *ᵥ e with hc
  set d := X *ᵥ f with hd
  have hgc : g *ᵥ c = d := by
    rw [hc, hd, hf, Matrix.mulVec_mulVec, hgX, ← Matrix.mulVec_mulVec]
  have hcross : c 0 * d 1 = c 1 * d 0 := by
    rw [Matrix.det_fin_two] at hdet
    simp only [hc, hd, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination (e 0 * f 1 - e 1 * f 0) * hdet
  have key : ∀ μ : K, (∀ j, d j = μ * c j) →
      ∃ v : Fin 2 → K, v ≠ 0 ∧ ∃ μ : K, g *ᵥ v = μ • v :=
    fun μ h => ⟨c, he, μ, by rw [hgc]; ext j; simp [h j]⟩
  by_cases hc0 : c 0 = 0
  · have hc1 : c 1 ≠ 0 := fun hc1 => he (by ext i; fin_cases i <;> simp [hc0, hc1])
    refine key (d 1 / c 1) fun j => ?_
    fin_cases j
    · rw [hc0, zero_mul] at hcross
      simp only [Fin.zero_eta, Fin.isValue, hc0, mul_zero]
      exact (mul_eq_zero.mp hcross.symm).resolve_left hc1
    · simp only [Fin.mk_one, Fin.isValue]
      field_simp
  · refine key (d 0 / c 0) fun j => ?_
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue]
      field_simp
    · simp only [Fin.mk_one, Fin.isValue]
      field_simp
      linear_combination hcross

private theorem trace_eq_of_mul_mul_eq {K : Type*} [Field K] {g X h : Matrix (Fin 2) (Fin 2) K}
    (hX : X.det ≠ 0) (hh : h.det = 1) (hgXh : g * X * h = X) : g.trace = h.trace := by
  have h1 : X.adjugate * g * X = X.det • h.adjugate := by
    calc X.adjugate * g * X = X.adjugate * g * X * (h * h.adjugate) := by
          rw [Matrix.mul_adjugate, hh, one_smul, Matrix.mul_one]
      _ = X.adjugate * (g * X * h) * h.adjugate := by simp only [Matrix.mul_assoc]
      _ = X.det • h.adjugate := by
          rw [hgXh, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have h2 := congrArg Matrix.trace h1
  rw [Matrix.trace_mul_cycle, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul] at h2
  have h3 : h.adjugate.trace = h.trace := by
    rw [Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.trace_fin_two]
    simp [add_comm]
  rw [h3] at h2
  exact mul_left_cancel₀ hX h2

private theorem exists_eigen_of_root {K : Type*} [Field K] [CharP K 2] {g : SL(2, K)} {x : K}
    (hx : x ^ 2 + (g : Matrix (Fin 2) (Fin 2) K).trace * x + 1 = 0) :
    ∃ v : Fin 2 → K, v ≠ 0 ∧ (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v = x • v := by
  have hdet : ((g : Matrix (Fin 2) (Fin 2) K) - x • 1).det = 0 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hg : (g : Matrix (Fin 2) (Fin 2) K).det = 1 := g.2
    rw [Matrix.det_fin_two] at hg ⊢
    rw [Matrix.trace_fin_two] at hx
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), mul_zero, sub_zero]
    linear_combination hx + hg -
      ((g : Matrix (Fin 2) (Fin 2) K) 0 0 + (g : Matrix (Fin 2) (Fin 2) K) 1 1) * x * h2
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hv0
  exact sub_eq_zero.mp hv0

private theorem exists_quadratic_root {l : ℕ} (hF : Fintype.card F = 2 ^ (2 * l)) {τ : F}
    (hτ : τ ^ 2 ^ l = τ) : ∃ x : F, x ^ 2 + τ * x + 1 = 0 := by
  classical
  by_contra hno
  have hno' : ∀ x : F, x ^ 2 + τ * x + 1 ≠ 0 := fun x hx => hno ⟨x, hx⟩
  set p : F[X] := X ^ 2 + C τ * X + 1 with hp
  have hpdeg : p.natDegree = 2 := by rw [hp]; compute_degree!
  have hpmon : p.Monic := by rw [hp]; monicity!
  have hroots : p.roots = 0 := by
    refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
    rw [Polynomial.mem_roots hpmon.ne_zero, Polynomial.IsRoot, hp] at hx
    apply hno' x
    simpa using hx
  have hirr : Irreducible p :=
    (hpmon.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)).mpr hroots
  haveI : Fact (Irreducible p) := ⟨hirr⟩
  have hinj : Function.Injective (algebraMap F (AdjoinRoot p)) := (algebraMap F _).injective
  haveI : CharP (AdjoinRoot p) 2 := charP_of_injective_algebraMap hinj 2
  set α : AdjoinRoot p := AdjoinRoot.root p with hαdef
  set t : AdjoinRoot p := algebraMap F (AdjoinRoot p) τ with htdef
  have h2 : (2 : AdjoinRoot p) = 0 := CharTwo.two_eq_zero
  have hα : α ^ 2 + t * α + 1 = 0 := by
    have h : Polynomial.eval₂ (AdjoinRoot.of p) (AdjoinRoot.root p)
        (X ^ 2 + C τ * X + 1 : F[X]) = 0 := AdjoinRoot.eval₂_root p
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_one] at h
    rw [hαdef, htdef, AdjoinRoot.algebraMap_eq]
    exact h
  have ht : t ^ 2 ^ l = t := by rw [htdef, ← map_pow, hτ]
  have hβ : (α ^ 2 ^ l) ^ 2 + t * α ^ 2 ^ l + 1 = 0 := by
    have h := congrArg (fun y => y ^ 2 ^ l) hα
    simp only [add_pow_char_pow, mul_pow, one_pow, ht] at h
    rw [zero_pow (pow_ne_zero _ two_ne_zero)] at h
    rw [← h]
    ring
  have hkey : α ^ 2 ^ l = α ∨ α ^ 2 ^ l = α + t := by
    have h : (α ^ 2 ^ l - α) * (α ^ 2 ^ l + α + t) = 0 := by linear_combination hβ - hα
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · right
      linear_combination h - (α + t) * h2
  have hfix : α ^ Fintype.card F = α := by
    rw [hF, two_mul, pow_add, pow_mul]
    rcases hkey with h | h
    · rw [h, h]
    · rw [h, add_pow_char_pow, h, ht]
      linear_combination t * h2
  obtain ⟨x, hx⟩ : ∃ x : F, algebraMap F (AdjoinRoot p) x = α := by
    have hq : 1 < Fintype.card F := Fintype.one_lt_card
    set P : (AdjoinRoot p)[X] := X ^ Fintype.card F - X with hP
    have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hq
    have hPdeg : P.natDegree = Fintype.card F := FiniteField.X_pow_card_sub_X_natDegree_eq _ hq
    have hmem : ∀ y : AdjoinRoot p, y ^ Fintype.card F = y → y ∈ P.roots.toFinset := by
      intro y hy
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot, hP]
      simp [hy]
    have hsub : Finset.univ.image (algebraMap F (AdjoinRoot p)) ⊆ P.roots.toFinset := by
      intro y hy
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hy
      exact hmem _ (by rw [← map_pow, FiniteField.pow_card])
    have hcard : P.roots.toFinset.card ≤ (Finset.univ.image (algebraMap F (AdjoinRoot p))).card := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
      exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' P).trans hPdeg.le)
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have hαmem := hmem α hfix
    rw [← heq] at hαmem
    obtain ⟨z, -, hz⟩ := Finset.mem_image.mp hαmem
    exact ⟨z, hz⟩
  apply hno' x
  apply hinj
  rw [map_add, map_add, map_pow, map_mul, map_one, map_zero, hx]
  exact hα

private theorem eq_zero_of_twist_fixed {l : ℕ} (hF : Fintype.card F = 2 ^ (2 * l))
    (hodd : Odd (Fintype.card F + 1)) {g : SL(2, F)} (hg1 : g ≠ 1)
    (hg : g ^ (Fintype.card F + 1) = 1) {X : Matrix (Fin 2) (Fin 2) F}
    (hX : (g : Matrix (Fin 2) (Fin 2) F) * X * (frobPow l (g : Matrix (Fin 2) (Fin 2) F))ᵀ = X) :
    X = 0 := by
  set h := (frobPow l (g : Matrix (Fin 2) (Fin 2) F))ᵀ with hh
  have hdeth : h.det = 1 := by
    rw [hh, Matrix.det_transpose, frobPow_eq_map, ← RingHom.map_det, g.2, map_one]
  by_contra hX0
  by_cases hdet : X.det = 0
  · have hgX : (g : Matrix (Fin 2) (Fin 2) F) * X = X * h.adjugate := by
      calc (g : Matrix (Fin 2) (Fin 2) F) * X
          = (g : Matrix (Fin 2) (Fin 2) F) * X * (h * h.adjugate) := by
            rw [Matrix.mul_adjugate, hdeth, one_smul, Matrix.mul_one]
        _ = X * h.adjugate := by rw [← Matrix.mul_assoc, hX]
    obtain ⟨v, hv, μ, hgv⟩ := exists_eigen_of_det_eq_zero hX0 hdet hgX
    exact hg1 (eq_one_of_mulVec_eq_smul hodd hg hv hgv)
  · have htr := trace_eq_of_mul_mul_eq hdet hdeth hX
    have htrh : h.trace = (g : Matrix (Fin 2) (Fin 2) F).trace ^ 2 ^ l := by
      rw [hh, Matrix.trace_transpose, frobPow_eq_map, Matrix.trace_fin_two, Matrix.trace_fin_two,
        RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, ← map_add, sig_apply]
    obtain ⟨x, hx⟩ := exists_quadratic_root hF (htrh ▸ htr).symm
    obtain ⟨v, hv, hgv⟩ := exists_eigen_of_root hx
    exact hg1 (eq_one_of_mulVec_eq_smul hodd hg hv hgv)

private def uHom : Multiplicative F →* SL(2, F) where
  toFun t := ⟨!![1, Multiplicative.toAdd t; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  map_one' := by
    apply Subtype.ext
    simp [Matrix.one_fin_two]
  map_mul' s t := by
    apply Subtype.ext
    change !![1, Multiplicative.toAdd (s * t); 0, 1] =
      !![1, Multiplicative.toAdd s; 0, 1] * !![1, Multiplicative.toAdd t; 0, 1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem uHom_injective : Function.Injective (uHom (F := F)) := by
  intro s t hst
  have h := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 1) hst
  change Multiplicative.toAdd s = Multiplicative.toAdd t at h
  exact Multiplicative.toAdd.injective h

private theorem natCard_range_uHom : Nat.card (uHom (F := F)).range = Fintype.card F := by
  rw [← Nat.card_congr (MonoidHom.ofInjective uHom_injective).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card]

private theorem mul_self_of_mem_range_uHom {a : SL(2, F)} (ha : a ∈ (uHom (F := F)).range) :
    a * a = 1 := by
  obtain ⟨t, rfl⟩ := ha
  rw [← map_mul, ← map_one uHom]
  congr 1
  apply Multiplicative.toAdd.injective
  simp [CharTwo.add_self_eq_zero]

theorem eq_zero_of_fixed_of_pow_two_pow_succ {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) SL(2, F) W) (hirr : ρ.IsIrreducible)
    (hW : Nat.card W = 2 ^ (2 * n)) {g : SL(2, F)} (hg1 : g ≠ 1) (hg : g ^ (2 ^ n + 1) = 1)
    {w : W} (hw : ρ g w = w) : w = 0 := by
  haveI : Fact ρ.IsIrreducible := ⟨hirr⟩
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · have h1 := Fintype.one_lt_card (α := F)
      rw [hF, h] at h1
      simp at h1
    · exact h
  rw [← hF] at hg
  have hodd : Odd (Fintype.card F + 1) := by
    rw [hF]
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hnt : ∃ g, ρ g ≠ 1 := by
    by_contra h
    simp only [not_exists, not_not] at h
    obtain ⟨φ, -⟩ := isTrivialLine_of_trivial ρ hirr h
    have h2 : Nat.card W = 2 := by rw [Nat.card_congr φ.toEquiv, Nat.card_zmod]
    rw [hW] at h2
    have h3 : 2 ^ (2 * n) = 2 ^ 1 := by simpa using h2
    have := Nat.pow_right_injective (le_refl 2) h3
    omega
  have hlt : Nat.card W < 2 ^ (4 * n) := by
    rw [hW]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  rcases CFSG.RankThree.GF2n.Tim81.Sec2.isNaturalModule_or_isOrthModule_or_of_card_lt hn hF ρ hnt
      (uHom (F := F)).range (fun a ha => mul_self_of_mem_range_uHom ha)
      (natCard_range_uHom.trans hF) hlt with
    hnat | ⟨l, hl, -, horth⟩ | ⟨l, hnl, hWl, -⟩
  · obtain ⟨φ, hφ⟩ := hnat
    by_contra hw0
    have hv : φ w ≠ 0 := fun h => hw0 (φ.injective (h.trans φ.map_zero.symm))
    have hgv : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ φ w = (1 : F) • φ w := by
      rw [one_smul, ← hφ, hw]
    exact hg1 (eq_one_of_mulVec_eq_smul hodd hg hv hgv)
  · obtain ⟨j, β, hβ⟩ := horth
    have hinj : Function.Injective (fieldAut F j) := by
      intro a b hab
      ext i k
      have h := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) i k) hab
      simp only [fieldAut_apply] at h
      exact (iterateFrobenius F 2 j).injective (by simpa [iterateFrobenius_def] using h)
    have hg'1 : fieldAut F j g ≠ 1 := fun h => hg1 (hinj (h.trans (map_one _).symm))
    have hg' : fieldAut F j g ^ (Fintype.card F + 1) = 1 := by rw [← map_pow, hg, map_one]
    have hfix : (fieldAut F j g : Matrix (Fin 2) (Fin 2) F) * (β w : Matrix (Fin 2) (Fin 2) F) *
        (frobPow l (fieldAut F j g : Matrix (Fin 2) (Fin 2) F))ᵀ = (β w : Matrix (Fin 2) (Fin 2) F) := by
      rw [← hermAct_coe l (sig_sig hl), ← hβ, hw]
    have h0 : β w = 0 := Subtype.ext (eq_zero_of_twist_fixed hl hodd hg'1 hg' hfix)
    exact β.injective (h0.trans β.map_zero.symm)
  · rw [hW] at hWl
    have := Nat.pow_right_injective (le_refl 2) hWl
    omega

end CFSG.Quasithin.Stroth.Rq

end

module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSp4Q8
import CFSG.RankThree.Classical.SpIsometry

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCSpFull CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

namespace SpSeitz

variable {r : ℕ} {K : Type} [Field K]

section Eig

variable {a b : StatedSp r K} (hAA : ∀ v, spEnd a (spEnd a v) = -v)

include hAA in
theorem form_adj (z w : Fin r ⊕ Fin r → K) :
    spForm r K (spEnd a z) w = -spForm r K z (spEnd a w) := by
  rw [← spEnd_isometry a, hAA, map_neg, LinearMap.neg_apply]

theorem form_eig_eq_zero (h2K : (2 : K) ≠ 0) {l : K} (hl : l * l = -1)
    {x y : Fin r ⊕ Fin r → K} (hx : spEnd a x = l • x) (hy : spEnd a y = l • y) :
    spForm r K x y = 0 := by
  have h := spEnd_isometry a x y
  rw [hx, hy, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    hl] at h
  have : 2 * spForm r K x y = 0 := by linear_combination -h
  exact (mul_eq_zero.1 this).resolve_left h2K

variable {i : K} (hi : i * i = -1)

include hAA hi in
theorem eig_one (z : Fin r ⊕ Fin r → K) :
    spEnd a ((2 : K)⁻¹ • (z - i • spEnd a z)) = i • ((2 : K)⁻¹ • (z - i • spEnd a z)) := by
  rw [map_smul, map_sub, map_smul, hAA]
  linear_combination (norm := module) ((2 : K)⁻¹) • hi • spEnd a z

include hAA hi in
theorem eig_two (z : Fin r ⊕ Fin r → K) :
    spEnd a ((2 : K)⁻¹ • (z + i • spEnd a z)) = -i • ((2 : K)⁻¹ • (z + i • spEnd a z)) := by
  rw [map_smul, map_add, map_smul, hAA]
  linear_combination (norm := module) ((2 : K)⁻¹) • hi • spEnd a z

theorem eig_decomp (h2K : (2 : K) ≠ 0) (z : Fin r ⊕ Fin r → K) :
    z = (2 : K)⁻¹ • (z - i • spEnd a z) + (2 : K)⁻¹ • (z + i • spEnd a z) := by
  have : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2K
  linear_combination (norm := module) (-1 : K) • this • z

end Eig

section Basis

variable {a b : StatedSp 2 K} (hAA : ∀ v, spEnd a (spEnd a v) = -v)
  (hBB : ∀ v, spEnd b (spEnd b v) = -v)
  (hBA : ∀ v, spEnd b (spEnd a v) = -(spEnd a (spEnd b v)))
  {i : K} (hi : i * i = -1)

include hBA in
theorem eig_b {l : K} {x : Fin 2 ⊕ Fin 2 → K} (hx : spEnd a x = l • x) :
    spEnd a (spEnd b x) = -l • spEnd b x := by
  have h := hBA x
  rw [hx, map_smul] at h
  rw [neg_smul, h, neg_neg]

include hAA hBB hBA hi in
theorem exists_compl_eig (h2K : (2 : K) ≠ 0) {x : Fin 2 ⊕ Fin 2 → K} (hx : spEnd a x = i • x) :
    ∃ x' : Fin 2 ⊕ Fin 2 → K, spEnd a x' = i • x' ∧ x' ≠ 0 ∧
      spForm 2 K x' (spEnd b x) = 0 := by
  classical
  set A := spEnd a with hAdef
  set B := spEnd b with hBdef
  have hsw : ∀ x y : Fin 2 ⊕ Fin 2 → K, spForm 2 K y x = -spForm 2 K x y := spForm_swap
  have adjA := form_adj hAA
  have adjB := form_adj hBB
  set W₁ : Submodule K (Fin 2 ⊕ Fin 2 → K) :=
    (spForm 2 K).orthogonal (Submodule.span K {x, B x}) with hW₁
  have hmem : ∀ w, w ∈ W₁ ↔ spForm 2 K x w = 0 ∧ spForm 2 K (B x) w = 0 := by
    intro w
    rw [hW₁, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      exact ⟨h x (Submodule.subset_span (by simp)), h (B x) (Submodule.subset_span (by simp))⟩
    · rintro ⟨h1, h2⟩ n hn
      obtain ⟨c₁, d₁, rfl⟩ := Submodule.mem_span_pair.1 hn
      change spForm 2 K (c₁ • x + d₁ • B x) w = 0
      rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, h1, h2, smul_zero, smul_zero, add_zero]
  have hBx : A (B x) = -i • B x := eig_b hBA hx
  have hW₁a : ∀ w ∈ W₁, A w ∈ W₁ := by
    intro w hw
    obtain ⟨h1, h2⟩ := (hmem w).1 hw
    refine (hmem _).2 ⟨?_, ?_⟩
    · have := adjA x w
      rw [hx, map_smul, LinearMap.smul_apply, h1, smul_zero] at this
      exact neg_eq_zero.1 this.symm
    · have := adjA (B x) w
      rw [hBx, map_smul, LinearMap.smul_apply, h2, smul_zero] at this
      exact neg_eq_zero.1 this.symm
  have hW₁b : ∀ w ∈ W₁, B w ∈ W₁ := by
    intro w hw
    obtain ⟨h1, h2⟩ := (hmem w).1 hw
    refine (hmem _).2 ⟨?_, ?_⟩
    · have := adjB x w
      rw [h2] at this
      exact neg_eq_zero.1 this.symm
    · rw [spEnd_isometry b, h1]
  have hW₁0 : W₁ ≠ ⊥ := by
    intro h
    have hf := LinearMap.BilinForm.finrank_orthogonal (spForm_nondegenerate (r := 2) (K := K))
      (Submodule.span K {x, B x})
    rw [← hW₁, h, finrank_bot] at hf
    have hle : Module.finrank K (Submodule.span K ({x, B x} : Set (Fin 2 ⊕ Fin 2 → K))) ≤ 2 := by
      have := finrank_span_finset_le_card (R := K) ({x, B x} : Finset (Fin 2 ⊕ Fin 2 → K))
      rw [Finset.coe_insert, Finset.coe_singleton] at this
      exact this.trans Finset.card_le_two
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at hf
    omega
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW₁0
  set w₁ := (2 : K)⁻¹ • (w - i • A w) with hw₁
  have hw₁W : w₁ ∈ W₁ := W₁.smul_mem _ (W₁.sub_mem hwW (W₁.smul_mem _ (hW₁a w hwW)))
  by_cases h0 : w₁ = 0
  · have hdec := eig_decomp (a := a) (i := i) h2K w
    rw [← hAdef, ← hw₁, h0, zero_add] at hdec
    have hAw : A w = -i • w := by
      conv_lhs => rw [hdec]
      rw [eig_two hAA hi w, ← hdec]
    refine ⟨B w, ?_, ?_, ?_⟩
    · rw [eig_b hBA hAw, neg_neg]
    · intro h
      have := hBB w
      rw [h, map_zero] at this
      exact hw0 (neg_eq_zero.1 this.symm)
    · rw [hsw, ((hmem _).1 (hW₁b w hwW)).2, neg_zero]
  · refine ⟨w₁, eig_one hAA hi w, h0, ?_⟩
    rw [hsw, ((hmem _).1 hw₁W).2, neg_zero]

omit hAA in
include hBB hBA hi in
theorem exists_comb_eig (h2K : (2 : K) ≠ 0) {x x' : Fin 2 ⊕ Fin 2 → K} (hx : spEnd a x = i • x)
    (hx' : spEnd a x' = i • x') (hκ : spForm 2 K x (spEnd b x) ≠ 0)
    (hκ' : spForm 2 K x' (spEnd b x') ≠ 0) (h0 : spForm 2 K x' (spEnd b x) = 0)
    (z : Fin 2 ⊕ Fin 2 → K) :
    ∃ s t s' t' : K, z = s • x + t • spEnd b x + (s' • x' + t' • spEnd b x') := by
  set B := spEnd b with hBdef
  have hsw : ∀ x y : Fin 2 ⊕ Fin 2 → K, spForm 2 K y x = -spForm 2 K x y := spForm_swap
  have hself : ∀ x : Fin 2 ⊕ Fin 2 → K, spForm 2 K x x = 0 := spForm_isAlt.self_eq_zero
  have hni : (-i) * (-i) = -1 := by rw [neg_mul_neg, hi]
  have hBx := eig_b hBA hx
  have hBx' := eig_b hBA hx'
  have t1 : spForm 2 K x x' = 0 := form_eig_eq_zero h2K hi hx hx'
  have t2 : spForm 2 K x' x = 0 := form_eig_eq_zero h2K hi hx' hx
  have t3 : spForm 2 K (B x) (B x') = 0 := form_eig_eq_zero h2K hni hBx hBx'
  have t4 : spForm 2 K (B x') (B x) = 0 := form_eig_eq_zero h2K hni hBx' hBx
  have t5 : spForm 2 K x (B x') = 0 := by
    have := form_adj hBB x x'
    rw [← hBdef] at this
    rw [← neg_eq_zero, ← this, hsw, h0, neg_zero]
  have t5' : spForm 2 K (B x') x = 0 := by rw [hsw, t5, neg_zero]
  have t6 : spForm 2 K (B x) x' = 0 := by rw [hsw, h0, neg_zero]
  have t7 : spForm 2 K (B x) x = -spForm 2 K x (B x) := hsw _ _
  have t8 : spForm 2 K (B x') x' = -spForm 2 K x' (B x') := hsw _ _
  set L : (Fin 4 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
    Fintype.linearCombination K ![x, B x, x', B x'] with hL
  have hLapp : ∀ f, L f = f 0 • x + f 1 • B x + (f 2 • x' + f 3 • B x') := by
    intro f
    rw [hL, Fintype.linearCombination_apply, Fin.sum_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]
    abel
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    rw [hLapp] at hf
    have e1 := congrArg (fun w => spForm 2 K w (B x)) hf
    have e2 := congrArg (fun w => spForm 2 K w x) hf
    have e3 := congrArg (fun w => spForm 2 K w (B x')) hf
    have e4 := congrArg (fun w => spForm 2 K w x') hf
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hself, t1, t2, t3, t4, t5, t5', t6, t7, t8, h0, map_zero, LinearMap.zero_apply] at e1 e2 e3 e4
    funext j
    fin_cases j
    · have : f 0 * spForm 2 K x (B x) = 0 := by linear_combination e1
      exact (mul_eq_zero.1 this).resolve_right hκ
    · have : f 1 * spForm 2 K x (B x) = 0 := by linear_combination -e2
      exact (mul_eq_zero.1 this).resolve_right hκ
    · have : f 2 * spForm 2 K x' (B x') = 0 := by linear_combination e3
      exact (mul_eq_zero.1 this).resolve_right hκ'
    · have : f 3 * spForm 2 K x' (B x') = 0 := by linear_combination -e4
      exact (mul_eq_zero.1 this).resolve_right hκ'
  have hsurj : Function.Surjective L := by
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    simp [Module.finrank_fintype_fun_eq_card]
  obtain ⟨f, rfl⟩ := hsurj z
  exact ⟨f 0, f 1, f 2, f 3, hLapp f⟩

end Basis

section Aniso

variable {E : Subgroup (StatedProj (StatedSp 2 K))} {a b : StatedSp 2 K}

theorem form_b_ne_zero (hBB : ∀ v, spEnd b (spEnd b v) = -v)
    (hBA : ∀ v, spEnd b (spEnd a v) = -(spEnd a (spEnd b v))) (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) (ha : proj 2 K a ∈ E) (hb : proj 2 K b ∈ E) (ha1 : proj 2 K a ≠ 1)
    (hb1 : proj 2 K b ≠ 1) (hab : proj 2 K a ≠ proj 2 K b)
    (hani : ∀ W : Submodule K (Fin 2 ⊕ Fin 2 → K), (∀ x ∈ W, ∀ y ∈ W, spForm 2 K x y = 0) →
      (∀ g : StatedSp 2 K, proj 2 K g ∈ E → ∀ w ∈ W, spEnd g w ∈ W) → W = ⊥)
    {i : K} {x : Fin 2 ⊕ Fin 2 → K} (hx0 : x ≠ 0) (hx : spEnd a x = i • x) :
    spForm 2 K x (spEnd b x) ≠ 0 := by
  have hAB : ∀ v, spEnd a (spEnd b v) = -(spEnd b (spEnd a v)) := fun v => by rw [hBA, neg_neg]
  exact form_ne_zero_of_quat_eig (a := b) (b := a) hBB hAB (r := 2) (by norm_num) hE h4 hb ha
    hb1 ha1 (Ne.symm hab) hani (x₀ := i) (y₀ := 0) hx0 (by rw [hx, zero_smul, add_zero])

end Aniso

section Commutant

variable {a b : StatedSp 2 K} (hAA : ∀ v, spEnd a (spEnd a v) = -v)
  (hBB : ∀ v, spEnd b (spEnd b v) = -v)
  (hBA : ∀ v, spEnd b (spEnd a v) = -(spEnd a (spEnd b v)))
  {i : K} (hi : i * i = -1)

include hAA hBB hBA hi in
theorem exists_quat_commutant (h2K : (2 : K) ≠ 0) {v₁ v₂ : Fin 2 ⊕ Fin 2 → K}
    (hv₁ : spEnd a v₁ = i • v₁) (hv₂ : spEnd a v₂ = i • v₂)
    (hγ₁ : spForm 2 K v₁ (spEnd b v₁) ≠ 0) (hγ₂ : spForm 2 K v₂ (spEnd b v₂) ≠ 0)
    (h12 : spForm 2 K v₂ (spEnd b v₁) = 0) :
    ∃ J ρ : Module.End K (Fin 2 ⊕ Fin 2 → K),
      (∀ z, J (spEnd a z) = spEnd a (J z)) ∧ (∀ z, J (spEnd b z) = spEnd b (J z)) ∧
      (∀ z, ρ (spEnd a z) = spEnd a (ρ z)) ∧ (∀ z, ρ (spEnd b z) = spEnd b (ρ z)) ∧
      (∀ z w, spForm 2 K (J z) w = -spForm 2 K z (J w)) ∧
      (∀ z w, spForm 2 K (ρ z) w = spForm 2 K z (ρ w)) ∧
      (∀ z, J (J z) = -(spForm 2 K v₂ (spEnd b v₂) / spForm 2 K v₁ (spEnd b v₁)) • z) ∧
      (∀ z, ρ (ρ z) = z) ∧ (∀ z, ρ (J z) = -J (ρ z)) := by
  set A := spEnd a with hAdef
  set B := spEnd b with hBdef
  set w₁ := B v₁ with hw₁
  set w₂ := B v₂ with hw₂
  set γ₁ := spForm 2 K v₁ w₁ with hγ₁def
  set γ₂ := spForm 2 K v₂ w₂ with hγ₂def
  have hsw : ∀ x y : Fin 2 ⊕ Fin 2 → K, spForm 2 K y x = -spForm 2 K x y := spForm_swap
  have hself : ∀ x : Fin 2 ⊕ Fin 2 → K, spForm 2 K x x = 0 := spForm_isAlt.self_eq_zero
  have adjA : ∀ z w, spForm 2 K (A z) w = -spForm 2 K z (A w) := form_adj hAA
  have adjB : ∀ z w, spForm 2 K (B z) w = -spForm 2 K z (B w) := form_adj hBB
  have hni : (-i) * (-i) = -1 := by rw [neg_mul_neg, hi]
  have hw₁A : A w₁ = -i • w₁ := eig_b hBA hv₁
  have hw₂A : A w₂ = -i • w₂ := eig_b hBA hv₂
  have hBw₁ : B w₁ = -v₁ := hBB v₁
  have hBw₂ : B w₂ = -v₂ := hBB v₂
  have t11 : spForm 2 K v₁ v₂ = 0 := form_eig_eq_zero h2K hi hv₁ hv₂
  have t12 : spForm 2 K v₂ v₁ = 0 := form_eig_eq_zero h2K hi hv₂ hv₁
  have t13 : spForm 2 K w₁ w₂ = 0 := form_eig_eq_zero h2K hni hw₁A hw₂A
  have t14 : spForm 2 K w₂ w₁ = 0 := form_eig_eq_zero h2K hni hw₂A hw₁A
  have t15 : spForm 2 K v₁ w₂ = 0 := by
    have := adjB v₁ v₂
    rw [← neg_eq_zero, ← this, hsw, h12, neg_zero]
  have t16 : spForm 2 K w₂ v₁ = 0 := by rw [hsw, t15, neg_zero]
  have t17 : spForm 2 K w₁ v₂ = 0 := by rw [hsw, h12, neg_zero]
  have t18 : spForm 2 K w₁ v₁ = -γ₁ := hsw _ _
  have t19 : spForm 2 K w₂ v₂ = -γ₂ := hsw _ _
  have t20 : spForm 2 K v₂ w₁ = 0 := h12
  set J : Module.End K (Fin 2 ⊕ Fin 2 → K) := γ₁⁻¹ •
    (((spForm 2 K).flip w₁).smulRight v₂ - ((spForm 2 K).flip v₁).smulRight w₂ -
      ((spForm 2 K).flip w₂).smulRight v₁ + ((spForm 2 K).flip v₂).smulRight w₁) with hJdef
  have hJ : ∀ z, J z = γ₁⁻¹ • (spForm 2 K z w₁ • v₂ - spForm 2 K z v₁ • w₂ -
      spForm 2 K z w₂ • v₁ + spForm 2 K z v₂ • w₁) := fun z => by
    simp [hJdef]
  set ρ : Module.End K (Fin 2 ⊕ Fin 2 → K) := 1 - (2 / γ₂) •
    ((spForm 2 K).flip w₂).smulRight v₂ + (2 / γ₂) • ((spForm 2 K).flip v₂).smulRight w₂
    with hρdef
  have hρ : ∀ z, ρ z = z - (2 / γ₂) • (spForm 2 K z w₂ • v₂) +
      (2 / γ₂) • (spForm 2 K z v₂ • w₂) := fun z => by
    simp [hρdef]
  have hJv₁ : J v₁ = v₂ := by
    rw [hJ]
    simp only [hself, t11, t15, zero_smul, sub_zero,
      add_zero, ← hγ₁def]
    match_scalars
    field_simp
  have hJv₂ : J v₂ = -(γ₂ / γ₁) • v₁ := by
    rw [hJ]
    simp only [hself, t12, t20, zero_smul, sub_zero,
      add_zero, zero_sub, ← hγ₂def]
    match_scalars
    field_simp
  have hJw₁ : J w₁ = w₂ := by
    rw [hJ]
    simp only [hself, t13, t17, t18, zero_smul, sub_zero,
      add_zero, zero_sub]
    match_scalars
    field_simp
  have hJw₂ : J w₂ = -(γ₂ / γ₁) • w₁ := by
    rw [hJ]
    simp only [hself, t14, t16, t19, zero_smul, sub_zero,
      zero_add]
    match_scalars
    field_simp
  have hρv₁ : ρ v₁ = v₁ := by
    rw [hρ]
    simp only [t11, t15, zero_smul, smul_zero, sub_zero,
      add_zero]
  have hρv₂ : ρ v₂ = -v₂ := by
    rw [hρ]
    simp only [hself, zero_smul, smul_zero, 
      add_zero, ← hγ₂def]
    match_scalars
    field_simp
    ring
  have hρw₁ : ρ w₁ = w₁ := by
    rw [hρ]
    simp only [t13, t17, zero_smul, smul_zero, sub_zero,
      add_zero]
  have hρw₂ : ρ w₂ = -w₂ := by
    rw [hρ]
    simp only [hself, t19, zero_smul, smul_zero, sub_zero]
    match_scalars
    field_simp
    ring
  have hcomb : ∀ z, ∃ s t s' t' : K, z = s • v₁ + t • w₁ + (s' • v₂ + t' • w₂) :=
    exists_comb_eig hBB hBA hi h2K hv₁ hv₂ hγ₁ hγ₂ h12
  refine ⟨J, ρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    rw [hJ, hJ]
    simp only [adjA z, hv₁, hv₂, hw₁A, hw₂A, map_add, map_sub, map_smul, smul_eq_mul]
    module
  · intro z
    rw [hJ, hJ]
    simp only [adjB z, hBw₁, hBw₂, map_add, map_sub, map_smul, map_neg, 
      ← hw₁, ← hw₂]
    module
  · intro z
    rw [hρ, hρ]
    simp only [adjA z, hv₂, hw₂A, map_add, map_sub, map_smul, smul_eq_mul]
    module
  · intro z
    rw [hρ, hρ]
    simp only [adjB z, hBw₂, map_add, map_sub, map_smul, map_neg, 
      ← hw₂]
    module
  · intro z w
    rw [hJ, hJ]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, hsw w]
    ring
  · intro z w
    rw [hρ, hρ]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, hsw w]
    ring
  · intro z
    obtain ⟨s, t, s', t', rfl⟩ := hcomb z
    simp only [map_add, map_smul, hJv₁, hJv₂, hJw₁, hJw₂]
    module
  · intro z
    obtain ⟨s, t, s', t', rfl⟩ := hcomb z
    simp only [map_add, map_smul, map_neg, hρv₁, hρv₂, hρw₁, hρw₂]
    module
  · intro z
    obtain ⟨s, t, s', t', rfl⟩ := hcomb z
    simp only [map_add, map_smul, map_neg, hJv₁, hJv₂, hJw₁, hJw₂, hρv₁, hρv₂, hρw₁, hρw₂]
    module

end Commutant

section Simil

variable {J : Module.End K (Fin 2 ⊕ Fin 2 → K)}
  (hJadj : ∀ z w, spForm 2 K (J z) w = -spForm 2 K z (J w))

include hJadj in
theorem form_add_J {d : K} (hJJ : ∀ z, J (J z) = -d • z) (x y : K) (z w : Fin 2 ⊕ Fin 2 → K) :
    spForm 2 K (x • z + y • J z) (x • w + y • J w) = (x ^ 2 + d * y ^ 2) * spForm 2 K z w := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hJadj, hJJ]
  ring

theorem form_sub_S {g : StatedSp 2 K} (hgg : ∀ v, spEnd g (spEnd g v) = -v)
    {S : Module.End K (Fin 2 ⊕ Fin 2 → K)} (hSadj : ∀ z w, spForm 2 K (S z) w = spForm 2 K z (S w))
    {σ : K} (hSS : ∀ z, S (S z) = σ • z) (hSg : ∀ z, S (spEnd g z) = spEnd g (S z))
    (c : K) (z w : Fin 2 ⊕ Fin 2 → K) :
    spForm 2 K (z + c • S (spEnd g z)) (w + c • S (spEnd g w)) =
      (1 + c ^ 2 * σ) * spForm 2 K z w := by
  have adj := form_adj hgg
  have e1 : spForm 2 K (S (spEnd g z)) w = -spForm 2 K z (S (spEnd g w)) := by
    rw [hSadj, adj, hSg]
  have e2 : spForm 2 K (S (spEnd g z)) (S (spEnd g w)) = σ * spForm 2 K z w := by
    rw [hSadj, hSS, map_smul, spEnd_isometry, smul_eq_mul]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, e1, e2]
  ring

end Simil

section Shift

variable {E : Subgroup (StatedProj (StatedSp 2 K))} {a b : StatedSp 2 K}

theorem proj_mul_ne_one (hE : IsElemAbelian 2 E) (hb : proj 2 K b ∈ E)
    (hab : proj 2 K a ≠ proj 2 K b) : proj 2 K (a * b) ≠ 1 := by
  intro h
  rw [map_mul] at h
  apply hab
  rw [eq_inv_of_mul_eq_one_left h]
  exact inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hE.2 _ hb)

theorem exists_levi_shift [Finite K] (h2K : (2 : K) ≠ 0) (h3 : Nat.card K ≠ 3)
    (hE : IsElemAbelian 2 E) (ha : proj 2 K a ∈ E) (hb : proj 2 K b ∈ E)
    (hb1 : proj 2 K b ≠ 1) (hab : proj 2 K a ≠ proj 2 K b)
    (hAA : ∀ v, spEnd a (spEnd a v) = -v) (hBB : ∀ v, spEnd b (spEnd b v) = -v)
    (hBA : ∀ v, spEnd b (spEnd a v) = -(spEnd a (spEnd b v))) {i : K} (hi : i * i = -1)
    {v₁ v₂ : Fin 2 ⊕ Fin 2 → K} (hv₁ : spEnd a v₁ = i • v₁) (hv₂ : spEnd a v₂ = i • v₂)
    (hγ₁ : spForm 2 K v₁ (spEnd b v₁) ≠ 0) (hγ₂ : spForm 2 K v₂ (spEnd b v₂) ≠ 0)
    (h12 : spForm 2 K v₂ (spEnd b v₁) = 0) :
    ∃ g ∈ cGen E, (∀ z, spEnd a z = i • z → spEnd a (spEnd g z) = i • spEnd g z) ∧
      (∀ l, spEnd a l = i • l → ∃ m, spEnd a m = i • m ∧ spEnd g m = l) ∧
      ∃ y, spEnd a y = -i • y ∧ spEnd a (spEnd g y) ≠ -i • spEnd g y := by
  obtain ⟨J, ρ, hJA, hJB, hρA, hρB, hJadj, hρadj, hJJ, hρρ, hρJ⟩ :=
    exists_quat_commutant hAA hBB hBA hi h2K hv₁ hv₂ hγ₁ hγ₂ h12
  set d := spForm 2 K v₂ (spEnd b v₂) / spForm 2 K v₁ (spEnd b v₁) with hd
  have hd0 : d ≠ 0 := div_ne_zero hγ₂ hγ₁
  obtain ⟨σ, hσ0, hσ1, hσm⟩ := exists_ne_zero_one_neg_one h2K h3
  have h1p : 1 + σ ≠ 0 := fun h => hσm (by linear_combination h)
  have h1m : 1 - σ ≠ 0 := fun h => hσ1 (by linear_combination -h)
  obtain ⟨α, β, hαβ⟩ := exists_sq_add_sq h2K one_ne_zero hd0 (-σ)
  obtain ⟨x, y, hxy⟩ := exists_sq_add_sq h2K one_ne_zero hd0 (-(1 + σ)⁻¹)
  obtain ⟨x', y', hxy'⟩ := exists_sq_add_sq h2K one_ne_zero hd0 (-(1 - σ)⁻¹)
  have hμ : x ^ 2 + d * y ^ 2 = (1 + σ)⁻¹ := by linear_combination hxy
  have hν : x' ^ 2 + d * y' ^ 2 = (1 - σ)⁻¹ := by linear_combination hxy'
  have hii : i ^ 2 = -1 := by rw [sq, hi]
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hi
    exact one_ne_zero (neg_eq_zero.1 hi.symm)
  have hAB : ∀ v, spEnd (a * b) v = spEnd a (spEnd b v) := fun v => by
    rw [spEnd_mul, Module.End.mul_apply]
  have hCC : ∀ v, spEnd (a * b) (spEnd (a * b) v) = -v := fun v => by
    rw [hAB, hAB, hBA, map_neg, hAA, hBB, neg_neg]
  set S : Module.End K (Fin 2 ⊕ Fin 2 → K) := α • ρ + β • (ρ * J) with hSdef
  have hS : ∀ z, S z = α • ρ z + β • ρ (J z) := fun z => by simp [hSdef]
  have hSA : ∀ z, S (spEnd a z) = spEnd a (S z) := fun z => by
    simp only [hS, hρA, hJA, map_add, map_smul]
  have hSB : ∀ z, S (spEnd b z) = spEnd b (S z) := fun z => by
    simp only [hS, hρB, hJB, map_add, map_smul]
  have hSC : ∀ z, S (spEnd (a * b) z) = spEnd (a * b) (S z) := fun z => by
    rw [hAB, hAB, hSA, hSB]
  have hSadj : ∀ z w, spForm 2 K (S z) w = spForm 2 K z (S w) := fun z w => by
    simp only [hS, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hρadj, hJadj, hρJ, map_neg, LinearMap.neg_apply]
    ring
  have hSS : ∀ z, S (S z) = σ • z := fun z => by
    simp only [hS, map_add, map_smul, hρρ, hρJ, hJJ, map_neg]
    linear_combination (norm := module) hαβ • z
  set P : Module.End K (Fin 2 ⊕ Fin 2 → K) := x • 1 + y • J with hPdef
  have hP : ∀ z, P z = x • z + y • J z := fun z => by simp [hPdef]
  set Pb : Module.End K (Fin 2 ⊕ Fin 2 → K) := x • 1 + (-y) • J with hPbdef
  have hPb : ∀ z, Pb z = x • z + (-y) • J z := fun z => by simp [hPbdef]
  set P' : Module.End K (Fin 2 ⊕ Fin 2 → K) := x' • 1 + y' • J with hP'def
  have hP' : ∀ z, P' z = x' • z + y' • J z := fun z => by simp [hP'def]
  set Pb' : Module.End K (Fin 2 ⊕ Fin 2 → K) := x' • 1 + (-y') • J with hPb'def
  have hPb' : ∀ z, Pb' z = x' • z + (-y') • J z := fun z => by simp [hPb'def]
  have hPA : ∀ z, P (spEnd a z) = spEnd a (P z) := fun z => by
    simp only [hP, hJA, map_add, map_smul]
  have hPB : ∀ z, P (spEnd b z) = spEnd b (P z) := fun z => by
    simp only [hP, hJB, map_add, map_smul]
  have hP'A : ∀ z, P' (spEnd a z) = spEnd a (P' z) := fun z => by
    simp only [hP', hJA, map_add, map_smul]
  have hP'B : ∀ z, P' (spEnd b z) = spEnd b (P' z) := fun z => by
    simp only [hP', hJB, map_add, map_smul]
  have hP'C : ∀ z, P' (spEnd (a * b) z) = spEnd (a * b) (P' z) := fun z => by
    rw [hAB, hAB, hP'A, hP'B]
  have hPbA : ∀ z, Pb (spEnd a z) = spEnd a (Pb z) := fun z => by
    simp only [hPb, hJA, map_add, map_smul]
  have hPb'A : ∀ z, Pb' (spEnd a z) = spEnd a (Pb' z) := fun z => by
    simp only [hPb', hJA, map_add, map_smul]
  have hPPb : ∀ z, P (Pb z) = (x ^ 2 + d * y ^ 2) • z := fun z => by
    simp only [hP, hPb, map_add, map_smul, hJJ]
    module
  have hPbP : ∀ z, Pb (P z) = (x ^ 2 + d * y ^ 2) • z := fun z => by
    simp only [hP, hPb, map_add, map_smul, hJJ]
    module
  have hP'Pb' : ∀ z, P' (Pb' z) = (x' ^ 2 + d * y' ^ 2) • z := fun z => by
    simp only [hP', hPb', map_add, map_smul, hJJ]
    module
  have hPb'P' : ∀ z, Pb' (P' z) = (x' ^ 2 + d * y' ^ 2) • z := fun z => by
    simp only [hP', hPb', map_add, map_smul, hJJ]
    module
  set G : Module.End K (Fin 2 ⊕ Fin 2 → K) := P + (-1 : K) • (S * spEnd b * P) with hGdef
  have hG : ∀ z, G z = P z + (-1 : K) • S (spEnd b (P z)) := fun z => by simp [hGdef]
  set Kk : Module.End K (Fin 2 ⊕ Fin 2 → K) := P' * (1 + i • (S * spEnd (a * b))) with hKdef
  have hK : ∀ z, Kk z = P' (z + i • S (spEnd (a * b) z)) := fun z => by simp [hKdef]
  have hGiso : ∀ z w, spForm 2 K (G z) (G w) = spForm 2 K z w := fun z w => by
    rw [hG, hG, form_sub_S hBB hSadj hSS hSB, hP, hP, form_add_J hJadj hJJ, hμ]
    field_simp
  have hKiso : ∀ z w, spForm 2 K (Kk z) (Kk w) = spForm 2 K z w := fun z w => by
    rw [hK, hK, hP', hP', form_add_J hJadj hJJ, form_sub_S hCC hSadj hSS hSC, hν, hii]
    field_simp
    ring
  obtain ⟨g, hg⟩ := exists_sp_of_isometry hGiso
  obtain ⟨k, hk⟩ := exists_sp_of_isometry hKiso
  have hgb : g * b = b * g := by
    apply spLin_injective
    refine Units.ext (LinearMap.ext fun z => ?_)
    change spEnd (g * b) z = spEnd (b * g) z
    rw [spEnd_mul, spEnd_mul, hg]
    show G (spEnd b z) = spEnd b (G z)
    rw [hG, hG, hPB, hBB, map_add, map_smul, hSB, hBB, map_neg]
  have hkc : k * (a * b) = (a * b) * k := by
    apply spLin_injective
    refine Units.ext (LinearMap.ext fun z => ?_)
    change spEnd (k * (a * b)) z = spEnd ((a * b) * k) z
    rw [spEnd_mul, spEnd_mul (a * b) k, hk]
    show Kk (spEnd (a * b) z) = spEnd (a * b) (Kk z)
    rw [hK, hK, ← hP'C]
    congr 1
    rw [map_add, map_smul, hSC]
  have hgH : g ∈ cGen E := mem_cGen_of_commute hb hb1 hgb
  have hkH : k ∈ cGen E := mem_cGen_of_commute (by rw [map_mul]; exact E.mul_mem ha hb)
    (proj_mul_ne_one hE hb hab) hkc
  have hform : ∀ (l : K) z, spEnd a z = l • z →
      spEnd (k * g) z = (1 + i * l * σ) • P' (P z) - (1 + i * l) • P' (S (P (spEnd b z))) := by
    intro l z hz
    have hBz : spEnd a (spEnd b z) = -l • spEnd b z := eig_b hBA hz
    have hGz : G z = P z + (-1 : K) • S (P (spEnd b z)) := by rw [hG, ← hPB]
    have hBG : spEnd b (G z) = P (spEnd b z) + S (P z) := by
      rw [hGz, map_add, map_smul, ← hSB, ← hPB (spEnd b z), hBB, map_neg, map_neg, neg_one_smul,
        neg_neg, ← hPB z]
    have hCG : spEnd (a * b) (G z) = (-l) • P (spEnd b z) + l • S (P z) := by
      rw [hAB, hBG, map_add, ← hPA, hBz, map_smul, ← hSA, ← hPA, hz, map_smul, map_smul]
    rw [spEnd_mul, Module.End.mul_apply, hk, hg, hK, hCG, hGz]
    simp only [map_add, map_smul, hSS]
    module
  refine ⟨k * g, (cGen E).mul_mem hkH hgH, ?_, ?_, ?_⟩
  · intro z hz
    rw [hform i z hz, hi]
    simp only [map_sub, map_smul, ← hP'A, ← hPA, hz]
    module
  · intro l hl
    refine ⟨((1 - σ) * (x ^ 2 + d * y ^ 2) * (x' ^ 2 + d * y' ^ 2))⁻¹ • Pb (Pb' l), ?_, ?_⟩
    · rw [map_smul, ← hPbA, ← hPb'A, hl, map_smul, map_smul, smul_comm]
    · rw [hform i _ (by rw [map_smul, ← hPbA, ← hPb'A, hl, map_smul, map_smul, smul_comm]), hi]
      simp only [map_smul, hPPb, hP'Pb']
      rw [hμ, hν]
      match_scalars <;> field_simp <;> ring
  · refine ⟨spEnd b v₁, eig_b hBA hv₁, fun h => ?_⟩
    have hin : i * -i = 1 := by rw [mul_neg, hi, neg_neg]
    rw [hform (-i) _ (eig_b hBA hv₁), hBB, hin] at h
    have hU : spEnd a (P' (P (spEnd b v₁))) = -i • P' (P (spEnd b v₁)) := by
      rw [← hP'A, ← hPA, eig_b hBA hv₁, map_smul, map_smul]
    have hW : spEnd a (P' (S (P v₁))) = i • P' (S (P v₁)) := by
      rw [← hP'A, ← hSA, ← hPA, hv₁, map_smul, map_smul, map_smul]
    simp only [map_neg, map_sub, map_smul, hU, hW] at h
    have h4 : ((2 * 2) * i) • P' (S (P v₁)) = 0 := by linear_combination (norm := module) h
    have hW0 : P' (S (P v₁)) = 0 :=
      (smul_eq_zero.1 h4).resolve_left (mul_ne_zero (mul_ne_zero h2K h2K) hi0)
    have e1 := hPb'P' (S (P v₁))
    rw [hW0, map_zero, hν] at e1
    have hS0 : S (P v₁) = 0 := (smul_eq_zero.1 e1.symm).resolve_left (inv_ne_zero h1m)
    have e2 := hSS (P v₁)
    rw [hS0, map_zero] at e2
    have hP0 : P v₁ = 0 := (smul_eq_zero.1 e2.symm).resolve_left hσ0
    have e3 := hPbP v₁
    rw [hP0, map_zero, hμ] at e3
    have hv0 : v₁ = 0 := (smul_eq_zero.1 e3.symm).resolve_left (inv_ne_zero h1p)
    exact hγ₁ (by rw [hv0, map_zero, LinearMap.zero_apply])

end Shift

theorem spEnd_inv_apply (g : StatedSp 2 K) (w : Fin 2 ⊕ Fin 2 → K) :
    spEnd g⁻¹ (spEnd g w) = w := by
  rw [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one, Module.End.one_apply]

section Siegel

variable {a : StatedSp 2 K} (hAA : ∀ v, spEnd a (spEnd a v) = -v) {i : K} (hi : i * i = -1)

include hAA hi in
theorem siegel_of_shift (h2K : (2 : K) ≠ 0) {g : StatedSp 2 K}
    (hg1 : ∀ z, spEnd a z = i • z → spEnd a (spEnd g z) = i • spEnd g z)
    (hg2 : ∀ l, spEnd a l = i • l → ∃ m, spEnd a m = i • m ∧ spEnd g m = l) :
    (∀ w, spEnd a w = i • w → spEnd (g⁻¹ * a⁻¹ * g * a) w = w) ∧
      (∀ z, spEnd a (spEnd (g⁻¹ * a⁻¹ * g * a) z - z) =
        i • (spEnd (g⁻¹ * a⁻¹ * g * a) z - z)) ∧
      (∀ y, spEnd a y = -i • y → spEnd a (spEnd g y) ≠ -i • spEnd g y →
        spEnd (g⁻¹ * a⁻¹ * g * a) y ≠ y) := by
  have hainv : ∀ w, spEnd a⁻¹ w = -spEnd a w := fun w => by
    have := spEnd_inv_apply a (-spEnd a w)
    rwa [map_neg, hAA, neg_neg] at this
  have hu : ∀ z, spEnd (g⁻¹ * a⁻¹ * g * a) z = spEnd g⁻¹ (-spEnd a (spEnd g (spEnd a z))) := by
    intro z
    simp only [spEnd_mul, Module.End.mul_apply, hainv]
  have hL2 : ∀ z, spEnd a z = -i • z → ∃ m, spEnd a m = i • m ∧
      spEnd g m = (2 : K)⁻¹ • (spEnd g z - i • spEnd a (spEnd g z)) ∧
      spEnd (g⁻¹ * a⁻¹ * g * a) z = z - (2 : K) • m := by
    intro z hz
    obtain ⟨m, hm, hgm⟩ := hg2 _ (eig_one hAA hi (spEnd g z))
    refine ⟨m, hm, hgm, ?_⟩
    rw [hu, hz, map_smul, map_smul]
    have e : -(-i • spEnd a (spEnd g z)) = spEnd g (z - (2 : K) • m) := by
      rw [map_sub, map_smul, hgm]
      have hii : (2 : K) * (2 : K)⁻¹ = 1 := mul_inv_cancel₀ h2K
      linear_combination (norm := module) hii • spEnd g z - i • hii • spEnd a (spEnd g z)
    rw [e, spEnd_inv_apply]
  have hL1 : ∀ w, spEnd a w = i • w → spEnd (g⁻¹ * a⁻¹ * g * a) w = w := by
    intro w hw
    rw [hu, hw, map_smul, map_smul, hg1 w hw, smul_smul, hi, neg_smul, one_smul, neg_neg,
      spEnd_inv_apply]
  refine ⟨hL1, ?_, ?_⟩
  · intro z
    have hdec := eig_decomp (a := a) (i := i) h2K z
    obtain ⟨m, hm, -, hum⟩ := hL2 _ (eig_two hAA hi z)
    have e : spEnd (g⁻¹ * a⁻¹ * g * a) z - z = -(2 : K) • m := by
      conv_lhs => rw [hdec]
      rw [map_add, hL1 _ (eig_one hAA hi z), hum]
      module
    rw [e, map_smul, hm, smul_comm]
  · intro y hy hgy h
    obtain ⟨m, hm, hgm, hum⟩ := hL2 y hy
    rw [h, eq_comm, sub_eq_self, smul_eq_zero] at hum
    have hm0 : m = 0 := hum.resolve_left h2K
    rw [hm0, map_zero, eq_comm, smul_eq_zero] at hgm
    have h1 : spEnd g y = i • spEnd a (spEnd g y) :=
      sub_eq_zero.1 (hgm.resolve_left (inv_ne_zero h2K))
    apply hgy
    rw [eq_comm]
    conv_lhs => rw [h1]
    rw [smul_smul, neg_mul, hi, neg_neg, one_smul]

end Siegel

section Second

variable {a : StatedSp 2 K} (hAA : ∀ v, spEnd a (spEnd a v) = -v) {i : K} (hi : i * i = -1)
  {u : StatedSp 2 K} (hL1 : ∀ w, spEnd a w = i • w → spEnd u w = w)
  (hφ : ∀ z, spEnd a (spEnd u z - z) = i • (spEnd u z - z))

include hAA hi hφ in
theorem exists_siegel_form (h2K : (2 : K) ≠ 0) {y₀ : Fin 2 ⊕ Fin 2 → K}
    (hy₀ : spEnd a y₀ = -i • y₀) (hu : spEnd u y₀ ≠ y₀) :
    ∃ e, spEnd a e = -i • e ∧ spForm 2 K (spEnd u e - e) e ≠ 0 := by
  have hni : (-i) * (-i) = -1 := by rw [neg_mul_neg, hi]
  have hiso0 : ∀ z w, spForm 2 K (spEnd u z - z) (spEnd u w - w) = 0 := fun z w =>
    form_eig_eq_zero h2K hi (hφ z) (hφ w)
  have hsym : ∀ y y', spEnd a y = -i • y → spEnd a y' = -i • y' →
      spForm 2 K (spEnd u y - y) y' = spForm 2 K (spEnd u y' - y') y := by
    intro y y' hy hy'
    have h := spEnd_isometry u y y'
    have hyy := form_eig_eq_zero h2K hni hy hy'
    have h0 := hiso0 y y'
    have e1 : spEnd u y = y + (spEnd u y - y) := by abel
    have e2 : spEnd u y' = y' + (spEnd u y' - y') := by abel
    rw [e1, e2] at h
    simp only [map_add, LinearMap.add_apply, h0, add_zero] at h
    rw [spForm_swap y (spEnd u y' - y')]
    linear_combination h
  have hlin : ∀ y y', spEnd u (y + y') - (y + y') = (spEnd u y - y) + (spEnd u y' - y') :=
    fun y y' => by rw [map_add]; abel
  have hf0 : spEnd u y₀ - y₀ ≠ 0 := sub_ne_zero.2 hu
  obtain ⟨z, hz⟩ : ∃ z, spForm 2 K (spEnd u y₀ - y₀) z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf0 ((spForm_nondegenerate (r := 2) (K := K)).1 _ hcon)
  set y' := (2 : K)⁻¹ • (z + i • spEnd a z) with hy'
  have hy'a : spEnd a y' = -i • y' := eig_two hAA hi z
  have hz' : spForm 2 K (spEnd u y₀ - y₀) y' ≠ 0 := by
    have hdec := eig_decomp (a := a) (i := i) h2K z
    have h1 := form_eig_eq_zero h2K hi (hφ y₀) (eig_one hAA hi z)
    rw [hdec, map_add, h1, zero_add] at hz
    exact hz
  by_cases h₀ : spForm 2 K (spEnd u y₀ - y₀) y₀ = 0
  · by_cases h₁ : spForm 2 K (spEnd u y' - y') y' = 0
    · refine ⟨y₀ + y', ?_, ?_⟩
      · rw [map_add, hy₀, hy'a, smul_add]
      · rw [hlin]
        simp only [map_add, LinearMap.add_apply, h₀, h₁, zero_add, add_zero]
        rw [hsym y' y₀ hy'a hy₀]
        intro h
        apply hz'
        have : (2 : K) * spForm 2 K (spEnd u y₀ - y₀) y' = 0 := by linear_combination h
        exact (mul_eq_zero.1 this).resolve_left h2K
    · exact ⟨y', hy'a, h₁⟩
  · exact ⟨y₀, hy₀, h₀⟩

include hi hL1 hφ in
theorem second_difference (h2K : (2 : K) ≠ 0) {e₁ e₂ : Fin 2 ⊕ Fin 2 → K}
    (he₁ : spEnd a e₁ = i • e₁) (he₂ : spEnd a e₂ = -i • e₂) (h12 : spForm 2 K e₁ e₂ = 0)
    (t : K) :
    spTransvection (e₁ + e₂) t * spTransvection (spEnd a (e₁ + e₂)) t * u *
        (spTransvection (e₁ + e₂) (-t) * spTransvection (spEnd a (e₁ + e₂)) (-t)) *
        ((spTransvection (e₁ + e₂) (-t) * spTransvection (spEnd a (e₁ + e₂)) (-t)) * u *
          (spTransvection (e₁ + e₂) t * spTransvection (spEnd a (e₁ + e₂)) t)) * u⁻¹ * u⁻¹ =
      spTransvection e₁ (-8 * t ^ 2 * spForm 2 K (spEnd u e₂ - e₂) e₂) := by
  have hni : (-i) * (-i) = -1 := by rw [neg_mul_neg, hi]
  have hsw : ∀ x y : Fin 2 ⊕ Fin 2 → K, spForm 2 K y x = -spForm 2 K x y := spForm_swap
  have hself : ∀ x : Fin 2 ⊕ Fin 2 → K, spForm 2 K x x = 0 := spForm_isAlt.self_eq_zero
  have h21 : spForm 2 K e₂ e₁ = 0 := by rw [hsw, h12, neg_zero]
  set c := e₁ + e₂ with hc
  have hAc : spEnd a c = i • e₁ - i • e₂ := by
    rw [hc, map_add, he₁, he₂, neg_smul, ← sub_eq_add_neg]
  have hcc : spForm 2 K (spEnd a c) c = 0 := by
    rw [hAc, hc]
    simp only [map_add, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, hself, h12, h21]
    ring
  set X : K → StatedSp 2 K := fun s => spTransvection c s * spTransvection (spEnd a c) s with hX
  have hXapp : ∀ s z, spEnd (X s) z =
      z + (s * spForm 2 K z (spEnd a c)) • spEnd a c + (s * spForm 2 K z c) • c := by
    intro s z
    simp only [hX, spEnd_mul, Module.End.mul_apply, spEnd_spTransvection, map_add, map_smul,
      hcc]
    module
  have hcc' : spForm 2 K c (spEnd a c) = 0 := by rw [hsw, hcc, neg_zero]
  have hXX : ∀ s w, spEnd (X s) (spEnd (X (-s)) w) = w := by
    intro s w
    rw [hXapp, hXapp]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hself, hcc, hcc', mul_zero, add_zero]
    module
  set φ : Module.End K (Fin 2 ⊕ Fin 2 → K) := spEnd u - 1 with hφdef
  have hφa : ∀ z, φ z = spEnd u z - z := fun z => by simp [hφdef]
  have hφi : ∀ z, spEnd a (φ z) = i • φ z := fun z => by rw [hφa]; exact hφ z
  have hφL1 : ∀ w, spEnd a w = i • w → φ w = 0 := fun w hw => by rw [hφa, hL1 w hw, sub_self]
  have hφφ : ∀ z, φ (φ z) = 0 := fun z => hφL1 _ (hφi z)
  have hux : ∀ z, spEnd u z = z + φ z := fun z => by rw [hφa]; abel
  have huinv : ∀ z, spEnd u⁻¹ z = z - φ z := by
    intro z
    have h := spEnd_inv_apply u (z - φ z)
    rwa [hux, map_sub, hφφ, sub_zero, sub_add_cancel] at h
  have M1 : ∀ s w, spEnd a w = i • w → spEnd (X s) w = w + (2 * s * spForm 2 K w e₂) • e₁ := by
    intro s w hw
    have hw1 : spForm 2 K w e₁ = 0 := form_eig_eq_zero h2K hi hw he₁
    rw [hXapp, hAc, hc]
    simp only [map_add, map_sub, map_smul, 
      smul_eq_mul, hw1]
    linear_combination (norm := module) (s * spForm 2 K w e₂) • hi • (e₂ - e₁)
  have M2 : ∀ s z, φ (spEnd (X s) z) = φ z + (2 * s * spForm 2 K z e₁) • φ e₂ := by
    intro s z
    rw [hXapp, hAc, hc]
    simp only [map_add, map_sub, map_smul, 
      smul_eq_mul, hφL1 e₁ he₁]
    linear_combination (norm := module)
      (s * (spForm 2 K z e₂ - spForm 2 K z e₁)) • hi • φ e₂
  set ψ : K → Module.End K (Fin 2 ⊕ Fin 2 → K) := fun s => spEnd (X s) * φ * spEnd (X (-s))
    with hψdef
  set ψ' : K → Module.End K (Fin 2 ⊕ Fin 2 → K) := fun s => spEnd (X (-s)) * φ * spEnd (X s)
    with hψ'def
  have hψ : ∀ s z, ψ s z = φ z + (2 * (-s) * spForm 2 K z e₁) • φ e₂ +
      (2 * s * spForm 2 K (φ z + (2 * (-s) * spForm 2 K z e₁) • φ e₂) e₂) • e₁ := by
    intro s z
    change spEnd (X s) (φ (spEnd (X (-s)) z)) = _
    rw [M2, M1]
    rw [map_add, map_smul, hφi, hφi]
    module
  have hψ' : ∀ s z, ψ' s z = φ z + (2 * s * spForm 2 K z e₁) • φ e₂ +
      (2 * (-s) * spForm 2 K (φ z + (2 * s * spForm 2 K z e₁) • φ e₂) e₂) • e₁ := by
    intro s z
    change spEnd (X (-s)) (φ (spEnd (X s) z)) = _
    rw [M2, M1]
    rw [map_add, map_smul, hφi, hφi]
    module
  have hψL1 : ∀ s w, spEnd a w = i • w → ψ s w = 0 := by
    intro s w hw
    rw [hψ, hφL1 w hw, form_eig_eq_zero h2K hi hw he₁]
    simp
  have hψ'L1 : ∀ s w, spEnd a w = i • w → ψ' s w = 0 := by
    intro s w hw
    rw [hψ', hφL1 w hw, form_eig_eq_zero h2K hi hw he₁]
    simp
  have hφe : spEnd a (φ e₂) = i • φ e₂ := hφi e₂
  have hψ'i : ∀ s z, spEnd a (ψ' s z) = i • ψ' s z := by
    intro s z
    rw [hψ']
    simp only [map_add, map_smul, hφi, he₁]
    module
  have hF : ∀ s w, spEnd (X s) (spEnd u (spEnd (X (-s)) w)) = w + ψ s w := by
    intro s w
    rw [hux, map_add, hXX]
    rfl
  have hF' : ∀ s w, spEnd (X (-s)) (spEnd u (spEnd (X s) w)) = w + ψ' s w := by
    intro s w
    have h := hXX (-s) w
    rw [neg_neg] at h
    rw [hux, map_add, h]
    rfl
  have key : X t * u * X (-t) * (X (-t) * u * X t) * u⁻¹ * u⁻¹ =
      spTransvection e₁ (-8 * t ^ 2 * spForm 2 K (spEnd u e₂ - e₂) e₂) := by
    apply spLin_injective
    refine Units.ext (LinearMap.ext fun z => ?_)
    change spEnd (X t * u * X (-t) * (X (-t) * u * X t) * u⁻¹ * u⁻¹) z = spEnd _ z
    simp only [spEnd_mul, Module.End.mul_apply]
    have hw1 : spEnd u⁻¹ (spEnd u⁻¹ z) = z - (2 : K) • φ z := by
      rw [huinv, huinv, map_sub, hφφ]
      module
    rw [hw1, hF', hF, map_add (ψ t), hψL1 t _ (hψ'i t _), add_zero, map_sub, map_smul, map_sub,
      map_smul, hψL1 t _ (hφi z), hψ'L1 t _ (hφi z), smul_zero, sub_zero, sub_zero,
      spEnd_spTransvection, hψ, hψ', ← hφa]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    module
  exact key

end Second

section Main

variable {a : StatedSp 2 K} {i : K}

theorem pair_apply_eig (h2K : (2 : K) ≠ 0) (hi : i * i = -1) {e f w : Fin 2 ⊕ Fin 2 → K}
    (he : spEnd a e = i • e) (hf : spEnd a f = -i • f) (hef : spForm 2 K e f = 0)
    (hw : spEnd a w = i • w) (s : K) :
    spEnd (spTransvection (e + f) s * spTransvection (spEnd a (e + f)) s) w =
      w + (2 * s * spForm 2 K w f) • e := by
  have hsw : ∀ x y : Fin 2 ⊕ Fin 2 → K, spForm 2 K y x = -spForm 2 K x y := spForm_swap
  have hself : ∀ x : Fin 2 ⊕ Fin 2 → K, spForm 2 K x x = 0 := spForm_isAlt.self_eq_zero
  have hfe : spForm 2 K f e = 0 := by rw [hsw, hef, neg_zero]
  have hwe : spForm 2 K w e = 0 := form_eig_eq_zero h2K hi hw he
  rw [spEnd_mul, Module.End.mul_apply, spEnd_spTransvection, spEnd_spTransvection, map_add, he,
    hf]
  simp only [map_add, map_smul, map_neg, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, smul_eq_mul, hself, hef, hfe, hwe, neg_smul]
  linear_combination (norm := module) (s * spForm 2 K w f) • hi • (f - e)

theorem pair_mem {E : Subgroup (StatedProj (StatedSp 2 K))} (ha : proj 2 K a ∈ E)
    (ha1 : proj 2 K a ≠ 1) (haa : spEnd a * spEnd a = -1) {c : Fin 2 ⊕ Fin 2 → K}
    (hc : spForm 2 K c (spEnd a c) = 0) (s : K) :
    spTransvection c s * spTransvection (spEnd a c) s ∈ cGen E :=
  mem_cGen_of_commute ha ha1 (commute_pair haa hc s)

end Main

section Center

variable {E : Subgroup (StatedProj (StatedSp 2 K))} {a b : StatedSp 2 K}

theorem exists_transCenter_eig [Finite K] (h2K : (2 : K) ≠ 0) (h3 : Nat.card K ≠ 3)
    (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (hani : ∀ W : Submodule K (Fin 2 ⊕ Fin 2 → K), (∀ x ∈ W, ∀ y ∈ W, spForm 2 K x y = 0) →
      (∀ g : StatedSp 2 K, proj 2 K g ∈ E → ∀ w ∈ W, spEnd g w ∈ W) → W = ⊥)
    (ha : proj 2 K a ∈ E) (hb : proj 2 K b ∈ E) (ha1 : proj 2 K a ≠ 1)
    (hb1 : proj 2 K b ≠ 1) (hab : proj 2 K a ≠ proj 2 K b) (haa : spEnd a * spEnd a = -1)
    (hAA : ∀ v, spEnd a (spEnd a v) = -v) (hBB : ∀ v, spEnd b (spEnd b v) = -v)
    (hBA : ∀ v, spEnd b (spEnd a v) = -(spEnd a (spEnd b v))) {i : K} (hi : i * i = -1) :
    ∃ e, spEnd a e = i • e ∧ e ≠ 0 ∧ TransCenter (cGen E) e := by
  have hfq : ∀ {x : Fin 2 ⊕ Fin 2 → K}, x ≠ 0 → spEnd a x = i • x →
      spForm 2 K x (spEnd b x) ≠ 0 := fun hx0 hx =>
    form_b_ne_zero hBB hBA hE h4 ha hb ha1 hb1 hab hani hx0 hx
  obtain ⟨v₁, hv₁, hv₁0, -⟩ := exists_compl_eig hAA hBB hBA hi h2K (x := 0) (by simp)
  obtain ⟨v₂, hv₂, hv₂0, h12⟩ := exists_compl_eig hAA hBB hBA hi h2K hv₁
  obtain ⟨g, hgH, hg1, hg2, y, hy, hgy⟩ := exists_levi_shift h2K h3 hE ha hb hb1 hab hAA hBB hBA
    hi hv₁ hv₂ (hfq hv₁0 hv₁) (hfq hv₂0 hv₂) h12
  obtain ⟨hL1, hφ, hmove⟩ := siegel_of_shift hAA hi h2K hg1 hg2
  have haH : a ∈ cGen E := mem_cGen_of_commute ha ha1 rfl
  set u := g⁻¹ * a⁻¹ * g * a with hu
  have huH : u ∈ cGen E :=
    (cGen E).mul_mem ((cGen E).mul_mem ((cGen E).mul_mem ((cGen E).inv_mem hgH)
      ((cGen E).inv_mem haH)) hgH) haH
  obtain ⟨e₂, he₂, hκ⟩ := exists_siegel_form hAA hi hφ h2K hy (hmove y hy hgy)
  have hBe₂ : spEnd a (spEnd b e₂) = i • spEnd b e₂ := by rw [eig_b hBA he₂, neg_neg]
  obtain ⟨e₁, he₁, he₁0, h0⟩ := exists_compl_eig hAA hBB hBA hi h2K hBe₂
  have h12' : spForm 2 K e₁ e₂ = 0 := by
    rw [hBB, map_neg, neg_eq_zero] at h0
    exact h0
  set κ := spForm 2 K (spEnd u e₂ - e₂) e₂ with hκdef
  have hcc : spForm 2 K (e₁ + e₂) (spEnd a (e₁ + e₂)) = 0 := by
    have h21 : spForm 2 K e₂ e₁ = 0 := by rw [spForm_swap, h12', neg_zero]
    rw [show spEnd a (e₁ + e₂) = i • e₁ + (-i) • e₂ by rw [map_add, he₁, he₂]]
    simp only [map_add, map_smul, LinearMap.add_apply, smul_eq_mul,
      spForm_isAlt.self_eq_zero, h12', h21]
    ring
  have hT : ∀ t, spTransvection e₁ (-8 * t ^ 2 * κ) ∈ cGen E := by
    intro t
    rw [← second_difference hi hL1 hφ h2K he₁ he₂ h12' t]
    have hX := fun s => pair_mem (E := E) ha ha1 haa hcc s
    exact (cGen E).mul_mem ((cGen E).mul_mem ((cGen E).mul_mem ((cGen E).mul_mem
      ((cGen E).mul_mem (hX t) huH) (hX (-t))) ((cGen E).mul_mem ((cGen E).mul_mem (hX (-t)) huH)
        (hX t))) ((cGen E).inv_mem huH)) ((cGen E).inv_mem huH)
  refine ⟨e₁, he₁, he₁0, fun s => ?_⟩
  have h8 : (8 : K) * κ ≠ 0 := mul_ne_zero (by
    rw [show (8 : K) = 2 * 2 * 2 by norm_num]
    exact mul_ne_zero (mul_ne_zero h2K h2K) h2K) hκ
  obtain ⟨t₁, t₂, ht⟩ := exists_sq_add_sq h2K one_ne_zero one_ne_zero (s / (8 * κ))
  have hs : s = -8 * t₁ ^ 2 * κ + -8 * t₂ ^ 2 * κ := by
    have : s / (8 * κ) * (8 * κ) = s := div_mul_cancel₀ s h8
    linear_combination (8 * κ) * ht - this
  rw [hs, ← spTransvection_mul_same]
  exact (cGen E).mul_mem (hT t₁) (hT t₂)

end Center

theorem form_pair_eig {a : StatedSp 2 K} {i : K} {e f : Fin 2 ⊕ Fin 2 → K}
    (he : spEnd a e = i • e) (hf : spEnd a f = -i • f) (hef : spForm 2 K e f = 0) :
    spForm 2 K (e + f) (spEnd a (e + f)) = 0 := by
  have hfe : spForm 2 K f e = 0 := by rw [spForm_swap, hef, neg_zero]
  rw [map_add (spEnd a), he, hf]
  simp only [map_add, map_smul, LinearMap.add_apply, smul_eq_mul,
    spForm_isAlt.self_eq_zero, hef, hfe]
  ring

theorem transCenter_plane {H : Subgroup (StatedSp 2 K)} {x y : Fin 2 ⊕ Fin 2 → K}
    (hx : TransCenter H x) (hy : TransCenter H y) (hxy : spForm 2 K x y ≠ 0) (s t : K) :
    TransCenter H (s • x + t • y) := by
  by_cases hs : s = 0
  · rw [hs, zero_smul, zero_add]
    exact hy.smul t
  by_cases ht : t = 0
  · rw [ht, zero_smul, add_zero]
    exact hx.smul s
  refine (hx.smul s).add (hy.smul t) ?_
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  exact mul_ne_zero ht (mul_ne_zero hs hxy)

section Final

variable {E : Subgroup (StatedProj (StatedSp 2 K))} {a b : StatedSp 2 K}

theorem cGen_eq_top_of_quat_one [Finite K] (h2K : (2 : K) ≠ 0) (h3 : Nat.card K ≠ 3)
    (hK : IsSquare (-1 : K)) (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (hani : ∀ W : Submodule K (Fin 2 ⊕ Fin 2 → K), (∀ x ∈ W, ∀ y ∈ W, spForm 2 K x y = 0) →
      (∀ g : StatedSp 2 K, proj 2 K g ∈ E → ∀ w ∈ W, spEnd g w ∈ W) → W = ⊥)
    (ha : proj 2 K a ∈ E) (hb : proj 2 K b ∈ E) (ha1 : proj 2 K a ≠ 1)
    (hb1 : proj 2 K b ≠ 1) (hab : proj 2 K a ≠ proj 2 K b) (haa : spEnd a * spEnd a = -1)
    (hbb : spEnd b * spEnd b = -1) (hc : spEnd a * spEnd b = -(spEnd b * spEnd a)) :
    cGen E = ⊤ := by
  have hAA : ∀ v, spEnd a (spEnd a v) = -v := fun v => by
    rw [← Module.End.mul_apply, haa, LinearMap.neg_apply, Module.End.one_apply]
  have hBB : ∀ v, spEnd b (spEnd b v) = -v := fun v => by
    rw [← Module.End.mul_apply, hbb, LinearMap.neg_apply, Module.End.one_apply]
  have hBA : ∀ v, spEnd b (spEnd a v) = -(spEnd a (spEnd b v)) := fun v => by
    rw [← Module.End.mul_apply, show spEnd b * spEnd a = -(spEnd a * spEnd b) by rw [hc, neg_neg],
      LinearMap.neg_apply, Module.End.mul_apply]
  obtain ⟨i, hi'⟩ := hK
  have hi : i * i = -1 := hi'.symm
  have hfq : ∀ {x : Fin 2 ⊕ Fin 2 → K}, x ≠ 0 → spEnd a x = i • x →
      spForm 2 K x (spEnd b x) ≠ 0 := fun hx0 hx =>
    form_b_ne_zero hBB hBA hE h4 ha hb ha1 hb1 hab hani hx0 hx
  obtain ⟨e, he, he0, hcen⟩ :=
    exists_transCenter_eig h2K h3 hE h4 hani ha hb ha1 hb1 hab haa hAA hBB hBA hi
  obtain ⟨e', he', he'0, he'b⟩ := exists_compl_eig hAA hBB hBA hi h2K he
  have hκ := hfq he0 he
  have hκ' := hfq he'0 he'
  have hbH : b ∈ cGen E := mem_cGen_of_commute hb hb1 rfl
  have hBe := eig_b hBA he
  have hBe' := eig_b hBA he'
  have hebe' : spForm 2 K e (spEnd b e') = 0 := by
    have := form_adj hBB e e'
    rw [spForm_swap, he'b, neg_zero] at this
    exact neg_eq_zero.1 this.symm
  have hmix : TransCenter (cGen E) (e + e') := by
    have hX := pair_mem (E := E) ha ha1 haa (form_pair_eig he' hBe he'b)
      (2 * spForm 2 K e (spEnd b e))⁻¹
    have := hcen.map hX
    have h1 : 2 * (2 * spForm 2 K e (spEnd b e))⁻¹ * spForm 2 K e (spEnd b e) = 1 := by
      field_simp
    rw [pair_apply_eig h2K hi he' hBe he'b he, h1, one_smul] at this
    exact this
  have hcen' : TransCenter (cGen E) e' := by
    have hX := pair_mem (E := E) ha ha1 haa (form_pair_eig he hBe' hebe')
      (-(2 * spForm 2 K e' (spEnd b e'))⁻¹)
    have := hmix.map hX
    have h1 : 2 * -(2 * spForm 2 K e' (spEnd b e'))⁻¹ * spForm 2 K e' (spEnd b e') = -1 := by
      field_simp
    rw [pair_apply_eig h2K hi he hBe' hebe' (by rw [map_add, he, he', smul_add]), map_add,
      LinearMap.add_apply, hebe', zero_add, h1, neg_one_smul, add_comm e e',
      add_neg_cancel_right] at this
    exact this
  have hP1 := transCenter_plane hcen (hcen.map hbH) hκ
  have hP2 := transCenter_plane hcen' (hcen'.map hbH) hκ'
  have hni : (-i) * (-i) = -1 := by rw [neg_mul_neg, hi]
  have hz1 : ∀ s t : K, spForm 2 K e' (s • e + t • spEnd b e) = 0 := fun s t => by
    simp only [map_add, map_smul, smul_eq_mul, form_eig_eq_zero h2K hi he' he, he'b, mul_zero,
      add_zero]
  have hz2 : ∀ s t : K, spForm 2 K (spEnd b e') (s • e + t • spEnd b e) = 0 := fun s t => by
    have h1 : spForm 2 K (spEnd b e') e = 0 := by rw [spForm_swap, hebe', neg_zero]
    simp only [map_add, map_smul, smul_eq_mul, h1, form_eig_eq_zero h2K hni hBe' hBe, mul_zero,
      add_zero]
  have hsweep1 := transCenter_sweep hκ hP1 (z := e') (form_eig_eq_zero h2K hi he he')
    (by rw [spForm_swap, he'b, neg_zero]) (s₀ := 1) (t₀ := 0) (Or.inl one_ne_zero)
    (by rw [one_smul, zero_smul, add_zero]; exact hmix)
  apply eq_top_of_transCenter
  intro v
  obtain ⟨s, t, s', t', rfl⟩ := exists_comb_eig hBB hBA hi h2K he he' hκ hκ' he'b v
  by_cases hst : s = 0 ∧ t = 0
  · rw [hst.1, hst.2, zero_smul, zero_smul, add_zero, zero_add]
    exact hP2 s' t'
  by_cases hst' : s' = 0 ∧ t' = 0
  · rw [hst'.1, hst'.2, zero_smul, zero_smul, add_zero, add_zero]
    exact hP1 s t
  have h1 := hsweep1 s t (not_and_or.mp hst)
  have e1 : s • e + t • spEnd b e + e' =
      (1 : K) • e' + (0 : K) • spEnd b e' + (s • e + t • spEnd b e) := by module
  rw [e1] at h1
  have h2 := transCenter_sweep (e₁ := e') (e₂ := spEnd b e') (z := s • e + t • spEnd b e) hκ'
    hP2 (hz1 s t) (hz2 s t) (s₀ := 1) (t₀ := 0) (Or.inl one_ne_zero) h1 s' t'
    (not_and_or.mp hst')
  have e2 : s' • e' + t' • spEnd b e' + (s • e + t • spEnd b e) =
      s • e + t • spEnd b e + (s' • e' + t' • spEnd b e') := by abel
  rwa [e2] at h2

end Final

end SpSeitz

theorem seitzFourSp4Q8One_holds : SeitzFourSp4Q8One := by
  intro K _ _ h2K h3 hK E hE h4 hA a b ha hb ha1 hb1 hab haa hbb hc
  have htop := SpSeitz.cGen_eq_top_of_quat_one h2K h3 hK hE h4 hA ha hb ha1 hb1 hab haa hbb hc
  intro k _
  obtain ⟨g, rfl⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective (r := 2) (K := K) k
  have hg : g ∈ SpSeitz.cGen E := htop ▸ Subgroup.mem_top g
  exact hg

theorem seitzFourSp4Q8_holds : SeitzFourSp4Q8 := seitzFourSp4Q8_of_one seitzFourSp4Q8One_holds

theorem seitzFourInner_psp :
    SeitzFourInner fun X _ => ∃ n p f : ℕ, 2 ≤ n ∧ p ≠ 2 ∧ CFSG.Models.LieModel X .PSp n p f :=
  seitzFourInner_psp_of_sp4Q8 seitzFourSp4Q8_holds

end CFSG.LocalAnalysis.WeakClosure81

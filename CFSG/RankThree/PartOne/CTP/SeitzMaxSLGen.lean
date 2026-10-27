module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSLTv
public import CFSG.RankThree.PartOne.CTP.SeitzMaxSL2

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix

section Restriction

variable {n : ℕ} {K : Type} [Field K]

@[expose] def colPair (j : Fin n) (v : Fin n → K) : Matrix (Fin n) (Fin 2) K :=
  Matrix.of fun i c => if c = 0 then (Pi.single j 1 : Fin n → K) i else v i

@[expose] def rows (α β : Fin n → K) : Matrix (Fin 2) (Fin n) K := Matrix.of ![α, β]

omit [Field K] in
@[simp] theorem rows_zero (α β : Fin n → K) : rows α β 0 = α := rfl

omit [Field K] in
@[simp] theorem rows_one (α β : Fin n → K) : rows α β 1 = β := rfl

theorem colPair_mul (j : Fin n) (v : Fin n → K) (Ψ : Matrix (Fin 2) (Fin n) K) :
    colPair j v * Ψ = vecMulVec (Pi.single j 1) (Ψ 0) + vecMulVec v (Ψ 1) := by
  ext i m
  simp [Matrix.mul_apply, Fin.sum_univ_two, colPair, vecMulVec_apply]

theorem mul_colPair (j : Fin n) (v : Fin n → K) (Ψ : Matrix (Fin 2) (Fin n) K) :
    Ψ * colPair j v = !![Ψ 0 j, Ψ 0 ⬝ᵥ v; Ψ 1 j, Ψ 1 ⬝ᵥ v] := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [Matrix.mul_apply, colPair, dotProduct, Pi.single_apply]

theorem one_add_mul_mul {m r : Type*} [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]
    (Φ : Matrix m r K) (Ψ Ψ' : Matrix r m K) :
    (1 + Φ * Ψ) * (1 + Φ * Ψ') = 1 + Φ * (Ψ + Ψ' + Ψ * Φ * Ψ') := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

theorem one_add_mul_mul' {m r : Type*} [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]
    (Φ : Matrix m r K) (Ψ Ψ' : Matrix r m K) :
    (1 + Ψ * Φ) * (1 + Ψ' * Φ) = 1 + (Ψ + Ψ' + Ψ * Φ * Ψ') * Φ := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

@[expose] def restrictSet (H : Subgroup (SpecialLinearGroup (Fin n) K)) (j : Fin n)
    (v : Fin n → K) : Set (SpecialLinearGroup (Fin 2) K) :=
  {X | ∃ g ∈ H, ∃ Ψ : Matrix (Fin 2) (Fin n) K,
    (g : Matrix (Fin n) (Fin n) K) = 1 + colPair j v * Ψ ∧
      (X : Matrix (Fin 2) (Fin 2) K) = 1 + Ψ * colPair j v}

theorem restrictSet_mul {H : Subgroup (SpecialLinearGroup (Fin n) K)} {j : Fin n}
    {v : Fin n → K} {X Y : SpecialLinearGroup (Fin 2) K} (hX : X ∈ restrictSet H j v)
    (hY : Y ∈ restrictSet H j v) : X * Y ∈ restrictSet H j v := by
  obtain ⟨g, hg, Ψ, hgΨ, hXΨ⟩ := hX
  obtain ⟨g', hg', Ψ', hgΨ', hYΨ⟩ := hY
  refine ⟨g * g', H.mul_mem hg hg', Ψ + Ψ' + Ψ * colPair j v * Ψ', ?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, hgΨ, hgΨ', one_add_mul_mul]
  · rw [Matrix.SpecialLinearGroup.coe_mul, hXΨ, hYΨ, one_add_mul_mul']

theorem one_mem_restrictSet (H : Subgroup (SpecialLinearGroup (Fin n) K)) (j : Fin n)
    (v : Fin n → K) : (1 : SpecialLinearGroup (Fin 2) K) ∈ restrictSet H j v :=
  ⟨1, H.one_mem, 0, by simp, by simp⟩

@[expose] def restrictSubgroup [Finite K] (H : Subgroup (SpecialLinearGroup (Fin n) K))
    (j : Fin n) (v : Fin n → K) : Subgroup (SpecialLinearGroup (Fin 2) K) where
  carrier := restrictSet H j v
  mul_mem' := restrictSet_mul
  one_mem' := one_mem_restrictSet H j v
  inv_mem' := fun {X} hX => by
    have hpow : ∀ m : ℕ, X ^ m ∈ restrictSet H j v := by
      intro m
      induction m with
      | zero => rw [pow_zero]; exact one_mem_restrictSet H j v
      | succ m ih => rw [pow_succ]; exact restrictSet_mul ih hX
    obtain ⟨m, hm⟩ : ∃ m, orderOf X = m + 1 := ⟨orderOf X - 1, by have := orderOf_pos X; omega⟩
    have h1 : X ^ (m + 1) = 1 := hm ▸ pow_orderOf_eq_one X
    have : X⁻¹ = X ^ m := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact h1)
    rw [this]
    exact hpow m

theorem single_rat {k : Subfield K} (m : Fin n) : ∀ i, (Pi.single m (1 : K) : Fin n → K) i ∈ k := by
  intro i
  by_cases h : i = m
  · subst h
    simp [k.one_mem]
  · simp [h, k.zero_mem]

end Restriction

section Generic

variable {n : ℕ} {K : Type} [Field K] [CharP K 2] {k : Subfield K}
  {H : Subgroup (SpecialLinearGroup (Fin n) K)}

omit [CharP K 2] in
theorem tv_eq_scale {v φ : Fin n → K} (h : φ ⬝ᵥ v = 0) {c : K} (hc : c ≠ 0) :
    tv v φ h = tv (c • v) (c⁻¹ • φ) (by rw [smul_dotProduct, dotProduct_smul, h]; simp) := by
  apply Subtype.ext
  rw [tv_coe, tv_coe, smul_vecMulVec, vecMulVec_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]

omit [CharP K 2] in
theorem exists_smul_of_vanishing {ψ₀ φ : Fin n → K} (hψ₀ : ∀ i, ψ₀ i ∈ k) (hψ₀0 : ψ₀ ≠ 0)
    (hvan : ∀ e : Fin n → K, (∀ i, e i ∈ k) → ψ₀ ⬝ᵥ e = 0 → φ ⬝ᵥ e = 0) :
    ∃ c : K, φ = c • ψ₀ := by
  obtain ⟨i, hi⟩ : ∃ i, ψ₀ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hψ₀0 (funext h)
  refine ⟨φ i / ψ₀ i, funext fun m => ?_⟩
  set e : Fin n → K := ψ₀ i • (Pi.single m 1 : Fin n → K) - ψ₀ m • (Pi.single i 1 : Fin n → K)
    with hedef
  have her : ∀ x, e x ∈ k := fun x => by
    rw [hedef, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    exact k.sub_mem (k.mul_mem (hψ₀ i) (single_rat m x)) (k.mul_mem (hψ₀ m) (single_rat i x))
  have hψe : ψ₀ ⬝ᵥ e = 0 := by
    rw [hedef, dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_single_one,
      dotProduct_single_one, smul_eq_mul, smul_eq_mul]
    ring
  have h1 := hvan e her hψe
  rw [hedef, dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_single_one,
    dotProduct_single_one, smul_eq_mul, smul_eq_mul] at h1
  rw [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination h1

theorem tv_mem_slSub_or_generic (hk : slSub n k ≤ H) (hn : 3 ≤ n)
    (NIR : ∀ a ∉ k, ∀ (i j : Fin n) (hij : i ≠ j), SpecialLinearGroup.transvection hij a ∉ H)
    {v φ : Fin n → K} (hφv : φ ⬝ᵥ v = 0) (hτ : tv v φ hφv ∈ H) (hv0 : v ≠ 0) :
    tv v φ hφv ∈ slSub n k ∨
      ∀ ψ : Fin n → K, (∀ i, ψ i ∈ k) → ψ ⬝ᵥ v = 0 → ψ = 0 := by
  by_cases hgen : ∀ ψ : Fin n → K, (∀ i, ψ i ∈ k) → ψ ⬝ᵥ v = 0 → ψ = 0
  · exact Or.inr hgen
  refine Or.inl ?_
  push Not at hgen
  obtain ⟨ψ₀, hψ₀, hψ₀v, hψ₀0⟩ := hgen
  have hcomm : ∀ e : Fin n → K, (∀ i, e i ∈ k) → ψ₀ ⬝ᵥ e = 0 →
      ∀ i, ((φ ⬝ᵥ e) • v) i ∈ k := by
    intro e he hψe
    have hs : tv e ψ₀ hψe ∈ H := hk (tv_mem_slSub hψe he hψ₀)
    have h1 := H.mul_mem (H.mul_mem hs hτ) (H.mul_mem hs hτ)
    rw [tv_sq hφv hψe hψ₀v] at h1
    have h2 : tv ((φ ⬝ᵥ e) • v) ψ₀ (by rw [dotProduct_smul, hψ₀v, smul_zero]) ∈ H := by
      rw [tv_smul (φ ⬝ᵥ e) hψ₀v]
      exact h1
    exact rat_center_of_rat_axis hk hn NIR hψ₀ hψ₀0 _ h2
  by_cases hex : ∃ e : Fin n → K, (∀ i, e i ∈ k) ∧ ψ₀ ⬝ᵥ e = 0 ∧ φ ⬝ᵥ e ≠ 0
  · obtain ⟨e, he, hψe, hφe⟩ := hex
    set c := φ ⬝ᵥ e with hc
    have hw := hcomm e he hψe
    have hw0 : c • v ≠ 0 := smul_ne_zero hφe hv0
    have hdot : (c⁻¹ • φ) ⬝ᵥ (c • v) = 0 := by
      rw [smul_dotProduct, dotProduct_smul, hφv]; simp
    have hmem : tv (c • v) (c⁻¹ • φ) hdot ∈ H := by
      rw [← tv_eq_scale hφv hφe]
      exact hτ
    have hrat := rat_axis_of_rat_center hk hn NIR hw hw0 hdot hmem
    rw [tv_eq_scale hφv hφe]
    exact tv_mem_slSub hdot hw hrat
  · push Not at hex
    obtain ⟨c, hcφ⟩ := exists_smul_of_vanishing hψ₀ hψ₀0 (fun e he hψe => hex e he hψe)
    have hdot : ψ₀ ⬝ᵥ (c • v) = 0 := by rw [dotProduct_smul, hψ₀v, smul_zero]
    have hmem : tv (c • v) ψ₀ hdot ∈ H := by
      have : tv v φ hφv = tv (c • v) ψ₀ hdot := by
        subst hcφ
        exact (tv_smul c hψ₀v).symm
      rw [← this]
      exact hτ
    have hrat := rat_center_of_rat_axis hk hn NIR hψ₀ hψ₀0 hdot hmem
    have : tv v φ hφv = tv (c • v) ψ₀ hdot := by
      subst hcφ
      exact (tv_smul c hψ₀v).symm
    rw [this]
    exact tv_mem_slSub hdot hrat hψ₀

end Generic

section Main

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_root_of_generic {k : Subfield K} {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hnd : n < d) (hn : 3 ≤ n) (hK : Nat.card K = Nat.card k ^ d)
    {H : Subgroup (SpecialLinearGroup (Fin n) K)} (hk : slSub n k ≤ H) {v φ : Fin n → K}
    (hφv : φ ⬝ᵥ v = 0) (hτ : tv v φ hφv ∈ H) (hφ0 : φ ≠ 0)
    (hgen : ∀ ψ : Fin n → K, (∀ i, ψ i ∈ k) → ψ ⬝ᵥ v = 0 → ψ = 0) :
    ∃ a ∉ k, ∃ (i j : Fin n) (hij : i ≠ j), SpecialLinearGroup.transvection hij a ∈ H := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, φ j ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ0 (funext h)
  obtain ⟨m₁, hm₁j, -⟩ := exists_fin_ne_ne' hn j j
  obtain ⟨m₂, hm₂j, hm₂m₁⟩ := exists_fin_ne_ne' hn j m₁
  have ha₁ : v m₁ ≠ 0 := by
    intro h0
    have h1 := hgen (Pi.single m₁ 1) (single_rat m₁) (by rw [single_dotProduct, h0, mul_zero])
    simpa using congrFun h1 m₁
  have ha₂ : v m₂ / v m₁ ∉ k := by
    intro hc
    set ψ : Fin n → K := (Pi.single m₂ 1 : Fin n → K) - (v m₂ / v m₁) • (Pi.single m₁ 1 : Fin n → K)
      with hψdef
    have hψ : ∀ i, ψ i ∈ k := by
      intro i
      rw [hψdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact k.sub_mem (single_rat m₂ i) (k.mul_mem hc (single_rat m₁ i))
    have hdot : ψ ⬝ᵥ v = 0 := by
      rw [hψdef, sub_dotProduct, smul_dotProduct, single_dotProduct, single_dotProduct,
        smul_eq_mul]
      field_simp
      ring
    have h1 := congrFun (hgen ψ hψ hdot) m₂
    simp [hψdef, hm₂m₁] at h1
  have hu : ∀ c₁ ∈ k, ∀ c₂ ∈ k, u2 (c₁ * v m₁ + c₂ * v m₂) ∈ restrictSubgroup H j v := by
    intro c₁ hc₁ c₂ hc₂
    set ψ : Fin n → K := c₁ • (Pi.single m₁ 1 : Fin n → K) + c₂ • (Pi.single m₂ 1 : Fin n → K)
      with hψdef
    have hψrat : ∀ i, ψ i ∈ k := fun i => by
      rw [hψdef, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      exact k.add_mem (k.mul_mem hc₁ (single_rat m₁ i)) (k.mul_mem hc₂ (single_rat m₂ i))
    have hψj0 : ψ j = 0 := by
      rw [hψdef]
      simp [hm₁j, hm₂j]
    have hψj : ψ ⬝ᵥ (Pi.single j 1 : Fin n → K) = 0 := by
      rw [dotProduct_single_one]
      exact hψj0
    have hψv : ψ ⬝ᵥ v = c₁ * v m₁ + c₂ * v m₂ := by
      rw [hψdef, add_dotProduct, smul_dotProduct, smul_dotProduct, single_dotProduct,
        single_dotProduct]
      simp
    refine ⟨tv (Pi.single j 1) ψ hψj, hk (tv_mem_slSub hψj (single_rat j) hψrat),
      rows ψ 0, ?_, ?_⟩
    · rw [tv_coe, colPair_mul]
      simp
    · rw [mul_colPair, u2_coe]
      ext r c
      fin_cases r <;> fin_cases c <;> simp [hψv, hψj0]
  have hl : l2 (φ j) ∈ restrictSubgroup H j v := by
    refine ⟨tv v φ hφv, hτ, rows 0 φ, ?_, ?_⟩
    · rw [tv_coe, colPair_mul]
      simp
    · rw [mul_colPair, l2_coe]
      ext r c
      fin_cases r <;> fin_cases c <;> simp [hφv]
  have hM : restrictSubgroup H j v = ⊤ :=
    sl2_eq_top_of_root_groups hd hd2 hK ha₁ ha₂ hj hu hl
  obtain ⟨a, haS⟩ : ∃ a : K, a ∉ Set.range (fun c : Fin n → k => ∑ m, (c m : K) * v m) := by
    by_contra h
    push Not at h
    have hsurj : Function.Surjective (fun c : Fin n → k => ∑ m, (c m : K) * v m) :=
      fun a => h a
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    simp only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    rw [hK] at h1
    have h2 : 2 ≤ Nat.card k := Finite.one_lt_card
    exact absurd h1 (not_le.mpr (Nat.pow_lt_pow_right h2 hnd))
  have ha0 : a ≠ 0 := fun h => haS ⟨0, by simp [h]⟩
  have hau : u2 a ∈ restrictSubgroup H j v := hM ▸ Subgroup.mem_top _
  obtain ⟨g, hg, Ψ, hgΨ, hXΨ⟩ := hau
  rw [mul_colPair, u2_coe] at hXΨ
  have e00 := congrFun (congrFun hXΨ 0) 0
  have e01 := congrFun (congrFun hXΨ 0) 1
  have e10 := congrFun (congrFun hXΨ 1) 0
  have e11 := congrFun (congrFun hXΨ 1) 1
  simp at e00 e01 e10 e11
  have hgmat : (g : Matrix (Fin n) (Fin n) K) =
      1 + (vecMulVec (Pi.single j 1) (Ψ 0) + vecMulVec v (Ψ 1)) := by
    rw [hgΨ, colPair_mul]
  suffices key : ∃ γ : Fin n → K, ∃ hγ : γ ⬝ᵥ (Pi.single j 1 : Fin n → K) = 0,
      tv (Pi.single j 1) γ hγ ∈ H ∧ ∃ m, γ m ∉ k by
    obtain ⟨γ, hγ, hmem, m, hm⟩ := key
    obtain ⟨l, hl, hroot⟩ := root_mem_of_tv_single hk hn hγ hmem m
    exact ⟨γ m, hm, j, l, hl, hroot⟩
  by_cases hβ : Ψ 1 = 0
  ·
    have hα : Ψ 0 ⬝ᵥ (Pi.single j 1 : Fin n → K) = 0 := by
      rw [dotProduct_single_one]
      exact e00
    have hgtv : g = tv (Pi.single j 1) (Ψ 0) hα := by
      apply Subtype.ext
      rw [hgmat, tv_coe, hβ]
      simp
    refine ⟨Ψ 0, hα, hgtv ▸ hg, ?_⟩
    by_contra hall
    push Not at hall
    apply haS
    exact ⟨fun m => ⟨Ψ 0 m, hall m⟩, by rw [e01]; rfl⟩
  ·
    have hZ : Ψ * colPair j v = !![0, a; 0, 0] := by
      rw [mul_colPair, e00, ← e01, ← e10, e11]
    have hNN : (colPair j v * Ψ) * (colPair j v * Ψ) =
        vecMulVec (Pi.single j 1) (a • Ψ 1) := by
      have h1 : (colPair j v * Ψ) * (colPair j v * Ψ) = colPair j v * ((Ψ * colPair j v) * Ψ) := by
        simp only [Matrix.mul_assoc]
      have h2 : (!![0, a; 0, 0] : Matrix (Fin 2) (Fin 2) K) * Ψ = rows (a • Ψ 1) 0 := by
        ext r m
        fin_cases r <;> simp [Matrix.mul_apply, Fin.sum_univ_two, rows]
      rw [h1, hZ, h2, colPair_mul]
      simp
    have hgg : ((g * g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        1 + vecMulVec (Pi.single j 1) (a • Ψ 1) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, hgΨ]
      have h3 : (1 + colPair j v * Ψ) * (1 + colPair j v * Ψ) =
          1 + (colPair j v * Ψ + colPair j v * Ψ) +
            (colPair j v * Ψ) * (colPair j v * Ψ) := by
        noncomm_ring
      rw [h3, matrix_add_self, hNN]
      simp
    have hγ : (a • Ψ 1) ⬝ᵥ (Pi.single j 1 : Fin n → K) = 0 := by
      rw [smul_dotProduct, dotProduct_single_one, ← e10, smul_zero]
    have hggtv : g * g = tv (Pi.single j 1) (a • Ψ 1) hγ := Subtype.ext hgg
    refine ⟨a • Ψ 1, hγ, hggtv ▸ H.mul_mem hg hg, ?_⟩
    by_contra hall
    push Not at hall
    have h0 := hgen (a • Ψ 1) hall (by rw [smul_dotProduct, e11, smul_zero])
    exact hβ ((smul_eq_zero.mp h0).resolve_left ha0)

end Main

end CFSG.RankThree.PartOne.CTP

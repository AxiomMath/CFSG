module

public import CFSG.LocalAnalysis.StandardType.GGQ2EichlerDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCZ1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggMonoE_zmod3_sq : ∀ a : ZMod 3, a ≠ 0 → a * a = 1 := by decide

private lemma ggMonoE_zmod3_cube : ∀ a : ZMod 3, a * a * a = 1 → a = 1 := by decide

private lemma ggMonoE_zmod3_one_add_one : (1 : ZMod 3) + 1 = -1 := by decide

private lemma ggMonoE_zmod3_mul_two : ∀ x : ZMod 3, x * 2 = -x := by decide

theorem ggEichler_not_monomial {U : Type} [AddCommGroup U] [Module (ZMod 3) U] {n : ℕ}
    (f : Fin n → U) (hf : LinearIndependent (ZMod 3) f)
    (hspan : Submodule.span (ZMod 3) (Set.range f) = ⊤)
    (g : U ≃ₗ[ZMod 3] U) (σ : Equiv.Perm (Fin n)) (ε : Fin n → ZMod 3) (hε : ∀ i, ε i ≠ 0)
    (hg : ∀ i, g (f i) = ε i • f (σ i)) : ¬ GGEichler g := by
  rintro ⟨hne, hE⟩
  have h3 : ∀ v, g (g (g v)) = v := by
    intro v
    have h1 : g (g v) + g v = -v := eq_neg_iff_add_eq_zero.mpr (hE v)
    have h2 : g (g (g v)) + (g (g v) + g v) = 0 := by
      simpa only [add_assoc] using hE (g v)
    rw [h1] at h2
    simpa using (eq_neg_iff_add_eq_zero.mpr h2)
  have hgg : ∀ i, g (g (g (f i))) = (ε i * ε (σ i) * ε (σ (σ i))) • f (σ (σ (σ i))) := by
    intro i
    simp only [hg, map_smul, smul_smul, mul_assoc]
  have hσ3 : ∀ i, σ (σ (σ i)) = i := by
    intro i
    have hrel : (ε i * ε (σ i) * ε (σ (σ i))) • f (σ (σ (σ i))) = (1 : ZMod 3) • f i := by
      rw [← hgg i, h3 (f i), one_smul]
    exact LinearIndependent.eq_of_smul_apply_eq_smul_apply hf
      (ε i * ε (σ i) * ε (σ (σ i))) 1 (σ (σ (σ i))) i
      (mul_ne_zero (mul_ne_zero (hε i) (hε (σ i))) (hε (σ (σ i)))) hrel
  by_cases hfix : ∀ i, σ i = i
  · have hgid : ∀ i, g (f i) = f i := by
      intro i
      have hcube : ε i * ε i * ε i = 1 := by
        have h1 := hgg i
        simp only [hfix] at h1
        rw [h3 (f i)] at h1
        have h2 : (ε i * ε i * ε i - 1) • f i = 0 := by
          rw [sub_smul, one_smul, ← h1, sub_self]
        rcases smul_eq_zero.mp h2 with h0 | h0
        · exact sub_eq_zero.mp h0
        · exact absurd h0 (hf.ne_zero i)
      have heq1 : ε i = 1 := ggMonoE_zmod3_cube (ε i) hcube
      rw [hg i, hfix i, heq1, one_smul]
    have hmap : (g : U →ₗ[ZMod 3] U) = (1 : U →ₗ[ZMod 3] U) :=
      LinearMap.ext_on hspan (by rintro x ⟨i, rfl⟩; exact hgid i)
    exact hne (LinearEquiv.ext (fun v => DFunLike.congr_fun hmap v))
  · obtain ⟨i, hi⟩ := not_forall.mp hfix
    have hσ2i : σ (σ i) ≠ i := by
      intro h
      have h' : σ (σ (σ i)) = σ i := congrArg σ h
      rw [hσ3 i] at h'
      exact hi h'.symm
    have hσi_ne_σ2i : σ i ≠ σ (σ i) := by
      intro h
      exact hσ2i ((congrArg σ h).trans (hσ3 i))
    have hi_ne_σ2i : i ≠ σ (σ i) := by
      intro h
      exact hi ((congrArg σ h).trans (hσ3 i))
    have hrel : f i + ε i • f (σ i) + (ε i * ε (σ i)) • f (σ (σ i)) = 0 := by
      have h := hE (f i)
      have hgg2 : g (g (f i)) = (ε i * ε (σ i)) • f (σ (σ i)) := by
        simp only [hg, map_smul, smul_smul]
      rw [hgg2, hg i] at h
      simpa only [add_comm, add_left_comm, add_assoc] using h
    let e : Fin 3 → Fin n := ![i, σ i, σ (σ i)]
    have he : Function.Injective e := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [e]
    have hli : LinearIndependent (ZMod 3) (f ∘ e) := hf.comp e he
    have hzero : ∑ j : Fin 3, (![1, ε i, ε i * ε (σ i)] : Fin 3 → ZMod 3) j • (f ∘ e) j = 0 := by
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Function.comp_apply, e, one_smul]
      exact hrel
    have h0 := (Fintype.linearIndependent_iff.mp hli) (![1, ε i, ε i * ε (σ i)]) hzero 0
    exact one_ne_zero h0

private def ggMonoE_monomial {n : ℕ} (g : GGBCV n ≃ₗ[ZMod 3] GGBCV n) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (ε : Fin n → ZMod 3), (∀ i, ε i ≠ 0) ∧
    ∀ i, g (Pi.single i 1) = ε i • Pi.single (σ i) 1

private def ggMonoE_monGroup {n : ℕ} : Subgroup (GGBCV n ≃ₗ[ZMod 3] GGBCV n) where
  carrier := {g | ggMonoE_monomial g}
  one_mem' := by
    refine ⟨1, fun _ => 1, fun _ => one_ne_zero, fun i => ?_⟩
    simp
  mul_mem' := by
    rintro g h ⟨σ, ε, hε, hg⟩ ⟨τ, δ, hδ, hh⟩
    refine ⟨σ * τ, fun i => δ i * ε (τ i), fun i => mul_ne_zero (hδ i) (hε (τ i)), fun i => ?_⟩
    rw [LinearEquiv.mul_apply, hh i, map_smul, hg (τ i), smul_smul]
    rfl
  inv_mem' := by
    rintro g ⟨σ, ε, hε, hg⟩
    refine ⟨σ⁻¹, fun i => (ε (σ⁻¹ i))⁻¹, fun i => inv_ne_zero (hε _), fun i => ?_⟩
    have h := hg (σ⁻¹ i)
    rw [show σ (σ⁻¹ i) = i from Equiv.apply_symm_apply σ i] at h
    have h2 : ε (σ⁻¹ i) • g⁻¹ (Pi.single i 1) = Pi.single (σ⁻¹ i) 1 := by
      rw [← map_smul, ← h]
      exact LinearEquiv.symm_apply_apply g _
    rw [← h2, inv_smul_smul₀ (hε (σ⁻¹ i))]

private lemma ggMonoE_eq_smul_single_of_card_one {n : ℕ} {c : GGBCV n}
    (h : (Finset.univ.filter (fun i => c i ≠ 0)).card = 1) :
    ∃ k, c k ≠ 0 ∧ c = c k • Pi.single k 1 := by
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h
  have hk_mem : k ∈ Finset.univ.filter (fun i => c i ≠ 0) := by
    rw [hk]; exact Finset.mem_singleton_self k
  refine ⟨k, (Finset.mem_filter.mp hk_mem).2, ?_⟩
  funext i
  by_cases hi : i = k
  · subst hi; simp
  · have hnot : i ∉ Finset.univ.filter (fun i => c i ≠ 0) := by rw [hk]; simp [hi]
    have hci : c i = 0 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
    rw [Pi.smul_apply, Pi.single_apply, if_neg hi, smul_zero]
    exact hci

private lemma ggMonoE_eq_pair_of_card_two {n : ℕ} {c : GGBCV n}
    (h : (Finset.univ.filter (fun i => c i ≠ 0)).card = 2) :
    ∃ i j, i ≠ j ∧ c i ≠ 0 ∧ c j ≠ 0 ∧
      c = c i • Pi.single i 1 + c j • Pi.single j 1 := by
  obtain ⟨i, j, hij, hset⟩ := Finset.card_eq_two.mp h
  have hi_mem : i ∈ Finset.univ.filter (fun m => c m ≠ 0) := by rw [hset]; simp [hij]
  have hj_mem : j ∈ Finset.univ.filter (fun m => c m ≠ 0) := by rw [hset]; simp
  refine ⟨i, j, hij, (Finset.mem_filter.mp hi_mem).2, (Finset.mem_filter.mp hj_mem).2, ?_⟩
  funext p
  by_cases hpi : p = i
  · subst hpi
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_apply, Pi.single_apply, if_pos rfl,
      if_neg hij, smul_eq_mul, mul_one, smul_eq_mul, mul_zero, add_zero]
  · by_cases hpj : p = j
    · subst hpj
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_apply, Pi.single_apply,
        if_neg (Ne.symm hij), if_pos rfl, smul_eq_mul, mul_zero, smul_eq_mul, mul_one, zero_add]
    · have hnot : p ∉ Finset.univ.filter (fun m => c m ≠ 0) := by rw [hset]; simp [hpi, hpj]
      have hcp : c p = 0 := by
        by_contra hne
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hne⟩)
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_apply, Pi.single_apply,
        if_neg hpi, if_neg hpj, smul_eq_mul, mul_zero, smul_eq_mul, mul_zero, add_zero]
      exact hcp

private lemma ggMonoE_dot_self_smul_single {n : ℕ} (k : Fin n) (a : ZMod 3) (ha : a ≠ 0) :
    (a • Pi.single k 1 : GGBCV n) ⬝ᵥ (a • Pi.single k 1) = 1 := by
  rw [smul_dotProduct, dotProduct_smul, dotProduct_single_one, Pi.single_eq_same]
  simp only [smul_eq_mul, mul_one]
  exact ggMonoE_zmod3_sq a ha

private lemma ggMonoE_dot_self_pair {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a b : ZMod 3)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (a • Pi.single i 1 + b • Pi.single j 1 : GGBCV n) ⬝ᵥ
      (a • Pi.single i 1 + b • Pi.single j 1) = 2 := by
  simp [dotProduct_add, dotProduct_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hij,
    Ne.symm hij, ggMonoE_zmod3_sq a ha, ggMonoE_zmod3_sq b hb]
  decide

private lemma ggMonoE_dot_pair {n : ℕ} (i j m : Fin n) (hij : i ≠ j) (a b : ZMod 3) :
    (a • Pi.single i 1 + b • Pi.single j 1 : GGBCV n) ⬝ᵥ Pi.single m 1 =
      if m = i then a else if m = j then b else 0 := by
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, dotProduct_single_one,
    dotProduct_single_one, Pi.single_apply, Pi.single_apply]
  by_cases hmi : m = i <;> by_cases hmj : m = j <;> simp_all [smul_eq_mul]

private lemma ggMonoE_monomial_refl_weight_one {n : ℕ} {c : GGBCV n} (hc : c ⬝ᵥ c ≠ 0)
    (hcard : (Finset.univ.filter (fun i => c i ≠ 0)).card = 1) :
    ggMonoE_monomial (ggBCRefl c hc) := by
  obtain ⟨k, hk, hc_eq⟩ := ggMonoE_eq_smul_single_of_card_one hcard
  refine ⟨1, fun i => if i = k then -1 else 1, ?_, ?_⟩
  · intro i
    by_cases h : i = k <;> simp [h]
  · intro i
    have hcc : c ⬝ᵥ c = 1 := by
      rw [hc_eq]
      exact ggMonoE_dot_self_smul_single k (c k) hk
    have hci : c ⬝ᵥ Pi.single i 1 = c i := dotProduct_single_one c i
    have hci' : c i = if i = k then c k else 0 := by
      by_cases hik : i = k
      · subst hik
        rw [if_pos rfl]
      · rw [if_neg hik]
        have h := congr_fun hc_eq i
        rw [Pi.smul_apply, Pi.single_eq_of_ne hik, smul_zero] at h
        exact h
    rw [ggQ2x_ggBCRefl_apply, hcc, hci, mul_one, hci']
    have h1i : (1 : Equiv.Perm (Fin n)) i = i := rfl
    simp only [h1i]
    by_cases hik : i = k
    · rw [if_pos hik, hc_eq, smul_smul]
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      rw [ggMonoE_zmod3_sq (c k) hk, one_smul, hik]
      rw [if_pos rfl, ← ggMonoE_zmod3_one_add_one, add_smul, one_smul]
    · rw [if_neg hik, zero_smul, add_zero, if_neg hik, one_smul]

private lemma ggMonoE_refl_single_left {n : ℕ} {c : GGBCV n} (hc : c ⬝ᵥ c ≠ 0)
    {i j : Fin n} (hij : i ≠ j) (hi : c i ≠ 0) (hj : c j ≠ 0)
    (hc_eq : c = c i • Pi.single i 1 + c j • Pi.single j 1) :
    ggBCRefl c hc (Pi.single i 1) = -(c i * c j) • Pi.single j 1 := by
  have hcc : c ⬝ᵥ c = 2 := by
    rw [hc_eq]; exact ggMonoE_dot_self_pair i j hij (c i) (c j) hi hj
  rw [ggQ2x_ggBCRefl_apply, hcc, dotProduct_single_one, ggMonoE_zmod3_mul_two, hc_eq]
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hij, Ne.symm hij]
  have hX : c i * c i = 1 := ggMonoE_zmod3_sq (c i) hi
  rw [smul_smul, smul_smul, hX]
  simp

private lemma ggMonoE_refl_single_right {n : ℕ} {c : GGBCV n} (hc : c ⬝ᵥ c ≠ 0)
    {i j : Fin n} (hij : i ≠ j) (hi : c i ≠ 0) (hj : c j ≠ 0)
    (hc_eq : c = c i • Pi.single i 1 + c j • Pi.single j 1) :
    ggBCRefl c hc (Pi.single j 1) = -(c i * c j) • Pi.single i 1 := by
  have hcc : c ⬝ᵥ c = 2 := by
    rw [hc_eq]; exact ggMonoE_dot_self_pair i j hij (c i) (c j) hi hj
  rw [ggQ2x_ggBCRefl_apply, hcc, dotProduct_single_one, ggMonoE_zmod3_mul_two, hc_eq]
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hij, Ne.symm hij]
  have hX : c j * c j = 1 := ggMonoE_zmod3_sq (c j) hj
  rw [smul_smul, smul_smul, hX, mul_comm (c j) (c i)]
  simp

private lemma ggMonoE_refl_single_other {n : ℕ} {c : GGBCV n} (hc : c ⬝ᵥ c ≠ 0)
    {i j m : Fin n} (hij : i ≠ j) (hi : c i ≠ 0) (hj : c j ≠ 0)
    (hc_eq : c = c i • Pi.single i 1 + c j • Pi.single j 1) (hmi : m ≠ i) (hmj : m ≠ j) :
    ggBCRefl c hc (Pi.single m 1) = Pi.single m 1 := by
  have hcc : c ⬝ᵥ c = 2 := by
    rw [hc_eq]; exact ggMonoE_dot_self_pair i j hij (c i) (c j) hi hj
  have hcm : c ⬝ᵥ Pi.single m 1 = 0 := by
    rw [hc_eq, ggMonoE_dot_pair i j m hij (c i) (c j)]
    rw [if_neg hmi, if_neg hmj]
  rw [ggQ2x_ggBCRefl_apply, hcc, hcm]
  rw [zero_mul, zero_smul, add_zero]

private lemma ggMonoE_monomial_refl_weight_two {n : ℕ} {c : GGBCV n} (hc : c ⬝ᵥ c ≠ 0)
    (hcard : (Finset.univ.filter (fun i => c i ≠ 0)).card = 2) :
    ggMonoE_monomial (ggBCRefl c hc) := by
  obtain ⟨i, j, hij, hi, hj, hc_eq⟩ := ggMonoE_eq_pair_of_card_two hcard
  refine ⟨Equiv.swap i j, fun m => if m = i ∨ m = j then -(c i * c j) else 1, ?_, ?_⟩
  · intro m
    change (if m = i ∨ m = j then -(c i * c j) else 1) ≠ 0
    by_cases h : m = i ∨ m = j
    · rw [if_pos h]
      exact neg_ne_zero.mpr (mul_ne_zero hi hj)
    · rw [if_neg h]
      exact one_ne_zero
  · intro m
    by_cases hmi : m = i
    · subst hmi
      rw [ggMonoE_refl_single_left hc hij hi hj hc_eq]
      simp [Equiv.swap_apply_left]
    · by_cases hmj : m = j
      · subst hmj
        rw [ggMonoE_refl_single_right hc hij hi hj hc_eq]
        simp [Equiv.swap_apply_right]
      · rw [ggMonoE_refl_single_other hc hij hi hj hc_eq hmi hmj]
        simp [if_neg (show ¬(m = i ∨ m = j) from fun h => h.elim hmi hmj),
          Equiv.swap_apply_of_ne_of_ne hmi hmj]

private lemma ggMonoE_reflSet_subset {n : ℕ} {S : Set (GGBCV n)} (hS : S ⊆ ggBCRoots n) :
    ggBCReflSet S ⊆ (ggMonoE_monGroup (n := n) : Set (GGBCV n ≃ₗ[ZMod 3] GGBCV n)) := by
  rintro t ⟨c, hcS, hc, rfl⟩
  have hroot := hS hcS
  simp only [ggBCRoots, Set.mem_setOf_eq, ggBCWt] at hroot
  have hcard : (Finset.univ.filter (fun i => c i ≠ 0)).card = 1 ∨
      (Finset.univ.filter (fun i => c i ≠ 0)).card = 2 := by omega
  rcases hcard with h1 | h2
  · exact ggMonoE_monomial_refl_weight_one hc h1
  · exact ggMonoE_monomial_refl_weight_two hc h2

theorem ggBCReflGp_monomial {n : ℕ} {S : Set (GGBCV n)} (hS : S ⊆ ggBCRoots n)
    {g : GGBCV n ≃ₗ[ZMod 3] GGBCV n} (hg : g ∈ ggBCReflGp S) :
    ∃ (σ : Equiv.Perm (Fin n)) (ε : Fin n → ZMod 3), (∀ i, ε i ≠ 0) ∧
      ∀ i, g (Pi.single i 1) = ε i • Pi.single (σ i) 1 := by
  have hle : ggBCReflGp S ≤ ggMonoE_monGroup := by
    change Subgroup.closure (ggBCReflSet S) ≤ ggMonoE_monGroup
    rw [Subgroup.closure_le]
    exact ggMonoE_reflSet_subset hS
  exact hle hg

end CFSG.StandardType

end

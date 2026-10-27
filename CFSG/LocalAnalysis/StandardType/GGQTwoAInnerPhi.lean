module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBCZ1
public import CFSG.LocalAnalysis.StandardType.GGQTwoInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoQuandleSym

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

@[expose] noncomputable def ggPermHom (m : ℕ) :
    Equiv.Perm (Fin m) →* (GGBCV m ≃ₗ[ZMod 3] GGBCV m) where
  toFun σ :=
    { toFun := fun v => v ∘ σ.symm
      invFun := fun v => v ∘ σ
      left_inv v := by funext i; simp
      right_inv v := by funext i; simp
      map_add' v w := by funext i; simp
      map_smul' c v := by funext i; simp }
  map_one' := by
    apply LinearEquiv.ext
    intro v
    funext i
    rfl
  map_mul' σ τ := by
    apply LinearEquiv.ext
    intro v
    funext i
    simp only [LinearEquiv.mul_apply, Function.comp_apply]
    congr 1

theorem ggPermHom_apply (m : ℕ) (σ : Equiv.Perm (Fin m)) (v : GGBCV m) (i : Fin m) :
    ggPermHom m σ v i = v (σ.symm i) := rfl

private lemma ggQ2xP_perm_single (m : ℕ) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    ggPermHom m σ (Pi.single i (1 : ZMod 3)) = Pi.single (σ i) 1 := by
  funext j
  rw [ggPermHom_apply]
  by_cases h : j = σ i
  · subst h
    rw [Equiv.symm_apply_apply, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) h,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3)
        (fun hc => h (by rw [← hc, Equiv.apply_symm_apply]))]

theorem ggPermHom_injective (m : ℕ) : Function.Injective (ggPermHom m) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  have hsingle : (Pi.single (σ i) (1 : ZMod 3) : GGBCV m) = Pi.single (τ i) 1 := by
    rw [← ggQ2xP_perm_single m σ i, ← ggQ2xP_perm_single m τ i, h]
  by_contra hne
  have h1 := congrFun hsingle (σ i)
  rw [Pi.single_eq_same, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hne] at h1
  exact (by decide : (1 : ZMod 3) ≠ 0) h1

theorem ggPermHom_swap {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (hc : ((Pi.single i (1 : ZMod 3) : GGBCV m) -
      (Pi.single j (1 : ZMod 3) : GGBCV m)) ⬝ᵥ
      ((Pi.single i (1 : ZMod 3) : GGBCV m) -
        (Pi.single j (1 : ZMod 3) : GGBCV m)) ≠ 0) :
    ggPermHom m (Equiv.swap i j) =
      ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV m) -
        (Pi.single j (1 : ZMod 3) : GGBCV m)) hc := by
  apply LinearEquiv.ext
  intro v
  funext k
  rw [ggPermHom_apply, Equiv.symm_swap, ggQ2x_ggBCRefl_apply, ggQ2x_sub_single_dot,
    ggQ2x_sub_single_norm i j hij]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hki : k = i
  · rw [hki, Equiv.swap_apply_left, ggQ2x_sub_single_apply_same i j hij, mul_one]
    exact (ggQ2x_scalar_a (v i) (v j)).symm
  · by_cases hkj : k = j
    · rw [hkj, Equiv.swap_apply_right, ggQ2x_sub_single_apply_other i j hij]
      exact (ggQ2x_scalar_b (v i) (v j)).symm
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj,
        ggQ2x_sub_single_apply_of_ne i j k hki hkj, mul_zero, add_zero]

private lemma ggQ2xP_dot_smul {m : ℕ} (a : ZMod 3) (v w : GGBCV m) :
    (a • v) ⬝ᵥ w = a * (v ⬝ᵥ w) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma ggQ2xP_dot_smul_right {m : ℕ} (a : ZMod 3) (v w : GGBCV m) :
    v ⬝ᵥ (a • w) = a * (v ⬝ᵥ w) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma ggQ2xP_norm_smul {m : ℕ} (a : ZMod 3) (ha : a ≠ 0) (c : GGBCV m) :
    (a • c) ⬝ᵥ (a • c) = c ⬝ᵥ c := by
  rw [ggQ2xP_dot_smul, ggQ2xP_dot_smul_right]
  rw [show a * (a * (c ⬝ᵥ c)) = c ⬝ᵥ c from by
    rw [← mul_assoc, ggQ2x_mul_self_eq_one a ha, one_mul]]

private lemma ggQ2xP_scalar_smul {m : ℕ} (a x y : ZMod 3) (ha : a ≠ 0) (c : GGBCV m) :
    ((a * x) * y) • (a • c) = (x * y) • c := by
  rw [smul_smul]
  congr 1
  calc (a * x) * y * a = (a * a) * (x * y) := by ring
    _ = 1 * (x * y) := by rw [ggQ2x_mul_self_eq_one a ha]
    _ = x * y := by rw [one_mul]

private lemma ggQ2xP_refl_smul {m : ℕ} (a : ZMod 3) (ha : a ≠ 0) (c : GGBCV m)
    (hc : c ⬝ᵥ c ≠ 0) (hac : (a • c) ⬝ᵥ (a • c) ≠ 0) :
    ggBCRefl (a • c) hac = ggBCRefl c hc := by
  apply LinearEquiv.ext
  intro v
  rw [ggQ2x_ggBCRefl_apply, ggQ2x_ggBCRefl_apply, ggQ2xP_dot_smul,
    ggQ2xP_norm_smul a ha c, ggQ2xP_scalar_smul a (c ⬝ᵥ v) (c ⬝ᵥ c) ha c]

private lemma ggQ2xP_sum_single {m : ℕ} (k : Fin m) (a : ZMod 3) :
    ∑ i, (a • (Pi.single k 1 : GGBCV m)) i = a := by
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, Fintype.sum_pi_single', mul_one]

private lemma ggQ2xP_sum_pair {m : ℕ} (k l : Fin m) (a b : ZMod 3) :
    ∑ i, (a • (Pi.single k 1 : GGBCV m) + b • (Pi.single l 1 : GGBCV m)) i = a + b := by
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, ggQ2xP_sum_single, ggQ2xP_sum_single]

private lemma ggQ2xP_weight_two {m : ℕ} {v : GGBCV m} (hv : ggBCWt v = 2) :
    ∃ (i j : Fin m) (a b : ZMod 3), i ≠ j ∧ a ≠ 0 ∧ b ≠ 0 ∧
      v = a • (Pi.single i 1 : GGBCV m) + b • (Pi.single j 1 : GGBCV m) := by
  unfold ggBCWt at hv
  obtain ⟨i, j, hij, hS⟩ := Finset.card_eq_two.mp hv
  have hvi : v i ≠ 0 := by
    have hmem : i ∈ Finset.univ.filter (fun k => v k ≠ 0) := by rw [hS]; simp
    simpa using hmem
  have hvj : v j ≠ 0 := by
    have hmem : j ∈ Finset.univ.filter (fun k => v k ≠ 0) := by rw [hS]; simp
    simpa using hmem
  refine ⟨i, j, v i, v j, hij, hvi, hvj, ?_⟩
  funext k
  by_cases hki : k = i
  · subst hki
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hij, smul_eq_mul, mul_one, mul_zero, add_zero]
  · by_cases hkj : k = j
    · subst hkj
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hij), smul_eq_mul, mul_one,
        mul_zero, zero_add]
    · have hvk : v k = 0 := by
        by_contra hne
        have hmem : k ∈ Finset.univ.filter (fun k => v k ≠ 0) := by simp [hne]
        rw [hS] at hmem
        simp [hki, hkj] at hmem
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hki,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hkj, smul_zero, smul_zero, add_zero]
      exact hvk

private lemma ggQ2xP_aroots_classify {m : ℕ} {v : GGBCV m} (hv : v ∈ ggARoots m) :
    ∃ (i j : Fin m), i ≠ j ∧ ∃ a : ZMod 3, a ≠ 0 ∧
      v = a • (Pi.single i 1 - Pi.single j 1 : GGBCV m) := by
  obtain ⟨hw, hsum⟩ := hv
  obtain ⟨i, j, a, b, hij, ha, hb, hvij⟩ := ggQ2xP_weight_two hw
  have hab : a + b = 0 := by
    rw [hvij] at hsum
    rw [ggQ2xP_sum_pair] at hsum
    exact hsum
  refine ⟨i, j, hij, a, ha, ?_⟩
  have hb_eq : b = -a := (neg_eq_of_add_eq_zero_right hab).symm
  rw [hvij, hb_eq, smul_sub, sub_eq_add_neg]
  congr 1
  exact neg_smul a (Pi.single j 1 : GGBCV m)

private lemma ggQ2xP_sum_pi_single {m : ℕ} (i : Fin m) :
    (∑ x, (Pi.single i (1 : ZMod 3) : GGBCV m) x) = 1 := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma ggQ2xP_sub_single_mem_aroots {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    (Pi.single i (1 : ZMod 3) - Pi.single j 1 : GGBCV m) ∈ ggARoots m := by
  refine ⟨ggQ2x_wt_sub_single i j hij, ?_⟩
  rw [show (∑ x, (Pi.single i (1 : ZMod 3) - Pi.single j 1 : GGBCV m) x)
      = (∑ x, (Pi.single i (1 : ZMod 3) : GGBCV m) x) -
        (∑ x, (Pi.single j (1 : ZMod 3) : GGBCV m) x) from
    Finset.sum_sub_distrib _ _]
  rw [ggQ2xP_sum_pi_single, ggQ2xP_sum_pi_single, sub_self]

private lemma ggQ2xP_hc_sub {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    ((Pi.single i (1 : ZMod 3) : GGBCV m) -
      (Pi.single j (1 : ZMod 3) : GGBCV m)) ⬝ᵥ
      ((Pi.single i (1 : ZMod 3) : GGBCV m) -
        (Pi.single j (1 : ZMod 3) : GGBCV m)) ≠ 0 := by
  simpa only [ggQ2x_sub_single_norm i j hij] using (by decide : (2 : ZMod 3) ≠ 0)

private lemma ggQ2xP_reflSet_eq_image (m : ℕ) :
    ggBCReflSet (ggARoots m) = ggPermHom m '' ggTransp m := by
  ext t
  constructor
  · rintro ⟨c, hc, hcc, rfl⟩
    obtain ⟨i, j, hij, a, ha, hc_eq⟩ := ggQ2xP_aroots_classify hc
    refine ⟨Equiv.swap i j, ⟨i, j, hij, rfl⟩, ?_⟩
    have hd := ggQ2xP_hc_sub i j hij
    simp only [hc_eq] at hcc ⊢
    exact (ggPermHom_swap i j hij hd).trans
      (ggQ2xP_refl_smul a ha _ hd hcc).symm
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨i, j, hij, rfl⟩ := hσ
    refine ⟨Pi.single i (1 : ZMod 3) - Pi.single j 1,
      ggQ2xP_sub_single_mem_aroots i j hij,
      ggQ2xP_hc_sub i j hij, ?_⟩
    exact ggPermHom_swap i j hij (ggQ2xP_hc_sub i j hij)

private lemma ggQ2xP_range_eq_reflGp (m : ℕ) :
    (ggPermHom m).range = ggBCReflGp (ggARoots m) := by
  rw [ggBCReflGp, ggQ2xP_reflSet_eq_image]
  have h := MonoidHom.map_closure (ggPermHom m) (ggTransp m)
  have htransp : Subgroup.closure (ggTransp m) = (⊤ : Subgroup (Equiv.Perm (Fin m))) :=
    Equiv.Perm.closure_isSwap
  rw [htransp, Subgroup.map_top] at h
  exact h

private lemma ggQ2xP_transp_conj {m : ℕ} {s t : Equiv.Perm (Fin m)}
    (hs : s ∈ ggTransp m) (ht : t ∈ ggTransp m) : s * t * s⁻¹ ∈ ggTransp m := by
  obtain ⟨a, b, hab, rfl⟩ := hs
  obtain ⟨c, d, hcd, rfl⟩ := ht
  rw [← Equiv.swap_apply_apply]
  exact ⟨_, _, fun h => hcd ((Equiv.swap a b).injective h), rfl⟩

theorem ggQ2_A_inner_phi (m : ℕ) (hm : 5 ≤ m) :
    GGQ2QuandleInner (ggBCReflSet (ggARoots m)) (ggBCReflGp (ggARoots m)) := by
  have h71a : GGQ2QuandleInner (ggTransp m) Set.univ := by
    intro π hT hinj hπ
    obtain ⟨g, hg⟩ := ggQ2_quandle_aut_sym m hm π hT hinj hπ
    exact ⟨g, Set.mem_univ g, hg⟩
  have hinner : GGQ2QuandleInner (ggPermHom m '' ggTransp m) (ggPermHom m '' Set.univ) :=
    ggQ2_inner_image (ggPermHom m) (ggPermHom_injective m)
      (fun s hs t ht => ggQ2xP_transp_conj hs ht) h71a
  rw [← ggQ2xP_reflSet_eq_image, Set.image_univ, ← MonoidHom.coe_range,
    ggQ2xP_range_eq_reflGp] at hinner
  exact hinner

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart21

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.UnipotentNo117

open CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

variable {R : Type} [CommRing R] {φ : (Fin τ.rank → ℤ) →+ ℤ}

theorem raises_zero (m : ℤ) : Raises (R := R) (τ := τ) φ m 0 := fun _ _ h => absurd rfl h

theorem raises_mono {m n : ℤ} {A : Module.End R (RootModule τ R)} (h : Raises φ m A)
    (hnm : n ≤ m) : Raises φ n A := fun a b hab => by
  have := h a b hab
  omega

theorem raises_add {m : ℤ} {A B : Module.End R (RootModule τ R)} (hA : Raises φ m A)
    (hB : Raises φ m B) : Raises φ m (A + B) := fun a b hab => by
  rw [LinearMap.add_apply, Finsupp.add_apply] at hab
  by_cases h : A (Finsupp.single b 1) a = 0
  · rw [h, zero_add] at hab
    exact hB a b hab
  · exact hA a b h

theorem raises_neg {m : ℤ} {A : Module.End R (RootModule τ R)} (hA : Raises φ m A) :
    Raises φ m (-A) := fun a b hab => hA a b (by simpa using hab)

theorem raises_sub {m : ℤ} {A B : Module.End R (RootModule τ R)} (hA : Raises φ m A)
    (hB : Raises φ m B) : Raises φ m (A - B) := by
  rw [sub_eq_add_neg]
  exact raises_add hA (raises_neg hB)

theorem raises_smul {m : ℤ} {A : Module.End R (RootModule τ R)} (hA : Raises φ m A) (r : R) :
    Raises φ m (r • A) := fun a b hab => by
  rw [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul] at hab
  exact hA a b (right_ne_zero_of_mul hab)

theorem raises_sum {ι : Type*} (s : Finset ι) {m : ℤ} {A : ι → Module.End R (RootModule τ R)}
    (h : ∀ i ∈ s, Raises φ m (A i)) : Raises φ m (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using raises_zero (R := R) (τ := τ) (φ := φ) m
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact raises_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem raises_mul {m n : ℤ} {A B : Module.End R (RootModule τ R)} (hA : Raises φ m A)
    (hB : Raises φ n B) : Raises φ (m + n) (A * B) := fun a b hab => by
  rw [Module.End.mul_apply, ← Finsupp.sum_single (B (Finsupp.single b 1)), Finsupp.sum,
    map_sum, Finsupp.finsetSum_apply] at hab
  obtain ⟨c, hc, hc'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
  rw [← Finsupp.smul_single_one, map_smul, Finsupp.smul_apply, smul_eq_mul] at hc'
  have h1 := hA a c (right_ne_zero_of_mul hc')
  have h2 := hB c b (Finsupp.mem_support_iff.mp hc)
  omega

theorem raises_of_mapsLabelWt {A : Module.End R (RootModule τ R)} {v : Fin τ.rank → ℤ}
    (h : MapsLabelWt A (· + v)) : Raises φ (φ v) A := fun a b hab => by
  rw [h a b hab, map_add]

theorem raises_apply_eq_zero {m : ℤ} {A : Module.End R (RootModule τ R)} (h : Raises φ m A)
    {a b : Label τ} (hab : φ (labelWt τ a) < φ (labelWt τ b) + m) :
    A (Finsupp.single b 1) a = 0 := by
  by_contra hne
  have := h a b hne
  omega

theorem D_raises_w
    (F : RootOperatorFamily τ) (α : Root τ) {k : ℕ} (hk : 1 ≤ k) :
    Raises φ (k * φ α.1) (F.D R α k) := by
  have := raises_of_mapsLabelWt (φ := φ) (F.mapsLabelWt_D (R := R) α hk)
  rwa [map_nsmul, nsmul_eq_mul] at this

theorem mul_sub_one_w (X P : Module.End R (RootModule τ R)) :
    X * P - 1 = (X - 1) + (P - 1) + (X - 1) * (P - 1) := by
  simp only [mul_sub, sub_mul, one_mul, mul_one]
  abel

theorem elt_sub_one_w
    (F : RootOperatorFamily τ) (α : Root τ) (c : R) :
    F.elt R α c - 1 = ∑ k ∈ Finset.Ico 1 4, c ^ k • F.D R α k := by
  rw [RootOperatorFamily.elt, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by norm_num),
    pow_zero, one_smul, F.D_zero, add_sub_cancel_left]

theorem elt_sub_one_raises_w
    (F : RootOperatorFamily τ) (α : Root τ) (hα : 0 ≤ φ α.1) (c : R) :
    Raises φ (φ α.1) (F.elt R α c - 1) := by
  rw [elt_sub_one_w]
  refine raises_sum _ fun k hk => raises_mono
    (raises_smul (D_raises_w F α (Finset.mem_Ico.1 hk).1) (c ^ k)) ?_
  have : (1 : ℤ) ≤ k := by exact_mod_cast (Finset.mem_Ico.1 hk).1
  nlinarith

theorem elt_neg_sub_one_raises_w
    (F : RootOperatorFamily τ) (α : Root τ) (hα : 0 ≤ φ α.1)
    (c : R) : Raises φ (φ α.1) (F.elt R α (-c) - 1) :=
  elt_sub_one_raises_w F α hα (-c)

theorem D_apply_eq_zero_of_shift_w
    (F : RootOperatorFamily τ) (α : Root τ) {k : ℕ}
    (hk : k ≠ 1) {a b : Label τ} (hab : labelWt τ a = labelWt τ b + α.1) :
    F.D R α k (Finsupp.single b 1) a = 0 := by
  by_contra hne
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [F.D_zero, Module.End.one_apply, Finsupp.single_apply] at hne
    split_ifs at hne with hba
    · subst hba
      have : α.1 = 0 := by simpa using hab
      exact α.2.ne_zero this
    · exact hne rfl
  · have h := F.mapsLabelWt_D (R := R) α hk0 a b hne
    rw [hab] at h
    have h' : (k - 1 : ℤ) • α.1 = 0 := by
      have := congrArg (· - labelWt τ b) h
      simp only [add_sub_cancel_left] at this
      rw [sub_smul, one_smul, natCast_zsmul, ← this, sub_self]
    rcases smul_eq_zero.1 h' with h0 | h0
    · omega
    · exact α.2.ne_zero h0

theorem elt_apply_of_shift_w
    (F : RootOperatorFamily τ) (α : Root τ) (c : R) {a b : Label τ}
    (hab : labelWt τ a = labelWt τ b + α.1) :
    F.elt R α c (Finsupp.single b 1) a = c * F.D R α 1 (Finsupp.single b 1) a := by
  rw [RootOperatorFamily.elt, LinearMap.sum_apply, Finsupp.finsetSum_apply,
    Finset.sum_eq_single 1]
  · rw [pow_one, LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul]
  · intro k _ hk
    rw [LinearMap.smul_apply, Finsupp.smul_apply, D_apply_eq_zero_of_shift_w F α hk hab,
      smul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 (by norm_num)) h

theorem eltOr_of_isRoot_w
    (F : RootOperatorFamily τ) {R : Type} [CommRing R]
    {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) (c : R) :
    RootOperatorFamily'.eltOr F R γ c = F.elt R ⟨γ, h⟩ c := by
  classical
  exact dite_eq_left h

theorem eltOr_of_not_isRoot_w
    (F : RootOperatorFamily τ) {R : Type} [CommRing R]
    {γ : Fin τ.rank → ℤ} (h : ¬IsRoot τ γ) (c : R) :
    RootOperatorFamily'.eltOr F R γ c = 1 := by
  classical
  exact dite_eq_right h

theorem eltOr_sub_one_raises_w
    (F : RootOperatorFamily τ) {γ : Fin τ.rank → ℤ}
    (hγ : 0 ≤ φ γ) (c : R) :
    Raises φ (φ γ) (RootOperatorFamily'.eltOr F R γ c - 1) := by
  by_cases h : IsRoot τ γ
  · rw [eltOr_of_isRoot_w F h]
    exact elt_sub_one_raises_w F ⟨γ, h⟩ hγ c
  · rw [eltOr_of_not_isRoot_w F h, sub_self]
    exact raises_zero _

theorem prod_sub_one_raises_w
    (F : RootOperatorFamily τ) {s : ℤ} (hs : 0 ≤ s)
    (c : (Fin τ.rank → ℤ) → R) :
    ∀ L : List (Fin τ.rank → ℤ), (∀ γ ∈ L, s ≤ φ γ) →
      Raises φ s ((L.map fun γ => RootOperatorFamily'.eltOr F R γ (c γ)).prod - 1)
  | [], _ => by simpa using raises_zero (R := R) (τ := τ) (φ := φ) s
  | γ :: L, hL => by
    rw [List.map_cons, List.prod_cons, mul_sub_one_w]
    have h1 := raises_mono
      (eltOr_sub_one_raises_w F (le_trans hs (hL γ (List.mem_cons_self))) (c γ))
      (hL γ List.mem_cons_self)
    have h2 := prod_sub_one_raises_w F hs c L fun δ hδ => hL δ (List.mem_cons_of_mem _ hδ)
    exact raises_add (raises_add h1 h2) (raises_mono (raises_mul h1 h2) (by omega))

theorem prod_sub_one_apply_eq_zero_w
    (F : RootOperatorFamily τ) {γ₀ : Fin τ.rank → ℤ}
    (h₀ : IsRoot τ γ₀) (h₀φ : 1 ≤ φ γ₀) (c : (Fin τ.rank → ℤ) → R) {a b : Label τ}
    (hab : labelWt τ a = labelWt τ b + γ₀) :
    ∀ L : List (Fin τ.rank → ℤ), (∀ γ ∈ L, γ ≠ γ₀ ∧ φ γ₀ ≤ φ γ) →
      ((L.map fun γ => RootOperatorFamily'.eltOr F R γ (c γ)).prod - 1)
        (Finsupp.single b 1) a = 0
  | [], _ => by simp
  | γ :: L, hL => by
    have hφab : φ (labelWt τ a) = φ (labelWt τ b) + φ γ₀ := by rw [hab, map_add]
    rw [List.map_cons, List.prod_cons, mul_sub_one_w, LinearMap.add_apply,
      LinearMap.add_apply, Finsupp.add_apply, Finsupp.add_apply,
      prod_sub_one_apply_eq_zero_w F h₀ h₀φ c hab L fun δ hδ => hL δ (List.mem_cons_of_mem _ hδ),
      add_zero]
    obtain ⟨hγne, hγφ⟩ := hL γ List.mem_cons_self
    have h2 := prod_sub_one_raises_w F (by omega : (0 : ℤ) ≤ φ γ₀) c L
      fun δ hδ => (hL δ (List.mem_cons_of_mem _ hδ)).2
    have h1 := raises_mono (eltOr_sub_one_raises_w F (by omega : 0 ≤ φ γ) (c γ)) hγφ
    rw [raises_apply_eq_zero (raises_mul h1 h2) (by omega), add_zero]
    by_cases hγ : IsRoot τ γ
    · rw [eltOr_of_isRoot_w F hγ, elt_sub_one_w, LinearMap.sum_apply,
        Finsupp.finsetSum_apply]
      refine Finset.sum_eq_zero fun k hk => ?_
      obtain ⟨hk1, hk4⟩ := Finset.mem_Ico.1 hk
      rw [LinearMap.smul_apply, Finsupp.smul_apply]
      by_contra hne
      have hD := F.mapsLabelWt_D (R := R) ⟨γ, hγ⟩ hk1 a b (right_ne_zero_of_smul hne)
      rw [hab] at hD
      have hv : γ₀ = k • γ := add_left_cancel hD
      have hφv : φ γ₀ = k * φ γ := by rw [hv, map_nsmul, nsmul_eq_mul]
      have hk1' : k = 1 := by
        have : (k : ℤ) * φ γ ≤ φ γ := by rw [← hφv]; exact hγφ
        have hk : (k : ℤ) ≤ 1 := by nlinarith
        omega
      subst hk1'
      exact hγne (by rw [hv, one_nsmul])
    · rw [eltOr_of_not_isRoot_w F hγ, sub_self, LinearMap.zero_apply,
        Finsupp.zero_apply]

theorem prod_apply_of_shift_w
    (F : RootOperatorFamily τ) {γ₀ : Fin τ.rank → ℤ}
    (h₀ : IsRoot τ γ₀) (h₀φ : 1 ≤ φ γ₀) (c : (Fin τ.rank → ℤ) → R) {a b : Label τ}
    (hab : labelWt τ a = labelWt τ b + γ₀) (L : List (Fin τ.rank → ℤ))
    (hL : ∀ γ ∈ L, γ ≠ γ₀ ∧ φ γ₀ ≤ φ γ) :
    ((γ₀ :: L).map fun γ => RootOperatorFamily'.eltOr F R γ (c γ)).prod
        (Finsupp.single b 1) a =
      c γ₀ * F.D R ⟨γ₀, h₀⟩ 1 (Finsupp.single b 1) a := by
  rw [List.map_cons, List.prod_cons]
  have hXP : ∀ X P : Module.End R (RootModule τ R), X * P = X + (P - 1) + (X - 1) * (P - 1) := by
    intro X P
    simp only [mul_sub, sub_mul, one_mul, mul_one]
    abel
  have hφab : φ (labelWt τ a) = φ (labelWt τ b) + φ γ₀ := by rw [hab, map_add]
  have h2 := prod_sub_one_raises_w F (by omega : (0 : ℤ) ≤ φ γ₀) c L fun δ hδ => (hL δ hδ).2
  have h1 := eltOr_sub_one_raises_w F (by omega : 0 ≤ φ γ₀) (c γ₀)
  rw [hXP, LinearMap.add_apply, LinearMap.add_apply, Finsupp.add_apply, Finsupp.add_apply,
    prod_sub_one_apply_eq_zero_w F h₀ h₀φ c hab L hL,
    raises_apply_eq_zero (raises_mul h1 h2) (by omega), add_zero, add_zero,
    eltOr_of_isRoot_w F h₀, elt_apply_of_shift_w F ⟨γ₀, h₀⟩ (c γ₀) hab]

theorem exists_D_eq_word_w
    (F : RootOperatorFamily τ) (α : Root τ) :
    ∃ (j : Fin τ.rank) (ε : ℤ) (w : List (Fin τ.rank)), (ε = 1 ∨ ε = -1) ∧
      ∀ (R : Type) [CommRing R] (k : ℕ), F.D R α k = ((ε ^ k : ℤ) : R) •
        ((((w.map fun i => weylElt τ R i 1).prod : (Module.End R (RootModule τ R))ˣ) :
            Module.End R (RootModule τ R)) * xCoeff τ R j k *
          (((w.map fun i => weylElt τ R i 1).prod⁻¹ : (Module.End R (RootModule τ R))ˣ) :
            Module.End R (RootModule τ R))) := by
  obtain ⟨v, hv⟩ := α
  induction hv with
  | basis j =>
    refine ⟨j, 1, [], Or.inl rfl, fun R _ k => ?_⟩
    rw [show (⟨Pi.single j 1, IsRoot.basis j⟩ : Root τ) = simpleRoot τ j from rfl, F.D_simple]
    simp
  | @reflect i v hv ih =>
    obtain ⟨j, ε, w, hε, h⟩ := ih
    refine ⟨j, F.sign i ⟨v, hv⟩ * ε, i :: w,
      CFSG.LieType.Steinberg.SpinOdd.sign_mul_sign_eq (F.sign_eq i _) hε, fun R _ k => ?_⟩
    have hs : (⟨reflect τ i v, IsRoot.reflect i hv⟩ : Root τ) = simple τ i • ⟨v, hv⟩ :=
      (simple_smul_eq_sRoot_without117 i ⟨v, hv⟩).symm
    rw [hs, F.D_simple_smul, h R k, mul_smul_comm, smul_mul_assoc, smul_smul, ← weylElt_inv,
      List.map_cons, List.prod_cons, mul_inv_rev, mul_pow, Int.cast_mul]
    simp only [Units.val_mul, mul_assoc]

theorem exists_D_one_apply_ne_zero_w
    (F : RootOperatorFamily τ) [Nontrivial R] (α : Root τ) :
    ∃ a b : Label τ, F.D R α 1 (Finsupp.single b 1) a ≠ 0 := by
  by_contra h
  push Not at h
  have hD0 : F.D R α 1 = 0 :=
    Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => by simpa using h a b)
  obtain ⟨j, ε, w, hε, hw⟩ := exists_D_eq_word_w F α
  set W := (w.map fun i => weylElt τ R i 1).prod
  have h1 : (W : Module.End R (RootModule τ R)) * xCoeff τ R j 1 *
      ((W⁻¹ : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R)) = 0 := by
    have := hw R 1
    rw [hD0, pow_one] at this
    have h2 := congrArg (((ε : ℤ) : R) • ·) this
    simp only [smul_zero, smul_smul, ← Int.cast_mul, show ε * ε = 1 by
      rcases hε with rfl | rfl <;> norm_num, Int.cast_one, one_smul] at h2
    exact h2.symm
  have h3 : xCoeff τ R j 1 = 0 := by
    have := congrArg (fun A => ((W⁻¹ : (Module.End R (RootModule τ R))ˣ) :
      Module.End R (RootModule τ R)) * A * (W : Module.End R (RootModule τ R))) h1
    simpa [mul_assoc] using this
  have h4 := congrArg (fun A : Module.End R (RootModule τ R) =>
    A (rootVec τ R (-Pi.single j 1)) (Sum.inl j)) h3
  simp [xCoeff_one, infE_rootVec_neg_single, hVec] at h4

theorem prod_eltOr_injective_w
    (F : RootOperatorFamily τ) {K : Type} [Field K] :
    ∀ L : List (Fin τ.rank → ℤ), L.Nodup → (∀ γ ∈ L, IsRoot τ γ ∧ 0 < φ γ) →
      L.Pairwise (fun γ δ => φ γ ≤ φ δ) → ∀ c c' : (Fin τ.rank → ℤ) → K,
        (L.map fun γ => RootOperatorFamily'.eltOr F K γ (c γ)).prod =
          (L.map fun γ => RootOperatorFamily'.eltOr F K γ (c' γ)).prod →
          ∀ γ ∈ L, c γ = c' γ
  | [], _, _, _, _, _, _ => by simp
  | γ₀ :: L, hnd, hL, hsort, c, c', heq => by
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨hsort₀, hsort'⟩ := List.pairwise_cons.1 hsort
    obtain ⟨h₀, h₀φ⟩ := hL γ₀ List.mem_cons_self
    have hL' : ∀ γ ∈ L, γ ≠ γ₀ ∧ φ γ₀ ≤ φ γ := fun γ hγ =>
      ⟨fun h => hnot (h ▸ hγ), hsort₀ γ hγ⟩
    obtain ⟨a, b, hab⟩ := exists_D_one_apply_ne_zero_w F (R := K) ⟨γ₀, h₀⟩
    have hshift : labelWt τ a = labelWt τ b + γ₀ := by
      have := F.mapsLabelWt_D (R := K) ⟨γ₀, h₀⟩ le_rfl a b hab
      rwa [one_nsmul] at this
    have hc₀ : c γ₀ = c' γ₀ := by
      have := congrArg (fun A : Module.End K (RootModule τ K) => A (Finsupp.single b 1) a) heq
      rw [prod_apply_of_shift_w F h₀ h₀φ c hshift L hL',
        prod_apply_of_shift_w F h₀ h₀φ c' hshift L hL'] at this
      exact mul_right_cancel₀ hab this
    have heq' : (L.map fun γ => RootOperatorFamily'.eltOr F K γ (c γ)).prod =
        (L.map fun γ => RootOperatorFamily'.eltOr F K γ (c' γ)).prod := by
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, hc₀] at heq
      have := congrArg (fun A => F.elt K ⟨γ₀, h₀⟩ (-c' γ₀) * A) heq
      simp only [eltOr_of_isRoot_w F h₀, ← mul_assoc, F.elt_neg_mul_elt,
        one_mul] at this
      exact this
    intro γ hγ
    rcases List.mem_cons.1 hγ with rfl | hγ
    · exact hc₀
    · exact prod_eltOr_injective_w F L hnd' (fun δ hδ => hL δ (List.mem_cons_of_mem _ hδ))
        hsort' c c' heq' γ hγ

theorem raises_zero_one_w {R : Type} [CommRing R] {φ : (Fin τ.rank → ℤ) →+ ℤ} :
    Raises φ 0 (1 : Module.End R (RootModule τ R)) := fun a b hab => by
  rw [Module.End.one_apply, Finsupp.single_apply] at hab
  split_ifs at hab with h
  · subst h
    omega
  · exact absurd rfl hab

theorem mul_sub_mul_apply_w {R : Type} [CommRing R] (X X' P P' : Module.End R (RootModule τ R))
    (a b : Label τ) :
    (X * P - X' * P') (Finsupp.single b 1) a =
      (P - P') (Finsupp.single b 1) a + ((X - 1) * (P - P')) (Finsupp.single b 1) a +
        ((X - X') (Finsupp.single b 1) a + ((X - X') * (P' - 1)) (Finsupp.single b 1) a) := by
  rw [show X * P - X' * P' = (P - P') + (X - 1) * (P - P') + ((X - X') + (X - X') * (P' - 1)) by
    simp only [mul_sub, sub_mul, one_mul, mul_one]
    abel]
  simp only [LinearMap.add_apply, Finsupp.add_apply]

theorem eltOr_raises_zero_w
    (F : RootOperatorFamily τ) {R : Type} [CommRing R]
    {φ : (Fin τ.rank → ℤ) →+ ℤ} {γ : Fin τ.rank → ℤ} (hγ : 0 ≤ φ γ) (c : R) :
    Raises φ 0 (RootOperatorFamily'.eltOr F R γ c) := by
  have h := raises_add (raises_zero_one_w (φ := φ))
    (raises_mono (eltOr_sub_one_raises_w F hγ c) hγ)
  rwa [add_sub_cancel] at h

theorem prod_raises_zero_w
    (F : RootOperatorFamily τ) {R : Type} [CommRing R]
    {φ : (Fin τ.rank → ℤ) →+ ℤ} (c : (Fin τ.rank → ℤ) → R) (L : List (Fin τ.rank → ℤ))
    (hL : ∀ γ ∈ L, 0 ≤ φ γ) :
    Raises φ 0 (L.map fun γ => RootOperatorFamily'.eltOr F R γ (c γ)).prod := by
  have h := raises_add (raises_zero_one_w (φ := φ))
    (prod_sub_one_raises_w F le_rfl c L hL)
  rwa [add_sub_cancel] at h

theorem eltOr_sub_eltOr_raises_w
    (F : RootOperatorFamily τ) {R : Type} [CommRing R]
    {φ : (Fin τ.rank → ℤ) →+ ℤ} {γ : Fin τ.rank → ℤ} (hγ : 0 ≤ φ γ) (c c' : R) :
    Raises φ (φ γ) (RootOperatorFamily'.eltOr F R γ c - RootOperatorFamily'.eltOr F R γ c') := by
  have h := raises_sub (eltOr_sub_one_raises_w F hγ c) (eltOr_sub_one_raises_w F hγ c')
  rwa [sub_sub_sub_cancel_right] at h

end CFSG.StandardType.F4ExplicitPos.UnipotentNo117
end

end

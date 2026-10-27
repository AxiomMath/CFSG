module

public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2

public section

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Chevalley

section SL2

variable {K : Type} [Field K]

theorem uSL_val (s : K) : ((uSL s : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![1, s; 0, 1] := rfl

theorem vSL_val (s : K) : ((vSL s : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; s, 1] := rfl

theorem uSL_mul_vSL_pow_three [CharP K 2] : ((uSL 1 : SL2 K) * vSL 1) ^ 3 = 1 := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul, uSL_val, vSL_val,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem uSL_mul_vSL_ne_one [CharP K 2] : ((uSL 1 : SL2 K) * vSL 1) ≠ 1 := by
  intro h
  have := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, uSL_val, vSL_val,
    Matrix.SpecialLinearGroup.coe_one] at this
  simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero] at this

theorem uSL_conj_uSL_mul_vSL [CharP K 2] :
    (uSL 1 : SL2 K) * (uSL 1 * vSL 1) * (uSL 1)⁻¹ = (uSL 1 * vSL 1)⁻¹ := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [eq_inv_iff_mul_eq_one]
  apply Subtype.ext
  have hinv : ((uSL (1 : K) : SL2 K)⁻¹ : SL2 K) = uSL 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_inv, uSL_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two, CharTwo.neg_eq]
  rw [hinv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, uSL_val, vSL_val,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]

end SL2

@[expose] noncomputable def evenH (τ : Tag) (K : Type) [Field K] (α : Fin τ.rank → ℤ) :
    ModGL τ K :=
  pinnedX τ K α 1 * pinnedX τ K (-α) 1

@[expose] def IsEvenFourRootData (τ : Tag) (K : Type) [Field K] (α : Fin 4 → Fin τ.rank → ℤ)
    (β : Fin τ.rank → ℤ) : Prop :=
  (∀ i, IsRoot τ (α i)) ∧ IsRoot τ β ∧
  (∀ i, evenH τ K (α i) ∈ adjointGroup τ K ∧ orderOf (evenH τ K (α i)) = 3) ∧
  (∀ i i', Commute (evenH τ K (α i)) (evenH τ K (α i'))) ∧
  (∀ i, pinnedX τ K (α i) 1 ∈ adjointGroup τ K ∧ orderOf (pinnedX τ K (α i) 1) = 2) ∧
  (∀ i, pinnedX τ K (α i) 1 * evenH τ K (α i) * (pinnedX τ K (α i) 1)⁻¹ =
    (evenH τ K (α i))⁻¹) ∧
  (∀ i i', i ≠ i' →
    pinnedX τ K (α i) 1 * evenH τ K (α i') * (pinnedX τ K (α i) 1)⁻¹ = evenH τ K (α i')) ∧
  pinnedX τ K β 1 ∈ adjointGroup τ K ∧ orderOf (pinnedX τ K β 1) = 2 ∧
  (∀ i, Commute (pinnedX τ K β 1) (evenH τ K (α i)))

@[expose] def IsEvenFourRootCheck (τ : Tag) (α : Fin 4 → Fin τ.rank → ℤ)
    (β : Fin τ.rank → ℤ) : Prop :=
  (∀ i, RootOps.isRootB τ (α i) = true) ∧ RootOps.isRootB τ β = true ∧
  (∀ i i', i ≠ i' → (∃ k, α i k ≠ α i' k) ∧ (∃ k, α i k ≠ -α i' k) ∧
    RootOps.isRootB τ (α i + α i') = false ∧ RootOps.isRootB τ (α i - α i') = false) ∧
  (∀ i, (∃ k, β k ≠ α i k) ∧ (∃ k, β k ≠ -α i k) ∧ RootOps.isRootB τ (β + α i) = false ∧
    RootOps.isRootB τ (β - α i) = false)

section Soundness

variable {τ : Tag} {K : Type} [Field K]

theorem commute_pinnedX_of_not_isRoot (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {a b : Fin τ.rank → ℤ} (ha : IsRoot τ a) (hb : IsRoot τ b) (hne : a ≠ b) (hne' : a ≠ -b)
    (hnr : ¬ IsRoot τ (a + b)) (c d : K) : Commute (pinnedX τ K a c) (pinnedX τ K b d) :=
  ((simply_laced_root_commutator_unit τ hτ ha hb hne hne').2 hnr K _
    (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩))

theorem commute_pinnedX_signs (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {a b : Fin τ.rank → ℤ} (ha : IsRoot τ a) (hb : IsRoot τ b) (hne : a ≠ b) (hne' : a ≠ -b)
    (h1 : ¬ IsRoot τ (a + b)) (h2 : ¬ IsRoot τ (a - b)) (c d : K) :
    Commute (pinnedX τ K a c) (pinnedX τ K b d) ∧ Commute (pinnedX τ K a c) (pinnedX τ K (-b) d) ∧
      Commute (pinnedX τ K (-a) c) (pinnedX τ K b d) ∧
      Commute (pinnedX τ K (-a) c) (pinnedX τ K (-b) d) := by
  have hnb := IsRoot.neg hb
  have hna := IsRoot.neg ha
  have e1 : ¬ IsRoot τ (a + -b) := by rwa [← sub_eq_add_neg]
  have e2 : ¬ IsRoot τ (-a + b) := fun h => h2 (by
    have := IsRoot.neg h
    rwa [neg_add, neg_neg, ← sub_eq_add_neg] at this)
  have e3 : ¬ IsRoot τ (-a + -b) := fun h => h1 (by
    have := IsRoot.neg h
    rwa [neg_add, neg_neg, neg_neg] at this)
  have n1 : -a ≠ b := fun h => hne' (neg_eq_iff_eq_neg.mp h)
  have n2 : -a ≠ -b := fun h => hne (neg_inj.mp h)
  have n3 : a ≠ -(-b) := by rwa [neg_neg]
  have n4 : -a ≠ -(-b) := by rwa [neg_neg]
  exact ⟨commute_pinnedX_of_not_isRoot hτ ha hb hne hne' h1 c d,
    commute_pinnedX_of_not_isRoot hτ ha hnb hne' n3 e1 c d,
    commute_pinnedX_of_not_isRoot hτ hna hb n1 n2 e2 c d,
    commute_pinnedX_of_not_isRoot hτ hna hnb n2 n4 e3 c d⟩

theorem commute_pinnedX_of_check (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α : Fin 4 → Fin τ.rank → ℤ} {β : Fin τ.rank → ℤ} (h : IsEvenFourRootCheck τ α β) :
    (∀ i i', i ≠ i' → ∀ c d : K,
      Commute (pinnedX τ K (α i) c) (pinnedX τ K (α i') d) ∧
        Commute (pinnedX τ K (α i) c) (pinnedX τ K (-α i') d) ∧
        Commute (pinnedX τ K (-α i) c) (pinnedX τ K (α i') d) ∧
        Commute (pinnedX τ K (-α i) c) (pinnedX τ K (-α i') d)) ∧
    (∀ i, ∀ c d : K,
      Commute (pinnedX τ K β c) (pinnedX τ K (α i) d) ∧
        Commute (pinnedX τ K β c) (pinnedX τ K (-α i) d)) := by
  obtain ⟨hroot, hβroot, hpair, hβ⟩ := h
  have hα : ∀ i, IsRoot τ (α i) := fun i => RootOps.isRootB_iff.1 (hroot i)
  have hβr : IsRoot τ β := RootOps.isRootB_iff.1 hβroot
  have hnr : ∀ x : Fin τ.rank → ℤ, RootOps.isRootB τ x = false → ¬ IsRoot τ x := fun x hx hr => by
    rw [← RootOps.isRootB_iff, hx] at hr
    exact Bool.false_ne_true hr
  refine ⟨fun i i' hii' c d => ?_, fun i c d => ?_⟩
  · obtain ⟨⟨k, hk⟩, ⟨k', hk'⟩, h1, h2⟩ := hpair i i' hii'
    exact commute_pinnedX_signs hτ (hα i) (hα i') (fun h => hk (congrFun h k))
      (fun h => hk' (congrFun h k')) (hnr _ h1) (hnr _ h2) c d
  · obtain ⟨⟨k, hk⟩, ⟨k', hk'⟩, h1, h2⟩ := hβ i
    exact (commute_pinnedX_signs hτ hβr (hα i) (fun h => hk (congrFun h k))
      (fun h => hk' (congrFun h k')) (hnr _ h1) (hnr _ h2) c d).imp_right (fun h => h.1)

variable [CharP K 2]

theorem pinnedX_one_pow_two (α : Fin τ.rank → ℤ) : pinnedX τ K α 1 ^ 2 = 1 := by
  rw [pow_two, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]

omit [CharP K 2] in
theorem pinnedX_one_ne_one (α : Fin τ.rank → ℤ) : pinnedX τ K α 1 ≠ 1 := by
  intro h
  rw [← pinnedX_zero τ K α] at h
  exact one_ne_zero (pinnedX_injective τ K α h)

theorem orderOf_pinnedX_one_charTwo (α : Fin τ.rank → ℤ) : orderOf (pinnedX τ K α 1) = 2 :=
  orderOf_eq_prime (pinnedX_one_pow_two α) (pinnedX_one_ne_one α)

theorem evenH_eq_rootSL2 {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    evenH τ K α = rootSL2 τ K α (uSL 1 * vSL 1) := by
  rw [map_mul, rootSL2_uSL_of_charTwo hα, rootSL2_vSL_of_charTwo hα]
  rfl

theorem pinnedX_one_eq_rootSL2 {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    pinnedX τ K α 1 = rootSL2 τ K α (uSL 1) := (rootSL2_uSL_of_charTwo hα 1).symm

theorem orderOf_evenH {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) : orderOf (evenH τ K α) = 3 := by
  have hinj : Function.Injective (rootSL2 τ K α) :=
    (even_Chevalley_pinned_root_SL2_maps τ K hα).1
  rw [evenH_eq_rootSL2 hα, orderOf_injective _ hinj]
  exact orderOf_eq_prime uSL_mul_vSL_pow_three uSL_mul_vSL_ne_one

theorem pinnedX_conj_evenH_self {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    pinnedX τ K α 1 * evenH τ K α * (pinnedX τ K α 1)⁻¹ = (evenH τ K α)⁻¹ := by
  rw [evenH_eq_rootSL2 hα, pinnedX_one_eq_rootSL2 hα, ← map_inv, ← map_mul, ← map_mul,
    ← map_inv, uSL_conj_uSL_mul_vSL]

theorem isEvenFourRootData_of_check (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α : Fin 4 → Fin τ.rank → ℤ} {β : Fin τ.rank → ℤ} (h : IsEvenFourRootCheck τ α β) :
    IsEvenFourRootData τ K α β := by
  obtain ⟨hroot, hβroot, hpair, hβ⟩ := h
  have hα : ∀ i, IsRoot τ (α i) := fun i => RootOps.isRootB_iff.1 (hroot i)
  have hβr : IsRoot τ β := RootOps.isRootB_iff.1 hβroot
  obtain ⟨hcα, hcβ⟩ := commute_pinnedX_of_check (K := K) hτ ⟨hroot, hβroot, hpair, hβ⟩
  have hcommH : ∀ i i', Commute (evenH τ K (α i)) (evenH τ K (α i')) := by
    intro i i'
    by_cases hii' : i = i'
    · rw [hii']
    · obtain ⟨c1, c2, c3, c4⟩ := hcα i i' hii' 1 1
      unfold evenH
      exact (c1.mul_right c2).mul_left ((c3.mul_right c4))
  refine ⟨hα, hβr, fun i => ⟨?_, orderOf_evenH (hα i)⟩, hcommH,
    fun i => ⟨pinnedX_mem_adjointGroup _ _, orderOf_pinnedX_one_charTwo _⟩,
    fun i => pinnedX_conj_evenH_self (hα i), fun i i' hii' => ?_,
    pinnedX_mem_adjointGroup _ _, orderOf_pinnedX_one_charTwo _, fun i => ?_⟩
  · exact mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)
  · obtain ⟨c1, c2, c3, c4⟩ := hcα i i' hii' 1 1
    unfold evenH
    rw [(c1.mul_right c2).eq, mul_inv_cancel_right]
  · obtain ⟨c1, c2⟩ := hcβ i 1 1
    unfold evenH
    exact c1.mul_right c2

end Soundness

abbrev evenE7Roots : Fin 4 → Fin Tag.E7.rank → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0]]

abbrev evenE7Beta : Fin Tag.E7.rank → ℤ := ![0, 1, 1, 2, 1, 0, 0]

theorem evenE7_check : IsEvenFourRootCheck .E7 evenE7Roots evenE7Beta := by
  unfold IsEvenFourRootCheck
  decide +kernel

abbrev evenE8Roots : Fin 4 → Fin Tag.E8.rank → ℤ :=
  ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

abbrev evenE8Beta : Fin Tag.E8.rank → ℤ := ![1, 2, 2, 3, 2, 1, 0, 0]

theorem evenE8_check : IsEvenFourRootCheck .E8 evenE8Roots evenE8Beta := by
  unfold IsEvenFourRootCheck
  decide +kernel

theorem even_E7_four_three_elements_with_inverters_and_centralizing_involution (K : Type)
    [Field K] [CharP K 2] :
    IsEvenFourRootData .E7 K
      ![![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0],
        ![0, 1, 0, 0, 0, 0, 0]] ![0, 1, 1, 2, 1, 0, 0] :=
  isEvenFourRootData_of_check (Or.inr (Or.inr (Or.inl rfl))) (α := evenE7Roots)
    (β := evenE7Beta) evenE7_check

theorem even_E8_four_three_elements_with_inverters_and_centralizing_involution (K : Type)
    [Field K] [CharP K 2] :
    IsEvenFourRootData .E8 K
      ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0],
        ![0, 0, 0, 0, 0, 0, 0, 1]] ![1, 2, 2, 3, 2, 1, 0, 0] :=
  isEvenFourRootData_of_check (Or.inr (Or.inr (Or.inr rfl))) (α := evenE8Roots)
    (β := evenE8Beta) evenE8_check

end CFSG.RankThree.PartOne

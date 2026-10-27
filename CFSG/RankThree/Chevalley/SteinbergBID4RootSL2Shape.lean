module

public import CFSG.RankThree.Chevalley.SteinbergBID4RootOps
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Ops

variable {R : Type*} [CommRing R]

theorem xOp_hVec_D4 (i j : Fin Tag.D4.rank) (c : R) :
    xOp Tag.D4 R i c (hVec Tag.D4 R j) = hVec Tag.D4 R j +
      (((Tag.D4.cartan j i).natAbs : R) * c) • rootVec Tag.D4 R (Pi.single i 1) := by
  change xOp _ _ i c (Finsupp.single (Sum.inl j) 1) = _
  rw [xOp, Finsupp.linearCombination_single, one_smul]

theorem yOp_hVec_D4 (i j : Fin Tag.D4.rank) (c : R) :
    yOp Tag.D4 R i c (hVec Tag.D4 R j) = hVec Tag.D4 R j +
      (((Tag.D4.cartan j i).natAbs : R) * c) • rootVec Tag.D4 R (-Pi.single i 1) := by
  change yOp _ _ i c (Finsupp.single (Sum.inl j) 1) = _
  rw [yOp, Finsupp.linearCombination_single, one_smul]

theorem single_ne_neg_single_D4 (i : Fin Tag.D4.rank) :
    (Pi.single i 1 : Fin Tag.D4.rank → ℤ) ≠ -Pi.single i 1 := fun h => by
  simpa using congrFun h i

theorem xOp_rootVec_single_D4 (i : Fin Tag.D4.rank) (c : R) :
    xOp Tag.D4 R i c (rootVec Tag.D4 R (Pi.single i 1)) = rootVec Tag.D4 R (Pi.single i 1) := by
  rw [rootVec_eq_single_D4 (isRoot_single _ i), xOp, Finsupp.linearCombination_single, one_smul]
  exact ite_eq_left rfl

theorem yOp_rootVec_neg_single_D4 (i : Fin Tag.D4.rank) (c : R) :
    yOp Tag.D4 R i c (rootVec Tag.D4 R (-Pi.single i 1)) = rootVec Tag.D4 R (-Pi.single i 1) := by
  rw [rootVec_eq_single_D4 (isRoot_neg_single _ i), yOp, Finsupp.linearCombination_single,
    one_smul]
  exact ite_eq_left rfl

theorem xOp_rootVec_neg_single_D4 (i : Fin Tag.D4.rank) (c : R) :
    xOp Tag.D4 R i c (rootVec Tag.D4 R (-Pi.single i 1)) =
      rootVec Tag.D4 R (-Pi.single i 1) + c • hVec Tag.D4 R i +
        c ^ 2 • rootVec Tag.D4 R (Pi.single i 1) := by
  rw [rootVec_eq_single_D4 (isRoot_neg_single _ i), xOp, Finsupp.linearCombination_single,
    one_smul]
  exact (ite_eq_right (single_ne_neg_single_D4 i).symm).trans (ite_eq_left rfl)

theorem yOp_rootVec_single_D4 (i : Fin Tag.D4.rank) (c : R) :
    yOp Tag.D4 R i c (rootVec Tag.D4 R (Pi.single i 1)) =
      rootVec Tag.D4 R (Pi.single i 1) + c • hVec Tag.D4 R i +
        c ^ 2 • rootVec Tag.D4 R (-Pi.single i 1) := by
  rw [rootVec_eq_single_D4 (isRoot_single _ i), yOp, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right (single_ne_neg_single_D4 i)).trans (ite_eq_left rfl)

theorem rootVec_apply_inl_D4 (β : Fin Tag.D4.rank → ℤ) (i : Fin Tag.D4.rank) :
    rootVec Tag.D4 R β (Sum.inl i) = 0 := by
  by_cases hβ : IsRoot Tag.D4 β
  · rw [rootVec_eq_single_D4 hβ, Finsupp.single_apply, ite_eq_right Sum.inr_ne_inl]
  · rw [rootVec_eq_zero_of_not_D4 hβ, Finsupp.zero_apply]

theorem rootVec_apply_inr_D4 (β : Fin Tag.D4.rank → ℤ)
    (γ : {v : Fin Tag.D4.rank → ℤ // IsRoot Tag.D4 v}) :
    rootVec Tag.D4 R β (Sum.inr γ) = if β = γ.1 then 1 else 0 := by
  by_cases hβ : IsRoot Tag.D4 β
  · rw [rootVec_eq_single_D4 hβ, Finsupp.single_apply]
    by_cases h : β = γ.1
    · rw [ite_eq_left (congrArg Sum.inr (Subtype.ext h)), ite_eq_left h]
    · rw [ite_eq_right fun e => h (congrArg Subtype.val (Sum.inr_injective e)), ite_eq_right h]
  · rw [rootVec_eq_zero_of_not_D4 hβ, Finsupp.zero_apply, ite_eq_right]
    rintro rfl
    exact hβ γ.2

theorem hVec_apply_inl_D4 (j i : Fin Tag.D4.rank) :
    hVec Tag.D4 R j (Sum.inl i) = if j = i then 1 else 0 := by
  rw [hVec, Finsupp.single_apply]
  by_cases h : j = i
  · rw [ite_eq_left (congrArg Sum.inl h), ite_eq_left h]
  · rw [ite_eq_right fun e => h (Sum.inl_injective e), ite_eq_right h]

theorem hVec_apply_inr_D4 (j : Fin Tag.D4.rank) (γ : {v : Fin Tag.D4.rank → ℤ // IsRoot Tag.D4 v}) :
    hVec Tag.D4 R j (Sum.inr γ) = 0 := by
  rw [hVec, Finsupp.single_apply, ite_eq_right Sum.inl_ne_inr]

end Ops

abbrev d4E0 : Fin Tag.D4.rank → ℤ := Pi.single 0 1

theorem d4RootVec_injective : Function.Injective d4RootVec := by
  intro a b h
  revert a b
  decide +kernel

theorem d4E0_string_facts : ∀ m m' : Fin 24, d4RootVec m' = d4RootVec m + d4E0 →
    d4RootVec m ≠ d4E0 ∧ d4RootVec m ≠ -d4E0 ∧ d4RootVec m' ≠ d4E0 ∧ d4RootVec m' ≠ -d4E0 ∧
      (∀ k, d4RootVec k ≠ d4RootVec m' + d4E0) ∧ ∀ k, d4RootVec k ≠ d4RootVec m - d4E0 := by
  decide +kernel

@[expose] def d4E0Cls : Fin 24 → Fin 5 :=
  ![3, 2, 1, 2, 4, 0, 2, 1, 0, 1, 2, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 2, 2]

theorem d4E0Cls_spec : ∀ m : Fin 24,
    (d4E0Cls m = 0 → ∃ m', d4RootVec m = d4RootVec m' + d4E0) ∧
    (d4E0Cls m = 1 → ∃ m', d4RootVec m' = d4RootVec m + d4E0) ∧
    (d4E0Cls m = 2 → d4RootVec m ≠ d4E0 ∧ d4RootVec m ≠ -d4E0 ∧
      (∀ k, d4RootVec k ≠ d4RootVec m + d4E0) ∧ ∀ k, d4RootVec k ≠ d4RootVec m - d4E0) ∧
    (d4E0Cls m = 3 → d4RootVec m = d4E0) ∧ (d4E0Cls m = 4 → d4RootVec m = -d4E0) := by
  decide +kernel

theorem sum_d4E0Cls {M : Type*} [AddCommMonoid M] (F : Fin 5 → M) :
    ∑ m : Fin 24, F (d4E0Cls m) = 8 • F 0 + 8 • F 1 + 6 • F 2 + F 3 + F 4 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, d4E0Cls, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  abel

theorem sum_roots_D4 {M : Type*} [AddCommMonoid M]
    (f : {v : Fin Tag.D4.rank → ℤ // IsRoot Tag.D4 v} → M) :
    ∑ α, f α = ∑ m : Fin 24, f ⟨d4RootVec m, isRoot_d4RootVec m⟩ := by
  refine (Function.Bijective.sum_comp ⟨fun a b h => ?_, fun α => ?_⟩ f).symm
  · exact d4RootVec_injective (congrArg Subtype.val h)
  · obtain ⟨m, hm⟩ := exists_d4RootVec_eq α.2
    exact ⟨m, Subtype.ext hm⟩

theorem not_isRoot_of_forall_ne {β : Fin Tag.D4.rank → ℤ} (h : ∀ k, d4RootVec k ≠ β) :
    ¬IsRoot Tag.D4 β := fun hr => by
  obtain ⟨k, hk⟩ := exists_d4RootVec_eq hr
  exact h k hk

theorem sum_fin_D4 {M : Type*} [AddCommMonoid M] (f : Fin Tag.D4.rank → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  rw [show (Finset.univ : Finset (Fin Tag.D4.rank)) = {0, 1, 2, 3} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  abel

variable {K : Type} [Field K]

structure D4E0Shape (g : Module.End K (RootModule Tag.D4 K)) (B : Matrix (Fin 2) (Fin 2) K) :
    Prop where
  top : ∀ m m' : Fin 24, d4RootVec m' = d4RootVec m + d4E0 →
    g (rootVec Tag.D4 K (d4RootVec m')) =
      B 0 0 • rootVec Tag.D4 K (d4RootVec m') + B 1 0 • rootVec Tag.D4 K (d4RootVec m)
  bot : ∀ m m' : Fin 24, d4RootVec m' = d4RootVec m + d4E0 →
    g (rootVec Tag.D4 K (d4RootVec m)) =
      B 0 1 • rootVec Tag.D4 K (d4RootVec m') + B 1 1 • rootVec Tag.D4 K (d4RootVec m)
  fix : ∀ m : Fin 24, d4E0Cls m = 2 →
    g (rootVec Tag.D4 K (d4RootVec m)) = rootVec Tag.D4 K (d4RootVec m)
  pos : g (rootVec Tag.D4 K d4E0) = B 0 0 ^ 2 • rootVec Tag.D4 K d4E0 +
    (B 0 0 * B 1 0) • hVec Tag.D4 K 0 + B 1 0 ^ 2 • rootVec Tag.D4 K (-d4E0)
  cartan : g (hVec Tag.D4 K 0) = (2 * B 0 0 * B 0 1) • rootVec Tag.D4 K d4E0 +
    (B 0 0 * B 1 1 + B 0 1 * B 1 0) • hVec Tag.D4 K 0 +
      (2 * B 1 0 * B 1 1) • rootVec Tag.D4 K (-d4E0)
  neg : g (rootVec Tag.D4 K (-d4E0)) = B 0 1 ^ 2 • rootVec Tag.D4 K d4E0 +
    (B 0 1 * B 1 1) • hVec Tag.D4 K 0 + B 1 1 ^ 2 • rootVec Tag.D4 K (-d4E0)
  h1 : g (hVec Tag.D4 K 1) = hVec Tag.D4 K 1
  h3 : g (hVec Tag.D4 K 3) = hVec Tag.D4 K 3
  h2 : ∃ x y z : K, g (hVec Tag.D4 K 2) = hVec Tag.D4 K 2 + x • rootVec Tag.D4 K d4E0 +
    y • hVec Tag.D4 K 0 + z • rootVec Tag.D4 K (-d4E0)

theorem cartan_natAbs_D4 :
    (Tag.D4.cartan 0 0).natAbs = 2 ∧ (Tag.D4.cartan 1 0).natAbs = 0 ∧
      (Tag.D4.cartan 2 0).natAbs = 1 ∧ (Tag.D4.cartan 3 0).natAbs = 0 := by
  decide

theorem d4E0Shape_xOp (c : K) : D4E0Shape (xOp Tag.D4 K 0 c) !![1, c; 0, 1] := by
  obtain ⟨n0, n1, n2, n3⟩ := cartan_natAbs_D4
  refine ⟨fun m m' h => ?_, fun m m' h => ?_, fun m hm => ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨c, 0, 0, ?_⟩⟩
  · obtain ⟨-, -, h₁, h₂, h₃, -⟩ := d4E0_string_facts m m' h
    rw [xOp_rootVec_D4 0 c (isRoot_d4RootVec m') h₁ h₂,
      rootVec_eq_zero_of_not_D4 (not_isRoot_of_forall_ne h₃)]
    simp
  · obtain ⟨h₁, h₂, -, -, -, -⟩ := d4E0_string_facts m m' h
    rw [xOp_rootVec_D4 0 c (isRoot_d4RootVec m) h₁ h₂, ← h]
    simp [add_comm]
  · obtain ⟨h₁, h₂, h₃, -⟩ := (d4E0Cls_spec m).2.2.1 hm
    rw [xOp_rootVec_D4 0 c (isRoot_d4RootVec m) h₁ h₂,
      rootVec_eq_zero_of_not_D4 (not_isRoot_of_forall_ne h₃), smul_zero, add_zero]
  · rw [xOp_rootVec_single_D4]
    simp
  · rw [xOp_hVec_D4, n0]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    module
  · rw [xOp_rootVec_neg_single_D4]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    module
  · rw [xOp_hVec_D4, n1]
    simp
  · rw [xOp_hVec_D4, n3]
    simp
  · rw [xOp_hVec_D4, n2]
    simp

theorem d4E0Shape_yOp (c : K) : D4E0Shape (yOp Tag.D4 K 0 c) !![1, 0; c, 1] := by
  obtain ⟨n0, n1, n2, n3⟩ := cartan_natAbs_D4
  refine ⟨fun m m' h => ?_, fun m m' h => ?_, fun m hm => ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨0, 0, c, ?_⟩⟩
  · obtain ⟨-, -, h₁, h₂, -, -⟩ := d4E0_string_facts m m' h
    rw [yOp_rootVec_D4 0 c (isRoot_d4RootVec m') h₁ h₂, h, add_sub_cancel_right]
    simp
  · obtain ⟨h₁, h₂, -, -, -, h₃⟩ := d4E0_string_facts m m' h
    rw [yOp_rootVec_D4 0 c (isRoot_d4RootVec m) h₁ h₂,
      rootVec_eq_zero_of_not_D4 (not_isRoot_of_forall_ne h₃)]
    simp
  · obtain ⟨h₁, h₂, -, h₃⟩ := (d4E0Cls_spec m).2.2.1 hm
    rw [yOp_rootVec_D4 0 c (isRoot_d4RootVec m) h₁ h₂,
      rootVec_eq_zero_of_not_D4 (not_isRoot_of_forall_ne h₃), smul_zero, add_zero]
  · rw [yOp_rootVec_single_D4]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    module
  · rw [yOp_hVec_D4, n0]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    module
  · rw [yOp_rootVec_neg_single_D4]
    simp
  · rw [yOp_hVec_D4, n1]
    simp
  · rw [yOp_hVec_D4, n3]
    simp
  · rw [yOp_hVec_D4, n2]
    simp

theorem d4E0Shape_one : D4E0Shape (1 : Module.End K (RootModule Tag.D4 K)) 1 := by
  refine ⟨fun m m' _ => ?_, fun m m' _ => ?_, fun m _ => rfl, ?_, ?_, ?_, rfl, rfl,
    ⟨0, 0, 0, ?_⟩⟩ <;> simp

theorem D4E0Shape.mul {g g' : Module.End K (RootModule Tag.D4 K)}
    {B B' : Matrix (Fin 2) (Fin 2) K} (h : D4E0Shape g B) (h' : D4E0Shape g' B') :
    D4E0Shape (g * g') (B * B') := by
  obtain ⟨x, y, z, h2⟩ := h.h2
  obtain ⟨x', y', z', h2'⟩ := h'.h2
  refine ⟨fun m m' hm => ?_, fun m m' hm => ?_, fun m hm => ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨x + x' * B 0 0 ^ 2 + y' * (2 * B 0 0 * B 0 1) + z' * B 0 1 ^ 2,
      y + x' * (B 0 0 * B 1 0) + y' * (B 0 0 * B 1 1 + B 0 1 * B 1 0) + z' * (B 0 1 * B 1 1),
      z + x' * B 1 0 ^ 2 + y' * (2 * B 1 0 * B 1 1) + z' * B 1 1 ^ 2, ?_⟩⟩
  · rw [Module.End.mul_apply, h'.top m m' hm, map_add, map_smul, map_smul, h.top m m' hm,
      h.bot m m' hm]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    module
  · rw [Module.End.mul_apply, h'.bot m m' hm, map_add, map_smul, map_smul, h.top m m' hm,
      h.bot m m' hm]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    module
  · rw [Module.End.mul_apply, h'.fix m hm, h.fix m hm]
  · rw [Module.End.mul_apply, h'.pos, map_add, map_add, map_smul, map_smul, map_smul, h.pos,
      h.cartan, h.neg]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    module
  · rw [Module.End.mul_apply, h'.cartan, map_add, map_add, map_smul, map_smul, map_smul, h.pos,
      h.cartan, h.neg]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    module
  · rw [Module.End.mul_apply, h'.neg, map_add, map_add, map_smul, map_smul, map_smul, h.pos,
      h.cartan, h.neg]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    module
  · rw [Module.End.mul_apply, h'.h1, h.h1]
  · rw [Module.End.mul_apply, h'.h3, h.h3]
  · rw [Module.End.mul_apply, h2', map_add, map_add, map_add, map_smul, map_smul, map_smul, h2,
      h.pos, h.cartan, h.neg]
    module

theorem exists_d4E0Shape {g : ModGL Tag.D4 K}
    (hg : g ∈ subsystemGroup Tag.D4 K ({0} : Set (Fin Tag.D4.rank))) :
    ∃ B, D4E0Shape (g : Module.End K (RootModule Tag.D4 K)) B := by
  induction hg using Subgroup.closure_induction'' with
  | mem g hg =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hg
    · rw [Set.mem_singleton_iff.1 hi, coe_xUnit]
      exact ⟨_, d4E0Shape_xOp c⟩
    · rw [Set.mem_singleton_iff.1 hi, coe_yUnit]
      exact ⟨_, d4E0Shape_yOp c⟩
  | inv_mem g hg =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hg
    · rw [Set.mem_singleton_iff.1 hi, coe_xUnit_inv]
      exact ⟨_, d4E0Shape_xOp (-c)⟩
    · rw [Set.mem_singleton_iff.1 hi, coe_yUnit_inv]
      exact ⟨_, d4E0Shape_yOp (-c)⟩
  | one => exact ⟨1, d4E0Shape_one⟩
  | mul g h _ _ hg hh =>
    obtain ⟨B, hB⟩ := hg
    obtain ⟨B', hB'⟩ := hh
    exact ⟨B * B', by rw [Units.val_mul]; exact hB.mul hB'⟩

theorem trace_rootModule_D4 (g : Module.End K (RootModule Tag.D4 K)) :
    LinearMap.trace K (RootModule Tag.D4 K) g =
      ∑ b : Label Tag.D4, g (Finsupp.single b 1) b := by
  rw [LinearMap.trace_eq_matrix_trace K Finsupp.basisSingleOne, Matrix.trace]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Finsupp.coe_basisSingleOne,
    Finsupp.basisSingleOne_repr]
  rfl

theorem d4E0_ne_neg : d4E0 ≠ -d4E0 := single_ne_neg_single_D4 0

theorem apply_rootVec_diag_of_d4E0Shape {g : Module.End K (RootModule Tag.D4 K)}
    {B : Matrix (Fin 2) (Fin 2) K} (h : D4E0Shape g B) (m : Fin 24) :
    g (Finsupp.single (Sum.inr ⟨d4RootVec m, isRoot_d4RootVec m⟩) 1)
        (Sum.inr ⟨d4RootVec m, isRoot_d4RootVec m⟩) =
      ![B 0 0, B 1 1, 1, B 0 0 ^ 2, B 1 1 ^ 2] (d4E0Cls m) := by
  rw [← rootVec_eq_single_D4]
  obtain ⟨c0, c1, c2, c3, c4⟩ := d4E0Cls_spec m
  have hcls : ∀ c : Fin 5, c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by decide
  rcases hcls (d4E0Cls m) with hc | hc | hc | hc | hc <;> rw [hc]
  · obtain ⟨m', hm'⟩ := c0 hc
    have hne : d4RootVec m' ≠ d4RootVec m := by
      rw [hm']
      intro e
      have := congrFun e 0
      simp at this
    rw [h.top m' m hm', Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
      rootVec_apply_inr_D4, rootVec_apply_inr_D4, ite_eq_left rfl, ite_eq_right hne]
    simp
  · obtain ⟨m', hm'⟩ := c1 hc
    have hne : d4RootVec m' ≠ d4RootVec m := by
      rw [hm']
      intro e
      have := congrFun e 0
      simp at this
    rw [h.bot m m' hm', Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
      rootVec_apply_inr_D4, rootVec_apply_inr_D4, ite_eq_left rfl, ite_eq_right hne]
    simp
  · rw [h.fix m hc, rootVec_apply_inr_D4, ite_eq_left rfl]
    simp
  · have e := c3 hc
    have hp := h.pos
    rw [← e] at hp
    have hne : -d4RootVec m ≠ d4RootVec m := by
      rw [e]
      exact d4E0_ne_neg.symm
    rw [hp, Finsupp.add_apply, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
      Finsupp.smul_apply, rootVec_apply_inr_D4, rootVec_apply_inr_D4, hVec_apply_inr_D4,
      ite_eq_left rfl, ite_eq_right hne]
    simp
  · have e := c4 hc
    have hn := h.neg
    rw [← e] at hn
    have hne : d4E0 ≠ d4RootVec m := by
      rw [e]
      exact d4E0_ne_neg
    rw [hn, Finsupp.add_apply, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
      Finsupp.smul_apply, rootVec_apply_inr_D4, rootVec_apply_inr_D4, hVec_apply_inr_D4,
      ite_eq_right hne, ite_eq_left rfl]
    simp

theorem trace_eq_of_d4E0Shape {g : Module.End K (RootModule Tag.D4 K)}
    {B : Matrix (Fin 2) (Fin 2) K} (h : D4E0Shape g B) :
    LinearMap.trace K (RootModule Tag.D4 K) g =
      8 * (B 0 0 + B 1 1) + 9 + B 0 0 ^ 2 + B 1 1 ^ 2 + (B 0 0 * B 1 1 + B 0 1 * B 1 0) := by
  rw [trace_rootModule_D4, Fintype.sum_sum_type, sum_roots_D4]
  simp only [apply_rootVec_diag_of_d4E0Shape h, sum_d4E0Cls]
  obtain ⟨x, y, z, h2⟩ := h.h2
  have e0 : g (Finsupp.single (Sum.inl 0) 1) (Sum.inl 0) = B 0 0 * B 1 1 + B 0 1 * B 1 0 := by
    change g (hVec Tag.D4 K 0) (Sum.inl 0) = _
    rw [h.cartan]
    simp [rootVec_apply_inl_D4, hVec_apply_inl_D4]
  have e1 : g (Finsupp.single (Sum.inl 1) 1) (Sum.inl 1) = 1 := by
    change g (hVec Tag.D4 K 1) (Sum.inl 1) = _
    rw [h.h1, hVec_apply_inl_D4, ite_eq_left rfl]
  have e2 : g (Finsupp.single (Sum.inl 2) 1) (Sum.inl 2) = 1 := by
    change g (hVec Tag.D4 K 2) (Sum.inl 2) = _
    rw [h2]
    simp [rootVec_apply_inl_D4, hVec_apply_inl_D4]
  have e3 : g (Finsupp.single (Sum.inl 3) 1) (Sum.inl 3) = 1 := by
    change g (hVec Tag.D4 K 3) (Sum.inl 3) = _
    rw [h.h3, hVec_apply_inl_D4, ite_eq_left rfl]
  rw [sum_fin_D4, e0, e1, e2, e3]
  simp [nsmul_eq_mul]
  ring

end CFSG.RankThree.Chevalley

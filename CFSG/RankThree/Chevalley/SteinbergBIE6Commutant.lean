module

public import CFSG.LieType.Chevalley.C2E6RootOperators

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

section Commutant

variable {Ω : Type} [Field Ω]

@[expose] def e6Commutant (S : Set (ModGL Tag.E6 Ω)) : Set (Module.End Ω (RootModule Tag.E6 Ω)) :=
  {X | ∀ g ∈ S, Commute X (g : Module.End Ω (RootModule Tag.E6 Ω))}

theorem mem_e6Commutant {S : Set (ModGL Tag.E6 Ω)} {X : Module.End Ω (RootModule Tag.E6 Ω)} :
    X ∈ e6Commutant S ↔ ∀ g ∈ S, Commute X (g : Module.End Ω (RootModule Tag.E6 Ω)) :=
  Iff.rfl

theorem e6Commutant_anti {S T : Set (ModGL Tag.E6 Ω)} (h : S ⊆ T) :
    e6Commutant T ⊆ e6Commutant S :=
  fun _ hX g hg => hX g (h hg)

@[expose] def commuteSubgroup (X : Module.End Ω (RootModule Tag.E6 Ω)) :
    Subgroup (ModGL Tag.E6 Ω) where
  carrier := {g | Commute X (g : Module.End Ω (RootModule Tag.E6 Ω))}
  mul_mem' {a b} ha hb := by
    change Commute X ((a * b : ModGL Tag.E6 Ω) : Module.End Ω (RootModule Tag.E6 Ω))
    rw [Units.val_mul]
    exact Commute.mul_right ha hb
  one_mem' := by
    change Commute X ((1 : ModGL Tag.E6 Ω) : Module.End Ω (RootModule Tag.E6 Ω))
    rw [Units.val_one]
    exact Commute.one_right X
  inv_mem' {a} ha := Commute.units_inv_right ha

theorem e6Commutant_closure (S : Set (ModGL Tag.E6 Ω)) :
    e6Commutant (Subgroup.closure S : Set (ModGL Tag.E6 Ω)) = e6Commutant S := by
  refine Set.Subset.antisymm (e6Commutant_anti Subgroup.subset_closure) fun X hX g hg => ?_
  exact (Subgroup.closure_le (commuteSubgroup X)).2 (fun h hh => hX h hh) hg

theorem mem_e6Commutant_subsystemGroup {J : Set (Fin Tag.E6.rank)}
    {X : Module.End Ω (RootModule Tag.E6 Ω)}
    (hx : ∀ i ∈ J, ∀ c : Ω, Commute X (xOp Tag.E6 Ω i c))
    (hy : ∀ i ∈ J, ∀ c : Ω, Commute X (yOp Tag.E6 Ω i c)) :
    X ∈ e6Commutant (subsystemGroup Tag.E6 Ω J : Set (ModGL Tag.E6 Ω)) := by
  rw [subsystemGroup, e6Commutant_closure]
  rintro g ⟨i, hi, c, rfl | rfl⟩
  · exact hx i hi c
  · exact hy i hi c

theorem commute_conj_iff (m : ModGL Tag.E6 Ω) (Y Z : Module.End Ω (RootModule Tag.E6 Ω)) :
    Commute ((m : Module.End Ω (RootModule Tag.E6 Ω)) * Y * ↑m⁻¹)
        ((m : Module.End Ω (RootModule Tag.E6 Ω)) * Z * ↑m⁻¹) ↔ Commute Y Z := by
  have key : ∀ Y Z : Module.End Ω (RootModule Tag.E6 Ω),
      ((m : Module.End Ω (RootModule Tag.E6 Ω)) * Y * ↑m⁻¹) *
        ((m : Module.End Ω (RootModule Tag.E6 Ω)) * Z * ↑m⁻¹) = ↑m * (Y * Z) * ↑m⁻¹ := by
    intro Y Z
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  constructor
  · intro h
    have h' : (m : Module.End Ω (RootModule Tag.E6 Ω)) * (Y * Z) * ↑m⁻¹ = ↑m * (Z * Y) * ↑m⁻¹ := by
      rw [← key, ← key]
      exact h.eq
    have h'' := congrArg (fun W => (↑m⁻¹ : Module.End Ω (RootModule Tag.E6 Ω)) * W * ↑m) h'
    simp only [← mul_assoc, Units.inv_mul, one_mul] at h''
    simp only [mul_assoc, Units.inv_mul, mul_one] at h''
    exact h''
  · intro h
    change _ * _ = _ * _
    rw [key, key, h.eq]

theorem e6Commutant_conj (m : ModGL Tag.E6 Ω) (S : Set (ModGL Tag.E6 Ω)) :
    e6Commutant ((fun g => m * g * m⁻¹) '' S) =
      (fun X => (m : Module.End Ω (RootModule Tag.E6 Ω)) * X * ↑m⁻¹) '' e6Commutant S := by
  ext X
  constructor
  · intro hX
    refine ⟨(↑m⁻¹ : Module.End Ω (RootModule Tag.E6 Ω)) * X * ↑m, fun g hg => ?_, ?_⟩
    · have h := hX _ ⟨g, hg, rfl⟩
      have e : X = (m : Module.End Ω (RootModule Tag.E6 Ω)) *
          ((↑m⁻¹ : Module.End Ω (RootModule Tag.E6 Ω)) * X * ↑m) * ↑m⁻¹ := by
        simp only [← mul_assoc, Units.mul_inv, one_mul]
        simp only [mul_assoc, Units.mul_inv, mul_one]
      rw [e, Units.val_mul, Units.val_mul] at h
      exact (commute_conj_iff m _ _).1 h
    · change (m : Module.End Ω (RootModule Tag.E6 Ω)) * (↑m⁻¹ * X * ↑m) * ↑m⁻¹ = X
      simp only [← mul_assoc, Units.mul_inv, one_mul]
      simp only [mul_assoc, Units.mul_inv, mul_one]
  · rintro ⟨Y, hY, rfl⟩ _ ⟨g, hg, rfl⟩
    rw [Units.val_mul, Units.val_mul]
    exact (commute_conj_iff m _ _).2 (hY g hg)

theorem e6Commutant_conj_eq {P Q : Set (ModGL Tag.E6 Ω)} (h : e6Commutant P = e6Commutant Q)
    (m : ModGL Tag.E6 Ω) :
    e6Commutant ((fun g => m * g * m⁻¹) '' P) = e6Commutant ((fun g => m * g * m⁻¹) '' Q) := by
  rw [e6Commutant_conj, e6Commutant_conj, h]

theorem e6Commutant_mul {S T : Set (ModGL Tag.E6 Ω)} (hS : 1 ∈ S) (hT : 1 ∈ T) :
    e6Commutant (S * T) = e6Commutant S ∩ e6Commutant T := by
  ext X
  constructor
  · intro hX
    exact ⟨fun s hs => by simpa using hX (s * 1) (Set.mul_mem_mul hs hT),
      fun t ht => by simpa using hX (1 * t) (Set.mul_mem_mul hS ht)⟩
  · rintro ⟨hXS, hXT⟩ _ ⟨s, hs, t, ht, rfl⟩
    rw [Units.val_mul]
    exact (hXS s hs).mul_right (hXT t ht)

end Commutant

section Interpolation

variable {Ω : Type} [Field Ω]

theorem eq_zero_of_forall_sum_pow_smul {M : Type*} [AddCommGroup M] [Module Ω M] {ι : Type*}
    [Fintype ι] {n : ι → ℕ} (hn : Function.Injective n) {F : Finset Ω}
    (hF : ∀ i, n i < F.card) {c : ι → M} (h : ∀ a ∈ F, ∑ i, a ^ n i • c i = 0) (i : ι) :
    c i = 0 := by
  classical
  refine (Module.forall_dual_apply_eq_zero_iff Ω (c i)).1 fun φ => ?_
  set p : Polynomial Ω := ∑ j, Polynomial.C (φ (c j)) * Polynomial.X ^ n j with hpdef
  have hcard : 0 < F.card := lt_of_le_of_lt (Nat.zero_le _) (hF i)
  have hdeg : p.natDegree < F.card := by
    have : p.natDegree ≤ F.card - 1 := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      rw [Polynomial.natDegree_X_pow]
      have := hF j
      omega
    omega
  have hp : p = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p F (fun a ha => ?_) hdeg
    have h1 := congrArg φ (h a ha)
    rw [map_sum, map_zero] at h1
    rw [hpdef, Polynomial.eval_finsetSum, ← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, map_smul,
      smul_eq_mul, mul_comm]
  have hco := congrArg (fun q : Polynomial Ω => q.coeff (n i)) hp
  simp only [hpdef, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_zero] at hco
  rw [Finset.sum_eq_single i
    (fun j _ hj => by rw [ite_eq_right (fun e => hj (hn e.symm)), mul_zero])
    (fun h => absurd (Finset.mem_univ i) h), ite_eq_left rfl, mul_one] at hco
  exact hco

end Interpolation

section Quadratic

variable {R : Type*} [CommRing R]

theorem not_isRoot_add_three_smul_E6 {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    {i : Fin Tag.E6.rank} (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) {k : ℕ}
    (hk : 2 ≤ k) : ¬IsRoot Tag.E6 (α + (k : ℤ) • Pi.single i 1) := by
  intro h
  obtain ⟨hp, -, -⟩ := C2E6Std.stringUp_add_stringDown_E6 hα h₁ h₂
  obtain ⟨-, hs⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  have := ((hs k).1 h).2
  omega

theorem not_isRoot_sub_three_smul_E6 {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    {i : Fin Tag.E6.rank} (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) {k : ℕ}
    (hk : 2 ≤ k) : ¬IsRoot Tag.E6 (α - (k : ℤ) • Pi.single i 1) := by
  intro h
  obtain ⟨-, hq, -⟩ := C2E6Std.stringUp_add_stringDown_E6 hα h₁ h₂
  obtain ⟨-, hs⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  have := ((hs (-(k : ℤ))).1 (by rwa [neg_smul, ← sub_eq_add_neg])).1
  omega

theorem xCoeff_E6_three (i : Fin Tag.E6.rank) : xCoeff Tag.E6 R i 3 = 0 := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  rcases b with j | ⟨α, hα⟩
  · change xCoeff Tag.E6 R i 3 (hVec Tag.E6 R j) = 0
    rw [xCoeff_hVec]
    simp
  · change xCoeff Tag.E6 R i 3 (Finsupp.single (Sum.inr ⟨α, hα⟩) 1) = 0
    rw [← C2E6Std.rootVec_eq_single hα]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [xCoeff_rootVec_single]
      simp
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [xCoeff_rootVec_neg_single]
      simp
    rw [xCoeff_rootVec_of_ne i 3 hα h₁ h₂,
      C2E6Std.rootVec_eq_zero_of_not (not_isRoot_add_three_smul_E6 hα h₁ h₂ (by norm_num)),
      smul_zero]

theorem yCoeff_E6_three (i : Fin Tag.E6.rank) : yCoeff Tag.E6 R i 3 = 0 := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  rcases b with j | ⟨α, hα⟩
  · change yCoeff Tag.E6 R i 3 (hVec Tag.E6 R j) = 0
    rw [yCoeff_hVec]
    simp
  · change yCoeff Tag.E6 R i 3 (Finsupp.single (Sum.inr ⟨α, hα⟩) 1) = 0
    rw [← C2E6Std.rootVec_eq_single hα]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [yCoeff_rootVec_single]
      simp
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [yCoeff_rootVec_neg_single]
      simp
    rw [yCoeff_rootVec_of_ne i 3 hα h₁ h₂,
      C2E6Std.rootVec_eq_zero_of_not (not_isRoot_sub_three_smul_E6 hα h₁ h₂ (by norm_num)),
      smul_zero]

theorem xOp_E6_eq (i : Fin Tag.E6.rank) (c : R) :
    xOp Tag.E6 R i c = 1 + c • xCoeff Tag.E6 R i 1 + c ^ 2 • xCoeff Tag.E6 R i 2 := by
  rw [xOp_eq_sum_xCoeff, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, xCoeff_zero, xCoeff_E6_three, pow_zero, one_smul, pow_one, smul_zero,
    add_zero]

theorem yOp_E6_eq (i : Fin Tag.E6.rank) (c : R) :
    yOp Tag.E6 R i c = 1 + c • yCoeff Tag.E6 R i 1 + c ^ 2 • yCoeff Tag.E6 R i 2 := by
  rw [yOp_eq_sum_yCoeff, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, yCoeff_zero, yCoeff_E6_three, pow_zero, one_smul, pow_one, smul_zero,
    add_zero]

end Quadratic

section QuadraticFamily

variable {Ω : Type} [Field Ω] {M : Type*} [Ring M] [Algebra Ω M]

theorem commute_one_add_iff {X A B : M} (c : Ω) :
    Commute X (1 + c • A + c ^ 2 • B) ↔
      c • (X * A - A * X) + c ^ 2 • (X * B - B * X) = 0 := by
  rw [Commute, SemiconjBy, ← sub_eq_zero]
  constructor <;> intro h <;> [rw [← h]; rw [← h]] <;>
    simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, smul_sub] <;>
    abel

theorem commute_of_three_le_card {X A B : M} {F : Finset Ω} (hF : 3 ≤ F.card)
    (h : ∀ c ∈ F, Commute X (1 + c • A + c ^ 2 • B)) : Commute X A ∧ Commute X B := by
  have key := eq_zero_of_forall_sum_pow_smul (n := ![1, 2]) (ι := Fin 2)
    (c := ![X * A - A * X, X * B - B * X]) (F := F)
    (fun a b hab => by fin_cases a <;> fin_cases b <;> simp_all)
    (fun i => by fin_cases i <;> simp <;> omega)
    (fun c hc => by
      have := (commute_one_add_iff c).1 (h c hc)
      simpa [Fin.sum_univ_two] using this)
  exact ⟨sub_eq_zero.1 (key 0), sub_eq_zero.1 (key 1)⟩

theorem commute_one_add_of_commute {X A B : M} (hA : Commute X A) (hB : Commute X B) (c : Ω) :
    Commute X (1 + c • A + c ^ 2 • B) :=
  ((Commute.one_right X).add_right (hA.smul_right c)).add_right (hB.smul_right _)

end QuadraticFamily

section E6Family

variable {Ω : Type} [Field Ω]

theorem commute_xOp_of_three_le_card {X : Module.End Ω (RootModule Tag.E6 Ω)}
    {i : Fin Tag.E6.rank} {F : Finset Ω} (hF : 3 ≤ F.card)
    (h : ∀ c ∈ F, Commute X (xOp Tag.E6 Ω i c)) (c : Ω) : Commute X (xOp Tag.E6 Ω i c) := by
  obtain ⟨hA, hB⟩ := commute_of_three_le_card hF fun c hc => by
    rw [← xOp_E6_eq]
    exact h c hc
  rw [xOp_E6_eq]
  exact commute_one_add_of_commute hA hB c

theorem commute_yOp_of_three_le_card {X : Module.End Ω (RootModule Tag.E6 Ω)}
    {i : Fin Tag.E6.rank} {F : Finset Ω} (hF : 3 ≤ F.card)
    (h : ∀ c ∈ F, Commute X (yOp Tag.E6 Ω i c)) (c : Ω) : Commute X (yOp Tag.E6 Ω i c) := by
  obtain ⟨hA, hB⟩ := commute_of_three_le_card hF fun c hc => by
    rw [← yOp_E6_eq]
    exact h c hc
  rw [yOp_E6_eq]
  exact commute_one_add_of_commute hA hB c

end E6Family

section Triple

variable {Ω : Type} [Field Ω] {M : Type*} [Ring M] [Algebra Ω M]

@[expose] def quadCoeff (A B : M) : Fin 3 → M := ![1, A, B]

theorem one_add_eq_sum (A B : M) (c : Ω) :
    1 + c • A + c ^ 2 • B = ∑ k : Fin 3, c ^ (k : ℕ) • quadCoeff A B k := by
  simp [Fin.sum_univ_three, quadCoeff, add_assoc]

theorem triple_expand (A₁ B₁ A₂ B₂ A₃ B₃ : M) (a b c : Ω) :
    (1 + a • A₁ + a ^ 2 • B₁) * (1 + b • A₂ + b ^ 2 • B₂) * (1 + c • A₃ + c ^ 2 • B₃) =
      ∑ t : Fin 3 × Fin 3 × Fin 3, (a ^ (t.1 : ℕ) * b ^ (t.2.1 : ℕ) * c ^ (t.2.2 : ℕ)) •
        (quadCoeff A₁ B₁ t.1 * quadCoeff A₂ B₂ t.2.1 * quadCoeff A₃ B₃ t.2.2) := by
  simp_rw [one_add_eq_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, smul_mul_smul_comm,
    Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_comm

end Triple

end CFSG.RankThree.Chevalley

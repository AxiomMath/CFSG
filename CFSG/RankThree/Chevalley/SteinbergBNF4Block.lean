module

public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.E7SupportedBruhatTorus

public noncomputable section

namespace CFSG.RankThree.Chevalley.SteinbergBN

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open scoped Pointwise

instance instNeZeroTagRank (τ : Tag) : NeZero τ.rank :=
  ⟨by cases τ <;> decide⟩

variable {τ : Tag} {K : Type} [Field K]

open _root_.Classical in
@[expose] def rootCoord (γ : Fin τ.rank → ℤ) : RootModule τ K →ₗ[K] K :=
  if h : IsRoot τ γ then Finsupp.lapply (Sum.inr ⟨γ, h⟩) else 0

theorem rootCoord_apply {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (m : RootModule τ K) :
    rootCoord γ m = m (Sum.inr ⟨γ, hγ⟩) := by
  rw [rootCoord, dite_eq_left hγ, Finsupp.lapply_apply]

theorem rootCoord_rootVec {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (δ : Fin τ.rank → ℤ) :
    rootCoord γ (rootVec τ K δ) = if δ = γ then 1 else 0 := by
  rw [rootCoord_apply hγ]
  by_cases hδ : IsRoot τ δ
  · rw [rootVec_eq_single_of_isRoot hδ, Finsupp.single_apply]
    by_cases h : δ = γ
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right fun e => h (congrArg Subtype.val (Sum.inr_injective e)), ite_eq_right h]
  · rw [rootVec, dite_eq_right hδ, Finsupp.zero_apply, ite_eq_right]
    rintro rfl
    exact hδ hγ

variable {n : ℕ} {β : Fin n → Fin τ.rank → ℤ}

variable (K β) in
@[expose] def blockSpan : Submodule K (RootModule τ K) :=
  Submodule.span K (Set.range fun k => rootVec τ K (β k))

variable (β) in
@[expose] def blockMat (g : ModGL τ K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun a b => rootCoord (β a) ((g : Module.End K (RootModule τ K)) (rootVec τ K (β b)))

theorem blockMat_apply (g : ModGL τ K) (a b : Fin n) :
    blockMat β g a b = rootCoord (β a) ((g : Module.End K (RootModule τ K)) (rootVec τ K (β b))) :=
  rfl

theorem rootVec_mem_blockSpan (k : Fin n) : rootVec τ K (β k) ∈ blockSpan K β :=
  Submodule.subset_span ⟨k, rfl⟩

section Injective

variable (hβ : ∀ k, IsRoot τ (β k)) (hinj : Function.Injective β)
include hβ hinj

theorem rootCoord_rootVec_block (a b : Fin n) :
    rootCoord (β a) (rootVec τ K (β b)) = if a = b then 1 else 0 := by
  rw [rootCoord_rootVec (hβ a)]
  by_cases h : a = b
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl]
  · rw [ite_eq_right fun e => h (hinj e).symm, ite_eq_right h]

theorem eq_sum_of_mem_blockSpan {m : RootModule τ K} (hm : m ∈ blockSpan K β) :
    m = ∑ k, rootCoord (β k) m • rootVec τ K (β k) := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    simp only [rootCoord_rootVec_block hβ hinj, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  | zero => simp
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add, add_smul]
  | smul c x _ hx =>
    conv_lhs => rw [hx]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, mul_smul]

theorem apply_rootVec_eq_sum {g : ModGL τ K}
    (hg : ∀ m ∈ blockSpan K β, (g : Module.End K (RootModule τ K)) m ∈ blockSpan K β)
    (b : Fin n) :
    (g : Module.End K (RootModule τ K)) (rootVec τ K (β b)) =
      ∑ a, blockMat β g a b • rootVec τ K (β a) :=
  eq_sum_of_mem_blockSpan hβ hinj (hg _ (rootVec_mem_blockSpan b))

theorem blockMat_one : blockMat β (1 : ModGL τ K) = 1 := by
  ext a b
  rw [blockMat_apply, Units.val_one, Module.End.one_apply, rootCoord_rootVec_block hβ hinj,
    Matrix.one_apply]

theorem blockMat_mul {g h : ModGL τ K}
    (hh : ∀ m ∈ blockSpan K β, (h : Module.End K (RootModule τ K)) m ∈ blockSpan K β) :
    blockMat β (g * h) = blockMat β g * blockMat β h := by
  ext a b
  rw [blockMat_apply, Units.val_mul, Module.End.mul_apply, apply_rootVec_eq_sum hβ hinj hh,
    map_sum, map_sum, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul, smul_eq_mul, mul_comm]
  rfl

theorem apply_eq_self_of_blockMat_eq_one {g : ModGL τ K}
    (hg : ∀ m ∈ blockSpan K β, (g : Module.End K (RootModule τ K)) m ∈ blockSpan K β)
    (h1 : blockMat β g = 1) (k : Fin n) :
    (g : Module.End K (RootModule τ K)) (rootVec τ K (β k)) = rootVec τ K (β k) := by
  rw [apply_rootVec_eq_sum hβ hinj hg, h1]
  simp [Matrix.one_apply]

omit hβ hinj in
theorem apply_eq_self_of_mem_blockSpan {g : ModGL τ K}
    (hg : ∀ k, (g : Module.End K (RootModule τ K)) (rootVec τ K (β k)) = rootVec τ K (β k))
    {m : RootModule τ K} (hm : m ∈ blockSpan K β) :
    (g : Module.End K (RootModule τ K)) m = m := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    exact hg b
  | zero => rw [map_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

end Injective

theorem blockMat_baseChangeGL {L : Type} [Field L] (σ : K →+* L) (hβ : ∀ k, IsRoot τ (β k))
    (g : ModGL τ K) : blockMat β (baseChangeGL σ g) = (blockMat β g).map σ := by
  ext a b
  rw [blockMat_apply, Matrix.map_apply, blockMat_apply, rootVec_eq_single_of_isRoot (hβ b),
    rootVec_eq_single_of_isRoot (hβ b), baseChangeGL_apply_single, rootCoord_apply (hβ a),
    rootCoord_apply (hβ a), Finsupp.mapRange_apply]

theorem mem_of_mem_subsystemGroup_of_gen {X : Set (Fin τ.rank)}
    {M : Submodule K (RootModule τ K)}
    (hx : ∀ i ∈ X, ∀ c : K, ∀ v ∈ M, xOp τ K i c v ∈ M)
    (hy : ∀ i ∈ X, ∀ c : K, ∀ v ∈ M, yOp τ K i c v ∈ M)
    {g : ModGL τ K} (hg : g ∈ subsystemGroup τ K X) :
    ∀ v ∈ M, (g : Module.End K (RootModule τ K)) v ∈ M := by
  induction hg using Subgroup.closure_induction'' with
  | mem g hg =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hg
    · exact hx i hi c
    · exact hy i hi c
  | inv_mem g hg =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hg
    · intro v hv
      rw [coe_xUnit_inv]
      exact hx i hi (-c) v hv
    · intro v hv
      rw [coe_yUnit_inv]
      exact hy i hi (-c) v hv
  | one => exact fun v hv => hv
  | mul g h _ _ hg hh => exact fun v hv => hg _ (hh v hv)

theorem xOp_rootVec_eq_sum (i : Fin τ.rank) (c : K) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    xOp τ K i c (rootVec τ K α) = ∑ k ∈ Finset.range (stringUp τ i α + 1),
      (((stringDown τ i α + k).choose k : K) * c ^ k) •
        rootVec τ K (α + (k : ℤ) • Pi.single i 1) := by
  rw [rootVec_eq_single_of_isRoot hα, xOp, Finsupp.linearCombination_single, one_smul]
  simp only [ite_eq_right h₁, ite_eq_right h₂]

theorem yOp_rootVec_eq_sum (i : Fin τ.rank) (c : K) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    yOp τ K i c (rootVec τ K α) = ∑ k ∈ Finset.range (stringDown τ i α + 1),
      (((stringUp τ i α + k).choose k : K) * c ^ k) •
        rootVec τ K (α - (k : ℤ) • Pi.single i 1) := by
  rw [rootVec_eq_single_of_isRoot hα, yOp, Finsupp.linearCombination_single, one_smul]
  simp only [ite_eq_right h₁, ite_eq_right h₂]

theorem mem_blockSpan_of_mem_slice {J : Set (Fin τ.rank)} {o : Fin τ.rank → ℤ}
    (hout : ∀ k, ∀ s ∉ J, β k s = o s)
    (hslice : ∀ γ, IsRoot τ γ → (∀ s ∉ J, γ s = o s) → ∃ k, β k = γ)
    (hβ : ∀ k, IsRoot τ (β k))
    (hne : ∀ k, ∀ i ∈ J, β k ≠ Pi.single i 1 ∧ β k ≠ -Pi.single i 1)
    {g : ModGL τ K} (hg : g ∈ subsystemGroup τ K J) {m : RootModule τ K}
    (hm : m ∈ blockSpan K β) : (g : Module.End K (RootModule τ K)) m ∈ blockSpan K β := by
  have hvec : ∀ k, ∀ i ∈ J, ∀ z : ℤ,
      rootVec τ K (β k + z • Pi.single i 1) ∈ blockSpan K β := by
    intro k i hi z
    by_cases hγ : IsRoot τ (β k + z • Pi.single i 1)
    · obtain ⟨k', hk'⟩ := hslice _ hγ fun s hs => by
        rw [Pi.add_apply, Pi.smul_apply, Pi.single_apply,
          ite_eq_right fun e => hs (by rw [e]; exact hi), smul_zero, add_zero, hout k s hs]
      rw [← hk']
      exact rootVec_mem_blockSpan k'
    · rw [rootVec, dite_eq_right hγ]
      exact zero_mem _
  refine mem_of_mem_subsystemGroup_of_gen (fun i hi c v hv => ?_) (fun i hi c v hv => ?_) hg m hm
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [xOp_rootVec_eq_sum i c (hβ k) (hne k i hi).1 (hne k i hi).2]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hvec k i hi l)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [yOp_rootVec_eq_sum i c (hβ k) (hne k i hi).1 (hne k i hi).2]
      refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ?_
      rw [sub_eq_add_neg, ← neg_smul]
      exact hvec k i hi _
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem stringUp_stringDown_eq_stringData {k : ℕ} (hk : k < τ.rootCertificate.roots.length)
    {α : Fin τ.rank → ℤ} (hkα : τ.rootCertificate.root k = α) (i : Fin τ.rank)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    stringUp τ i α = τ.stringData.up k i ∧ stringDown τ i α = τ.stringData.down k i := by
  subst hkα
  have hα := RootCertificate.isRoot_root τ.rootCertificate_check k hk
  obtain ⟨-, h⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  obtain ⟨-, h'⟩ := StringData.isRoot_root_add_iff τ.rootCertificate_check τ.stringData_check hk
    i h₁ h₂
  have e : ∀ m : ℤ, (-(stringDown τ i (τ.rootCertificate.root k) : ℤ) ≤ m ∧
      m ≤ stringUp τ i (τ.rootCertificate.root k)) ↔
        (-(τ.stringData.down k i : ℤ) ≤ m ∧ m ≤ τ.stringData.up k i) := fun m => by
    rw [← h, h']
  have a1 := (e (stringUp τ i (τ.rootCertificate.root k))).1 ⟨by omega, le_rfl⟩
  have a2 := (e (τ.stringData.up k i)).2 ⟨by omega, le_rfl⟩
  have a3 := (e (-(stringDown τ i (τ.rootCertificate.root k) : ℤ))).1 ⟨le_rfl, by omega⟩
  have a4 := (e (-(τ.stringData.down k i : ℤ))).2 ⟨le_rfl, by omega⟩
  omega

variable (β) in
@[expose] def xCoeff (P Q : Fin n → ℕ) (i : Fin τ.rank) (k : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun a b =>
    if k ≤ P b ∧ β b + (k : ℤ) • Pi.single i 1 = β a then ((Q b + k).choose k : ℤ) else 0

variable (β) in
@[expose] def yCoeff (P Q : Fin n → ℕ) (i : Fin τ.rank) (k : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun a b =>
    if k ≤ Q b ∧ β b - (k : ℤ) • Pi.single i 1 = β a then ((P b + k).choose k : ℤ) else 0

theorem rootCoord_sum_range {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (p : ℕ) (hp : p ≤ 3)
    (f : ℕ → K) (v : ℕ → Fin τ.rank → ℤ) :
    rootCoord γ (∑ k ∈ Finset.range (p + 1), f k • rootVec τ K (v k)) =
      ∑ k ∈ Finset.range 4, if k ≤ p ∧ v k = γ then f k else 0 := by
  rw [map_sum]
  simp only [map_smul, rootCoord_rootVec hγ, smul_eq_mul, mul_ite, mul_one, mul_zero]
  symm
  rw [← Finset.sum_subset (Finset.range_mono (show p + 1 ≤ 4 by omega)) ?_]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ p := by
      rw [Finset.mem_range] at hk
      omega
    simp only [hk', true_and]
  · intro k _ hk
    have hk' : ¬k ≤ p := by
      rw [Finset.mem_range] at hk
      omega
    simp only [hk', false_and, ite_false]

theorem blockMat_xUnit (hβ : ∀ k, IsRoot τ (β k)) (i : Fin τ.rank)
    (hne : ∀ b, β b ≠ Pi.single i 1 ∧ β b ≠ -Pi.single i 1) {P Q : Fin n → ℕ}
    (hP : ∀ b, stringUp τ i (β b) = P b) (hQ : ∀ b, stringDown τ i (β b) = Q b) (c : K) :
    blockMat β (xUnit τ K i c) =
      ∑ k ∈ Finset.range 4, c ^ k • (xCoeff β P Q i k).map (Int.cast : ℤ → K) := by
  ext a b
  have hpq := (isRoot_add_smul_single_iff (hβ b) i (hne b).1 (hne b).2).1
  rw [blockMat_apply, coe_xUnit, xOp_rootVec_eq_sum i c (hβ b) (hne b).1 (hne b).2,
    rootCoord_sum_range (hβ a) _ (by omega), Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_apply, Matrix.map_apply, xCoeff, Matrix.of_apply, hP, hQ]
  split_ifs <;> simp [mul_comm]

theorem blockMat_yUnit (hβ : ∀ k, IsRoot τ (β k)) (i : Fin τ.rank)
    (hne : ∀ b, β b ≠ Pi.single i 1 ∧ β b ≠ -Pi.single i 1) {P Q : Fin n → ℕ}
    (hP : ∀ b, stringUp τ i (β b) = P b) (hQ : ∀ b, stringDown τ i (β b) = Q b) (c : K) :
    blockMat β (yUnit τ K i c) =
      ∑ k ∈ Finset.range 4, c ^ k • (yCoeff β P Q i k).map (Int.cast : ℤ → K) := by
  ext a b
  have hpq := (isRoot_add_smul_single_iff (hβ b) i (hne b).1 (hne b).2).1
  rw [blockMat_apply, coe_yUnit, yOp_rootVec_eq_sum i c (hβ b) (hne b).1 (hne b).2,
    rootCoord_sum_range (hβ a) _ (by omega), Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_apply, Matrix.map_apply, yCoeff, Matrix.of_apply, hP, hQ]
  split_ifs <;> simp [mul_comm]

theorem baseChangeGL_mem_subsystemGroup {L : Type} [Field L] (σ : K →+* L)
    {J : Set (Fin τ.rank)} {g : ModGL τ K} (hg : g ∈ subsystemGroup τ K J) :
    baseChangeGL σ g ∈ subsystemGroup τ L J := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rw [baseChangeGL_xUnit]
      exact xUnit_mem_subsystemGroup hi _
    · rw [baseChangeGL_yUnit]
      exact yUnit_mem_subsystemGroup hi _
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

theorem list_prod_weylElt_rootVec_unit (ω : List (Fin τ.rank)) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) : ∃ ε : K, ε ≠ 0 ∧
      (((ω.map fun i => weylElt τ K i 1).prod : ModGL τ K) :
        Module.End K (RootModule τ K)) (rootVec τ K α) =
      ε • rootVec τ K ((coxeterSystem τ).wordProd ω • α) := by
  induction ω with
  | nil => exact ⟨1, one_ne_zero, by simp⟩
  | cons i ω ih =>
    obtain ⟨ε, hε, h⟩ := ih
    refine ⟨ε * ((-1) ^ stringDown τ i ((coxeterSystem τ).wordProd ω • α) *
      (((1 : Kˣ) ^ (-∑ j, τ.cartan i j * ((coxeterSystem τ).wordProd ω • α) j) : Kˣ) :
        K)), mul_ne_zero hε (by simp), ?_⟩
    have e : (coxeterSystem τ).wordProd (i :: ω) • α =
        reflect τ i ((coxeterSystem τ).wordProd ω • α) := by
      rw [CoxeterSystem.wordProd_cons, mul_smul]
      exact simple_smul i _
    rw [e, List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, h, map_smul,
      weylElt_rootVec i 1 (IsRoot.smul hα _), smul_smul]

theorem canonicalRep_rootVec_unit (w : WeylGroup τ) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ ε : K, ε ≠ 0 ∧
      (canonicalRep (coxeterSystem τ) K w : Module.End K (RootModule τ K))
        (rootVec τ K α) = ε • rootVec τ K (w • α) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω]
  exact list_prod_weylElt_rootVec_unit ω hα

section Slice

variable {J : Set (Fin τ.rank)} {o : Fin τ.rank → ℤ}

theorem exists_smul_eq_of_slice (hout : ∀ k, ∀ s ∉ J, β k s = o s)
    (hslice : ∀ γ, IsRoot τ γ → (∀ s ∉ J, γ s = o s) → ∃ k, β k = γ)
    (hβ : ∀ k, IsRoot τ (β k)) {w : WeylGroup τ} (hw : w ∈ parabolicWeylGroup τ J)
    (k : Fin n) : ∃ k', β k' = w • β k :=
  hslice _ (IsRoot.smul (hβ k) w) fun s hs => by
    rw [smul_apply_of_mem_parabolicWeylGroup hw _ hs, hout k s hs]

theorem smul_eq_of_not_lt (hinj : Function.Injective β) {w : WeylGroup τ}
    (hperm : ∀ k, ∃ k', β k' = w • β k)
    (hprec : ∀ j j', β j' = w • β j → ¬j < j') (j : Fin n) : w • β j = β j := by
  by_contra hj
  classical
  set M : Finset (Fin n) := Finset.univ.filter fun k => w • β k ≠ β k
  have hM : M.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  obtain ⟨k, hkM, hmin⟩ := M.exists_min_image id hM
  have hk : w • β k ≠ β k := (Finset.mem_filter.mp hkM).2
  obtain ⟨k', hk'⟩ := hperm k
  have hne : k' ≠ k := fun h => hk (by rw [← hk', h])
  have hlt : k' < k := lt_of_le_of_ne (not_lt.1 (hprec k k' hk')) hne
  have hk'M : k' ∈ M := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => hne ?_⟩
    apply hinj
    apply smul_left_cancel w
    rw [h]
    exact hk'
  exact absurd (hmin k' hk'M) (not_le.mpr hlt)

theorem eq_one_of_smul_eq (hsimple : ∀ i ∈ J, ∃ a b, (Pi.single i 1 : Fin τ.rank → ℤ) = β a - β b)
    {w : WeylGroup τ} (hw : w ∈ parabolicWeylGroup τ J) (h : ∀ k, w • β k = β k) : w = 1 := by
  refine eq_one_of_forall_height_pos fun i => ?_
  by_cases hi : i ∈ J
  · obtain ⟨a, b, hab⟩ := hsimple i hi
    have hfix : w • (Pi.single i 1 : Fin τ.rank → ℤ) = Pi.single i 1 := by
      rw [hab, smul_sub, h, h]
    rw [hfix, height_single]
    exact one_pos
  · have hroot := IsRoot.smul (isRoot_single τ i) w
    have hcoord : (w • (Pi.single i 1 : Fin τ.rank → ℤ)) i = 1 := by
      rw [smul_apply_of_mem_parabolicWeylGroup hw _ hi, Pi.single_eq_same]
    refine (IsRoot.height_pos_iff hroot).2 ?_
    rcases hroot.nonneg_or_nonpos with hs | hs
    · exact hs
    · have := hs i
      omega

theorem mem_subsystemBorel_of_fix
    (hout : ∀ k, ∀ s ∉ J, β k s = o s)
    (hslice : ∀ γ, IsRoot τ γ → (∀ s ∉ J, γ s = o s) → ∃ k, β k = γ)
    (hβ : ∀ k, IsRoot τ (β k)) (hinj : Function.Injective β)
    (hne : ∀ k, ∀ i ∈ J, β k ≠ Pi.single i 1 ∧ β k ≠ -Pi.single i 1)
    (hprec : ∀ j j', j < j' →
      Label.Precedes (Sum.inr ⟨β j, hβ j⟩ : Label τ) (Sum.inr ⟨β j', hβ j'⟩))
    (hsimple : ∀ i ∈ J, ∃ a b, (Pi.single i 1 : Fin τ.rank → ℤ) = β a - β b)
    {g : ModGL τ K} (hg : g ∈ subsystemGroup τ K J)
    (hfix : ∀ k, (g : Module.End K (RootModule τ K)) (rootVec τ K (β k)) = rootVec τ K (β k)) :
    g ∈ subsystemBorel τ K J := by
  have hgS : g ∈ (subsystemGroup τ K J : Set (ModGL τ K)) := hg
  rw [(subsystem_root_group_bruhat (τ := τ) (K := K) (A := J)).2.2.1] at hgS
  simp only [Set.mem_iUnion] at hgS
  obtain ⟨w, hw, hgw⟩ := hgS
  obtain ⟨_, ⟨b, hb, _, rfl, rfl⟩, v, hv, hgbv⟩ := hgw
  beta_reduce at hgbv
  have hbB : b ∈ borelGroup τ K := subsystemBorel_le_borelGroup hb
  have hvU : v ∈ posUnipotent τ K :=
    rootSpan_le_posUnipotent (fun _ h => inversionSet_pos h) hv
  have hvB : v ∈ borelGroup τ K := Subgroup.mem_sup_right hvU
  have hvS : v ∈ subsystemGroup τ K J :=
    parabolicLeviUnipotent_le_subsystemGroup (τ := τ) (K := K) (A := J)
      (rootSpan_mono (inversionSet_subset_parabolicPosRoots hw) hv)
  have hn : ∀ j, (canonicalRep (coxeterSystem τ) K w : Module.End K (RootModule τ K))
      (rootVec τ K (β j)) = ((b⁻¹ * v⁻¹ : ModGL τ K) : Module.End K (RootModule τ K))
        (rootVec τ K (β j)) := by
    intro j
    have hn' : canonicalRep (coxeterSystem τ) K w = b⁻¹ * g * v⁻¹ := by
      rw [← hgbv]
      group
    rw [hn', Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      apply_eq_self_of_mem_blockSpan hfix (mem_blockSpan_of_mem_slice hout hslice hβ hne
        (inv_mem hvS) (rootVec_mem_blockSpan j)), Units.val_mul, Module.End.mul_apply]
  have hprec' : ∀ j j', β j' = w • β j → ¬j < j' := by
    intro j j' hj' hlt
    obtain ⟨ε, hε, hne'⟩ := canonicalRep_rootVec_unit (K := K) w (hβ j)
    have h0 := (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.1 _
      (mul_mem (inv_mem hbB) (inv_mem hvB)) (Sum.inr ⟨β j', hβ j'⟩) (Sum.inr ⟨β j, hβ j⟩)
      (hprec j j' hlt)
    rw [← rootVec_eq_single_of_isRoot (hβ j), ← hn j, hne', ← hj',
      rootVec_eq_single_of_isRoot (hβ j'), Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one] at h0
    exact hε h0
  have hw1 : w = 1 := eq_one_of_smul_eq hsimple hw
    (smul_eq_of_not_lt hinj (exists_smul_eq_of_slice hout hslice hβ hw) hprec')
  subst hw1
  have hv1 : v = 1 := by
    rw [inversionSet_one, show rootSpan τ K (∅ : Set (Fin τ.rank → ℤ)) = ⊥ by
      simp [rootSpan]] at hv
    exact hv
  rw [canonicalRep_one, hv1, mul_one, mul_one] at hgbv
  rw [← hgbv]
  exact hb

end Slice

section Pair

variable {i j : Fin τ.rank}

theorem torusElt_pair_mul (t u t' u' : Kˣ) :
    torusElt τ K i t * torusElt τ K j u * (torusElt τ K i t' * torusElt τ K j u') =
      torusElt τ K i (t * t') * torusElt τ K j (u * u') := by
  simp only [torusElt_mul]
  have h1 := torusElt_mul_comm (τ := τ) (R := K) j i u t'
  calc torusElt τ K i t * torusElt τ K j u * (torusElt τ K i t' * torusElt τ K j u')
      = torusElt τ K i t * (torusElt τ K j u * torusElt τ K i t') * torusElt τ K j u' := by
        group
    _ = _ := by rw [h1]; group

theorem mem_subsystemTorus_pair {g : ModGL τ K} :
    g ∈ subsystemTorus τ K {i, j} ↔ ∃ t u : Kˣ, g = torusElt τ K i t * torusElt τ K j u := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, t, rfl⟩ := hx
      rcases hk with rfl | rfl
      · exact ⟨t, 1, by rw [torusElt_one, mul_one]⟩
      · exact ⟨1, t, by rw [torusElt_one, one_mul]⟩
    | one => exact ⟨1, 1, by rw [torusElt_one, torusElt_one, mul_one]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨t, u, rfl⟩ := hx
      obtain ⟨t', u', rfl⟩ := hy
      exact ⟨_, _, torusElt_pair_mul t u t' u'⟩
    | inv x _ hx =>
      obtain ⟨t, u, rfl⟩ := hx
      refine ⟨t⁻¹, u⁻¹, inv_eq_of_mul_eq_one_right ?_⟩
      rw [torusElt_pair_mul, mul_inv_cancel, mul_inv_cancel, torusElt_one, torusElt_one, mul_one]
  · rintro ⟨t, u, rfl⟩
    exact mul_mem (torusElt_mem_subsystemTorus (Set.mem_insert i {j}) t)
      (torusElt_mem_subsystemTorus (Set.mem_insert_of_mem i (Set.mem_singleton j)) u)

end Pair

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
theorem conj_xUnit_of_apply_single {h : ModGL τ K} (hh : h ∈ torusGroup τ K)
    {i : Fin τ.rank} {a : K}
    (ha : (h : Module.End K (RootModule τ K)) (rootVec τ K (Pi.single i 1)) =
      a • rootVec τ K (Pi.single i 1)) :
    a ≠ 0 ∧ (∀ c : K, h * xUnit τ K i c * h⁻¹ = xUnit τ K i (a * c)) ∧
      ∀ c : K, h * yUnit τ K i c * h⁻¹ = yUnit τ K i (a⁻¹ * c) := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  obtain ⟨hx, hy, -⟩ := root_diagonal_conjugation τ K l
  have hal : a = l i := by
    rw [← torusRootChar_eq_of_apply (isRoot_single τ i) ha]
    refine (eq_torusRootChar_of_conj hh (isRoot_single τ i) fun c => ?_).symm
    rw [pinnedX_single, pinnedX_single]
    exact hx i c
  subst hal
  refine ⟨(l i).ne_zero, hx i, fun c => ?_⟩
  rw [hy i c, Units.val_inv_eq_inv_val]

structure IsSliceBlock (J : Set (Fin τ.rank)) (β : Fin n → Fin τ.rank → ℤ) : Prop where
  isRoot : ∀ k, IsRoot τ (β k)
  injective : Function.Injective β
  slice : ∃ o : Fin τ.rank → ℤ, (∀ k, ∀ s ∉ J, β k s = o s) ∧
    ∀ γ, IsRoot τ γ → (∀ s ∉ J, γ s = o s) → ∃ k, β k = γ
  ne_single : ∀ k, ∀ i ∈ J, β k ≠ Pi.single i 1 ∧ β k ≠ -Pi.single i 1
  precedes : ∀ j j', j < j' →
    Label.Precedes (Sum.inr ⟨β j, isRoot j⟩ : Label τ) (Sum.inr ⟨β j', isRoot j'⟩)
  simple : ∀ i ∈ J, ∃ a b, (Pi.single i 1 : Fin τ.rank → ℤ) = β a - β b

namespace IsSliceBlock

variable {J : Set (Fin τ.rank)} (hB : IsSliceBlock J β)
include hB

theorem mem_blockSpan {g : ModGL τ K} (hg : g ∈ subsystemGroup τ K J) {m : RootModule τ K}
    (hm : m ∈ blockSpan K β) : (g : Module.End K (RootModule τ K)) m ∈ blockSpan K β := by
  obtain ⟨o, hout, hslice⟩ := hB.slice
  exact mem_blockSpan_of_mem_slice hout hslice hB.isRoot hB.ne_single hg hm

theorem blockMat_mul' {g h : ModGL τ K} (hh : h ∈ subsystemGroup τ K J) :
    blockMat β (g * h) = blockMat β g * blockMat β h :=
  blockMat_mul hB.isRoot hB.injective fun _ hm => hB.mem_blockSpan hh hm

theorem blockMat_one' : blockMat β (1 : ModGL τ K) = 1 :=
  blockMat_one hB.isRoot hB.injective

theorem mem_subsystemBorel
    {g : ModGL τ K} (hg : g ∈ subsystemGroup τ K J)
    (h1 : blockMat β g = 1) : g ∈ subsystemBorel τ K J := by
  obtain ⟨o, hout, hslice⟩ := hB.slice
  exact mem_subsystemBorel_of_fix hout hslice hB.isRoot hB.injective hB.ne_single hB.precedes
    hB.simple hg (apply_eq_self_of_blockMat_eq_one hB.isRoot hB.injective
      (fun _ hm => hB.mem_blockSpan hg hm) h1)

theorem blockMat_xUnit_of_idx (idx : Fin n → ℕ)
    (hidx : ∀ b, idx b < τ.rootCertificate.roots.length ∧ τ.rootCertificate.root (idx b) = β b)
    {i : Fin τ.rank} (hi : i ∈ J) (c : K) :
    blockMat β (xUnit τ K i c) = ∑ k ∈ Finset.range 4, c ^ k •
      (xCoeff β (fun b => τ.stringData.up (idx b) i) (fun b => τ.stringData.down (idx b) i) i
        k).map (Int.cast : ℤ → K) :=
  blockMat_xUnit hB.isRoot i (fun b => hB.ne_single b i hi)
    (fun b => (stringUp_stringDown_eq_stringData (hidx b).1 (hidx b).2 i
      (hB.ne_single b i hi).1 (hB.ne_single b i hi).2).1)
    (fun b => (stringUp_stringDown_eq_stringData (hidx b).1 (hidx b).2 i
      (hB.ne_single b i hi).1 (hB.ne_single b i hi).2).2) c

theorem blockMat_yUnit_of_idx (idx : Fin n → ℕ)
    (hidx : ∀ b, idx b < τ.rootCertificate.roots.length ∧ τ.rootCertificate.root (idx b) = β b)
    {i : Fin τ.rank} (hi : i ∈ J) (c : K) :
    blockMat β (yUnit τ K i c) = ∑ k ∈ Finset.range 4, c ^ k •
      (yCoeff β (fun b => τ.stringData.up (idx b) i) (fun b => τ.stringData.down (idx b) i) i
        k).map (Int.cast : ℤ → K) :=
  blockMat_yUnit hB.isRoot i (fun b => hB.ne_single b i hi)
    (fun b => (stringUp_stringDown_eq_stringData (hidx b).1 (hidx b).2 i
      (hB.ne_single b i hi).1 (hB.ne_single b i hi).2).1)
    (fun b => (stringUp_stringDown_eq_stringData (hidx b).1 (hidx b).2 i
      (hB.ne_single b i hi).1 (hB.ne_single b i hi).2).2) c

end IsSliceBlock

end CFSG.RankThree.Chevalley.SteinbergBN

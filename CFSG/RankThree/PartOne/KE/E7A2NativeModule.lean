module

public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.Adapters.TauCetiExceptional.MinusculeAdjointY
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LinearAlgebra.LinearGroups.Generation

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open CFSG.RankThree.E6 (chainRoot)
open scoped commutatorElement Pointwise

@[expose] def e7Index (i : Fin 7) : Fin Tag.E7.rank := i

@[expose] def e7RootVec (m : Fin 126) : Fin Tag.E7.rank → ℤ := e7Certificate.root m

theorem length_e7Certificate_roots : e7Certificate.roots.length = 126 := by decide +kernel

theorem isRoot_e7RootVec (m : Fin 126) : IsRoot Tag.E7 (e7RootVec m) :=
  RootCertificate.isRoot_root e7Certificate_check m (by rw [length_e7Certificate_roots]; exact m.2)

theorem isRoot_iff_exists_e7RootVec {v : Fin Tag.E7.rank → ℤ} :
    IsRoot Tag.E7 v ↔ ∃ m : Fin 126, e7RootVec m = v := by
  refine ⟨fun h => ?_, fun ⟨m, hm⟩ => hm ▸ isRoot_e7RootVec m⟩
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq e7Certificate_check h
  exact ⟨⟨k, length_e7Certificate_roots ▸ hk⟩, rfl⟩

@[expose] def support13 : Set (Fin Tag.E7.rank) := {e7Index 0, e7Index 2}

theorem mem_support13 (i : Fin Tag.E7.rank) :
    i ∈ support13 ↔ (i = e7Index 0 ∨ i = e7Index 2) := by
  simp only [support13, Set.mem_insert_iff, Set.mem_singleton_iff]

@[expose] def chain13 : Fin 2 → Fin Tag.E7.rank := ![e7Index 0, e7Index 2]

theorem mem_support13_0 : e7Index 0 ∈ support13 := (mem_support13 _).2 (Or.inl rfl)

theorem mem_support13_2 : e7Index 2 ∈ support13 := (mem_support13 _).2 (Or.inr rfl)

@[expose] def a2Weight : Fin 3 → Fin Tag.E7.rank → ℤ :=
  (![![1, 0, 1, 1, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0]] :
    Fin 3 → Fin 7 → ℤ)

theorem exists_e7RootVec_a2Weight : ∀ k : Fin 3, ∃ m : Fin 126, e7RootVec m = a2Weight k := by
  decide +kernel

theorem isRoot_a2Weight (k : Fin 3) : IsRoot Tag.E7 (a2Weight k) := by
  obtain ⟨m, hm⟩ := exists_e7RootVec_a2Weight k
  rw [← hm]
  exact isRoot_e7RootVec m

theorem a2Weight_injective : Function.Injective a2Weight := by
  intro k k' h
  revert k k'
  decide

abbrev a2Label (k : Fin 3) : Label Tag.E7 := Sum.inr ⟨a2Weight k, isRoot_a2Weight k⟩

theorem a2Label_injective : Function.Injective a2Label := by
  intro k k' h
  exact a2Weight_injective (congrArg Subtype.val (Sum.inr_injective h))

variable (K : Type) [Field K]

@[expose] def a2Vec (k : Fin 3) : RootModule Tag.E7 K := Finsupp.single (a2Label k) 1

theorem rootVec_a2Weight (k : Fin 3) : rootVec Tag.E7 K (a2Weight k) = a2Vec K k :=
  CFSG.TauCetiBridge.Minuscule.rootVec_eq_single K (isRoot_a2Weight k)

variable {K}

theorem rootVec_eq_zero_of_not_isRoot {β : Fin Tag.E7.rank → ℤ} (hβ : ¬IsRoot Tag.E7 β) :
    rootVec Tag.E7 K β = 0 := by
  rw [rootVec, dite_eq_right hβ]

theorem a2Vec_apply (k i : Fin 3) : a2Vec K k (a2Label i) = if i = k then 1 else 0 := by
  rw [a2Vec, Finsupp.single_apply]
  by_cases h : i = k
  · rw [ite_eq_left (congrArg a2Label h).symm, ite_eq_left h]
  · rw [ite_eq_right fun e => h (a2Label_injective e).symm, ite_eq_right h]

theorem rootVec_apply_a2Label (γ : Fin Tag.E7.rank → ℤ) (i : Fin 3) :
    rootVec Tag.E7 K γ (a2Label i) = if γ = a2Weight i then 1 else 0 := by
  by_cases hγ : IsRoot Tag.E7 γ
  · rw [CFSG.TauCetiBridge.Minuscule.rootVec_eq_single K hγ, Finsupp.single_apply]
    by_cases h : γ = a2Weight i
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right fun e => h (congrArg Subtype.val (Sum.inr_injective e)), ite_eq_right h]
  · rw [rootVec_eq_zero_of_not_isRoot hγ, Finsupp.zero_apply, ite_eq_right]
    rintro rfl
    exact hγ (isRoot_a2Weight i)

variable (K) in
@[expose] def a2Module : Submodule K (RootModule Tag.E7 K) :=
  Submodule.span K (Set.range (a2Vec K))

theorem a2Vec_mem (k : Fin 3) : a2Vec K k ∈ a2Module K :=
  Submodule.subset_span ⟨k, rfl⟩

theorem eq_sum_of_mem_a2Module {m : RootModule Tag.E7 K} (hm : m ∈ a2Module K) :
    m = ∑ k, m (a2Label k) • a2Vec K k := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [a2Vec_apply, ite_eq_right hj, zero_smul])
      (by simp), a2Vec_apply, ite_eq_left rfl, one_smul]
  | zero => simp
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finsupp.add_apply, add_smul]
  | smul c x _ hx =>
    conv_lhs => rw [hx]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul, mul_smul]

theorem rootVec_mem_a2Module {γ : Fin Tag.E7.rank → ℤ}
    (h : (∀ m : Fin 126, e7RootVec m ≠ γ) ∨ ∃ k, a2Weight k = γ) :
    rootVec Tag.E7 K γ ∈ a2Module K := by
  rcases h with h | ⟨k, rfl⟩
  · have hγ : ¬IsRoot Tag.E7 γ := fun hγ => by
      obtain ⟨m, hm⟩ := isRoot_iff_exists_e7RootVec.1 hγ
      exact h m hm
    rw [rootVec_eq_zero_of_not_isRoot hγ]
    exact zero_mem _
  · rw [rootVec_a2Weight]
    exact a2Vec_mem k

theorem xOp_rootVec_E7 (i : Fin Tag.E7.rank) (c : K) {α : Fin Tag.E7.rank → ℤ}
    (hα : IsRoot Tag.E7 α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    xOp Tag.E7 K i c (rootVec Tag.E7 K α) =
      rootVec Tag.E7 K α + c • rootVec Tag.E7 K (α + Pi.single i 1) := by
  by_cases hr : IsRoot Tag.E7 (α + Pi.single i 1)
  · exact CFSG.TauCetiBridge.Minuscule.xOp_rootVec_of_add K
      CFSG.LieType.Steinberg.Minuscule.posDef_cartan_E7 i c hα h₁ h₂ hr
  · rw [CFSG.TauCetiBridge.Minuscule.xOp_rootVec_of_not_add K i c hα h₁ h₂ hr,
      rootVec_eq_zero_of_not_isRoot hr, smul_zero, add_zero]

theorem yOp_rootVec_E7 (i : Fin Tag.E7.rank) (c : K) {α : Fin Tag.E7.rank → ℤ}
    (hα : IsRoot Tag.E7 α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    yOp Tag.E7 K i c (rootVec Tag.E7 K α) =
      rootVec Tag.E7 K α + c • rootVec Tag.E7 K (α - Pi.single i 1) := by
  by_cases hr : IsRoot Tag.E7 (α - Pi.single i 1)
  · exact CFSG.TauCetiBridge.Minuscule.yOp_rootVec_of_sub K
      CFSG.LieType.Steinberg.Minuscule.posDef_cartan_E7 i c hα h₁ h₂ hr
  · rw [CFSG.TauCetiBridge.Minuscule.yOp_rootVec_of_not_sub K i c hα h₁ h₂ hr,
      rootVec_eq_zero_of_not_isRoot hr, smul_zero, add_zero]

theorem a2Weight_ne_single : ∀ k : Fin 3, ∀ i : Fin 7, (i = 0 ∨ i = 2) →
    a2Weight k ≠ Pi.single (e7Index i) 1 ∧ a2Weight k ≠ -Pi.single (e7Index i) 1 := by
  decide +kernel

theorem a2Weight_add_single : ∀ k : Fin 3, ∀ i : Fin 7, (i = 0 ∨ i = 2) →
    (∀ m : Fin 126, e7RootVec m ≠ a2Weight k + Pi.single (e7Index i) 1) ∨
      ∃ k', a2Weight k' = a2Weight k + Pi.single (e7Index i) 1 := by
  decide +kernel

theorem a2Weight_sub_single : ∀ k : Fin 3, ∀ i : Fin 7, (i = 0 ∨ i = 2) →
    (∀ m : Fin 126, e7RootVec m ≠ a2Weight k - Pi.single (e7Index i) 1) ∨
      ∃ k', a2Weight k' = a2Weight k - Pi.single (e7Index i) 1 := by
  decide +kernel

theorem xOp_a2Vec {i : Fin Tag.E7.rank} (hi : i ∈ support13) (c : K) (k : Fin 3) :
    xOp Tag.E7 K i c (a2Vec K k) =
      a2Vec K k + c • rootVec Tag.E7 K (a2Weight k + Pi.single i 1) := by
  rw [← rootVec_a2Weight]
  exact xOp_rootVec_E7 i c (isRoot_a2Weight k) (a2Weight_ne_single k i ((mem_support13 i).1 hi)).1
    (a2Weight_ne_single k i ((mem_support13 i).1 hi)).2

theorem yOp_a2Vec {i : Fin Tag.E7.rank} (hi : i ∈ support13) (c : K) (k : Fin 3) :
    yOp Tag.E7 K i c (a2Vec K k) =
      a2Vec K k + c • rootVec Tag.E7 K (a2Weight k - Pi.single i 1) := by
  rw [← rootVec_a2Weight]
  exact yOp_rootVec_E7 i c (isRoot_a2Weight k) (a2Weight_ne_single k i ((mem_support13 i).1 hi)).1
    (a2Weight_ne_single k i ((mem_support13 i).1 hi)).2

theorem mem_of_mem_subsystemGroup_of_invariant {τ : Tag} {X : Set (Fin τ.rank)}
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

theorem mem_a2Module_of_mem {g : ModGL Tag.E7 K} (hg : g ∈ subsystemGroup Tag.E7 K support13)
    {m : RootModule Tag.E7 K} (hm : m ∈ a2Module K) :
    (g : Module.End K (RootModule Tag.E7 K)) m ∈ a2Module K := by
  refine mem_of_mem_subsystemGroup_of_invariant (fun i hi c v hv => ?_)
    (fun i hi c v hv => ?_) hg m hm
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [xOp_a2Vec hi]
      exact add_mem (a2Vec_mem k) (Submodule.smul_mem _ _
        (rootVec_mem_a2Module (a2Weight_add_single k i ((mem_support13 i).1 hi))))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [yOp_a2Vec hi]
      exact add_mem (a2Vec_mem k) (Submodule.smul_mem _ _
        (rootVec_mem_a2Module (a2Weight_sub_single k i ((mem_support13 i).1 hi))))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

@[expose] def a2Mat (g : ModGL Tag.E7 K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => (g : Module.End K (RootModule Tag.E7 K)) (a2Vec K j) (a2Label i)

theorem apply_a2Vec {g : ModGL Tag.E7 K} (hg : g ∈ subsystemGroup Tag.E7 K support13)
    (j : Fin 3) :
    (g : Module.End K (RootModule Tag.E7 K)) (a2Vec K j) = ∑ i, a2Mat g i j • a2Vec K i :=
  eq_sum_of_mem_a2Module (mem_a2Module_of_mem hg (a2Vec_mem j))

theorem a2Mat_one : a2Mat (1 : ModGL Tag.E7 K) = 1 := by
  ext i j
  rw [a2Mat, Matrix.of_apply, Units.val_one, Module.End.one_apply, a2Vec_apply, Matrix.one_apply]

theorem a2Mat_mul {g h : ModGL Tag.E7 K} (_hg : g ∈ subsystemGroup Tag.E7 K support13)
    (hh : h ∈ subsystemGroup Tag.E7 K support13) :
    a2Mat (g * h) = a2Mat g * a2Mat h := by
  ext i j
  rw [a2Mat, Matrix.of_apply, Units.val_mul, Module.End.mul_apply, apply_a2Vec hh, map_sum,
    Finsupp.finsetSum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  rfl

theorem a2Mat_xUnit {i₀ : Fin 7} (hi : e7Index i₀ ∈ support13) {p q : Fin 3}
    (hpq : ∀ i j : Fin 3, a2Weight j + Pi.single (e7Index i₀) 1 = a2Weight i ↔ (i = p ∧ j = q))
    (t : K) : a2Mat (xUnit Tag.E7 K (e7Index i₀) t) = 1 + single p q t := by
  ext i j
  rw [a2Mat, Matrix.of_apply, coe_xUnit, xOp_a2Vec hi, Finsupp.add_apply, Finsupp.smul_apply,
    rootVec_apply_a2Label, a2Vec_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have key := hpq i j
  by_cases h : a2Weight j + Pi.single (e7Index i₀) 1 = a2Weight i
  · obtain ⟨rfl, rfl⟩ := key.1 h
    simp [h]
  · have h' : ¬(p = i ∧ q = j) := fun e => h (key.2 ⟨e.1.symm, e.2.symm⟩)
    simp [h, h']

theorem a2Mat_yUnit {i₀ : Fin 7} (hi : e7Index i₀ ∈ support13) {p q : Fin 3}
    (hpq : ∀ i j : Fin 3, a2Weight j - Pi.single (e7Index i₀) 1 = a2Weight i ↔ (i = p ∧ j = q))
    (t : K) : a2Mat (yUnit Tag.E7 K (e7Index i₀) t) = 1 + single p q t := by
  ext i j
  rw [a2Mat, Matrix.of_apply, coe_yUnit, yOp_a2Vec hi, Finsupp.add_apply, Finsupp.smul_apply,
    rootVec_apply_a2Label, a2Vec_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have key := hpq i j
  by_cases h : a2Weight j - Pi.single (e7Index i₀) 1 = a2Weight i
  · obtain ⟨rfl, rfl⟩ := key.1 h
    simp [h]
  · have h' : ¬(p = i ∧ q = j) := fun e => h (key.2 ⟨e.1.symm, e.2.symm⟩)
    simp [h, h']

theorem a2Mat_x1 (t : K) : a2Mat (xUnit Tag.E7 K (e7Index 0) t) = 1 + single 0 1 t :=
  a2Mat_xUnit mem_support13_0 (by decide +kernel) t

theorem a2Mat_y1 (t : K) : a2Mat (yUnit Tag.E7 K (e7Index 0) t) = 1 + single 1 0 t :=
  a2Mat_yUnit mem_support13_0 (by decide +kernel) t

theorem a2Mat_x3 (t : K) : a2Mat (xUnit Tag.E7 K (e7Index 2) t) = 1 + single 1 2 t :=
  a2Mat_xUnit mem_support13_2 (by decide +kernel) t

theorem a2Mat_y3 (t : K) : a2Mat (yUnit Tag.E7 K (e7Index 2) t) = 1 + single 2 1 t :=
  a2Mat_yUnit mem_support13_2 (by decide +kernel) t

theorem a2Weight_pairing : ∀ k : Fin 3,
    (∑ j, Tag.E7.cartan (e7Index 0) j * a2Weight k j) = (![1, -1, 0] : Fin 3 → ℤ) k ∧
    (∑ j, Tag.E7.cartan (e7Index 2) j * a2Weight k j) = (![0, 1, -1] : Fin 3 → ℤ) k := by
  decide +kernel

theorem a2Mat_torusElt (i : Fin Tag.E7.rank) (a : Kˣ) :
    a2Mat (torusElt Tag.E7 K i a) = Matrix.diagonal fun k =>
      ((a ^ (∑ j, Tag.E7.cartan i j * a2Weight k j) : Kˣ) : K) := by
  ext p q
  rw [a2Mat, Matrix.of_apply, ← rootVec_a2Weight, torusElt_rootVec i a (isRoot_a2Weight q),
    rootVec_a2Weight, Finsupp.smul_apply, a2Vec_apply, Matrix.diagonal_apply]
  by_cases h : p = q
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, smul_eq_mul, mul_one]
  · rw [ite_eq_right h, ite_eq_right h, smul_zero]

theorem torusElt_mem_a2Group {i : Fin Tag.E7.rank} (hi : i ∈ support13) (a : Kˣ) :
    torusElt Tag.E7 K i a ∈ subsystemGroup Tag.E7 K support13 :=
  subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hi a)

@[expose] def a2TorusElt (a b : Kˣ) : ModGL Tag.E7 K :=
  torusElt Tag.E7 K (e7Index 0) a * torusElt Tag.E7 K (e7Index 2) b

theorem a2TorusElt_mem (a b : Kˣ) : a2TorusElt a b ∈ subsystemGroup Tag.E7 K support13 :=
  mul_mem (torusElt_mem_a2Group mem_support13_0 a) (torusElt_mem_a2Group mem_support13_2 b)

theorem a2Mat_a2TorusElt (a b : Kˣ) :
    a2Mat (a2TorusElt a b) =
      Matrix.diagonal ![(a : K), ((a⁻¹ * b : Kˣ) : K), ((b⁻¹ : Kˣ) : K)] := by
  rw [a2TorusElt, a2Mat_mul (torusElt_mem_a2Group mem_support13_0 a)
      (torusElt_mem_a2Group mem_support13_2 b), a2Mat_torusElt, a2Mat_torusElt,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  obtain ⟨h0, h2⟩ := a2Weight_pairing k
  rw [h0, h2]
  fin_cases k <;> simp [Units.val_mul, _root_.zpow_neg]

theorem det_a2Mat {g : ModGL Tag.E7 K} (hg : g ∈ subsystemGroup Tag.E7 K support13) :
    (a2Mat g).det = 1 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rcases (mem_support13 i).1 hi with rfl | rfl
      · rw [a2Mat_x1]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [a2Mat_x3]; exact det_transvection_of_ne _ _ (by decide) _
    · rcases (mem_support13 i).1 hi with rfl | rfl
      · rw [a2Mat_y1]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [a2Mat_y3]; exact det_transvection_of_ne _ _ (by decide) _
  | one => rw [a2Mat_one, det_one]
  | mul x y hx hy ihx ihy => rw [a2Mat_mul hx hy, det_mul, ihx, ihy, mul_one]
  | inv x hx ih =>
    have h := a2Mat_mul (inv_mem hx) hx
    rw [inv_mul_cancel, a2Mat_one] at h
    have h' := congrArg Matrix.det h
    rw [det_one, det_mul, ih, mul_one] at h'
    exact h'.symm

variable (K) in
@[expose] def a2Rep : subsystemGroup Tag.E7 K support13 →* SpecialLinearGroup (Fin 3) K where
  toFun g := ⟨a2Mat (g : ModGL Tag.E7 K), det_a2Mat g.2⟩
  map_one' := Subtype.ext a2Mat_one
  map_mul' g h := Subtype.ext (a2Mat_mul g.2 h.2)

theorem coe_a2Rep (g : subsystemGroup Tag.E7 K support13) :
    ((a2Rep K g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      a2Mat (g : ModGL Tag.E7 K) :=
  rfl

theorem a2Mat_inv {g : ModGL Tag.E7 K} (hg : g ∈ subsystemGroup Tag.E7 K support13) :
    a2Mat g⁻¹ = (a2Mat g)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← a2Mat_mul hg (inv_mem hg), mul_inv_cancel, a2Mat_one]

theorem chainRoot13_mem : ∀ k l : Fin 3, k ≠ l → ∃ m : Fin 126,
    e7RootVec m = chainRoot chain13 k l ∧
      ∀ i, ¬(i = e7Index 0 ∨ i = e7Index 2) → e7RootVec m i = 0 := by
  decide +kernel

theorem chainRoot13_mem_parabolicRoots {k l : Fin 3} (hkl : k ≠ l) :
    chainRoot chain13 k l ∈ parabolicRoots Tag.E7 support13 := by
  obtain ⟨m, hm, hs⟩ := chainRoot13_mem k l hkl
  rw [← hm]
  exact ⟨isRoot_e7RootVec m, fun i hi => hs i ((mem_support13 i).not.1 hi)⟩

theorem exists_chainRoot13_of_support13 : ∀ m : Fin 126,
    (∀ i, ¬(i = e7Index 0 ∨ i = e7Index 2) → e7RootVec m i = 0) →
      ∃ k l : Fin 3, k ≠ l ∧ chainRoot chain13 k l = e7RootVec m := by
  decide +kernel

theorem exists_chainRoot13_of_mem {α : Fin Tag.E7.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E7 support13) :
    ∃ k l : Fin 3, k ≠ l ∧ chainRoot chain13 k l = α := by
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e7RootVec.1 hα.1
  exact exists_chainRoot13_of_support13 m fun i hi => hα.2 i ((mem_support13 i).not.2 hi)

theorem chainRoot13_eq_sub : ∀ i j : Fin 3, chainRoot chain13 i j = a2Weight i - a2Weight j := by
  decide +kernel

theorem pinnedX_mem_a2Group {α : Fin Tag.E7.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E7 support13) (t : K) :
    pinnedX Tag.E7 K α t ∈ subsystemGroup Tag.E7 K support13 :=
  rootSubgroup_le_subsystemGroup hα (mem_rootSubgroup.2 ⟨t, rfl⟩)

variable (K) in
@[expose] def A2RootFamily (i j : Fin 3) : Prop :=
  ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ t : K,
    a2Mat (pinnedX Tag.E7 K (chainRoot chain13 i j) t) = 1 + single i j ((ε : K) * t)

theorem a2RootFamily_of_eq {i j : Fin 3} {g : K → ModGL Tag.E7 K}
    (hg : ∀ t, pinnedX Tag.E7 K (chainRoot chain13 i j) t = g t)
    (h : ∀ t, a2Mat (g t) = 1 + single i j t) : A2RootFamily K i j :=
  ⟨1, Or.inl rfl, fun t => by rw [hg, h, Int.cast_one, one_mul]⟩

theorem a2RootFamily_comp {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hsum : chainRoot chain13 i j + chainRoot chain13 j k = chainRoot chain13 i k)
    (hne : chainRoot chain13 i j ≠ chainRoot chain13 j k)
    (hne' : chainRoot chain13 i j ≠ -chainRoot chain13 j k)
    (h₁ : A2RootFamily K i j) (h₂ : A2RootFamily K j k) : A2RootFamily K i k := by
  obtain ⟨ε₁, hε₁, h₁⟩ := h₁
  obtain ⟨ε₂, hε₂, h₂⟩ := h₂
  have hα := chainRoot13_mem_parabolicRoots hij
  have hβ := chainRoot13_mem_parabolicRoots hjk
  have hγ := chainRoot13_mem_parabolicRoots hik
  obtain ⟨hC, hcomm⟩ := (simply_laced_root_commutator_unit Tag.E7 (Or.inr (Or.inr (Or.inl rfl)))
    hα.1 hβ.1 hne hne').1 (hsum ▸ hγ.1)
  set C := commConst Tag.E7 (chainRoot chain13 i j) (chainRoot chain13 j k) (1, 1)
  have hCC : (C : K) * C = 1 := by rcases hC with h | h <;> rw [h] <;> norm_num
  refine ⟨ε₁ * ε₂ * C, ?_, fun t => ?_⟩
  · rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl <;> rcases hC with h | h <;>
      simp [h]
  have e : pinnedX Tag.E7 K (chainRoot chain13 i k) t =
      ⁅pinnedX Tag.E7 K (chainRoot chain13 i j) 1,
        pinnedX Tag.E7 K (chainRoot chain13 j k) ((C : K) * t)⁆ := by
    rw [hcomm K 1 ((C : K) * t), hsum]
    congr 1
    rw [mul_one, ← mul_assoc, hCC, one_mul]
  have m1 := pinnedX_mem_a2Group hα (1 : K)
  have m2 := pinnedX_mem_a2Group hβ ((C : K) * t)
  rw [e, commutatorElement_def, a2Mat_mul (mul_mem (mul_mem m1 m2) (inv_mem m1)) (inv_mem m2),
    a2Mat_mul (mul_mem m1 m2) (inv_mem m1), a2Mat_mul m1 m2, a2Mat_inv m1, a2Mat_inv m2, h₁, h₂,
    CFSG.LinearGroups.elementary_three_index_commutator hik hij hjk.symm]
  congr 2
  push_cast
  ring

theorem chainRoot13_values :
    chainRoot chain13 0 1 = Pi.single (e7Index 0) 1 ∧
    chainRoot chain13 1 2 = Pi.single (e7Index 2) 1 ∧
    chainRoot chain13 1 0 = -Pi.single (e7Index 0) 1 ∧
    chainRoot chain13 2 1 = -Pi.single (e7Index 2) 1 := by
  decide +kernel

theorem chainRoot13_sums :
    (chainRoot chain13 0 1 + chainRoot chain13 1 2 = chainRoot chain13 0 2 ∧
      chainRoot chain13 0 1 ≠ chainRoot chain13 1 2 ∧
      chainRoot chain13 0 1 ≠ -chainRoot chain13 1 2) ∧
    (chainRoot chain13 2 1 + chainRoot chain13 1 0 = chainRoot chain13 2 0 ∧
      chainRoot chain13 2 1 ≠ chainRoot chain13 1 0 ∧
      chainRoot chain13 2 1 ≠ -chainRoot chain13 1 0) := by
  decide +kernel

theorem a2RootFamily_all : ∀ i j : Fin 3, i ≠ j → A2RootFamily K i j := by
  obtain ⟨c01, c12, c10, c21⟩ := chainRoot13_values
  obtain ⟨s02, s20⟩ := chainRoot13_sums
  have f01 : A2RootFamily K 0 1 := a2RootFamily_of_eq (fun t => by rw [c01, pinnedX_single])
    a2Mat_x1
  have f12 : A2RootFamily K 1 2 := a2RootFamily_of_eq (fun t => by rw [c12, pinnedX_single])
    a2Mat_x3
  have f10 : A2RootFamily K 1 0 := a2RootFamily_of_eq
    (fun t => by rw [c10, pinnedX_neg_single]) a2Mat_y1
  have f21 : A2RootFamily K 2 1 := a2RootFamily_of_eq
    (fun t => by rw [c21, pinnedX_neg_single]) a2Mat_y3
  have f02 := a2RootFamily_comp (by decide) (by decide) (by decide) s02.1 s02.2.1 s02.2.2 f01 f12
  have f20 := a2RootFamily_comp (by decide) (by decide) (by decide) s20.1 s20.2.1 s20.2.2 f21 f10
  intro i j hij
  match i, j, hij with
  | 0, 0, h => exact absurd rfl h
  | 0, 1, _ => exact f01
  | 0, 2, _ => exact f02
  | 1, 0, _ => exact f10
  | 1, 1, h => exact absurd rfl h
  | 1, 2, _ => exact f12
  | 2, 0, _ => exact f20
  | 2, 1, _ => exact f21
  | 2, 2, h => exact absurd rfl h

theorem a2Rep_surjective : Function.Surjective (a2Rep K) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← CFSG.LinearGroups.special_linear_elementary_generation, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  obtain ⟨ε, hε, h⟩ := a2RootFamily_all (K := K) i j hij
  have hmem := pinnedX_mem_a2Group (chainRoot13_mem_parabolicRoots hij) ((ε : K) * c)
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  rw [coe_a2Rep, h, CFSG.LinearGroups.coe_transvection]
  congr 1
  rcases hε with rfl | rfl <;> simp

end CFSG.RankThree.PartOne.KE

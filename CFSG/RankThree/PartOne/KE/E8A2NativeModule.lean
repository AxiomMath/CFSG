module

public import Certificates.Certificate1952

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open CFSG.RankThree.E6 (chainRoot)
open scoped commutatorElement Pointwise

theorem length_e8Certificate_roots : e8Certificate.roots.length = 240 :=
  Certificates.certificate1952.1

theorem isRoot_e8RootVec (m : Fin 240) : IsRoot Tag.E8 (e8RootVec m) :=
  RootCertificate.isRoot_root e8Certificate_check m (by rw [length_e8Certificate_roots]; exact m.2)

theorem isRoot_iff_exists_e8RootVec {v : Fin Tag.E8.rank → ℤ} :
    IsRoot Tag.E8 v ↔ ∃ m : Fin 240, e8RootVec m = v := by
  refine ⟨fun h => ?_, fun ⟨m, hm⟩ => hm ▸ isRoot_e8RootVec m⟩
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq e8Certificate_check h
  exact ⟨⟨k, length_e8Certificate_roots ▸ hk⟩, rfl⟩

@[expose] def e8support13 : Set (Fin Tag.E8.rank) := {e8Index 0, e8Index 2}

theorem mem_e8support13 (i : Fin Tag.E8.rank) :
    i ∈ e8support13 ↔ (i = e8Index 0 ∨ i = e8Index 2) := by
  simp only [e8support13, Set.mem_insert_iff, Set.mem_singleton_iff]

theorem mem_e8support13_0 : e8Index 0 ∈ e8support13 := (mem_e8support13 _).2 (Or.inl rfl)

theorem mem_e8support13_2 : e8Index 2 ∈ e8support13 := (mem_e8support13 _).2 (Or.inr rfl)

theorem exists_e8RootVec_e8a2Weight :
    ∀ k : Fin 3, ∃ m : Fin 240, e8RootVec m = e8a2Weight k :=
  Certificates.certificate1952.2.1

theorem isRoot_e8a2Weight (k : Fin 3) : IsRoot Tag.E8 (e8a2Weight k) := by
  obtain ⟨m, hm⟩ := exists_e8RootVec_e8a2Weight k
  rw [← hm]
  exact isRoot_e8RootVec m

theorem e8a2Weight_injective : Function.Injective e8a2Weight := by
  intro k k' h
  revert k k'
  decide

abbrev e8a2Label (k : Fin 3) : Label Tag.E8 := Sum.inr ⟨e8a2Weight k, isRoot_e8a2Weight k⟩

theorem e8a2Label_injective : Function.Injective e8a2Label := by
  intro k k' h
  exact e8a2Weight_injective (congrArg Subtype.val (Sum.inr_injective h))

variable (K : Type) [Field K]

@[expose] def e8a2Vec (k : Fin 3) : RootModule Tag.E8 K := Finsupp.single (e8a2Label k) 1

theorem rootVec_e8a2Weight (k : Fin 3) : rootVec Tag.E8 K (e8a2Weight k) = e8a2Vec K k :=
  CFSG.TauCetiBridge.Minuscule.rootVec_eq_single K (isRoot_e8a2Weight k)

variable {K}

theorem e8_rootVec_eq_zero_of_not_isRoot {β : Fin Tag.E8.rank → ℤ} (hβ : ¬IsRoot Tag.E8 β) :
    rootVec Tag.E8 K β = 0 := by
  rw [rootVec, dite_eq_right hβ]

theorem e8a2Vec_apply (k i : Fin 3) : e8a2Vec K k (e8a2Label i) = if i = k then 1 else 0 := by
  rw [e8a2Vec, Finsupp.single_apply]
  by_cases h : i = k
  · rw [ite_eq_left (congrArg e8a2Label h).symm, ite_eq_left h]
  · rw [ite_eq_right fun e => h (e8a2Label_injective e).symm, ite_eq_right h]

theorem rootVec_apply_e8a2Label (γ : Fin Tag.E8.rank → ℤ) (i : Fin 3) :
    rootVec Tag.E8 K γ (e8a2Label i) = if γ = e8a2Weight i then 1 else 0 := by
  by_cases hγ : IsRoot Tag.E8 γ
  · rw [CFSG.TauCetiBridge.Minuscule.rootVec_eq_single K hγ, Finsupp.single_apply]
    by_cases h : γ = e8a2Weight i
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right fun e => h (congrArg Subtype.val (Sum.inr_injective e)), ite_eq_right h]
  · rw [e8_rootVec_eq_zero_of_not_isRoot hγ, Finsupp.zero_apply, ite_eq_right]
    rintro rfl
    exact hγ (isRoot_e8a2Weight i)

variable (K) in
@[expose] def e8a2Module : Submodule K (RootModule Tag.E8 K) :=
  Submodule.span K (Set.range (e8a2Vec K))

theorem e8a2Vec_mem (k : Fin 3) : e8a2Vec K k ∈ e8a2Module K :=
  Submodule.subset_span ⟨k, rfl⟩

theorem eq_sum_of_mem_e8a2Module {m : RootModule Tag.E8 K} (hm : m ∈ e8a2Module K) :
    m = ∑ k, m (e8a2Label k) • e8a2Vec K k := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [e8a2Vec_apply, ite_eq_right hj, zero_smul])
      (by simp), e8a2Vec_apply, ite_eq_left rfl, one_smul]
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

theorem rootVec_mem_e8a2Module {γ : Fin Tag.E8.rank → ℤ}
    (h : (∀ m : Fin 240, e8RootVec m ≠ γ) ∨ ∃ k, e8a2Weight k = γ) :
    rootVec Tag.E8 K γ ∈ e8a2Module K := by
  rcases h with h | ⟨k, rfl⟩
  · have hγ : ¬IsRoot Tag.E8 γ := fun hγ => by
      obtain ⟨m, hm⟩ := isRoot_iff_exists_e8RootVec.1 hγ
      exact h m hm
    rw [e8_rootVec_eq_zero_of_not_isRoot hγ]
    exact zero_mem _
  · rw [rootVec_e8a2Weight]
    exact e8a2Vec_mem k

theorem e8_cartan_eq : Tag.cartan .E8 = CartanMatrix.E 8 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem e8_posDef_cartan : ((Tag.cartan .E8).map (Int.cast : ℤ → ℚ)).PosDef := by
  rw [e8_cartan_eq]
  exact TauCeti.posDef_map_intCast_cartanMatrix_E8

theorem xOp_rootVec_E8 (i : Fin Tag.E8.rank) (c : K) {α : Fin Tag.E8.rank → ℤ}
    (hα : IsRoot Tag.E8 α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    xOp Tag.E8 K i c (rootVec Tag.E8 K α) =
      rootVec Tag.E8 K α + c • rootVec Tag.E8 K (α + Pi.single i 1) := by
  by_cases hr : IsRoot Tag.E8 (α + Pi.single i 1)
  · exact CFSG.TauCetiBridge.Minuscule.xOp_rootVec_of_add K e8_posDef_cartan i c hα h₁ h₂ hr
  · rw [CFSG.TauCetiBridge.Minuscule.xOp_rootVec_of_not_add K i c hα h₁ h₂ hr,
      e8_rootVec_eq_zero_of_not_isRoot hr, smul_zero, add_zero]

theorem yOp_rootVec_E8 (i : Fin Tag.E8.rank) (c : K) {α : Fin Tag.E8.rank → ℤ}
    (hα : IsRoot Tag.E8 α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    yOp Tag.E8 K i c (rootVec Tag.E8 K α) =
      rootVec Tag.E8 K α + c • rootVec Tag.E8 K (α - Pi.single i 1) := by
  by_cases hr : IsRoot Tag.E8 (α - Pi.single i 1)
  · exact CFSG.TauCetiBridge.Minuscule.yOp_rootVec_of_sub K e8_posDef_cartan i c hα h₁ h₂ hr
  · rw [CFSG.TauCetiBridge.Minuscule.yOp_rootVec_of_not_sub K i c hα h₁ h₂ hr,
      e8_rootVec_eq_zero_of_not_isRoot hr, smul_zero, add_zero]

theorem e8a2Weight_ne_single : ∀ k : Fin 3, ∀ i : Fin 8, (i = 0 ∨ i = 2) →
    e8a2Weight k ≠ Pi.single (e8Index i) 1 ∧ e8a2Weight k ≠ -Pi.single (e8Index i) 1 :=
  Certificates.certificate1952.2.2.1

theorem e8a2Weight_add_single : ∀ k : Fin 3, ∀ i : Fin 8, (i = 0 ∨ i = 2) →
    (∀ m : Fin 240, e8RootVec m ≠ e8a2Weight k + Pi.single (e8Index i) 1) ∨
      ∃ k', e8a2Weight k' = e8a2Weight k + Pi.single (e8Index i) 1 :=
  Certificates.certificate1952.2.2.2.1

theorem e8a2Weight_sub_single : ∀ k : Fin 3, ∀ i : Fin 8, (i = 0 ∨ i = 2) →
    (∀ m : Fin 240, e8RootVec m ≠ e8a2Weight k - Pi.single (e8Index i) 1) ∨
      ∃ k', e8a2Weight k' = e8a2Weight k - Pi.single (e8Index i) 1 :=
  Certificates.certificate1952.2.2.2.2.1

theorem xOp_e8a2Vec {i : Fin Tag.E8.rank} (hi : i ∈ e8support13) (c : K) (k : Fin 3) :
    xOp Tag.E8 K i c (e8a2Vec K k) =
      e8a2Vec K k + c • rootVec Tag.E8 K (e8a2Weight k + Pi.single i 1) := by
  rw [← rootVec_e8a2Weight]
  exact xOp_rootVec_E8 i c (isRoot_e8a2Weight k)
    (e8a2Weight_ne_single k i ((mem_e8support13 i).1 hi)).1
    (e8a2Weight_ne_single k i ((mem_e8support13 i).1 hi)).2

theorem yOp_e8a2Vec {i : Fin Tag.E8.rank} (hi : i ∈ e8support13) (c : K) (k : Fin 3) :
    yOp Tag.E8 K i c (e8a2Vec K k) =
      e8a2Vec K k + c • rootVec Tag.E8 K (e8a2Weight k - Pi.single i 1) := by
  rw [← rootVec_e8a2Weight]
  exact yOp_rootVec_E8 i c (isRoot_e8a2Weight k)
    (e8a2Weight_ne_single k i ((mem_e8support13 i).1 hi)).1
    (e8a2Weight_ne_single k i ((mem_e8support13 i).1 hi)).2

theorem mem_e8a2Module_of_mem {g : ModGL Tag.E8 K}
    (hg : g ∈ subsystemGroup Tag.E8 K e8support13)
    {m : RootModule Tag.E8 K} (hm : m ∈ e8a2Module K) :
    (g : Module.End K (RootModule Tag.E8 K)) m ∈ e8a2Module K := by
  refine mem_of_mem_subsystemGroup_of_invariant (fun i hi c v hv => ?_)
    (fun i hi c v hv => ?_) hg m hm
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [xOp_e8a2Vec hi]
      exact add_mem (e8a2Vec_mem k) (Submodule.smul_mem _ _
        (rootVec_mem_e8a2Module (e8a2Weight_add_single k i ((mem_e8support13 i).1 hi))))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [yOp_e8a2Vec hi]
      exact add_mem (e8a2Vec_mem k) (Submodule.smul_mem _ _
        (rootVec_mem_e8a2Module (e8a2Weight_sub_single k i ((mem_e8support13 i).1 hi))))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

@[expose] def e8a2Mat (g : ModGL Tag.E8 K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => (g : Module.End K (RootModule Tag.E8 K)) (e8a2Vec K j) (e8a2Label i)

theorem apply_e8a2Vec {g : ModGL Tag.E8 K} (hg : g ∈ subsystemGroup Tag.E8 K e8support13)
    (j : Fin 3) :
    (g : Module.End K (RootModule Tag.E8 K)) (e8a2Vec K j) = ∑ i, e8a2Mat g i j • e8a2Vec K i :=
  eq_sum_of_mem_e8a2Module (mem_e8a2Module_of_mem hg (e8a2Vec_mem j))

theorem e8a2Mat_one : e8a2Mat (1 : ModGL Tag.E8 K) = 1 := by
  ext i j
  rw [e8a2Mat, Matrix.of_apply, Units.val_one, Module.End.one_apply, e8a2Vec_apply,
    Matrix.one_apply]

theorem e8a2Mat_mul {g h : ModGL Tag.E8 K} (_hg : g ∈ subsystemGroup Tag.E8 K e8support13)
    (hh : h ∈ subsystemGroup Tag.E8 K e8support13) :
    e8a2Mat (g * h) = e8a2Mat g * e8a2Mat h := by
  ext i j
  rw [e8a2Mat, Matrix.of_apply, Units.val_mul, Module.End.mul_apply, apply_e8a2Vec hh, map_sum,
    Finsupp.finsetSum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  rfl

theorem e8a2Mat_xUnit {i₀ : Fin 8} (hi : e8Index i₀ ∈ e8support13) {p q : Fin 3}
    (hpq : ∀ i j : Fin 3, e8a2Weight j + Pi.single (e8Index i₀) 1 = e8a2Weight i ↔
      (i = p ∧ j = q))
    (t : K) : e8a2Mat (xUnit Tag.E8 K (e8Index i₀) t) = 1 + single p q t := by
  ext i j
  rw [e8a2Mat, Matrix.of_apply, coe_xUnit, xOp_e8a2Vec hi, Finsupp.add_apply, Finsupp.smul_apply,
    rootVec_apply_e8a2Label, e8a2Vec_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  have key := hpq i j
  by_cases h : e8a2Weight j + Pi.single (e8Index i₀) 1 = e8a2Weight i
  · obtain ⟨rfl, rfl⟩ := key.1 h
    simp [h]
  · have h' : ¬(p = i ∧ q = j) := fun e => h (key.2 ⟨e.1.symm, e.2.symm⟩)
    simp [h, h']

theorem e8a2Mat_yUnit {i₀ : Fin 8} (hi : e8Index i₀ ∈ e8support13) {p q : Fin 3}
    (hpq : ∀ i j : Fin 3, e8a2Weight j - Pi.single (e8Index i₀) 1 = e8a2Weight i ↔
      (i = p ∧ j = q))
    (t : K) : e8a2Mat (yUnit Tag.E8 K (e8Index i₀) t) = 1 + single p q t := by
  ext i j
  rw [e8a2Mat, Matrix.of_apply, coe_yUnit, yOp_e8a2Vec hi, Finsupp.add_apply, Finsupp.smul_apply,
    rootVec_apply_e8a2Label, e8a2Vec_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  have key := hpq i j
  by_cases h : e8a2Weight j - Pi.single (e8Index i₀) 1 = e8a2Weight i
  · obtain ⟨rfl, rfl⟩ := key.1 h
    simp [h]
  · have h' : ¬(p = i ∧ q = j) := fun e => h (key.2 ⟨e.1.symm, e.2.symm⟩)
    simp [h, h']

theorem e8a2Mat_x1 (t : K) : e8a2Mat (xUnit Tag.E8 K (e8Index 0) t) = 1 + single 0 1 t :=
  e8a2Mat_xUnit mem_e8support13_0 (Certificates.certificate1952.2.2.2.2.2.1) t

theorem e8a2Mat_y1 (t : K) : e8a2Mat (yUnit Tag.E8 K (e8Index 0) t) = 1 + single 1 0 t :=
  e8a2Mat_yUnit mem_e8support13_0 (Certificates.certificate1952.2.2.2.2.2.2.1) t

theorem e8a2Mat_x3 (t : K) : e8a2Mat (xUnit Tag.E8 K (e8Index 2) t) = 1 + single 1 2 t :=
  e8a2Mat_xUnit mem_e8support13_2 (Certificates.certificate1952.2.2.2.2.2.2.2.1) t

theorem e8a2Mat_y3 (t : K) : e8a2Mat (yUnit Tag.E8 K (e8Index 2) t) = 1 + single 2 1 t :=
  e8a2Mat_yUnit mem_e8support13_2 (Certificates.certificate1952.2.2.2.2.2.2.2.2.1) t

theorem e8a2Weight_pairing : ∀ k : Fin 3,
    (∑ j, Tag.E8.cartan (e8Index 0) j * e8a2Weight k j) = (![1, -1, 0] : Fin 3 → ℤ) k ∧
    (∑ j, Tag.E8.cartan (e8Index 2) j * e8a2Weight k j) = (![0, 1, -1] : Fin 3 → ℤ) k :=
  Certificates.certificate1952.2.2.2.2.2.2.2.2.2.1

theorem e8a2Mat_torusElt (i : Fin Tag.E8.rank) (a : Kˣ) :
    e8a2Mat (torusElt Tag.E8 K i a) = Matrix.diagonal fun k =>
      ((a ^ (∑ j, Tag.E8.cartan i j * e8a2Weight k j) : Kˣ) : K) := by
  ext p q
  rw [e8a2Mat, Matrix.of_apply, ← rootVec_e8a2Weight, torusElt_rootVec i a (isRoot_e8a2Weight q),
    rootVec_e8a2Weight, Finsupp.smul_apply, e8a2Vec_apply, Matrix.diagonal_apply]
  by_cases h : p = q
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, smul_eq_mul, mul_one]
  · rw [ite_eq_right h, ite_eq_right h, smul_zero]

theorem torusElt_mem_e8a2Group {i : Fin Tag.E8.rank} (hi : i ∈ e8support13) (a : Kˣ) :
    torusElt Tag.E8 K i a ∈ subsystemGroup Tag.E8 K e8support13 :=
  subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hi a)

@[expose] def e8a2TorusElt (a b : Kˣ) : ModGL Tag.E8 K :=
  torusElt Tag.E8 K (e8Index 0) a * torusElt Tag.E8 K (e8Index 2) b

theorem e8a2TorusElt_mem (a b : Kˣ) :
    e8a2TorusElt a b ∈ subsystemGroup Tag.E8 K e8support13 :=
  mul_mem (torusElt_mem_e8a2Group mem_e8support13_0 a) (torusElt_mem_e8a2Group mem_e8support13_2 b)

theorem e8a2Mat_e8a2TorusElt (a b : Kˣ) :
    e8a2Mat (e8a2TorusElt a b) =
      Matrix.diagonal ![(a : K), ((a⁻¹ * b : Kˣ) : K), ((b⁻¹ : Kˣ) : K)] := by
  rw [e8a2TorusElt, e8a2Mat_mul (torusElt_mem_e8a2Group mem_e8support13_0 a)
      (torusElt_mem_e8a2Group mem_e8support13_2 b), e8a2Mat_torusElt, e8a2Mat_torusElt,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  obtain ⟨h0, h2⟩ := e8a2Weight_pairing k
  rw [h0, h2]
  fin_cases k <;> simp [Units.val_mul, _root_.zpow_neg]

theorem det_e8a2Mat {g : ModGL Tag.E8 K} (hg : g ∈ subsystemGroup Tag.E8 K e8support13) :
    (e8a2Mat g).det = 1 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rcases (mem_e8support13 i).1 hi with rfl | rfl
      · rw [e8a2Mat_x1]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [e8a2Mat_x3]; exact det_transvection_of_ne _ _ (by decide) _
    · rcases (mem_e8support13 i).1 hi with rfl | rfl
      · rw [e8a2Mat_y1]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [e8a2Mat_y3]; exact det_transvection_of_ne _ _ (by decide) _
  | one => rw [e8a2Mat_one, det_one]
  | mul x y hx hy ihx ihy => rw [e8a2Mat_mul hx hy, det_mul, ihx, ihy, mul_one]
  | inv x hx ih =>
    have h := e8a2Mat_mul (inv_mem hx) hx
    rw [inv_mul_cancel, e8a2Mat_one] at h
    have h' := congrArg Matrix.det h
    rw [det_one, det_mul, ih, mul_one] at h'
    exact h'.symm

variable (K) in
@[expose] def e8a2Rep :
    subsystemGroup Tag.E8 K e8support13 →* SpecialLinearGroup (Fin 3) K where
  toFun g := ⟨e8a2Mat (g : ModGL Tag.E8 K), det_e8a2Mat g.2⟩
  map_one' := Subtype.ext e8a2Mat_one
  map_mul' g h := Subtype.ext (e8a2Mat_mul g.2 h.2)

theorem coe_e8a2Rep (g : subsystemGroup Tag.E8 K e8support13) :
    ((e8a2Rep K g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      e8a2Mat (g : ModGL Tag.E8 K) :=
  rfl

theorem e8a2Mat_inv {g : ModGL Tag.E8 K} (hg : g ∈ subsystemGroup Tag.E8 K e8support13) :
    e8a2Mat g⁻¹ = (e8a2Mat g)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← e8a2Mat_mul hg (inv_mem hg), mul_inv_cancel, e8a2Mat_one]

theorem e8chainRoot13_mem : ∀ k l : Fin 3, k ≠ l → ∃ m : Fin 240,
    e8RootVec m = chainRoot e8chain13 k l ∧
      ∀ i, ¬(i = e8Index 0 ∨ i = e8Index 2) → e8RootVec m i = 0 :=
  Certificates.certificate1952.2.2.2.2.2.2.2.2.2.2.1

theorem e8chainRoot13_mem_parabolicRoots {k l : Fin 3} (hkl : k ≠ l) :
    chainRoot e8chain13 k l ∈ parabolicRoots Tag.E8 e8support13 := by
  obtain ⟨m, hm, hs⟩ := e8chainRoot13_mem k l hkl
  rw [← hm]
  exact ⟨isRoot_e8RootVec m, fun i hi => hs i ((mem_e8support13 i).not.1 hi)⟩

theorem exists_e8chainRoot13_of_support13 : ∀ m : Fin 240,
    (∀ i, ¬(i = e8Index 0 ∨ i = e8Index 2) → e8RootVec m i = 0) →
      ∃ k l : Fin 3, k ≠ l ∧ chainRoot e8chain13 k l = e8RootVec m :=
  Certificates.certificate1952.2.2.2.2.2.2.2.2.2.2.2.1

theorem exists_e8chainRoot13_of_mem {α : Fin Tag.E8.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E8 e8support13) :
    ∃ k l : Fin 3, k ≠ l ∧ chainRoot e8chain13 k l = α := by
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hα.1
  exact exists_e8chainRoot13_of_support13 m fun i hi => hα.2 i ((mem_e8support13 i).not.2 hi)

theorem e8chainRoot13_eq_sub :
    ∀ i j : Fin 3, chainRoot e8chain13 i j = e8a2Weight i - e8a2Weight j :=
  Certificates.certificate1952.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem pinnedX_mem_e8a2Group {α : Fin Tag.E8.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E8 e8support13) (t : K) :
    pinnedX Tag.E8 K α t ∈ subsystemGroup Tag.E8 K e8support13 :=
  rootSubgroup_le_subsystemGroup hα (mem_rootSubgroup.2 ⟨t, rfl⟩)

variable (K) in
@[expose] def E8A2RootFamily (i j : Fin 3) : Prop :=
  ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ t : K,
    e8a2Mat (pinnedX Tag.E8 K (chainRoot e8chain13 i j) t) = 1 + single i j ((ε : K) * t)

theorem e8a2RootFamily_of_eq {i j : Fin 3} {g : K → ModGL Tag.E8 K}
    (hg : ∀ t, pinnedX Tag.E8 K (chainRoot e8chain13 i j) t = g t)
    (h : ∀ t, e8a2Mat (g t) = 1 + single i j t) : E8A2RootFamily K i j :=
  ⟨1, Or.inl rfl, fun t => by rw [hg, h, Int.cast_one, one_mul]⟩

theorem e8a2RootFamily_comp {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hsum : chainRoot e8chain13 i j + chainRoot e8chain13 j k = chainRoot e8chain13 i k)
    (hne : chainRoot e8chain13 i j ≠ chainRoot e8chain13 j k)
    (hne' : chainRoot e8chain13 i j ≠ -chainRoot e8chain13 j k)
    (h₁ : E8A2RootFamily K i j) (h₂ : E8A2RootFamily K j k) : E8A2RootFamily K i k := by
  obtain ⟨ε₁, hε₁, h₁⟩ := h₁
  obtain ⟨ε₂, hε₂, h₂⟩ := h₂
  have hα := e8chainRoot13_mem_parabolicRoots hij
  have hβ := e8chainRoot13_mem_parabolicRoots hjk
  have hγ := e8chainRoot13_mem_parabolicRoots hik
  obtain ⟨hC, hcomm⟩ := (simply_laced_root_commutator_unit Tag.E8
    (Or.inr (Or.inr (Or.inr rfl))) hα.1 hβ.1 hne hne').1 (hsum ▸ hγ.1)
  set C := commConst Tag.E8 (chainRoot e8chain13 i j) (chainRoot e8chain13 j k) (1, 1)
  have hCC : (C : K) * C = 1 := by rcases hC with h | h <;> rw [h] <;> norm_num
  refine ⟨ε₁ * ε₂ * C, ?_, fun t => ?_⟩
  · rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl <;> rcases hC with h | h <;>
      simp [h]
  have e : pinnedX Tag.E8 K (chainRoot e8chain13 i k) t =
      ⁅pinnedX Tag.E8 K (chainRoot e8chain13 i j) 1,
        pinnedX Tag.E8 K (chainRoot e8chain13 j k) ((C : K) * t)⁆ := by
    rw [hcomm K 1 ((C : K) * t), hsum]
    congr 1
    rw [mul_one, ← mul_assoc, hCC, one_mul]
  have m1 := pinnedX_mem_e8a2Group hα (1 : K)
  have m2 := pinnedX_mem_e8a2Group hβ ((C : K) * t)
  rw [e, commutatorElement_def, e8a2Mat_mul (mul_mem (mul_mem m1 m2) (inv_mem m1)) (inv_mem m2),
    e8a2Mat_mul (mul_mem m1 m2) (inv_mem m1), e8a2Mat_mul m1 m2, e8a2Mat_inv m1, e8a2Mat_inv m2,
    h₁, h₂, CFSG.LinearGroups.elementary_three_index_commutator hik hij hjk.symm]
  congr 2
  push_cast
  ring

theorem e8chainRoot13_values :
    chainRoot e8chain13 0 1 = Pi.single (e8Index 0) 1 ∧
    chainRoot e8chain13 1 2 = Pi.single (e8Index 2) 1 ∧
    chainRoot e8chain13 1 0 = -Pi.single (e8Index 0) 1 ∧
    chainRoot e8chain13 2 1 = -Pi.single (e8Index 2) 1 :=
  Certificates.certificate1952.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem e8chainRoot13_sums :
    (chainRoot e8chain13 0 1 + chainRoot e8chain13 1 2 = chainRoot e8chain13 0 2 ∧
      chainRoot e8chain13 0 1 ≠ chainRoot e8chain13 1 2 ∧
      chainRoot e8chain13 0 1 ≠ -chainRoot e8chain13 1 2) ∧
    (chainRoot e8chain13 2 1 + chainRoot e8chain13 1 0 = chainRoot e8chain13 2 0 ∧
      chainRoot e8chain13 2 1 ≠ chainRoot e8chain13 1 0 ∧
      chainRoot e8chain13 2 1 ≠ -chainRoot e8chain13 1 0) :=
  Certificates.certificate1952.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem e8a2RootFamily_all : ∀ i j : Fin 3, i ≠ j → E8A2RootFamily K i j := by
  obtain ⟨c01, c12, c10, c21⟩ := e8chainRoot13_values
  obtain ⟨s02, s20⟩ := e8chainRoot13_sums
  have f01 : E8A2RootFamily K 0 1 := e8a2RootFamily_of_eq
    (fun t => by rw [c01, pinnedX_single]) e8a2Mat_x1
  have f12 : E8A2RootFamily K 1 2 := e8a2RootFamily_of_eq
    (fun t => by rw [c12, pinnedX_single]) e8a2Mat_x3
  have f10 : E8A2RootFamily K 1 0 := e8a2RootFamily_of_eq
    (fun t => by rw [c10, pinnedX_neg_single]) e8a2Mat_y1
  have f21 : E8A2RootFamily K 2 1 := e8a2RootFamily_of_eq
    (fun t => by rw [c21, pinnedX_neg_single]) e8a2Mat_y3
  have f02 := e8a2RootFamily_comp (by decide) (by decide) (by decide) s02.1 s02.2.1 s02.2.2 f01
    f12
  have f20 := e8a2RootFamily_comp (by decide) (by decide) (by decide) s20.1 s20.2.1 s20.2.2 f21
    f10
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

theorem e8a2Rep_surjective : Function.Surjective (e8a2Rep K) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← CFSG.LinearGroups.special_linear_elementary_generation, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  obtain ⟨ε, hε, h⟩ := e8a2RootFamily_all (K := K) i j hij
  have hmem := pinnedX_mem_e8a2Group (e8chainRoot13_mem_parabolicRoots hij) ((ε : K) * c)
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  rw [coe_e8a2Rep, h, CFSG.LinearGroups.coe_transvection]
  congr 1
  rcases hε with rfl | rfl <;> simp

end CFSG.RankThree.PartOne.KE

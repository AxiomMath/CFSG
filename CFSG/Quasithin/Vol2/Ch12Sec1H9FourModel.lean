module

public import Certificates.Data.H9Four
public import CFSG.Quasithin.Vol2.Ch12Sec1H9Conj

public section

namespace CFSG.Quasithin.H13.H9Four

open CFSG.Open CFSG.Quasithin.E3
open scoped Matrix

theorem Mat.toMatrix_ofMatrix (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    (Mat.ofMatrix M).toMatrix = M := by
  ext i j
  simp [Mat.toMatrix, Mat.ofMatrix]

theorem Mat.toMatrix_mul (v w : Mat) : (Mat.mul v w).toMatrix = v.toMatrix * w.toMatrix :=
  Mat.toMatrix_ofMatrix _

theorem Mat.toMatrix_tr (v : Mat) : (Mat.tr v).toMatrix = v.toMatrixᵀ :=
  Mat.toMatrix_ofMatrix _

theorem Mat.toMatrix_one : Mat.one.toMatrix = 1 :=
  Mat.toMatrix_ofMatrix _

theorem Mat.toMatrix_injective : Function.Injective Mat.toMatrix := by
  intro v w h
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have h1 := congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩
  simpa [Mat.toMatrix] using h1

theorem mul_mul_cancel {B B' X : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : B * B' = 1) :
    B * (B' * X) = X := by
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]

theorem Elt.valid_iff (e : Elt) :
    e.valid = true ↔ e.a.toMatrix * e.ai.toMatrix = 1 ∧ e.ai.toMatrix * e.a.toMatrix = 1 := by
  simp [Elt.valid]

theorem Elt.act_mul (e f : Elt) (w : Pt) : (e.mul f).act w = e.act (f.act w) := by
  cases he : e.b <;> cases hf : f.b <;>
    simp [Elt.act, Elt.mul, he, hf, Mat.app, Mat.toMatrix_mul, Mat.toMatrix_tr,
      Matrix.mulVec_mulVec, Matrix.transpose_mul] <;> rfl

theorem Elt.valid_mul {e f : Elt} (he : e.valid = true) (hf : f.valid = true) :
    (e.mul f).valid = true := by
  rw [Elt.valid_iff] at he hf ⊢
  obtain ⟨he1, he2⟩ := he
  obtain ⟨hf1, hf2⟩ := hf
  have hf1' : f.ai.toMatrixᵀ * f.a.toMatrixᵀ = 1 := by
    rw [← Matrix.transpose_mul, hf1, Matrix.transpose_one]
  have hf2' : f.a.toMatrixᵀ * f.ai.toMatrixᵀ = 1 := by
    rw [← Matrix.transpose_mul, hf2, Matrix.transpose_one]
  cases hb : e.b
  · simp only [Elt.mul, hb, Bool.false_eq_true, ite_false, Mat.toMatrix_mul]
    constructor
    · rw [Matrix.mul_assoc, mul_mul_cancel hf1, he1]
    · rw [Matrix.mul_assoc, mul_mul_cancel he2, hf2]
  · simp only [Elt.mul, hb, ite_true, Mat.toMatrix_mul, Mat.toMatrix_tr]
    constructor
    · rw [Matrix.mul_assoc, mul_mul_cancel hf1', he1]
    · rw [Matrix.mul_assoc, mul_mul_cancel he2, hf2']

theorem Elt.valid_one : Elt.one.valid = true := by
  rw [Elt.valid_iff]
  simp [Elt.one, Mat.toMatrix_one]

theorem Elt.act_one (w : Pt) : Elt.one.act w = w := by
  simp [Elt.act, Elt.one, Mat.app, Mat.toMatrix_one, Mat.toMatrix_tr]
  rfl

theorem Elt.act_injective {e f : Elt} (he : e.valid = true) (hf : f.valid = true)
    (h : ∀ w : Pt, e.act w = f.act w) : e = f := by
  rw [Elt.valid_iff] at he hf
  have hcol : ∀ (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (j : Fin 4),
      A *ᵥ Pi.single j 1 = fun i => A i j := fun A j => by
    ext i
    simp [Matrix.mulVec_single]
  have hA0 : ∀ (A A' : Matrix (Fin 4) (Fin 4) (ZMod 2)), A' * A = 1 →
      ¬ ∀ x : Fin 4 → ZMod 2, A *ᵥ x = 0 := fun A A' hA hz => by
    have h1 := hz (Pi.single 0 1)
    have h2 := congrArg (fun v => A' *ᵥ v) h1
    simp only [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    have h3 := congrFun h2 0
    simp at h3
  have hbb : e.b = f.b := by
    by_contra hne
    have key : ∀ E F : Elt, E.b = false → F.b = true → (∀ w, E.act w = F.act w) →
        E.ai.toMatrix * E.a.toMatrix = 1 → False := by
      intro E F hE hF hEF hinv
      apply hA0 E.a.toMatrix E.ai.toMatrix hinv
      intro x
      have h1 := congrArg (fun w : Pt => Multiplicative.toAdd w.1)
        (hEF (Multiplicative.ofAdd x, 1))
      simpa [Elt.act, hE, hF, Mat.app] using h1
    cases hb : e.b <;> cases hf' : f.b
    · exact hne (by rw [hb, hf'])
    · exact key e f hb hf' h he.2
    · exact key f e hf' hb (fun w => (h w).symm) hf.2
    · exact hne (by rw [hb, hf'])
  have hA : e.a.toMatrix = f.a.toMatrix := by
    ext i j
    have h1 : ∀ x : Fin 4 → ZMod 2, e.a.toMatrix *ᵥ x = f.a.toMatrix *ᵥ x := by
      intro x
      cases hb : e.b
      · have h2 := congrArg (fun w : Pt => Multiplicative.toAdd w.1)
          (h (Multiplicative.ofAdd x, 1))
        rw [hbb] at hb
        simpa [Elt.act, hb, hbb, Mat.app] using h2
      · have h2 := congrArg (fun w : Pt => Multiplicative.toAdd w.1)
          (h (1, Multiplicative.ofAdd x))
        rw [hbb] at hb
        simpa [Elt.act, hb, hbb, Mat.app] using h2
    have h2 := congrFun (h1 (Pi.single j 1)) i
    rw [hcol, hcol] at h2
    exact h2
  have hAi : e.ai.toMatrix = f.ai.toMatrix := by
    calc e.ai.toMatrix = e.ai.toMatrix * (f.a.toMatrix * f.ai.toMatrix) := by
          rw [hf.1, Matrix.mul_one]
      _ = (e.ai.toMatrix * e.a.toMatrix) * f.ai.toMatrix := by rw [hA, Matrix.mul_assoc]
      _ = f.ai.toMatrix := by rw [he.2, Matrix.one_mul]
  cases e
  cases f
  simp only at hbb hA hAi
  rw [Mat.toMatrix_injective hA, Mat.toMatrix_injective hAi, hbb]

theorem Elt.valid_inv {e : Elt} (he : e.valid = true) : e.inv.valid = true := by
  rw [Elt.valid_iff] at he ⊢
  obtain ⟨he1, he2⟩ := he
  cases hb : e.b
  · simp only [Elt.inv, hb, Bool.false_eq_true, ite_false]
    exact ⟨he2, he1⟩
  · simp only [Elt.inv, hb, ite_true, Mat.toMatrix_tr]
    exact ⟨by rw [← Matrix.transpose_mul, he2, Matrix.transpose_one],
      by rw [← Matrix.transpose_mul, he1, Matrix.transpose_one]⟩

theorem Elt.act_inv_act {e : Elt} (he : e.valid = true) (w : Pt) :
    e.inv.act (e.act w) = w := by
  rw [Elt.valid_iff] at he
  obtain ⟨he1, he2⟩ := he
  have he1' : e.ai.toMatrixᵀ * e.a.toMatrixᵀ = 1 := by
    rw [← Matrix.transpose_mul, he1, Matrix.transpose_one]
  have he2' : e.a.toMatrixᵀ * e.ai.toMatrixᵀ = 1 := by
    rw [← Matrix.transpose_mul, he2, Matrix.transpose_one]
  cases hb : e.b <;>
    simp [Elt.act, Elt.inv, hb, Mat.app, Mat.toMatrix_tr, Matrix.mulVec_mulVec, he2, he2'] <;> rfl

theorem Elt.act_act_inv {e : Elt} (he : e.valid = true) (w : Pt) : e.act (e.inv.act w) = w := by
  rw [Elt.valid_iff] at he
  obtain ⟨he1, he2⟩ := he
  have he1' : e.ai.toMatrixᵀ * e.a.toMatrixᵀ = 1 := by
    rw [← Matrix.transpose_mul, he1, Matrix.transpose_one]
  cases hb : e.b <;>
    simp [Elt.act, Elt.inv, hb, Mat.app, Mat.toMatrix_tr, Matrix.mulVec_mulVec, he1, he1'] <;> rfl

theorem Mat.app_mul (v : Mat) (a b : Multiplicative (Fin 4 → ZMod 2)) :
    v.app (a * b) = v.app a * v.app b := by
  simp only [Mat.app, toAdd_mul, Matrix.mulVec_add, ofAdd_add]

theorem Elt.act_mulPt (e : Elt) (x y : Pt) : e.act (x * y) = e.act x * e.act y := by
  cases hb : e.b
  · simp only [Elt.act, hb, Bool.false_eq_true]
    exact Prod.ext (Mat.app_mul _ _ _) (Mat.app_mul _ _ _)
  · simp only [Elt.act, hb]
    exact Prod.ext (Mat.app_mul _ _ _) (Mat.app_mul _ _ _)

@[expose] def Elt.sem (e : Elt) : MulAut Pt :=
  if he : e.valid = true then
    { toFun := e.act
      invFun := e.inv.act
      left_inv := Elt.act_inv_act he
      right_inv := Elt.act_act_inv he
      map_mul' := e.act_mulPt }
  else 1

theorem Elt.sem_apply {e : Elt} (he : e.valid = true) (w : Pt) : e.sem w = e.act w := by
  simp only [Elt.sem, he, ↓reduceDIte]
  rfl

theorem Elt.sem_mul {e f : Elt} (he : e.valid = true) (hf : f.valid = true) :
    (e.mul f).sem = e.sem * f.sem :=
  MulEquiv.ext fun w => by
    rw [MulAut.mul_apply, Elt.sem_apply (Elt.valid_mul he hf), Elt.sem_apply he,
      Elt.sem_apply hf, Elt.act_mul]

theorem Elt.sem_one : Elt.one.sem = 1 :=
  MulEquiv.ext fun w => by rw [Elt.sem_apply Elt.valid_one, Elt.act_one]; rfl

theorem Elt.sem_inv {e : Elt} (he : e.valid = true) : e.inv.sem = e.sem⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  refine MulEquiv.ext fun w => ?_
  rw [MulAut.mul_apply, Elt.sem_apply (Elt.valid_inv he), Elt.sem_apply he, Elt.act_inv_act he]
  rfl

theorem Elt.sem_injective {e f : Elt} (he : e.valid = true) (hf : f.valid = true)
    (h : e.sem = f.sem) : e = f :=
  Elt.act_injective he hf fun w => by rw [← Elt.sem_apply he, ← Elt.sem_apply hf, h]

@[expose] def modelM4 : Subgroup (MulAut Pt) where
  carrier := {x | ∃ e : Elt, e.valid = true ∧ e.sem = x}
  mul_mem' := fun ⟨e, he, h1⟩ ⟨f, hf, h2⟩ =>
    ⟨e.mul f, Elt.valid_mul he hf, by rw [Elt.sem_mul he hf, h1, h2]⟩
  one_mem' := ⟨Elt.one, Elt.valid_one, Elt.sem_one⟩
  inv_mem' := fun ⟨e, he, h1⟩ => ⟨e.inv, Elt.valid_inv he, by rw [Elt.sem_inv he, h1]⟩

theorem Elt.sem_mem {e : Elt} (he : e.valid = true) : e.sem ∈ modelM4 := ⟨e, he, rfl⟩

@[expose] def semSet (gs : List Elt) : Set (MulAut (Pt)) := {x | ∃ g ∈ gs, g.sem = x}

@[expose] noncomputable def sub (gs : List Elt) : Subgroup (MulAut (Pt)) :=
  Subgroup.closure (semSet gs)

theorem sub_le_modelM4 {gs : List Elt} (hv : ∀ g ∈ gs, g.valid = true) : sub gs ≤ modelM4 :=
  (Subgroup.closure_le _).mpr fun _ ⟨g, hg, h⟩ => h ▸ Elt.sem_mem (hv g hg)

theorem elems_cons (g : Elt) (gs : List Elt) :
    elems (g :: gs) = elems gs ++ (elems gs).map (Elt.mul g) := rfl

theorem one_mem_elems (gs : List Elt) : Elt.one ∈ elems gs := by
  induction gs with
  | nil => simp [elems]
  | cons g gs ih =>
    rw [elems_cons]
    exact List.mem_append_left _ ih

theorem valid_of_mem_elems {gs : List Elt} (hv : ∀ g ∈ gs, g.valid = true) :
    ∀ e ∈ elems gs, e.valid = true := by
  induction gs with
  | nil =>
    intro e he
    simp only [elems, List.mem_singleton] at he
    rw [he]
    exact Elt.valid_one
  | cons g gs ih =>
    intro e he
    have hv' : ∀ g' ∈ gs, g'.valid = true := fun g' hg' => hv g' (List.mem_cons_of_mem _ hg')
    rw [elems_cons, List.mem_append, List.mem_map] at he
    rcases he with he | ⟨e', he', rfl⟩
    · exact ih hv' e he
    · exact Elt.valid_mul (hv g List.mem_cons_self) (ih hv' e' he')

theorem mem_sub_iff {gs : List Elt} (hv : ∀ g ∈ gs, g.valid = true)
    (hinv : ∀ g ∈ gs, g.sem * g.sem = 1)
    (hcomm : ∀ g ∈ gs, ∀ h ∈ gs, g.sem * h.sem = h.sem * g.sem) (x : MulAut (Pt)) :
    x ∈ sub gs ↔ ∃ e ∈ elems gs, e.sem = x := by
  induction gs generalizing x with
  | nil =>
    have h0 : semSet [] = ∅ := by
      ext y
      simp [semSet]
    simp only [sub, h0, Subgroup.closure_empty, Subgroup.mem_bot, elems, List.mem_singleton,
      exists_eq_left, Elt.sem_one]
    exact eq_comm
  | cons g gs ih =>
    have hv' : ∀ g' ∈ gs, g'.valid = true := fun g' hg' => hv g' (List.mem_cons_of_mem _ hg')
    have hinv' : ∀ g' ∈ gs, g'.sem * g'.sem = 1 := fun g' hg' =>
      hinv g' (List.mem_cons_of_mem _ hg')
    have hcomm' : ∀ g' ∈ gs, ∀ h ∈ gs, g'.sem * h.sem = h.sem * g'.sem := fun g' hg' h hh =>
      hcomm g' (List.mem_cons_of_mem _ hg') h (List.mem_cons_of_mem _ hh)
    have ih' := ih hv' hinv' hcomm'
    have hg := hv g List.mem_cons_self
    have hsub : sub gs ≤ sub (g :: gs) :=
      Subgroup.closure_mono fun _ ⟨g', hg', h⟩ => ⟨g', List.mem_cons_of_mem _ hg', h⟩
    have hgmem : g.sem ∈ sub (g :: gs) := Subgroup.subset_closure ⟨g, List.mem_cons_self, rfl⟩
    have hgH : ∀ a ∈ sub gs, g.sem * a = a * g.sem := by
      intro a ha
      have hle : sub gs ≤ Subgroup.centralizer {g.sem} := by
        refine (Subgroup.closure_le _).mpr ?_
        rintro _ ⟨g', hg', rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm g List.mem_cons_self g' (List.mem_cons_of_mem _ hg')).symm
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle ha)).symm
    have hg2 : g.sem * g.sem = 1 := hinv g List.mem_cons_self
    have hginv : g.sem⁻¹ = g.sem := inv_eq_of_mul_eq_one_right hg2
    constructor
    · intro hx
      have key : ∃ a ∈ sub gs, x = a ∨ x = g.sem * a := by
        induction hx using Subgroup.closure_induction with
        | mem y hy =>
          obtain ⟨g', hg', rfl⟩ := hy
          rcases List.mem_cons.mp hg' with rfl | hg'
          · exact ⟨1, Subgroup.one_mem _, Or.inr (mul_one _).symm⟩
          · exact ⟨g'.sem, Subgroup.subset_closure ⟨g', hg', rfl⟩, Or.inl rfl⟩
        | one => exact ⟨1, Subgroup.one_mem _, Or.inl rfl⟩
        | mul y z _ _ hy hz =>
          obtain ⟨a, ha, hya⟩ := hy
          obtain ⟨b, hb, hzb⟩ := hz
          rcases hya with hya | hya <;> rcases hzb with hzb | hzb <;> rw [hya, hzb]
          · exact ⟨a * b, Subgroup.mul_mem _ ha hb, Or.inl rfl⟩
          · refine ⟨a * b, Subgroup.mul_mem _ ha hb, Or.inr ?_⟩
            rw [← mul_assoc, ← hgH a ha, mul_assoc]
          · exact ⟨a * b, Subgroup.mul_mem _ ha hb, Or.inr (mul_assoc _ _ _)⟩
          · refine ⟨a * b, Subgroup.mul_mem _ ha hb, Or.inl ?_⟩
            rw [mul_assoc, ← mul_assoc a, ← hgH a ha, ← mul_assoc, ← mul_assoc, hg2, one_mul]
        | inv y _ hy =>
          obtain ⟨a, ha, hya⟩ := hy
          rcases hya with hya | hya <;> rw [hya]
          · exact ⟨a⁻¹, Subgroup.inv_mem _ ha, Or.inl rfl⟩
          · refine ⟨a⁻¹, Subgroup.inv_mem _ ha, Or.inr ?_⟩
            rw [_root_.mul_inv_rev, hginv, ← hgH a⁻¹ (Subgroup.inv_mem _ ha)]
      obtain ⟨a, ha, hxa⟩ := key
      obtain ⟨e, he, hea⟩ := (ih' a).mp ha
      rcases hxa with hxa | hxa
      · exact ⟨e, by rw [elems_cons]; exact List.mem_append_left _ he, by rw [hxa, hea]⟩
      · refine ⟨g.mul e, ?_, by rw [hxa, Elt.sem_mul hg (valid_of_mem_elems hv' e he), hea]⟩
        rw [elems_cons]
        exact List.mem_append_right _ (List.mem_map_of_mem he)
    · rintro ⟨e, he, rfl⟩
      rw [elems_cons, List.mem_append, List.mem_map] at he
      rcases he with he | ⟨e', he', rfl⟩
      · exact hsub ((ih' _).mpr ⟨e, he, rfl⟩)
      · rw [Elt.sem_mul hg (valid_of_mem_elems hv' e' he')]
        exact Subgroup.mul_mem _ hgmem (hsub ((ih' _).mpr ⟨e', he', rfl⟩))

theorem card_sub {gs : List Elt} (hv : ∀ g ∈ gs, g.valid = true)
    (hinv : ∀ g ∈ gs, g.sem * g.sem = 1)
    (hcomm : ∀ g ∈ gs, ∀ h ∈ gs, g.sem * h.sem = h.sem * g.sem) (hnd : (elems gs).Nodup) :
    Nat.card (sub gs) = (elems gs).length := by
  have hval := valid_of_mem_elems hv
  have h1 : ((sub gs : Subgroup (MulAut (Pt))) : Set (MulAut (Pt))) =
      Elt.sem '' {e | e ∈ elems gs} := by
    ext x
    rw [SetLike.mem_coe, mem_sub_iff hv hinv hcomm]
    simp
  have hinj : Set.InjOn Elt.sem {e | e ∈ elems gs} := fun e he f hf h =>
    Elt.sem_injective (hval e he) (hval f hf) h
  rw [← SetLike.coe_sort_coe, h1, Nat.card_coe_set_eq, hinj.ncard_image]
  rw [show {e | e ∈ elems gs} = ((elems gs).toFinset : Set Elt) by ext; simp,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem pt_mul_self (w : Pt) : w * w = 1 := by
  have h : ∀ a : ZMod 2, a + a = 0 := by decide
  refine Prod.ext ?_ ?_ <;> funext i <;> exact h _

theorem mem_fixV_sub {gs : List Elt} (hv : ∀ g ∈ gs, g.valid = true) (w : Pt) :
    w ∈ fixV (sub gs) ↔ ∀ g ∈ gs, g.act w = w := by
  show (∀ x ∈ sub gs, x w = w) ↔ _
  constructor
  · intro h g hg
    rw [← Elt.sem_apply (hv g hg)]
    exact h _ (Subgroup.subset_closure ⟨g, hg, rfl⟩)
  · intro h x hx
    have hle : sub gs ≤ MulAction.stabilizer (MulAut (Pt)) w := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨g, hg, rfl⟩
      rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, MulAut.smul_def,
        Elt.sem_apply (hv g hg)]
      exact h g hg
    have h1 := MulAction.mem_stabilizer_iff.mp (hle hx)
    rwa [MulAut.smul_def] at h1

theorem card_subgroup_eq_length {K : Subgroup (Pt)} {l : List (Pt)} (hl : l.Nodup)
    (h : ∀ w, w ∈ K ↔ w ∈ l) : Nat.card K = l.length := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq,
    show (K : Set (Pt)) = (l.toFinset : Set (Pt)) by ext w; simp [h],
    Set.ncard_coe_finset, List.toFinset_card_of_nodup hl]

@[expose] def codeOfPt (w : Pt) : ℕ :=
  (Multiplicative.toAdd w.1 0).val + 2 * (Multiplicative.toAdd w.1 1).val +
    4 * (Multiplicative.toAdd w.1 2).val + 8 * (Multiplicative.toAdd w.1 3).val +
    16 * ((Multiplicative.toAdd w.2 0).val + 2 * (Multiplicative.toAdd w.2 1).val +
      4 * (Multiplicative.toAdd w.2 2).val + 8 * (Multiplicative.toAdd w.2 3).val)

theorem codeOfPt_ptOfCode : ∀ k, k < 256 → codeOfPt (ptOfCode k) = k := by
  decide +kernel

theorem card_pt : Nat.card Pt = 2 ^ 8 := by
  change Nat.card (Multiplicative (Fin 4 → ZMod 2) × Multiplicative (Fin 4 → ZMod 2)) = _
  rw [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd (α := Fin 4 → ZMod 2)), Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin]
  norm_num

theorem allPts_nodup : allPts.Nodup := by
  refine List.Nodup.map_on (fun a ha b hb h => ?_) List.nodup_range
  rw [← codeOfPt_ptOfCode a (List.mem_range.mp ha), h,
    codeOfPt_ptOfCode b (List.mem_range.mp hb)]

theorem mem_allPts (w : Pt) : w ∈ allPts := by
  have hc : allPts.toFinset.card = Fintype.card Pt := by
    rw [List.toFinset_card_of_nodup allPts_nodup, ← Nat.card_eq_fintype_card, card_pt]
    simp [allPts]
  rw [← List.mem_toFinset, Finset.eq_univ_of_card _ hc]
  exact Finset.mem_univ w

theorem mem_fixPts {gs : List Elt}
    (hv : ∀ g ∈ gs, g.valid = true) (w : Pt) : w ∈ fixPts gs ↔ w ∈ fixV (sub gs) := by
  rw [mem_fixV_sub hv, fixPts, List.mem_filter, List.all_eq_true]
  simp only [beq_iff_eq]
  exact ⟨fun h => h.2, fun h => ⟨mem_allPts w, h⟩⟩

theorem card_fixV_sub {gs : List Elt}
    (hv : ∀ g ∈ gs, g.valid = true) : Nat.card (fixV (sub gs)) = (fixPts gs).length :=
  card_subgroup_eq_length (allPts_nodup.filter _) fun w => (mem_fixPts hv w).symm

section Span

variable {G : Type*} [CommGroup G] [DecidableEq G]

omit [DecidableEq G] in
theorem mem_closure_insert_iff_of_sq (h2 : ∀ g : G, g * g = 1) {S : Set G} {s w : G} :
    w ∈ Subgroup.closure (insert s S) ↔
      w ∈ Subgroup.closure S ∨ w * s ∈ Subgroup.closure S := by
  have hss := h2 s
  constructor
  · intro hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · right
        rw [hss]
        exact Subgroup.one_mem _
      · left
        exact Subgroup.subset_closure hx
    | one => left; exact Subgroup.one_mem _
    | mul x y _ _ hx hy =>
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · left; exact Subgroup.mul_mem _ hx hy
      · right
        rw [mul_assoc]
        exact Subgroup.mul_mem _ hx hy
      · right
        rw [mul_assoc, mul_comm y s, ← mul_assoc]
        exact Subgroup.mul_mem _ hx hy
      · left
        have h1 := Subgroup.mul_mem _ hx hy
        rwa [mul_assoc, mul_comm s (y * s), mul_assoc, hss, mul_one] at h1
    | inv x _ hx =>
      rcases hx with hx | hx
      · left; exact Subgroup.inv_mem _ hx
      · right
        have e : x⁻¹ * s = (x * s)⁻¹ := by
          rw [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_right hss, mul_comm]
        rw [e]
        exact Subgroup.inv_mem _ hx
  · rintro (hw | hw)
    · exact Subgroup.closure_mono (Set.subset_insert _ _) hw
    · have h1 := Subgroup.mul_mem _ (Subgroup.closure_mono (Set.subset_insert _ _) hw)
        (Subgroup.subset_closure (Set.mem_insert s S))
      rwa [mul_assoc, hss, mul_one] at h1

@[expose] def spanG : List G → List G
  | [] => [1]
  | s :: ss => if (spanG ss).contains s then spanG ss else spanG ss ++ (spanG ss).map (· * s)

theorem spanG_cons (s : G) (ss : List G) : spanG (s :: ss) =
    if (spanG ss).contains s then spanG ss else spanG ss ++ (spanG ss).map (· * s) := rfl

theorem mem_spanG (h2 : ∀ g : G, g * g = 1) (S : List G) :
    (∀ w, w ∈ spanG S ↔ w ∈ Subgroup.closure {x | x ∈ S}) ∧ (spanG S).Nodup := by
  induction S with
  | nil =>
    refine ⟨fun w => ?_, List.nodup_singleton 1⟩
    simp [spanG]
  | cons s ss ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hset : {x | x ∈ s :: ss} = insert s {x | x ∈ ss} := by
      ext x
      simp
    rw [spanG_cons, hset]
    cases hs : (spanG ss).contains s
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hs' : s ∉ spanG ss := fun h => by
        rw [List.contains_iff_mem.mpr h] at hs
        exact Bool.noConfusion hs
      refine ⟨fun w => ?_, ?_⟩
      · rw [List.mem_append, List.mem_map, ih1, mem_closure_insert_iff_of_sq h2]
        constructor
        · rintro (h | ⟨t, ht, rfl⟩)
          · exact Or.inl h
          · right
            rw [mul_assoc, h2, mul_one]
            exact (ih1 t).mp ht
        · rintro (h | h)
          · exact Or.inl h
          · right
            exact ⟨w * s, (ih1 _).mpr h, by rw [mul_assoc, h2, mul_one]⟩
      · refine List.Nodup.append ih2 (ih2.map fun a b h => mul_right_cancel h) ?_
        intro a ha hb
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
        apply hs'
        have h1 := Subgroup.mul_mem _ (Subgroup.inv_mem _ ((ih1 t).mp ht)) ((ih1 _).mp ha)
        rw [← mul_assoc, inv_mul_cancel, one_mul] at h1
        exact (ih1 s).mpr h1
    · simp only [↓reduceIte]
      have hs' : s ∈ Subgroup.closure {x | x ∈ ss} := (ih1 s).mp (List.contains_iff_mem.mp hs)
      refine ⟨fun w => ?_, ih2⟩
      rw [ih1, mem_closure_insert_iff_of_sq h2]
      constructor
      · exact Or.inl
      · rintro (h | h)
        · exact h
        · have h1 := Subgroup.mul_mem _ h hs'
          rwa [mul_assoc, h2, mul_one] at h1

end Span

theorem spanList_eq_spanG (S : List Pt) : spanList S = spanG S := by
  induction S with
  | nil => rfl
  | cons s ss ih =>
    show (if (spanList ss).contains s then spanList ss
      else spanList ss ++ (spanList ss).map (· * s)) = spanG (s :: ss)
    rw [ih]
    rfl

theorem mem_spanList (S : List Pt) :
    (∀ w, w ∈ spanList S ↔ w ∈ Subgroup.closure {x | x ∈ S}) ∧ (spanList S).Nodup := by
  rw [spanList_eq_spanG]
  exact mem_spanG pt_mul_self S

theorem card_closure_eq_spanList (S : List Pt) :
    Nat.card (Subgroup.closure {x | x ∈ S}) = (spanList S).length :=
  card_subgroup_eq_length (mem_spanList S).2 fun w => ((mem_spanList S).1 w).symm

@[expose] def Good (gs : List Elt) : Prop :=
  (∀ g ∈ gs, g.valid = true) ∧ (∀ g ∈ gs, g.sem * g.sem = 1) ∧
    ∀ g ∈ gs, ∀ h ∈ gs, g.sem * h.sem = h.sem * g.sem

theorem nil_mem_reps : ([] : List Elt) ∈ reps :=
  List.mem_map.mpr ⟨[], List.mem_cons_self, rfl⟩

theorem sub_nil : sub [] = ⊥ := by
  rw [sub, eq_bot_iff, Subgroup.closure_le]
  rintro _ ⟨g, hg, -⟩
  exact absurd hg List.not_mem_nil

theorem conjAut_conjAut' (X : Subgroup (MulAut (Pt))) (a b : MulAut (Pt)) :
    conjAut (conjAut X a) b = conjAut X (b * a) := by
  ext x
  rw [H9Conj.mem_conjAut, H9Conj.mem_conjAut, H9Conj.mem_conjAut, _root_.mul_inv_rev]
  simp only [mul_assoc]

theorem Elt.eq_of_a {e f : Elt} (he : e.valid = true) (hf : f.valid = true)
    (ha : e.a.toMatrix = f.a.toMatrix) (hb : e.b = f.b) : e = f := by
  have he' := (Elt.valid_iff e).mp he
  have hf' := (Elt.valid_iff f).mp hf
  have hai : e.ai.toMatrix = f.ai.toMatrix := by
    calc e.ai.toMatrix = e.ai.toMatrix * (f.a.toMatrix * f.ai.toMatrix) := by
          rw [hf'.1, Matrix.mul_one]
      _ = (e.ai.toMatrix * e.a.toMatrix) * f.ai.toMatrix := by rw [ha, Matrix.mul_assoc]
      _ = f.ai.toMatrix := by rw [he'.2, Matrix.one_mul]
  cases e
  cases f
  simp only at ha hb hai
  rw [Mat.toMatrix_injective ha, Mat.toMatrix_injective hai, hb]

theorem conjAut_conj_inv' (X : Subgroup (MulAut Pt)) (a : MulAut Pt) :
    conjAut (conjAut X a) a⁻¹ = X := by
  rw [conjAut_conjAut', inv_mul_cancel, H9Conj.conjAut_one]

@[expose] def RepClosed (R : List (List Elt)) : Prop :=
  ∀ gs ∈ R, ∀ y : Elt, y.valid = true → y.sem * y.sem = 1 →
    (∀ g ∈ gs, y.sem * g.sem = g.sem * y.sem) → y.sem ∉ sub gs →
      ∃ gs' ∈ R, ∃ c ∈ modelM4, conjAut (sub (gs ++ [y])) c = sub gs'

theorem exists_rep_of {R : List (List Elt)} (hnil : [] ∈ R) (hgoodR : ∀ gs ∈ R, Good gs)
    (hcl : RepClosed R) (A : Subgroup (MulAut Pt))
    (hAM : A ≤ modelM4) (hA : IsElemAbelian2 A) :
    ∃ gs ∈ R, ∃ m ∈ modelM4, A = conjAut (sub gs) m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ : ∃ k, Nat.card A = k := ⟨_, rfl⟩
  induction k using Nat.strong_induction_on generalizing A with
  | _ k ih =>
  by_cases hbot : A = ⊥
  · exact ⟨[], hnil, 1, modelM4.one_mem, by rw [hbot, sub_nil, H9Conj.conjAut_one]⟩
  have hAp : IsPGroup 2 ↥A := isPGroup_of_isElemAbelian2 hA
  have hAc := card_eq_two_pow_of_isPGroup hAp
  have hr : 1 ≤ rk ↥A := by
    by_contra h0
    push Not at h0
    apply hbot
    rw [← Subgroup.card_eq_one, hAc, show rk ↥A = 0 by omega, pow_zero]
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2
    (show 2 ^ (rk ↥A - 1) ∣ Nat.card ↥A from hAc ▸ pow_dvd_pow 2 (Nat.sub_le _ _))
  have hBA : K.map A.subtype ≤ A := Subgroup.map_subtype_le K
  have hBc : Nat.card (K.map A.subtype) = 2 ^ (rk ↥A - 1) := by
    rw [Subgroup.card_map_of_injective A.subtype_injective, hK]
  have hAB : Nat.card A = 2 * Nat.card (K.map A.subtype) := by
    rw [hBc, hAc, ← pow_succ']
    congr 1
    omega
  have hBe : IsElemAbelian2 (K.map A.subtype) :=
    ⟨fun x hx y hy => hA.1 x (hBA hx) y (hBA hy), fun x hx => hA.2 x (hBA hx)⟩
  have hBlt : Nat.card (K.map A.subtype) < k := by
    rw [← hk, hAB]
    have : 0 < Nat.card (K.map A.subtype) := Nat.card_pos
    omega
  obtain ⟨gs, hgs, m, hmM, hBm⟩ := ih _ hBlt _ (hBA.trans hAM) hBe rfl
  have hgood := hgoodR gs hgs
  have hBneA : K.map A.subtype ≠ A := fun h => by
    rw [h] at hAB
    have : 0 < Nat.card A := Nat.card_pos
    omega
  obtain ⟨x, hxA, hxB⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hBA hBneA)
  set x' := m⁻¹ * x * m with hx'
  have hsubB : sub gs = conjAut (K.map A.subtype) m⁻¹ := by
    rw [hBm, conjAut_conj_inv']
  have hx'M : x' ∈ modelM4 :=
    modelM4.mul_mem (modelM4.mul_mem (modelM4.inv_mem hmM) (hAM hxA)) hmM
  have hx2 : x * x = 1 := by rw [← pow_two]; exact hA.2 x hxA
  have hx'2 : x' * x' = 1 := by
    rw [hx', show m⁻¹ * x * m * (m⁻¹ * x * m) = m⁻¹ * (x * x) * m by group, hx2]
    group
  have hx'A : x' ∈ conjAut A m⁻¹ := by
    rw [H9Conj.mem_conjAut, inv_inv, hx']
    simpa [mul_assoc] using hxA
  have hx'c : ∀ r ∈ sub gs, x' * r = r * x' := by
    intro r hr
    rw [hsubB] at hr
    have hrA : m * r * m⁻¹ ∈ A := by
      have h1 := H9Conj.mem_conjAut.mp hr
      rw [inv_inv] at h1
      exact hBA h1
    have h1 := hA.1 x hxA _ hrA
    calc x' * r = m⁻¹ * (x * (m * r * m⁻¹)) * m := by rw [hx']; group
      _ = m⁻¹ * ((m * r * m⁻¹) * x) * m := by rw [h1]
      _ = r * x' := by rw [hx']; group
  have hx'n : x' ∉ sub gs := fun h => by
    rw [hsubB] at h
    have h1 := H9Conj.mem_conjAut.mp h
    rw [inv_inv, hx'] at h1
    apply hxB
    simpa [mul_assoc] using h1
  obtain ⟨y, hyv, hyx⟩ := hx'M
  have hyc : ∀ g ∈ gs, y.sem * g.sem = g.sem * y.sem := fun g hg => by
    rw [hyx]
    exact hx'c _ (Subgroup.subset_closure ⟨g, hg, rfl⟩)
  obtain ⟨gs', hgs', c, hcM, hconj⟩ := hcl gs hgs y hyv (by rw [hyx]; exact hx'2) hyc
    (by rw [hyx]; exact hx'n)
  have hle : sub (gs ++ [y]) ≤ conjAut A m⁻¹ := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    rcases List.mem_append.mp hg with hg | hg
    · have h1 : g.sem ∈ sub gs := Subgroup.subset_closure ⟨g, hg, rfl⟩
      rw [hsubB] at h1
      exact (H9Conj.conjAut_le_conjAut.mpr hBA) h1
    · rw [List.mem_singleton.mp hg, hyx]
      exact hx'A
  have hlt : sub gs < sub (gs ++ [y]) := by
    refine lt_of_le_of_ne (Subgroup.closure_mono fun _ ⟨g, hg, h⟩ =>
      ⟨g, List.mem_append_left _ hg, h⟩) fun h => hx'n ?_
    rw [h, ← hyx]
    exact Subgroup.subset_closure ⟨y, List.mem_append_right _ (List.mem_singleton_self y), rfl⟩
  have heq : sub (gs ++ [y]) = conjAut A m⁻¹ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have h1 := Subgroup.card_lt_of_lt hlt
    obtain ⟨q, hq⟩ := Subgroup.card_dvd_of_le hlt.le
    have h4 : Nat.card (sub gs) = Nat.card (K.map A.subtype) := by
      rw [hsubB, H9Conj.card_conjAut]
    rw [H9Conj.card_conjAut, hAB]
    rw [h4] at h1 hq
    have hq1 : 2 ≤ q := by
      by_contra hq2
      push Not at hq2
      interval_cases q <;> omega
    rw [hq, mul_comm]
    exact Nat.mul_le_mul_left _ hq1
  refine ⟨gs', hgs', m * c⁻¹, modelM4.mul_mem hmM (modelM4.inv_mem hcM), ?_⟩
  have h1 : sub (gs ++ [y]) = conjAut (sub gs') c⁻¹ := by
    rw [← hconj, conjAut_conj_inv']
  rw [← conjAut_conjAut', ← h1, heq, conjAut_conjAut', mul_inv_cancel, H9Conj.conjAut_one]

end CFSG.Quasithin.H13.H9Four

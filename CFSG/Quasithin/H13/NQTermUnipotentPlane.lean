module

public import CFSG.Quasithin.SteinbergCDScalarQuotientCentralCover
public import CFSG.Quasithin.H13.NQTermClassicalOuterPrime

public section

namespace CFSG.Quasithin.H13.NQTerm

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix.SpecialLinearGroup (toGL coe_GL_coe_matrix)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open scoped commutatorElement

section Nil

variable {F : Type*} [Field F]

@[expose] def flagNil (V : Submodule F (Fin 3 → F)) : Set (Matrix (Fin 3) (Fin 3) F) :=
  {u | (∀ x, u *ᵥ x ∈ V) ∧ ∀ v ∈ V, u *ᵥ v = 0}

theorem matrix_eq_zero_of_mulVec {M : Matrix (Fin 3) (Fin 3) F} (h : ∀ x, M *ᵥ x = 0) :
    M = 0 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rwa [mulVec_single_one, col_apply] at this

theorem mul_eq_zero_of_mem_flagNil {V : Submodule F (Fin 3 → F)}
    {u w : Matrix (Fin 3) (Fin 3) F} (hu : u ∈ flagNil V) (hw : w ∈ flagNil V) : u * w = 0 :=
  matrix_eq_zero_of_mulVec fun x => by rw [← mulVec_mulVec, hu.2 _ (hw.1 x)]

theorem add_mem_flagNil {V : Submodule F (Fin 3 → F)} {u w : Matrix (Fin 3) (Fin 3) F}
    (hu : u ∈ flagNil V) (hw : w ∈ flagNil V) : u + w ∈ flagNil V :=
  ⟨fun x => by rw [add_mulVec]; exact V.add_mem (hu.1 x) (hw.1 x),
    fun v hv => by rw [add_mulVec, hu.2 v hv, hw.2 v hv, add_zero]⟩

theorem neg_mem_flagNil {V : Submodule F (Fin 3 → F)} {u : Matrix (Fin 3) (Fin 3) F}
    (hu : u ∈ flagNil V) : -u ∈ flagNil V :=
  ⟨fun x => by rw [neg_mulVec]; exact V.neg_mem (hu.1 x),
    fun v hv => by rw [neg_mulVec, hu.2 v hv, neg_zero]⟩

theorem smul_mem_flagNil {V : Submodule F (Fin 3 → F)} {u : Matrix (Fin 3) (Fin 3) F} (c : F)
    (hu : u ∈ flagNil V) : c • u ∈ flagNil V :=
  ⟨fun x => by rw [smul_mulVec]; exact V.smul_mem c (hu.1 x),
    fun v hv => by rw [smul_mulVec, hu.2 v hv, smul_zero]⟩

theorem one_add_pow_of_mem_flagNil {V : Submodule F (Fin 3 → F)} {u : Matrix (Fin 3) (Fin 3) F}
    (hu : u ∈ flagNil V) (n : ℕ) : (1 + u) ^ n = 1 + (n : F) • u := by
  have hsq := mul_eq_zero_of_mem_flagNil hu hu
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hsq, smul_zero,
      add_zero, Nat.cast_succ, add_smul, one_smul]
    abel

theorem det_one_add_of_mem_flagNil {p : ℕ} [Fact p.Prime] [CharP F p]
    {V : Submodule F (Fin 3 → F)} {u : Matrix (Fin 3) (Fin 3) F} (hu : u ∈ flagNil V) :
    (1 + u).det = 1 := by
  have hp : p.Prime := Fact.out
  have h1 : (1 + u) ^ p = 1 := by
    rw [one_add_pow_of_mem_flagNil hu p, CharP.cast_eq_zero, zero_smul, add_zero]
  have h2 : (1 + u).det ^ p = 1 := by rw [← det_pow, h1, det_one]
  have h3 : ((1 + u).det - 1) ^ p = 0 := by rw [sub_pow_char, h2, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff hp.ne_zero).mp h3)

theorem coe_inv_eq_one_sub {g : SpecialLinearGroup (Fin 3) F} {u : Matrix (Fin 3) (Fin 3) F}
    (hgu : (g : Matrix (Fin 3) (Fin 3) F) = 1 + u) (hsq : u * u = 0) :
    ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 - u := by
  have h1 : (g : Matrix (Fin 3) (Fin 3) F) * (1 - u) = 1 := by
    rw [hgu, add_mul, one_mul, mul_sub, mul_one, hsq, sub_zero]
    abel
  have h3 : ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (g : Matrix (Fin 3) (Fin 3) F) = 1 :=
    congrArg Subtype.val (inv_mul_cancel g)
  calc ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      = ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          ((g : Matrix (Fin 3) (Fin 3) F) * (1 - u)) := by rw [h1, mul_one]
    _ = 1 - u := by rw [← mul_assoc, h3, one_mul]

@[expose] def flagUnipotent (V : Submodule F (Fin 3 → F)) :
    Subgroup (SpecialLinearGroup (Fin 3) F) where
  carrier := elationGenerators V
  one_mem' := one_mem_elationGenerators V
  mul_mem' {g h} hg hh := by
    change ((g : Matrix (Fin 3) (Fin 3) F) - 1) ∈ flagNil V at hg
    change ((h : Matrix (Fin 3) (Fin 3) F) - 1) ∈ flagNil V at hh
    change (((g * h : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) - 1) ∈ flagNil V
    have e : ((g * h : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) - 1 =
        ((g : Matrix (Fin 3) (Fin 3) F) - 1) + ((h : Matrix (Fin 3) (Fin 3) F) - 1) +
          ((g : Matrix (Fin 3) (Fin 3) F) - 1) * ((h : Matrix (Fin 3) (Fin 3) F) - 1) := by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      noncomm_ring
    rw [e, mul_eq_zero_of_mem_flagNil hg hh, add_zero]
    exact add_mem_flagNil hg hh
  inv_mem' {g} hg := by
    change ((g : Matrix (Fin 3) (Fin 3) F) - 1) ∈ flagNil V at hg
    change (((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) - 1) ∈ flagNil V
    rw [coe_inv_eq_one_sub (u := (g : Matrix (Fin 3) (Fin 3) F) - 1) (by abel)
      (mul_eq_zero_of_mem_flagNil hg hg), sub_sub_cancel_left]
    exact neg_mem_flagNil hg

theorem mem_flagUnipotent {V : Submodule F (Fin 3 → F)} {g : SpecialLinearGroup (Fin 3) F} :
    g ∈ flagUnipotent V ↔ ((g : Matrix (Fin 3) (Fin 3) F) - 1) ∈ flagNil V :=
  Iff.rfl

theorem elationSubgroup_eq_flagUnipotent (V : Submodule F (Fin 3 → F)) :
    elationSubgroup V = flagUnipotent V :=
  Subgroup.closure_eq (flagUnipotent V)

theorem mul_comm_of_mem_flagUnipotent {V : Submodule F (Fin 3 → F)}
    {g h : SpecialLinearGroup (Fin 3) F} (hg : g ∈ flagUnipotent V) (hh : h ∈ flagUnipotent V) :
    g * h = h * g := by
  have hgh := mul_eq_zero_of_mem_flagNil (mem_flagUnipotent.mp hg) (mem_flagUnipotent.mp hh)
  have hhg := mul_eq_zero_of_mem_flagNil (mem_flagUnipotent.mp hh) (mem_flagUnipotent.mp hg)
  have key : ∀ a b : Matrix (Fin 3) (Fin 3) F, a * b = 0 → b * a = 0 →
      (1 + a) * (1 + b) = (1 + b) * (1 + a) := by
    intro a b hab hba
    calc (1 + a) * (1 + b) = 1 + a + b + a * b := by noncomm_ring
      _ = 1 + b + a + b * a := by rw [hab, hba]; abel
      _ = (1 + b) * (1 + a) := by noncomm_ring
  have h1 := key _ _ hgh hhg
  rw [add_sub_cancel, add_sub_cancel] at h1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact h1

theorem pow_char_of_mem_flagUnipotent {p : ℕ} [CharP F p] {V : Submodule F (Fin 3 → F)}
    {g : SpecialLinearGroup (Fin 3) F} (hg : g ∈ flagUnipotent V) : g ^ p = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  have eg : (g : Matrix (Fin 3) (Fin 3) F) = 1 + ((g : Matrix (Fin 3) (Fin 3) F) - 1) := by abel
  rw [eg, one_add_pow_of_mem_flagNil (mem_flagUnipotent.mp hg) p, CharP.cast_eq_zero, zero_smul,
    add_zero]

theorem isElementaryAbelian_flagUnipotent {p : ℕ} [CharP F p] (V : Submodule F (Fin 3 → F)) :
    CFSG.IsElementaryAbelian p (flagUnipotent V) where
  toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (mul_comm_of_mem_flagUnipotent a.2 b.2)⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
    Subtype.ext (pow_char_of_mem_flagUnipotent g.2)

noncomputable def flagUnipotentEquiv {p : ℕ} [Fact p.Prime] [CharP F p]
    (V : Submodule F (Fin 3 → F)) : flagUnipotent V ≃ flagNil V where
  toFun g := ⟨((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) - 1,
    mem_flagUnipotent.mp g.2⟩
  invFun u := ⟨⟨1 + u, det_one_add_of_mem_flagNil (p := p) u.2⟩, by
    change (1 + (u : Matrix (Fin 3) (Fin 3) F)) - 1 ∈ flagNil V
    rw [add_sub_cancel_left]
    exact u.2⟩
  left_inv g := Subtype.ext (Subtype.ext (add_sub_cancel _ _))
  right_inv u := Subtype.ext (add_sub_cancel_left _ _)

@[expose] def stdLine : Submodule F (Fin 3 → F) where
  carrier := {x | x 1 = 0 ∧ x 2 = 0}
  add_mem' := fun {a b} ha hb =>
    ⟨by change (a + b) 1 = 0; rw [Pi.add_apply, ha.1, hb.1, add_zero],
      by change (a + b) 2 = 0; rw [Pi.add_apply, ha.2, hb.2, add_zero]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' := fun c {x} hx =>
    ⟨by change (c • x) 1 = 0; rw [Pi.smul_apply, hx.1, smul_zero],
      by change (c • x) 2 = 0; rw [Pi.smul_apply, hx.2, smul_zero]⟩

@[expose] def stdPlane : Submodule F (Fin 3 → F) where
  carrier := {x | x 2 = 0}
  add_mem' := fun {a b} ha hb => by
    change (a + b) 2 = 0
    rw [Pi.add_apply, show a 2 = 0 from ha, show b 2 = 0 from hb, add_zero]
  zero_mem' := rfl
  smul_mem' := fun c {x} hx => by
    change (c • x) 2 = 0
    rw [Pi.smul_apply, show x 2 = 0 from hx, smul_zero]

theorem mem_stdPlane {x : Fin 3 → F} : x ∈ (stdPlane : Submodule F (Fin 3 → F)) ↔ x 2 = 0 :=
  Iff.rfl

theorem finrank_stdLine : Module.finrank F (stdLine : Submodule F (Fin 3 → F)) = 1 := by
  have h : (stdLine : Submodule F (Fin 3 → F)) = Submodule.span F {Pi.single 0 1} := by
    apply le_antisymm
    · intro x hx
      have hx' : x = x 0 • Pi.single 0 1 := by
        funext i
        fin_cases i <;> simp [hx.1, hx.2]
      rw [hx']
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨by simp, by simp⟩
  rw [h, finrank_span_singleton]
  simp

theorem finrank_stdPlane : Module.finrank F (stdPlane : Submodule F (Fin 3 → F)) = 2 := by
  have hker : (stdPlane : Submodule F (Fin 3 → F)) =
      LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : Fin 3 => F) 2) := by
    ext x
    rw [mem_stdPlane, LinearMap.mem_ker, LinearMap.proj_apply]
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.proj (R := F) (φ := fun _ : Fin 3 => F) 2)
  have hr : LinearMap.range (LinearMap.proj (R := F) (φ := fun _ : Fin 3 => F) 2) = ⊤ :=
    LinearMap.range_eq_top.mpr fun c => ⟨Pi.single 2 c, by simp⟩
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
  rw [hker]
  omega

@[expose] def lineNil (b c : F) : Matrix (Fin 3) (Fin 3) F := !![0, b, c; 0, 0, 0; 0, 0, 0]

@[expose] def planeNil (b c : F) : Matrix (Fin 3) (Fin 3) F := !![0, 0, b; 0, 0, c; 0, 0, 0]

theorem lineNil_mem (b c : F) : lineNil b c ∈ flagNil (stdLine : Submodule F (Fin 3 → F)) := by
  refine ⟨fun x => ⟨?_, ?_⟩, fun v hv => ?_⟩
  · simp [lineNil, mulVec, dotProduct, Fin.sum_univ_three]
  · simp [lineNil, mulVec, dotProduct, Fin.sum_univ_three]
  · funext i
    fin_cases i <;> simp [lineNil, mulVec, dotProduct, Fin.sum_univ_three, hv.1, hv.2]

theorem planeNil_mem (b c : F) :
    planeNil b c ∈ flagNil (stdPlane : Submodule F (Fin 3 → F)) := by
  refine ⟨fun x => ?_, fun v hv => ?_⟩
  · simp [mem_stdPlane, planeNil, dotProduct, Fin.sum_univ_three]
  · funext i
    have hv' : v 2 = 0 := hv
    fin_cases i <;> simp [planeNil, mulVec, dotProduct, Fin.sum_univ_three, hv']

theorem eq_lineNil {u : Matrix (Fin 3) (Fin 3) F}
    (hu : u ∈ flagNil (stdLine : Submodule F (Fin 3 → F))) : u = lineNil (u 0 1) (u 0 2) := by
  have hrow : ∀ j, u 1 j = 0 ∧ u 2 j = 0 := fun j => by
    have h := hu.1 (Pi.single j 1)
    rw [mulVec_single_one] at h
    exact h
  have hrow1 : ∀ j, u 1 j = 0 := fun j => (hrow j).1
  have hrow2 : ∀ j, u 2 j = 0 := fun j => (hrow j).2
  have hcol : ∀ i, u i 0 = 0 := fun i => by
    have h := congrFun (hu.2 (Pi.single 0 1) ⟨by simp, by simp⟩) i
    rwa [mulVec_single_one, col_apply, Pi.zero_apply] at h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lineNil, hcol, hrow1, hrow2]

theorem eq_planeNil {u : Matrix (Fin 3) (Fin 3) F}
    (hu : u ∈ flagNil (stdPlane : Submodule F (Fin 3 → F))) : u = planeNil (u 0 2) (u 1 2) := by
  have hrow : ∀ j, u 2 j = 0 := fun j => by
    have h := hu.1 (Pi.single j 1)
    rw [mulVec_single_one] at h
    exact h
  have hcol : ∀ i, u i 0 = 0 ∧ u i 1 = 0 := fun i => by
    have h0 := congrFun (hu.2 (Pi.single 0 1) (by simp [mem_stdPlane])) i
    have h1 := congrFun (hu.2 (Pi.single 1 1) (by simp [mem_stdPlane])) i
    rw [mulVec_single_one, col_apply, Pi.zero_apply] at h0 h1
    exact ⟨h0, h1⟩
  have hcol0 : ∀ i, u i 0 = 0 := fun i => (hcol i).1
  have hcol1 : ∀ i, u i 1 = 0 := fun i => (hcol i).2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeNil, hrow, hcol0, hcol1]

theorem card_flagNil_stdLine :
    Nat.card (flagNil (stdLine : Submodule F (Fin 3 → F))) = Nat.card F ^ 2 := by
  have hrange : flagNil (stdLine : Submodule F (Fin 3 → F)) =
      Set.range (fun bc : F × F => lineNil bc.1 bc.2) := by
    ext u
    constructor
    · intro hu
      exact ⟨(u 0 1, u 0 2), (eq_lineNil hu).symm⟩
    · rintro ⟨bc, rfl⟩
      exact lineNil_mem _ _
  have hinj : Function.Injective (fun bc : F × F => lineNil bc.1 bc.2) := by
    intro bc bc' h
    have h1 := congrFun (congrFun h 0) 1
    have h2 := congrFun (congrFun h 0) 2
    simp only [lineNil] at h1 h2
    simp at h1 h2
    exact Prod.ext h1 h2
  rw [hrange, Nat.card_range_of_injective hinj, Nat.card_prod, sq]

theorem card_flagNil_stdPlane :
    Nat.card (flagNil (stdPlane : Submodule F (Fin 3 → F))) = Nat.card F ^ 2 := by
  have hrange : flagNil (stdPlane : Submodule F (Fin 3 → F)) =
      Set.range (fun bc : F × F => planeNil bc.1 bc.2) := by
    ext u
    constructor
    · intro hu
      exact ⟨(u 0 2, u 1 2), (eq_planeNil hu).symm⟩
    · rintro ⟨bc, rfl⟩
      exact planeNil_mem _ _
  have hinj : Function.Injective (fun bc : F × F => planeNil bc.1 bc.2) := by
    intro bc bc' h
    have h1 := congrFun (congrFun h 0) 2
    have h2 := congrFun (congrFun h 1) 2
    simp only [planeNil] at h1 h2
    simp at h1 h2
    exact Prod.ext h1 h2
  rw [hrange, Nat.card_range_of_injective hinj, Nat.card_prod, sq]

theorem exists_sub_smul_mem_flagNil_stdLine {A : Matrix (Fin 3) (Fin 3) F}
    (hA : ∀ u ∈ flagNil (stdLine : Submodule F (Fin 3 → F)), A * u = u * A) :
    ∃ a : F, A - a • 1 ∈ flagNil (stdLine : Submodule F (Fin 3 → F)) := by
  have e1 := hA _ (lineNil_mem 1 0)
  have e2 := hA _ (lineNil_mem 0 1)
  have f1 : ∀ i j, (A * lineNil (1 : F) 0) i j = (lineNil (1 : F) 0 * A) i j := fun i j => by
    rw [e1]
  have f2 : ∀ i j, (A * lineNil (0 : F) 1) i j = (lineNil (0 : F) 1 * A) i j := fun i j => by
    rw [e2]
  simp only [mul_apply, Fin.sum_univ_three, lineNil] at f1 f2
  have a10 : A 1 0 = 0 := by simpa using f1 1 1
  have a20 : A 2 0 = 0 := by simpa using f1 2 1
  have a11 : A 0 0 = A 1 1 := by simpa using f1 0 1
  have a12 : A 1 2 = 0 := by simpa using (f1 0 2).symm
  have a22 : A 0 0 = A 2 2 := by simpa using f2 0 2
  have a21 : A 2 1 = 0 := by simpa using (f2 0 1).symm
  refine ⟨A 0 0, ?_⟩
  have h : A - A 0 0 • 1 = lineNil (A 0 1) (A 0 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lineNil, one_apply, a10, a20, a12, a21, ← a11, ← a22]
  rw [h]
  exact lineNil_mem _ _

theorem exists_sub_smul_mem_flagNil_stdPlane {A : Matrix (Fin 3) (Fin 3) F}
    (hA : ∀ u ∈ flagNil (stdPlane : Submodule F (Fin 3 → F)), A * u = u * A) :
    ∃ a : F, A - a • 1 ∈ flagNil (stdPlane : Submodule F (Fin 3 → F)) := by
  have e1 := hA _ (planeNil_mem 1 0)
  have e2 := hA _ (planeNil_mem 0 1)
  have f1 : ∀ i j, (A * planeNil (1 : F) 0) i j = (planeNil (1 : F) 0 * A) i j := fun i j => by
    rw [e1]
  have f2 : ∀ i j, (A * planeNil (0 : F) 1) i j = (planeNil (0 : F) 1 * A) i j := fun i j => by
    rw [e2]
  simp only [mul_apply, Fin.sum_univ_three, planeNil] at f1 f2
  have a10 : A 1 0 = 0 := by simpa using f1 1 2
  have a20 : A 2 0 = 0 := by simpa using f1 2 2
  have a00 : A 0 0 = A 2 2 := by simpa using f1 0 2
  have a21 : A 2 1 = 0 := by simpa using (f1 0 1).symm
  have a01 : A 0 1 = 0 := by simpa using f2 0 2
  have a11 : A 1 1 = A 2 2 := by simpa using f2 1 2
  refine ⟨A 2 2, ?_⟩
  have h : A - A 2 2 • 1 = planeNil (A 0 2) (A 1 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [planeNil, one_apply, a10, a20, a21, a01, a00, a11]
  rw [h]
  exact planeNil_mem _ _

theorem not_dual_flagNil_stdLine {B : Matrix (Fin 3) (Fin 3) F} (hB : IsUnit B.det)
    (h : ∀ u ∈ flagNil (stdLine : Submodule F (Fin 3 → F)), B * uᵀ + u * B = 0) : False := by
  have e1 := h _ (lineNil_mem 1 0)
  have e2 := h _ (lineNil_mem 0 1)
  have f1 : ∀ i j, (B * (lineNil (1 : F) 0)ᵀ + lineNil (1 : F) 0 * B) i j = 0 := fun i j => by
    rw [e1, Matrix.zero_apply]
  have f2 : ∀ i j, (B * (lineNil (0 : F) 1)ᵀ + lineNil (0 : F) 1 * B) i j = 0 := fun i j => by
    rw [e2, Matrix.zero_apply]
  simp only [Matrix.add_apply, mul_apply, transpose_apply, Fin.sum_univ_three, lineNil] at f1 f2
  have b11 : B 1 1 = 0 := by simpa using f1 1 0
  have b21 : B 2 1 = 0 := by simpa using f1 2 0
  have b12 : B 1 2 = 0 := by simpa using f1 0 2
  have b22 : B 2 2 = 0 := by simpa using f2 2 0
  apply hB.ne_zero
  rw [det_fin_three, b11, b21, b12, b22]
  ring

theorem not_dual_flagNil_stdPlane {B : Matrix (Fin 3) (Fin 3) F} (hB : IsUnit B.det)
    (h : ∀ u ∈ flagNil (stdPlane : Submodule F (Fin 3 → F)), B * uᵀ + u * B = 0) : False := by
  have e1 := h _ (planeNil_mem 1 0)
  have e2 := h _ (planeNil_mem 0 1)
  have f1 : ∀ i j, (B * (planeNil (1 : F) 0)ᵀ + planeNil (1 : F) 0 * B) i j = 0 := fun i j => by
    rw [e1, Matrix.zero_apply]
  have f2 : ∀ i j, (B * (planeNil (0 : F) 1)ᵀ + planeNil (0 : F) 1 * B) i j = 0 := fun i j => by
    rw [e2, Matrix.zero_apply]
  simp only [Matrix.add_apply, mul_apply, transpose_apply, Fin.sum_univ_three, planeNil] at f1 f2
  have b12 : B 1 2 = 0 := by simpa using f1 1 0
  have b22 : B 2 2 = 0 := by simpa using f1 2 0
  have b02 : B 0 2 = 0 := by simpa using f2 0 1
  apply hB.ne_zero
  rw [det_fin_three, b12, b22, b02]
  ring

section Transport

variable {V V₀ : Submodule F (Fin 3 → F)} {M M' : Matrix (Fin 3) (Fin 3) F}

theorem mem_flagNil_iff_of_transport (hMM' : M * M' = 1) (hM'M : M' * M = 1)
    (hV : ∀ y, y ∈ V ↔ M' *ᵥ y ∈ V₀) (u : Matrix (Fin 3) (Fin 3) F) :
    u ∈ flagNil V ↔ M' * u * M ∈ flagNil V₀ := by
  have key : ∀ x, (M' * u * M) *ᵥ x = M' *ᵥ (u *ᵥ (M *ᵥ x)) := fun x => by
    simp only [mulVec_mulVec, mul_assoc]
  have hMx : ∀ x, M' *ᵥ (M *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, hM'M, one_mulVec]
  have hxM : ∀ x, M *ᵥ (M' *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, hMM', one_mulVec]
  constructor
  · rintro ⟨hu1, hu2⟩
    refine ⟨fun x => ?_, fun v hv => ?_⟩
    · rw [key]
      exact (hV _).mp (hu1 _)
    · rw [key, hu2 _ ((hV _).mpr (by rw [hMx]; exact hv)), mulVec_zero]
  · rintro ⟨h1, h2⟩
    refine ⟨fun x => (hV _).mpr ?_, fun v hv => ?_⟩
    · have h3 := h1 (M' *ᵥ x)
      rwa [key, hxM] at h3
    · have h3 := h2 (M' *ᵥ v) ((hV v).mp hv)
      rw [key, hxM] at h3
      have h4 := congrArg (M *ᵥ ·) h3
      simp only [hxM, mulVec_zero] at h4
      exact h4

theorem conj_conj_eq_of_transport (hM'M : M' * M = 1) (w : Matrix (Fin 3) (Fin 3) F) :
    M' * (M * w * M') * M = w := by
  rw [show M' * (M * w * M') * M = (M' * M) * w * (M' * M) by simp only [mul_assoc]]
  rw [hM'M, one_mul, mul_one]

theorem card_flagNil_of_transport (hMM' : M * M' = 1) (hM'M : M' * M = 1)
    (hV : ∀ y, y ∈ V ↔ M' *ᵥ y ∈ V₀) : Nat.card (flagNil V) = Nat.card (flagNil V₀) :=
  Nat.card_congr
    { toFun := fun u => ⟨M' * u.1 * M, (mem_flagNil_iff_of_transport hMM' hM'M hV _).mp u.2⟩
      invFun := fun w => ⟨M * w.1 * M', (mem_flagNil_iff_of_transport hMM' hM'M hV _).mpr
        (by rw [conj_conj_eq_of_transport hM'M]; exact w.2)⟩
      left_inv := fun u => Subtype.ext (conj_conj_eq_of_transport (M := M') (M' := M) hMM' u.1)
      right_inv := fun w => Subtype.ext (conj_conj_eq_of_transport hM'M w.1) }

theorem exists_sub_smul_mem_flagNil_of_transport (hMM' : M * M' = 1) (hM'M : M' * M = 1)
    (hV : ∀ y, y ∈ V ↔ M' *ᵥ y ∈ V₀)
    (hstd : ∀ B : Matrix (Fin 3) (Fin 3) F, (∀ w ∈ flagNil V₀, B * w = w * B) →
      ∃ a : F, B - a • 1 ∈ flagNil V₀)
    {A : Matrix (Fin 3) (Fin 3) F} (hA : ∀ u ∈ flagNil V, A * u = u * A) :
    ∃ a : F, A - a • 1 ∈ flagNil V := by
  obtain ⟨a, ha⟩ := hstd (M' * A * M) fun w hw => by
    have hu : M * w * M' ∈ flagNil V := (mem_flagNil_iff_of_transport hMM' hM'M hV _).mpr
      (by rw [conj_conj_eq_of_transport hM'M]; exact hw)
    have h1 := hA _ hu
    calc M' * A * M * w = M' * (A * (M * w * M')) * M := by
          simp only [mul_assoc, hM'M, mul_one]
      _ = M' * (M * w * M' * A) * M := by rw [h1]
      _ = w * (M' * A * M) := by simp only [← mul_assoc, hM'M, one_mul]
  refine ⟨a, (mem_flagNil_iff_of_transport hMM' hM'M hV _).mpr ?_⟩
  have h : M' * (A - a • 1) * M = M' * A * M - a • 1 := by
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hM'M]
  rw [h]
  exact ha

theorem not_dual_of_transport (hMM' : M * M' = 1) (hM'M : M' * M = 1)
    (hV : ∀ y, y ∈ V ↔ M' *ᵥ y ∈ V₀)
    (hstd : ∀ B : Matrix (Fin 3) (Fin 3) F, IsUnit B.det →
      (∀ w ∈ flagNil V₀, B * wᵀ + w * B = 0) → False)
    {A : Matrix (Fin 3) (Fin 3) F} (hA : IsUnit A.det)
    (h : ∀ u ∈ flagNil V, A * uᵀ + u * A = 0) : False := by
  have hT : Mᵀ * M'ᵀ = 1 := by rw [← transpose_mul, hM'M, transpose_one]
  have hM' : IsUnit M'.det := isUnit_det_of_left_inverse hMM'
  refine hstd (M' * A * M'ᵀ) ?_ fun w hw => ?_
  · rw [det_mul, det_mul, det_transpose]
    exact (hM'.mul hA).mul hM'
  · have hu : M * w * M' ∈ flagNil V := (mem_flagNil_iff_of_transport hMM' hM'M hV _).mpr
      (by rw [conj_conj_eq_of_transport hM'M]; exact hw)
    have h1 := h _ hu
    have t1 : M' * (A * (M * w * M')ᵀ) * M'ᵀ = M' * A * M'ᵀ * wᵀ := by
      rw [transpose_mul, transpose_mul]
      simp only [mul_assoc, hT, mul_one]
    have t2 : M' * (M * w * M' * A) * M'ᵀ = w * (M' * A * M'ᵀ) := by
      simp only [← mul_assoc, hM'M, one_mul]
    calc M' * A * M'ᵀ * wᵀ + w * (M' * A * M'ᵀ) =
        M' * (A * (M * w * M')ᵀ) * M'ᵀ + M' * (M * w * M' * A) * M'ᵀ := by rw [t1, t2]
      _ = M' * (A * (M * w * M')ᵀ + M * w * M' * A) * M'ᵀ := by rw [mul_add, add_mul]
      _ = 0 := by rw [h1, mul_zero, zero_mul]

end Transport

theorem exists_transport {V V₀ : Submodule F (Fin 3 → F)}
    (h : Module.finrank F V₀ = Module.finrank F V) :
    ∃ M M' : Matrix (Fin 3) (Fin 3) F, M * M' = 1 ∧ M' * M = 1 ∧
      ∀ y, y ∈ V ↔ M' *ᵥ y ∈ V₀ := by
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq (LinearEquiv.ofFinrankEq V₀ V h)
  refine ⟨LinearMap.toMatrix' (g : (Fin 3 → F) →ₗ[F] (Fin 3 → F)),
    LinearMap.toMatrix' (g.symm : (Fin 3 → F) →ₗ[F] (Fin 3 → F)), ?_, ?_, fun y => ?_⟩
  · rw [← LinearMap.toMatrix'_comp]
    rw [show (g : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) ∘ₗ (g.symm : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) =
      LinearMap.id from LinearMap.ext fun x => by simp, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp]
    rw [show (g.symm : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) ∘ₗ (g : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) =
      LinearMap.id from LinearMap.ext fun x => by simp, LinearMap.toMatrix'_id]
  · rw [LinearMap.toMatrix'_mulVec]
    change y ∈ V ↔ g.symm y ∈ V₀
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := (LinearEquiv.ofFinrankEq V₀ V h).surjective ⟨y, hy⟩
      have hgx : g x = y := by
        rw [← hg x, hx]
      rw [← hgx, LinearEquiv.symm_apply_apply]
      exact x.2
    · intro hy
      have h1 := hg ⟨g.symm y, hy⟩
      simp only [LinearEquiv.apply_symm_apply] at h1
      rw [← h1]
      exact (LinearEquiv.ofFinrankEq V₀ V h ⟨g.symm y, hy⟩).2

theorem exists_transport_std {V : Submodule F (Fin 3 → F)}
    (hV : Module.finrank F V = 1 ∨ Module.finrank F V = 2) :
    ∃ (V₀ : Submodule F (Fin 3 → F)) (M M' : Matrix (Fin 3) (Fin 3) F),
      (V₀ = stdLine ∨ V₀ = stdPlane) ∧ M * M' = 1 ∧ M' * M = 1 ∧
        ∀ y, y ∈ V ↔ M' *ᵥ y ∈ V₀ := by
  rcases hV with hV | hV
  · obtain ⟨M, M', h1, h2, h3⟩ := exists_transport (V := V) (V₀ := stdLine)
      (by rw [finrank_stdLine, hV])
    exact ⟨stdLine, M, M', .inl rfl, h1, h2, h3⟩
  · obtain ⟨M, M', h1, h2, h3⟩ := exists_transport (V := V) (V₀ := stdPlane)
      (by rw [finrank_stdPlane, hV])
    exact ⟨stdPlane, M, M', .inr rfl, h1, h2, h3⟩

theorem card_flagNil {V : Submodule F (Fin 3 → F)}
    (hV : Module.finrank F V = 1 ∨ Module.finrank F V = 2) :
    Nat.card (flagNil V) = Nat.card F ^ 2 := by
  obtain ⟨V₀, M, M', hV₀, h1, h2, h3⟩ := exists_transport_std hV
  rw [card_flagNil_of_transport h1 h2 h3]
  rcases hV₀ with rfl | rfl
  · exact card_flagNil_stdLine
  · exact card_flagNil_stdPlane

theorem exists_sub_smul_mem_flagNil {V : Submodule F (Fin 3 → F)}
    (hV : Module.finrank F V = 1 ∨ Module.finrank F V = 2) {A : Matrix (Fin 3) (Fin 3) F}
    (hA : ∀ u ∈ flagNil V, A * u = u * A) : ∃ a : F, A - a • 1 ∈ flagNil V := by
  obtain ⟨V₀, M, M', hV₀, h1, h2, h3⟩ := exists_transport_std hV
  refine exists_sub_smul_mem_flagNil_of_transport h1 h2 h3 (fun B hB => ?_) hA
  rcases hV₀ with rfl | rfl
  · exact exists_sub_smul_mem_flagNil_stdLine hB
  · exact exists_sub_smul_mem_flagNil_stdPlane hB

theorem not_dual_flagNil {V : Submodule F (Fin 3 → F)}
    (hV : Module.finrank F V = 1 ∨ Module.finrank F V = 2) {A : Matrix (Fin 3) (Fin 3) F}
    (hA : IsUnit A.det) (h : ∀ u ∈ flagNil V, A * uᵀ + u * A = 0) : False := by
  obtain ⟨V₀, M, M', hV₀, h1, h2, h3⟩ := exists_transport_std hV
  refine not_dual_of_transport h1 h2 h3 (fun B hB hw => ?_) hA h
  rcases hV₀ with rfl | rfl
  · exact not_dual_flagNil_stdLine hB hw
  · exact not_dual_flagNil_stdPlane hB hw

end Nil

theorem ringEquiv_eq_one_of_card_prime {K : Type*} [Field K] [Fintype K] {p : ℕ}
    [Fact p.Prime] (hK : Fintype.card K = p) (σ : K ≃+* K) : σ = 1 := by
  have : CharP K p := charP_of_card_eq_prime_pow (f := 1) (by rw [pow_one, hK])
  ext x
  obtain ⟨y, rfl⟩ := (ZMod.castHom_bijective K hK).2 x
  exact congrArg (fun f : ZMod p →+* K => f y)
    (RingHom.ext_zmod (σ.toRingHom.comp (ZMod.castHom (dvd_refl p) K))
      (ZMod.castHom (dvd_refl p) K))

theorem mulAut_mul_conj_mul_inv {S : Type*} [Group S] (α : MulAut S) (s : S) :
    α * MulAut.conj s * α⁻¹ = MulAut.conj (α s) := by
  ext x
  simp [MulAut.conj_apply]

section Group

variable {F : Type} [Field F]

theorem eq_of_proj_eq_of_pow_eq_one {p : ℕ} (hp3 : Nat.Coprime p 3)
    {x y : SpecialLinearGroup (Fin 3) F} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : proj 3 F x = proj 3 F y) : x = y := by
  have hz : x⁻¹ * y ∈ scalars 3 F := proj_eq_proj_iff.mp hxy
  have hzc : x⁻¹ * y ∈ center (SpecialLinearGroup (Fin 3) F) := scalars_le_center 3 F hz
  have hyz : y = x * (x⁻¹ * y) := by rw [mul_inv_cancel_left]
  have hzp : (x⁻¹ * y) ^ p = 1 := by
    have h1 : (x * (x⁻¹ * y)) ^ p = x ^ p * (x⁻¹ * y) ^ p :=
      Commute.mul_pow (mem_center_iff.mp hzc x) p
    rw [← hyz, hy, hx, one_mul] at h1
    exact h1.symm
  have hz3 : (x⁻¹ * y) ^ 3 = 1 := by
    obtain ⟨c, hc, hzc'⟩ := hz
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hzc', ← map_pow, ← Units.val_pow_eq_pow_val, hc,
      Units.val_one, map_one, Matrix.SpecialLinearGroup.coe_one]
  have h1 := pow_gcd_eq_one.mpr ⟨hzp, hz3⟩
  rw [hp3.gcd_eq_one, pow_one] at h1
  rw [hyz, h1, mul_one]

theorem conj_injective_projectiveSL_three [Finite F] :
    Function.Injective (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  obtain ⟨g, rfl⟩ := proj_surjective 3 F s
  rw [← conjAut_toGL] at hs
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num : 3 ≤ 3)
    (toGL g) 1 (by rw [map_one, mul_one, hs])
  have hgu : (g : Matrix (Fin 3) (Fin 3) F) = scalar (Fin 3) (c : F) := by
    have h1 := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) hc
    simpa [Matrix.GeneralLinearGroup.coe_scalar] using h1.symm
  have hun : c ^ 3 = 1 := by
    apply Units.ext
    have h1 := g.2
    rw [hgu, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h1
    rw [Units.val_pow_eq_pow_val, h1, Units.val_one]
  exact (QuotientGroup.eq_one_iff g).2 ⟨c, hun, hgu⟩

open CFSG.Assembly.LowTwoRank in
theorem prime_linear_three_unipotent_plane_normalizes_no_two_subgroup [Finite F] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hF : Nat.card F = p) (V : Submodule F (Fin 3 → F))
    (hV : Module.finrank F V = 1 ∨ Module.finrank F V = 2) :
    ((elationSubgroup V : Set (SpecialLinearGroup (Fin 3) F)) = elationGenerators V ∧
      ∀ u : Matrix (Fin 3) (Fin 3) F, (∀ x, u *ᵥ x ∈ V) → (∀ v ∈ V, u *ᵥ v = 0) →
        ∃ g ∈ elationSubgroup V, (g : Matrix (Fin 3) (Fin 3) F) = 1 + u) ∧
    CFSG.IsElementaryAbelian p (elationSubgroup V) ∧ Nat.card (elationSubgroup V) = p ^ 2 ∧
    CFSG.IsElementaryAbelian p (projElationSubgroup V) ∧
      Nat.card (projElationSubgroup V) = p ^ 2 ∧
    Function.Injective ((proj 3 F).comp (elationSubgroup V).subtype) ∧
    (centralizer ((elationSubgroup V).map toGL : Set (GL (Fin 3) F)) :
        Set (GL (Fin 3) F)) =
      {A | ∃ a : Fˣ, ∃ v ∈ elationSubgroup V,
        A = Matrix.GeneralLinearGroup.scalar (Fin 3) a * toGL v} ∧
    centralizer (projElationSubgroup V : Set (projectiveSL 3 F)) = projElationSubgroup V ∧
    centralizer ((projElationSubgroup V).map MulAut.conj : Set (MulAut (projectiveSL 3 F))) =
      (projElationSubgroup V).map MulAut.conj ∧
    ∀ Q : Subgroup (MulAut (projectiveSL 3 F)), IsPGroup 2 Q →
      (projElationSubgroup V).map MulAut.conj ≤
        normalizer (Q : Set (MulAut (projectiveSL 3 F))) → Q = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = p := by rw [← Nat.card_eq_fintype_card, hF]
  have : CharP F p := charP_of_card_eq_prime_pow (f := 1) (by rw [pow_one, hF'])
  have hp3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).mpr (by omega)
  set U₀ := elationSubgroup V with hU₀def
  have hU₀ : U₀ = flagUnipotent V := elationSubgroup_eq_flagUnipotent V
  have hmemU₀ : ∀ g, g ∈ U₀ ↔ ((g : Matrix (Fin 3) (Fin 3) F) - 1) ∈ flagNil V := fun g => by
    rw [hU₀]
    rfl
  set U := projElationSubgroup V with hUdef
  have hUmap : U = U₀.map (proj 3 F) := rfl
  have hlift : ∀ u ∈ flagNil V, ∃ g ∈ U₀, (g : Matrix (Fin 3) (Fin 3) F) = 1 + u := fun u hu =>
    ⟨⟨1 + u, det_one_add_of_mem_flagNil (p := p) hu⟩, (hmemU₀ _).mpr (by
      change (1 + u) - 1 ∈ flagNil V
      rw [add_sub_cancel_left]
      exact hu), rfl⟩
  have hset : (U₀ : Set (SpecialLinearGroup (Fin 3) F)) = elationGenerators V := by
    rw [hU₀]
    rfl
  have hU₀ea : CFSG.IsElementaryAbelian p U₀ := by
    rw [hU₀]
    exact isElementaryAbelian_flagUnipotent V
  have hU₀comm : ∀ g ∈ U₀, ∀ h ∈ U₀, g * h = h * g := fun g hg h hh =>
    mul_comm_of_mem_flagUnipotent (hU₀ ▸ hg) (hU₀ ▸ hh)
  have hU₀pow : ∀ g ∈ U₀, g ^ p = 1 := fun g hg => pow_char_of_mem_flagUnipotent (hU₀ ▸ hg)
  have hU₀card : Nat.card U₀ = p ^ 2 := by
    rw [hU₀, Nat.card_congr (flagUnipotentEquiv (p := p) V), card_flagNil hV, hF]
  have hV0 : ∃ v ∈ V, v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hbot : V = ⊥ := (Submodule.eq_bot_iff V).mpr hcon
    rw [hbot, finrank_bot] at hV
    omega
  have hinj : Function.Injective ((proj 3 F).comp U₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    change proj 3 F (g : SpecialLinearGroup (Fin 3) F) = 1 at hg
    obtain ⟨c, -, hc⟩ := proj_eq_one_iff.mp hg
    obtain ⟨v, hv, hv0⟩ := hV0
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    have h1 := congrFun (((hmemU₀ g).mp g.2).2 v hv) i
    rw [hc, sub_mulVec, one_mulVec, Pi.sub_apply, scalar_apply, mulVec_diagonal,
      Pi.zero_apply] at h1
    have hc1 : (c : F) = 1 := by
      have h3 : ((c : F) - 1) * v i = 0 := by rw [sub_mul, one_mul]; exact h1
      exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hi)
    apply Subtype.ext
    apply Subtype.ext
    rw [hc, hc1, map_one]
    rfl
  have hUea : CFSG.IsElementaryAbelian p U := by
    rw [hUmap]
    exact CFSG.IsElementaryAbelian.map (proj 3 F)
  have hUcard : Nat.card U = p ^ 2 := by
    have hr : U = ((proj 3 F).comp U₀.subtype).range := by
      rw [hUmap, MonoidHom.range_comp, range_subtype]
    rw [hr, ← hU₀card]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hcentGL : ∀ A : GL (Fin 3) F,
      (∀ v ∈ U₀, toGL v * A = A * toGL v) →
      ∃ a : Fˣ, ∃ v ∈ U₀, A = Matrix.GeneralLinearGroup.scalar (Fin 3) a * toGL v := by
    intro A hA
    have hAu : IsUnit (A : Matrix (Fin 3) (Fin 3) F).det := isUnit_det_of_left_inverse A.inv_mul
    have hcomm : ∀ u ∈ flagNil V, (A : Matrix (Fin 3) (Fin 3) F) * u = u * A := by
      intro u hu
      obtain ⟨g, hg, hgu⟩ := hlift u hu
      have h1 := congrArg (fun B : GL (Fin 3) F => (B : Matrix (Fin 3) (Fin 3) F)) (hA g hg)
      simp only [Units.val_mul, coe_GL_coe_matrix, hgu] at h1
      rw [add_mul, mul_add, one_mul, mul_one] at h1
      exact (add_left_cancel h1).symm
    obtain ⟨a, ha⟩ := exists_sub_smul_mem_flagNil hV hcomm
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul, sub_zero] at ha
      have h2 : ((A : Matrix (Fin 3) (Fin 3) F) * A).det = 0 := by
        rw [mul_eq_zero_of_mem_flagNil ha ha, det_zero]
      rw [det_mul] at h2
      exact hAu.ne_zero (mul_self_eq_zero.mp h2)
    obtain ⟨g, hg, hgu⟩ := hlift _ (smul_mem_flagNil a⁻¹ ha)
    refine ⟨Units.mk0 a ha0, g, hg, Units.ext ?_⟩
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_GL_coe_matrix, hgu,
      Units.val_mk0, scalar_apply, ← smul_eq_diagonal_mul, smul_add, smul_smul,
      mul_inv_cancel₀ ha0, one_smul, add_sub_cancel]
  have hsc : ∀ (a : Fˣ) (B : GL (Fin 3) F),
      B * Matrix.GeneralLinearGroup.scalar (Fin 3) a =
        Matrix.GeneralLinearGroup.scalar (Fin 3) a * B := by
    intro a B
    have ha : Matrix.GeneralLinearGroup.scalar (Fin 3) a ∈ center (GL (Fin 3) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨a, rfl⟩
    exact mem_center_iff.mp ha B
  have hcentGLset : (centralizer ((U₀.map toGL : Subgroup (GL (Fin 3) F)) :
      Set (GL (Fin 3) F)) : Set (GL (Fin 3) F)) =
      {A | ∃ a : Fˣ, ∃ v ∈ U₀,
        A = Matrix.GeneralLinearGroup.scalar (Fin 3) a * toGL v} := by
    ext A
    constructor
    · intro hA
      exact hcentGL A fun v hv => mem_centralizer_iff.mp hA _ ⟨v, hv, rfl⟩
    · rintro ⟨a, v, hv, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      calc toGL w *
          (Matrix.GeneralLinearGroup.scalar (Fin 3) a * toGL v) =
          Matrix.GeneralLinearGroup.scalar (Fin 3) a * toGL (w * v) := by
            rw [← mul_assoc, hsc a, mul_assoc, map_mul]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 3) a * toGL v *
            toGL w := by
            rw [hU₀comm w hw v hv, map_mul, mul_assoc]
  have hUcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, hU₀comm g hg h hh]
  have hcentS : centralizer (U : Set (projectiveSL 3 F)) = U := by
    apply le_antisymm
    · intro s hs
      obtain ⟨g, rfl⟩ := proj_surjective 3 F s
      have hconj : ∀ v ∈ U₀, g * v * g⁻¹ = v := by
        intro v hv
        apply eq_of_proj_eq_of_pow_eq_one hp3
        · rw [conj_pow, hU₀pow v hv, mul_one, mul_inv_cancel]
        · exact hU₀pow v hv
        · have h1 := mem_centralizer_iff.mp hs (proj 3 F v) ⟨v, hv, rfl⟩
          rw [map_mul, map_mul, map_inv, ← h1, mul_inv_cancel_right]
      obtain ⟨a, v₀, hv₀, hAeq⟩ := hcentGL (toGL g) fun v hv => by
        have hvg : v * g = g * v := by
          calc v * g = g * v * g⁻¹ * g := by rw [hconj v hv]
            _ = g * v := by group
        rw [← map_mul, ← map_mul, hvg]
      have hmat : (g : Matrix (Fin 3) (Fin 3) F) = scalar (Fin 3) (a : F) * v₀ := by
        have h1 := congrArg (fun B : GL (Fin 3) F => (B : Matrix (Fin 3) (Fin 3) F)) hAeq
        simpa [Matrix.GeneralLinearGroup.coe_scalar] using h1
      have ha3 : a ^ 3 = 1 := by
        apply Units.ext
        have h1 := g.2
        rw [hmat, det_mul, v₀.2, mul_one, scalar_apply, det_diagonal, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin] at h1
        rw [Units.val_pow_eq_pow_val, h1, Units.val_one]
      have hg : g = scalarElement a ha3 * v₀ :=
        Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, hmat])
      refine ⟨v₀, hv₀, ?_⟩
      rw [hg, map_mul, proj_eq_one_iff.mpr (scalarElement_mem_scalars a ha3), one_mul]
    · intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      exact hUcomm y hy x hx
  have hι := conj_injective_projectiveSL_three (F := F)
  set IU := U.map (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) with hIU
  have hIUcomm : ∀ x ∈ IU, ∀ y ∈ IU, x * y = y * x := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, hUcomm s hs t ht]
  have hcentAut : centralizer (IU : Set (MulAut (projectiveSL 3 F))) = IU := by
    apply le_antisymm
    · intro α hα
      have hfix : ∀ x ∈ U, α x = x := by
        intro x hx
        have h1 := mem_centralizer_iff.mp hα (MulAut.conj x) ⟨x, hx, rfl⟩
        apply hι
        rw [← mulAut_mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
      obtain ⟨A, σ, ε, hε, hα'⟩ := (automorphism_generation (K := F) (n := 3) (by norm_num)).2 α
      rw [ringEquiv_eq_one_of_card_prime hF' σ, map_one, mul_one] at hα'
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
      · rw [pow_zero, mul_one] at hα'
        have hAc : ∀ v ∈ U₀, toGL v * A = A * toGL v := by
          intro v hv
          have h1 : slConjugation 3 F A v = v := by
            apply eq_of_proj_eq_of_pow_eq_one hp3
            · rw [← map_pow, hU₀pow v hv, map_one]
            · exact hU₀pow v hv
            · rw [← conjAut_proj, ← hα']
              exact hfix _ ⟨v, hv, rfl⟩
          have h2 := congrArg (fun g : SpecialLinearGroup (Fin 3) F =>
            (g : Matrix (Fin 3) (Fin 3) F)) h1
          simp only [coe_slConjugation] at h2
          apply Units.ext
          rw [Units.val_mul, Units.val_mul, coe_GL_coe_matrix]
          calc (v : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
              (A : Matrix (Fin 3) (Fin 3) F) * v * ((A⁻¹ : GL (Fin 3) F) :
                Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) := by rw [h2]
            _ = (A : Matrix (Fin 3) (Fin 3) F) * v := by
              rw [mul_assoc (_ * _), A.inv_mul, mul_one]
        obtain ⟨a, v₀, hv₀, hAeq⟩ := hcentGL A hAc
        rw [hα', hAeq, map_mul, conjAut_scalar, one_mul, conjAut_toGL]
        exact ⟨proj 3 F v₀, ⟨v₀, hv₀, rfl⟩, rfl⟩
      · rw [pow_one] at hα'
        exfalso
        refine not_dual_flagNil hV (A := (A : Matrix (Fin 3) (Fin 3) F))
          (isUnit_det_of_left_inverse A.inv_mul) fun u hu => ?_
        obtain ⟨v, hv, hvu⟩ := hlift u hu
        have hvinv := coe_inv_eq_one_sub hvu (mul_eq_zero_of_mem_flagNil hu hu)
        have h1 : slConjugation 3 F A (v⁻¹).transpose = v := by
          apply eq_of_proj_eq_of_pow_eq_one hp3
          · have h3 : ((v⁻¹).transpose) ^ p = 1 := by
              apply Subtype.ext
              rw [Matrix.SpecialLinearGroup.coe_pow]
              change (((v⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ) ^ p =
                ((1 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
              rw [← transpose_pow, ← Matrix.SpecialLinearGroup.coe_pow, inv_pow, hU₀pow v hv,
                inv_one,
                Matrix.SpecialLinearGroup.coe_one, transpose_one]
            rw [← map_pow, h3, map_one]
          · exact hU₀pow v hv
          · rw [← conjAut_proj, ← dualAut_proj, ← MulAut.mul_apply, ← hα']
            exact hfix _ ⟨v, hv, rfl⟩
        have h2 : (A : Matrix (Fin 3) (Fin 3) F) *
            ((v⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ *
              ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = v := by
          have h4 := congrArg (fun g : SpecialLinearGroup (Fin 3) F =>
            (g : Matrix (Fin 3) (Fin 3) F)) h1
          rw [coe_slConjugation] at h4
          exact h4
        rw [hvinv, hvu] at h2
        have h3 : (A : Matrix (Fin 3) (Fin 3) F) * (1 - u)ᵀ =
            (1 + u) * (A : Matrix (Fin 3) (Fin 3) F) := by
          calc (A : Matrix (Fin 3) (Fin 3) F) * (1 - u)ᵀ =
              (A : Matrix (Fin 3) (Fin 3) F) * (1 - u)ᵀ *
                ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
                  (A : Matrix (Fin 3) (Fin 3) F) := by
                rw [mul_assoc (_ * _), A.inv_mul, mul_one]
            _ = (1 + u) * (A : Matrix (Fin 3) (Fin 3) F) := by rw [h2]
        rw [transpose_sub, transpose_one, mul_sub, mul_one, add_mul, one_mul] at h3
        calc (A : Matrix (Fin 3) (Fin 3) F) * uᵀ + u * (A : Matrix (Fin 3) (Fin 3) F) =
            ((A : Matrix (Fin 3) (Fin 3) F) + u * (A : Matrix (Fin 3) (Fin 3) F)) -
              ((A : Matrix (Fin 3) (Fin 3) F) - (A : Matrix (Fin 3) (Fin 3) F) * uᵀ) := by abel
          _ = 0 := by rw [h3, sub_self]
    · intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      exact hIUcomm y hy x hx
  refine ⟨⟨hset, fun u h1 h2 => hlift u ⟨h1, h2⟩⟩, hU₀ea, hU₀card, hUea, hUcard, hinj,
    hcentGLset, hcentS, hcentAut, ?_⟩
  intro Q hQ hQn
  set Q' := Q.comap (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) with hQ'
  have hQ'2 : IsPGroup 2 Q' := hQ.comap_of_injective _ hι
  have hUQ' : U ≤ normalizer (Q' : Set (projectiveSL 3 F)) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro q
    have h1 := (mem_normalizer_iff.mp (hQn ⟨x, hx, rfl⟩)) (MulAut.conj q)
    change MulAut.conj q ∈ Q ↔ MulAut.conj (x * q * x⁻¹) ∈ Q
    rw [map_mul, map_mul, map_inv]
    exact h1
  have h2F : (2 : F) ≠ 0 := by
    intro h2
    have h3 : ((2 : ℕ) : F) = 0 := by exact_mod_cast h2
    rw [CharP.cast_eq_zero_iff F p] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hUp : IsPGroup p U := CFSG.IsElementaryAbelian.isPGroup p U
  have hlp := (SteinbergCD.central_extensions_scalar_quotients_trivial_large_prime_two_action h2F
    (n := 3) le_rfl (Γ := StatedSL 3 F)
    (D := (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F))
    (fun d hd => by
      obtain ⟨u, hu⟩ := (mem_subgroupOf.mp hd : (d : GL (Fin 3) F) ∈ StatedScalars (Fin 3) F)
      exact ⟨u, by rw [← hu]; rfl⟩)
    (K := projectiveSL 3 F) (Z := ⊥) bot_le
    ((QuotientGroup.quotientBot).trans (statedProjSLEquivProjectiveSL 3 F).symm) hQ'2 hp hp5
    hUp hUQ').1
  have hQ'U : Q' ≤ U := by
    intro q hq
    rw [← hcentS, mem_centralizer_iff]
    intro x hx
    have h1 : ⁅q, x⁆ ∈ ⁅Q', U⁆ := commutator_mem_commutator hq hx
    rw [hlp, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hodd : ∀ H : Subgroup (MulAut (projectiveSL 3 F)), IsPGroup 2 H →
      Nat.card H ∣ p ^ 2 → H = ⊥ := by
    intro H hH hdvd
    obtain ⟨k, hk⟩ := hH.exists_card_eq
    rw [hk] at hdvd
    rcases k with _ | k
    · exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])
    · exfalso
      have h2 : 2 ∣ p ^ 2 := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2)
      omega
  have hQ'bot : Q' = ⊥ := by
    have h1 : Q'.map MulAut.conj = ⊥ := hodd _ (hQ'2.map _) (by
      rw [card_map_of_injective hι, ← hUcard]
      exact card_dvd_of_le hQ'U)
    rwa [map_eq_bot_iff_of_injective Q' hι] at h1
  have hQinn : ∀ s : projectiveSL 3 F, MulAut.conj s ∈ Q → s = 1 := by
    intro s hs
    have h1 : s ∈ Q' := hs
    rw [hQ'bot, mem_bot] at h1
    exact h1
  have hQC : Q ≤ centralizer (IU : Set (MulAut (projectiveSL 3 F))) := by
    intro q hq
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hc1 : MulAut.conj x * q * (MulAut.conj x)⁻¹ * q⁻¹ ∈ Q :=
      mul_mem ((mem_normalizer_iff.mp (hQn ⟨x, hx, rfl⟩) q).mp hq) (inv_mem hq)
    have hc2 : MulAut.conj x * q * (MulAut.conj x)⁻¹ * q⁻¹ = MulAut.conj (x * q x⁻¹) := by
      rw [mul_assoc, mul_assoc, ← mul_assoc q, ← map_inv, mulAut_mul_conj_mul_inv, ← map_mul]
    rw [hc2] at hc1
    have h2 : MulAut.conj x * q * (MulAut.conj x)⁻¹ * q⁻¹ = 1 := by
      rw [hc2, hQinn _ hc1, map_one]
    calc MulAut.conj x * q =
        (MulAut.conj x * q * (MulAut.conj x)⁻¹ * q⁻¹) * q * MulAut.conj x := by group
      _ = q * MulAut.conj x := by rw [h2, one_mul]
  have hQIU : Q ≤ IU := hQC.trans hcentAut.le
  exact hodd Q hQ (by
    rw [← hUcard, ← card_map_of_injective hι]
    exact card_dvd_of_le hQIU)

end Group

end CFSG.Quasithin.H13.NQTerm

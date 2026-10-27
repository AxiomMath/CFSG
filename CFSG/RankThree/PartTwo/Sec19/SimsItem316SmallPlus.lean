module

public import CFSG.RankThree.PartTwo.Sec19.SimsItem316SmallTransfer

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsItem316Small

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Matrix
open CFSG.Assembly.RankThreeEven (orthogonalPlus plusQuadForm)
open scoped commutatorElement

section General

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def stabSet (A : Set (ι → ZMod 2)) : Subgroup (GL ι (ZMod 2)) where
  carrier := {g | ∀ w, w ∈ A ↔ (g : Matrix ι ι (ZMod 2)) *ᵥ w ∈ A}
  mul_mem' {g h} hg hh w := by
    rw [Units.val_mul, ← mulVec_mulVec]
    exact (hh w).trans (hg _)
  one_mem' w := by rw [Units.val_one, one_mulVec]
  inv_mem' {g} hg w := by
    have := hg (((g⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w)
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at this
    exact this.symm

theorem inv_mulVec_mulVec (g : GL ι (ZMod 2)) (w : ι → ZMod 2) :
    ((g⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ ((g : Matrix ι ι (ZMod 2)) *ᵥ w) = w := by
  rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem mulVec_inv_mulVec (g : GL ι (ZMod 2)) (w : ι → ZMod 2) :
    (g : Matrix ι ι (ZMod 2)) *ᵥ (((g⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w) = w := by
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

abbrev MapsIn (g : GL ι (ZMod 2)) (A A' : Set (ι → ZMod 2)) : Prop :=
  ∀ w ∈ A, (g : Matrix ι ι (ZMod 2)) *ᵥ w ∈ A'

theorem mapsTo_of_mem_commutator {O : Subgroup (GL ι (ZMod 2))} (A B : Set (ι → ZMod 2))
    {a : ι → ZMod 2} (ha : a ∈ A) (haB : a ∉ B)
    (htype : ∀ g ∈ O, (MapsIn g A A ∧ MapsIn g B B) ∨ (MapsIn g A B ∧ MapsIn g B A)) :
    ∀ g ∈ ⁅O, O⁆, ∀ w ∈ A, ((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w ∈ A := by
  have hinv : ∀ g ∈ O, ((MapsIn g A A ∧ MapsIn g B B) ∧ (MapsIn g⁻¹ A A ∧ MapsIn g⁻¹ B B)) ∨
      ((MapsIn g A B ∧ MapsIn g B A) ∧ (MapsIn g⁻¹ A B ∧ MapsIn g⁻¹ B A)) := by
    intro g hg
    rcases htype g hg with hP | hS <;> rcases htype g⁻¹ (O.inv_mem hg) with hP' | hS'
    · exact Or.inl ⟨hP, hP'⟩
    · exfalso
      have h1 := hP.2 _ (hS'.1 a ha)
      rw [mulVec_inv_mulVec] at h1
      exact haB h1
    · exfalso
      have h1 := hP'.2 _ (hS.1 a ha)
      rw [inv_mulVec_mulVec] at h1
      exact haB h1
    · exact Or.inr ⟨hS, hS'⟩
  have hmaps : ∀ g ∈ O, ∀ h ∈ O, MapsIn ⁅g, h⁆ A A := by
    intro g hg h hh w hw
    rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, ← mulVec_mulVec,
      ← mulVec_mulVec, ← mulVec_mulVec]
    rcases hinv g hg with ⟨hg1, hg2⟩ | ⟨hg1, hg2⟩ <;> rcases hinv h hh with ⟨hh1, hh2⟩ | ⟨hh1, hh2⟩
    · exact hg1.1 _ (hh1.1 _ (hg2.1 _ (hh2.1 _ hw)))
    · exact hg1.1 _ (hh1.2 _ (hg2.2 _ (hh2.1 _ hw)))
    · exact hg1.2 _ (hh1.2 _ (hg2.1 _ (hh2.1 _ hw)))
    · exact hg1.2 _ (hh1.1 _ (hg2.2 _ (hh2.1 _ hw)))
  have hle : ⁅O, O⁆ ≤ stabSet A := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    show ∀ w, w ∈ A ↔ ((⁅g, h⁆ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w ∈ A
    intro w
    refine ⟨hmaps g hg h hh w, fun hw => ?_⟩
    have h1 := hmaps h hh g hg _ hw
    rwa [mulVec_mulVec, ← Units.val_mul, ← commutatorElement_inv, inv_mul_cancel, Units.val_one,
      one_mulVec] at h1
  intro g hg w hw
  exact (hle hg w).1 hw

theorem isometry_of_mem_closure {Q : (ι → ZMod 2) → ZMod 2} {g : GL ι (ZMod 2)}
    (hg : g ∈ Subgroup.closure
      {A : GL ι (ZMod 2) | ∀ v, Q ((A : Matrix ι ι (ZMod 2)) *ᵥ v) = Q v}) :
    ∀ v, Q ((g : Matrix ι ι (ZMod 2)) *ᵥ v) = Q v := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => intro v; rw [Units.val_one, one_mulVec]
  | mul x y _ _ hx hy => intro v; rw [Units.val_mul, ← mulVec_mulVec, hx, hy]
  | inv x _ hx =>
    intro v
    have := hx (((x⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ v)
    rw [mulVec_inv_mulVec] at this
    exact this.symm

theorem mulVec_injective (g : GL ι (ZMod 2)) :
    Function.Injective fun w : ι → ZMod 2 => (g : Matrix ι ι (ZMod 2)) *ᵥ w := by
  intro v v' h
  have h' := congrArg (fun u => ((g⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ u) h
  simpa only [inv_mulVec_mulVec] using h'

end General

@[expose] def ex1 : Fin 1 ⊕ Fin 1 → ZMod 2 := Sum.elim ![1] ![0]

@[expose] def ey1 : Fin 1 ⊕ Fin 1 → ZMod 2 := Sum.elim ![0] ![1]

abbrev InX (w : Fin 1 ⊕ Fin 1 → ZMod 2) : Prop := w (Sum.inr 0) = 0

abbrev InY (w : Fin 1 ⊕ Fin 1 → ZMod 2) : Prop := w (Sum.inl 0) = 0

@[expose] def lineX : AddSubgroup (Fin 1 ⊕ Fin 1 → ZMod 2) where
  carrier := {w | InX w}
  add_mem' {a b} ha hb := by
    have ha' : a (Sum.inr 0) = 0 := ha
    have hb' : b (Sum.inr 0) = 0 := hb
    show (a + b) (Sum.inr 0) = 0
    rw [Pi.add_apply, ha', hb', add_zero]
  zero_mem' := rfl
  neg_mem' {a} ha := by
    have ha' : a (Sum.inr 0) = 0 := ha
    show (-a) (Sum.inr 0) = 0
    rw [Pi.neg_apply, ha']
    decide

theorem mem_lineX {w : Fin 1 ⊕ Fin 1 → ZMod 2} : w ∈ lineX ↔ InX w := Iff.rfl

abbrev lineY : Set (Fin 1 ⊕ Fin 1 → ZMod 2) := {w | InY w}

theorem plusOne_singular : ∀ x : Fin 1 ⊕ Fin 1 → ZMod 2, plusQuadForm 1 x = 0 → x ≠ 0 →
    x = ex1 ∨ x = ey1 := by
  decide +kernel

theorem plusOne_lineX : ∀ w : Fin 1 ⊕ Fin 1 → ZMod 2, InX w → w = 0 ∨ w = ex1 := by
  decide +kernel

theorem plusOne_lineY : ∀ w : Fin 1 ⊕ Fin 1 → ZMod 2, InY w → w = 0 ∨ w = ey1 := by
  decide +kernel

theorem plusOne_type (g : GL (Fin 1 ⊕ Fin 1) (ZMod 2))
    (hg : ∀ v, plusQuadForm 1 ((g : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) (ZMod 2)) *ᵥ v) =
      plusQuadForm 1 v) :
    (MapsIn g (lineX : Set _) lineX ∧ MapsIn g lineY lineY) ∨
      (MapsIn g (lineX : Set _) lineY ∧ MapsIn g lineY lineX) := by
  let f := fun w : Fin 1 ⊕ Fin 1 → ZMod 2 =>
    (g : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) (ZMod 2)) *ᵥ w
  have hinj : Function.Injective f := mulVec_injective g
  have hf0 : f 0 = 0 := mulVec_zero _
  have hQ : ∀ v, plusQuadForm 1 (f v) = plusQuadForm 1 v := hg
  have hx := plusOne_singular (f ex1) (by rw [hQ]; decide)
    (fun h => absurd (hinj (h.trans hf0.symm)) (by decide))
  have hy := plusOne_singular (f ey1) (by rw [hQ]; decide)
    (fun h => absurd (hinj (h.trans hf0.symm)) (by decide))
  have hxy : f ex1 ≠ f ey1 := fun h => absurd (hinj h) (by decide)
  have hX : ∀ w ∈ (lineX : Set (Fin 1 ⊕ Fin 1 → ZMod 2)), w = 0 ∨ w = ex1 :=
    fun w hw => plusOne_lineX w hw
  have hY : ∀ w ∈ lineY, w = 0 ∨ w = ey1 := fun w hw => plusOne_lineY w hw
  have memX : ∀ w, w = 0 ∨ w = ex1 → InX w := by
    rintro w (rfl | rfl) <;> decide
  have memY : ∀ w, w = 0 ∨ w = ey1 → InY w := by
    rintro w (rfl | rfl) <;> decide
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · exact absurd (hx.trans hy.symm) hxy
    · left
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · rcases hX w hw with rfl | rfl
        · exact memX _ (Or.inl hf0)
        · exact memX _ (Or.inr hx)
      · rcases hY w hw with rfl | rfl
        · exact memY _ (Or.inl hf0)
        · exact memY _ (Or.inr hy)
  · rcases hy with hy | hy
    · right
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · rcases hX w hw with rfl | rfl
        · exact memY _ (Or.inl hf0)
        · exact memY _ (Or.inr hx)
      · rcases hY w hw with rfl | rfl
        · exact memX _ (Or.inl hf0)
        · exact memX _ (Or.inr hy)
    · exact absurd (hx.trans hy.symm) hxy

@[expose] def planeOne : AddSubgroup (Fin 2 ⊕ Fin 2 → ZMod 2) where
  carrier := {w | w (Sum.inl 1) = w (Sum.inl 0) + w (Sum.inr 0) ∧
    w (Sum.inr 1) = w (Sum.inl 0) + w (Sum.inr 0)}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Pi.add_apply] at ha hb ⊢
    refine ⟨?_, ?_⟩
    · rw [ha.1, hb.1]; ring
    · rw [ha.2, hb.2]; ring
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, Pi.neg_apply] at ha ⊢
    refine ⟨?_, ?_⟩
    · rw [ha.1]; ring
    · rw [ha.2]; ring

theorem mem_planeOne {w : Fin 2 ⊕ Fin 2 → ZMod 2} :
    w ∈ planeOne ↔ (w (Sum.inl 1) = w (Sum.inl 0) + w (Sum.inr 0) ∧
      w (Sum.inr 1) = w (Sum.inl 0) + w (Sum.inr 0)) := Iff.rfl

abbrev planeTwo : Set (Fin 2 ⊕ Fin 2 → ZMod 2) :=
  {w | w (Sum.inr 0) = w (Sum.inl 0) ∧ w (Sum.inl 0) = w (Sum.inl 1) + w (Sum.inr 1)}

@[expose] def a1 : Fin 2 ⊕ Fin 2 → ZMod 2 := Sum.elim ![1, 0] ![1, 0]

@[expose] def a2 : Fin 2 ⊕ Fin 2 → ZMod 2 := Sum.elim ![1, 1] ![0, 1]

@[expose] def b1 : Fin 2 ⊕ Fin 2 → ZMod 2 := Sum.elim ![1, 1] ![1, 0]

@[expose] def b2 : Fin 2 ⊕ Fin 2 → ZMod 2 := Sum.elim ![1, 0] ![1, 1]

abbrev InOne (w : Fin 2 ⊕ Fin 2 → ZMod 2) : Prop :=
  w (Sum.inl 1) = w (Sum.inl 0) + w (Sum.inr 0) ∧ w (Sum.inr 1) = w (Sum.inl 0) + w (Sum.inr 0)

abbrev InTwo (w : Fin 2 ⊕ Fin 2 → ZMod 2) : Prop :=
  w (Sum.inr 0) = w (Sum.inl 0) ∧ w (Sum.inl 0) = w (Sum.inl 1) + w (Sum.inr 1)

set_option synthInstance.maxSize 1024 in
theorem plusTwo_same : ∀ x y : Fin 2 ⊕ Fin 2 → ZMod 2, plusQuadForm 2 x = 1 →
    plusQuadForm 2 y = 1 → plusQuadForm 2 (x + y) = 1 →
    (InOne x ∧ InOne y) ∨ (InTwo x ∧ InTwo y) := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
theorem plusTwo_diff : ∀ x y : Fin 2 ⊕ Fin 2 → ZMod 2, plusQuadForm 2 x = 1 →
    plusQuadForm 2 y = 1 → plusQuadForm 2 (x + y) = 0 → x ≠ y →
    (InOne x ∧ InTwo y) ∨ (InTwo x ∧ InOne y) := by
  decide +kernel

theorem plusTwo_meet : ∀ x : Fin 2 ⊕ Fin 2 → ZMod 2, InOne x → InTwo x → x = 0 := by
  decide +kernel

theorem plusTwo_planeOne : ∀ w : Fin 2 ⊕ Fin 2 → ZMod 2, InOne w →
    w = 0 ∨ w = a1 ∨ w = a2 ∨ w = a1 + a2 := by
  decide +kernel

theorem plusTwo_planeTwo : ∀ w : Fin 2 ⊕ Fin 2 → ZMod 2, InTwo w →
    w = 0 ∨ w = b1 ∨ w = b2 ∨ w = b1 + b2 := by
  decide +kernel

theorem inOne_add {x y : Fin 2 ⊕ Fin 2 → ZMod 2} (hx : InOne x) (hy : InOne y) : InOne (x + y) :=
  planeOne.add_mem hx hy

theorem inTwo_add {x y : Fin 2 ⊕ Fin 2 → ZMod 2} (hx : InTwo x) (hy : InTwo y) :
    InTwo (x + y) := by
  simp only [InTwo, Pi.add_apply] at hx hy ⊢
  refine ⟨?_, ?_⟩
  · rw [hx.1, hy.1]
  · rw [hx.2, hy.2]; ring

theorem plusTwo_type (g : GL (Fin 2 ⊕ Fin 2) (ZMod 2))
    (hg : ∀ v, plusQuadForm 2 ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ v) =
      plusQuadForm 2 v) :
    (MapsIn g (planeOne : Set _) planeOne ∧ MapsIn g planeTwo planeTwo) ∨
      (MapsIn g (planeOne : Set _) planeTwo ∧ MapsIn g planeTwo planeOne) := by
  let f := fun w : Fin 2 ⊕ Fin 2 → ZMod 2 =>
    (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ w
  have hinj : Function.Injective f := mulVec_injective g
  have hf0 : f 0 = 0 := mulVec_zero _
  have hadd : ∀ x y, f (x + y) = f x + f y := fun x y => mulVec_add _ x y
  have hQ : ∀ v, plusQuadForm 2 (f v) = plusQuadForm 2 v := hg
  have sA := plusTwo_same (f a1) (f a2) (by rw [hQ]; decide) (by rw [hQ]; decide)
    (by rw [← hadd, hQ]; decide)
  have sB := plusTwo_same (f b1) (f b2) (by rw [hQ]; decide) (by rw [hQ]; decide)
    (by rw [← hadd, hQ]; decide)
  have d11 := plusTwo_diff (f a1) (f b1) (by rw [hQ]; decide) (by rw [hQ]; decide)
    (by rw [← hadd, hQ]; decide) (fun h => absurd (hinj h) (by decide))
  have hne : ∀ x : Fin 2 ⊕ Fin 2 → ZMod 2, plusQuadForm 2 x = 1 → x ≠ 0 := fun x hx h => by
    rw [h] at hx
    exact absurd hx (by decide)
  have hfa1 : f a1 ≠ 0 := hne (f a1) (by rw [hQ]; decide)
  have hfb1 : f b1 ≠ 0 := hne (f b1) (by rw [hQ]; decide)
  have hOne : ∀ w ∈ (planeOne : Set (Fin 2 ⊕ Fin 2 → ZMod 2)),
      w = 0 ∨ w = a1 ∨ w = a2 ∨ w = a1 + a2 := fun w hw => plusTwo_planeOne w hw
  have hTwo : ∀ w ∈ planeTwo, w = 0 ∨ w = b1 ∨ w = b2 ∨ w = b1 + b2 :=
    fun w hw => plusTwo_planeTwo w hw
  have hz1 : InOne 0 := planeOne.zero_mem
  have hz2 : InTwo 0 := by decide
  have mapOne : ∀ P : (Fin 2 ⊕ Fin 2 → ZMod 2) → Prop, P 0 → (∀ x y, P x → P y → P (x + y)) →
      P (f a1) → P (f a2) → ∀ w ∈ (planeOne : Set (Fin 2 ⊕ Fin 2 → ZMod 2)), P (f w) := by
    intro P h0 hP h1 h2 w hw
    rcases hOne w hw with rfl | rfl | rfl | rfl
    · rw [hf0]; exact h0
    · exact h1
    · exact h2
    · rw [hadd]; exact hP _ _ h1 h2
  have mapTwo : ∀ P : (Fin 2 ⊕ Fin 2 → ZMod 2) → Prop, P 0 → (∀ x y, P x → P y → P (x + y)) →
      P (f b1) → P (f b2) → ∀ w ∈ planeTwo, P (f w) := by
    intro P h0 hP h1 h2 w hw
    rcases hTwo w hw with rfl | rfl | rfl | rfl
    · rw [hf0]; exact h0
    · exact h1
    · exact h2
    · rw [hadd]; exact hP _ _ h1 h2
  have i1 : ∀ x y, InOne x → InOne y → InOne (x + y) := fun _ _ => inOne_add
  have i2 : ∀ x y, InTwo x → InTwo y → InTwo (x + y) := fun _ _ => inTwo_add
  rcases d11 with ⟨ha, hb⟩ | ⟨ha, hb⟩
  ·
    have hA : InOne (f a1) ∧ InOne (f a2) := by
      rcases sA with h | h
      · exact h
      · exact absurd (plusTwo_meet _ ha h.1) hfa1
    have hB : InTwo (f b1) ∧ InTwo (f b2) := by
      rcases sB with h | h
      · exact absurd (plusTwo_meet _ h.1 hb) hfb1
      · exact h
    exact Or.inl ⟨mapOne InOne hz1 i1 hA.1 hA.2, mapTwo InTwo hz2 i2 hB.1 hB.2⟩
  ·
    have hA : InTwo (f a1) ∧ InTwo (f a2) := by
      rcases sA with h | h
      · exact absurd (plusTwo_meet _ h.1 ha) hfa1
      · exact h
    have hB : InOne (f b1) ∧ InOne (f b2) := by
      rcases sB with h | h
      · exact h
      · exact absurd (plusTwo_meet _ hb h.1) hfb1
    exact Or.inr ⟨mapOne InTwo hz2 i2 hA.1 hA.2, mapTwo InOne hz1 i1 hB.1 hB.2⟩

variable {G : Type*} [Group G] [Finite G]

theorem false_of_isOmegaPlusType_one {L : Subgroup G} (hL : IsShort L)
    (h : IsOmegaPlusType L 1) : False := by
  refine false_of_invariant_addSubgroup hL (isMatrixType_of_isOmegaPlusType h) lineX ?_ ?_ ?_
  · intro hbot
    have : ex1 ∈ lineX := mem_lineX.2 (by decide)
    rw [hbot, AddSubgroup.mem_bot] at this
    exact absurd this (by decide)
  · intro htop
    have : ey1 ∈ lineX := by rw [htop]; exact AddSubgroup.mem_top _
    exact absurd (mem_lineX.1 this) (by decide)
  · intro g hg w hw
    exact mapsTo_of_mem_commutator (lineX : Set _) lineY (a := ex1) (mem_lineX.2 (by decide))
      (by decide) (fun g hg => plusOne_type g (isometry_of_mem_closure hg)) g hg w hw

theorem false_of_isOmegaPlusType_two {L : Subgroup G} (hL : IsShort L)
    (h : IsOmegaPlusType L 2) : False := by
  refine false_of_invariant_addSubgroup hL (isMatrixType_of_isOmegaPlusType h) planeOne ?_ ?_ ?_
  · intro hbot
    have : a1 ∈ planeOne := mem_planeOne.2 (by decide)
    rw [hbot, AddSubgroup.mem_bot] at this
    exact absurd this (by decide)
  · intro htop
    have : b1 ∈ planeOne := by rw [htop]; exact AddSubgroup.mem_top _
    exact absurd (mem_planeOne.1 this) (by decide)
  · intro g hg w hw
    exact mapsTo_of_mem_commutator (planeOne : Set _) planeTwo (a := a1)
      (mem_planeOne.2 (by decide)) (by decide)
      (fun g hg => plusTwo_type g (isometry_of_mem_closure hg)) g hg w hw

theorem false_of_isOmegaPlusType_le_two {L : Subgroup G} (hL : IsShort L) {m : ℕ} (hm : m ≤ 2)
    (h : IsOmegaPlusType L m) : False := by
  interval_cases m
  · exact false_of_isMatrixType_of_isEmpty hL (isMatrixType_of_isOmegaPlusType h)
  · exact false_of_isOmegaPlusType_one hL h
  · exact false_of_isOmegaPlusType_two hL h

end CFSG.RankThree.PartTwo.Sec19.SimsItem316Small

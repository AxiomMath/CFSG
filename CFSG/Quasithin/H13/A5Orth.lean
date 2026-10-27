module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Quasithin.H13.A5.Orth

abbrev V4 := Fin 4 → ZMod 2

@[expose] def q (v : V4) : ZMod 2 := v 0 + v 1 + v 0 * v 1 + (v 2 + v 3 + v 2 * v 3)

@[expose] def app (c : Fin 4 → V4) (v : V4) : V4 := v 0 • c 0 + v 1 • c 1 + v 2 • c 2 + v 3 • c 3

@[expose] def comp (c d : Fin 4 → V4) : Fin 4 → V4 := fun j => app c (d j)

@[expose] def idc : Fin 4 → V4 := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]

abbrev OC :=
  Σ c0 : {c : V4 // q c = 1},
  Σ c1 : {c : V4 // q c = 1 ∧ q (c0.1 + c) = 1},
  Σ c2 : {c : V4 // q c = 1 ∧ q (c0.1 + c) = 0 ∧ q (c1.1 + c) = 0},
  {c : V4 // q c = 1 ∧ q (c0.1 + c) = 0 ∧ q (c1.1 + c) = 0 ∧ q (c2.1 + c) = 1}

@[expose] def OC.cols (x : OC) : Fin 4 → V4 := ![x.1.1, x.2.1.1, x.2.2.1.1, x.2.2.2.1]

theorem card_OC : Fintype.card OC = 72 := by decide +kernel

theorem OC_props : ∀ x : OC, (∀ v : V4, q (app x.cols v) = q v) ∧
    ∀ v : V4, app x.cols v = 0 → v = 0 := by
  decide +kernel

@[expose] def Ord3 (c : Fin 4 → V4) : Prop := c ≠ idc ∧ comp c (comp c c) = idc

instance : DecidablePred Ord3 := fun c =>
  inferInstanceAs (Decidable (c ≠ idc ∧ comp c (comp c c) = idc))

@[expose] def NormC (c a : Fin 4 → V4) : Prop := comp a c = comp c a ∨ comp a c = comp (comp c c) a

instance (c : Fin 4 → V4) : DecidablePred (NormC c) := fun a =>
  inferInstanceAs (Decidable (comp a c = comp c a ∨ comp a c = comp (comp c c) a))

@[expose] def InvC (c t : Fin 4 → V4) : Prop := t ≠ idc ∧ comp t t = idc ∧ comp t c = comp c t

instance (c : Fin 4 → V4) : DecidablePred (InvC c) := fun t =>
  inferInstanceAs (Decidable (t ≠ idc ∧ comp t t = idc ∧ comp t c = comp c t))

@[expose] def ConjIn (t₁ t₂ a : Fin 4 → V4) : Prop :=
  comp a t₁ = comp idc a ∨ comp a t₁ = comp t₁ a ∨ comp a t₁ = comp t₂ a ∨
    comp a t₁ = comp (comp t₁ t₂) a ∨ comp a t₁ = comp (comp t₂ t₁) a ∨
    comp a t₁ = comp (comp t₁ (comp t₂ t₁)) a

instance (t₁ t₂ : Fin 4 → V4) : DecidablePred (ConjIn t₁ t₂) := fun a =>
  inferInstanceAs (Decidable (comp a t₁ = comp idc a ∨ comp a t₁ = comp t₁ a ∨
    comp a t₁ = comp t₂ a ∨ comp a t₁ = comp (comp t₁ t₂) a ∨
    comp a t₁ = comp (comp t₂ t₁) a ∨ comp a t₁ = comp (comp t₁ (comp t₂ t₁)) a))

@[expose] def NormS3 (c t₁ t₂ : Fin 4 → V4) : Prop := ∀ a : OC, NormC c a.cols → ConjIn t₁ t₂ a.cols

instance (c t₁ t₂ : Fin 4 → V4) : Decidable (NormS3 c t₁ t₂) :=
  inferInstanceAs (Decidable (∀ a : OC, NormC c a.cols → ConjIn t₁ t₂ a.cols))

@[expose] def NormS3All (c t₁ : Fin 4 → V4) : Prop :=
  ∀ t₂ : OC, InvC c t₂.cols → Ord3 (comp t₁ t₂.cols) → NormS3 c t₁ t₂.cols

instance (c t₁ : Fin 4 → V4) : Decidable (NormS3All c t₁) :=
  inferInstanceAs (Decidable (∀ t₂ : OC, InvC c t₂.cols → Ord3 (comp t₁ t₂.cols) →
    NormS3 c t₁ t₂.cols))

@[expose] def NormS3AllAll (c : Fin 4 → V4) : Prop :=
  ∀ t₁ : OC, InvC c t₁.cols → NormS3All c t₁.cols

instance (c : Fin 4 → V4) : Decidable (NormS3AllAll c) :=
  inferInstanceAs (Decidable (∀ t₁ : OC, InvC c t₁.cols → NormS3All c t₁.cols))

theorem normalizes_S3 : ∀ c : OC, Ord3 c.cols → NormS3AllAll c.cols := by
  decide +kernel

@[expose] def InS (t₁ t₂ x : Fin 4 → V4) : Prop :=
  x = idc ∨ x = t₁ ∨ x = t₂ ∨ x = comp t₁ t₂ ∨ x = comp t₂ t₁ ∨ x = comp t₁ (comp t₂ t₁)

instance (t₁ t₂ : Fin 4 → V4) : DecidablePred (InS t₁ t₂) := fun x =>
  inferInstanceAs (Decidable (x = idc ∨ x = t₁ ∨ x = t₂ ∨ x = comp t₁ t₂ ∨ x = comp t₂ t₁ ∨
    x = comp t₁ (comp t₂ t₁)))

@[expose] def InCS (c t₁ t₂ x : Fin 4 → V4) : Prop :=
  InS t₁ t₂ x ∨ InS t₁ t₂ (comp (comp c c) x) ∨ InS t₁ t₂ (comp c x)

instance (c t₁ t₂ : Fin 4 → V4) : DecidablePred (InCS c t₁ t₂) := fun x =>
  inferInstanceAs (Decidable (InS t₁ t₂ x ∨ InS t₁ t₂ (comp (comp c c) x) ∨
    InS t₁ t₂ (comp c x)))

@[expose] def CentS3 (c t₁ t₂ : Fin 4 → V4) : Prop :=
  ∀ b : OC, comp b.cols c = comp c b.cols → InCS c t₁ t₂ b.cols

instance (c t₁ t₂ : Fin 4 → V4) : Decidable (CentS3 c t₁ t₂) :=
  inferInstanceAs (Decidable (∀ b : OC, comp b.cols c = comp c b.cols → InCS c t₁ t₂ b.cols))

@[expose] def CentS3All (c t₁ : Fin 4 → V4) : Prop :=
  ∀ t₂ : OC, InvC c t₂.cols → Ord3 (comp t₁ t₂.cols) → CentS3 c t₁ t₂.cols

instance (c t₁ : Fin 4 → V4) : Decidable (CentS3All c t₁) :=
  inferInstanceAs (Decidable (∀ t₂ : OC, InvC c t₂.cols → Ord3 (comp t₁ t₂.cols) →
    CentS3 c t₁ t₂.cols))

@[expose] def CentS3AllAll (c : Fin 4 → V4) : Prop :=
  ∀ t₁ : OC, InvC c t₁.cols → CentS3All c t₁.cols

instance (c : Fin 4 → V4) : Decidable (CentS3AllAll c) :=
  inferInstanceAs (Decidable (∀ t₁ : OC, InvC c t₁.cols → CentS3All c t₁.cols))

theorem centralizer_S3 : ∀ c : OC, Ord3 c.cols → CentS3AllAll c.cols := by
  decide +kernel

theorem card_centralizer : ∀ c : OC, Ord3 c.cols →
    (Finset.univ.filter fun b : OC => comp b.cols c.cols = comp c.cols b.cols).card = 18 := by
  decide +kernel


theorem app_add (c : Fin 4 → V4) (v w : V4) : app c (v + w) = app c v + app c w := by
  funext i
  simp only [app, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem app_zero (c : Fin 4 → V4) : app c 0 = 0 := by
  funext i
  simp only [app, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul, add_zero]

theorem app_idc : ∀ (c : Fin 4 → V4) (j : Fin 4), app c (idc j) = c j := by
  intro c j
  funext i
  fin_cases j <;> simp [app, idc]

theorem eq_sum_idc : ∀ v : V4, v = v 0 • idc 0 + v 1 • idc 1 + v 2 • idc 2 + v 3 • idc 3 := by
  decide +kernel

@[expose] def Oq : Subgroup (MulAut (Multiplicative V4)) where
  carrier := {α | ∀ v : V4, q (Multiplicative.toAdd (α (Multiplicative.ofAdd v))) = q v}
  mul_mem' := by
    intro α β hα hβ v
    simp only [Set.mem_ofPred_eq] at hα hβ ⊢
    rw [MulAut.mul_apply]
    have := hα (Multiplicative.toAdd (β (Multiplicative.ofAdd v)))
    rw [ofAdd_toAdd] at this
    rw [this, hβ]
  one_mem' := by
    intro v
    simp
  inv_mem' := by
    intro α hα v
    simp only [Set.mem_ofPred_eq] at hα ⊢
    have := hα (Multiplicative.toAdd (α⁻¹ (Multiplicative.ofAdd v)))
    rw [ofAdd_toAdd, ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply, toAdd_ofAdd] at this
    exact this.symm

@[expose] def colsOf (α : MulAut (Multiplicative V4)) : Fin 4 → V4 :=
  fun j => Multiplicative.toAdd (α (Multiplicative.ofAdd (idc j)))

theorem app_colsOf (α : MulAut (Multiplicative V4)) (v : V4) :
    Multiplicative.toAdd (α (Multiplicative.ofAdd v)) = app (colsOf α) v := by
  have hadd : ∀ x y : V4, Multiplicative.toAdd (α (Multiplicative.ofAdd (x + y))) =
      Multiplicative.toAdd (α (Multiplicative.ofAdd x)) +
        Multiplicative.toAdd (α (Multiplicative.ofAdd y)) := by
    intro x y
    rw [ofAdd_add, map_mul, toAdd_mul]
  have hsmul : ∀ (r : ZMod 2) (x : V4), Multiplicative.toAdd (α (Multiplicative.ofAdd (r • x))) =
      r • Multiplicative.toAdd (α (Multiplicative.ofAdd x)) := by
    intro r x
    rcases (by decide : ∀ r : ZMod 2, r = 0 ∨ r = 1) r with rfl | rfl
    · rw [zero_smul, zero_smul, ofAdd_zero, map_one, toAdd_one]
    · rw [one_smul, one_smul]
  conv_lhs => rw [eq_sum_idc v]
  rw [hadd, hadd, hadd, hsmul, hsmul, hsmul, hsmul]
  rfl

theorem colsOf_mul (α β : MulAut (Multiplicative V4)) :
    colsOf (α * β) = comp (colsOf α) (colsOf β) := by
  funext j
  simp only [colsOf, comp, MulAut.mul_apply]
  rw [← app_colsOf, ofAdd_toAdd]

theorem colsOf_one : colsOf 1 = idc := by
  funext j
  simp [colsOf]

theorem colsOf_injective : Function.Injective colsOf := by
  intro α β h
  apply MulEquiv.ext
  intro x
  apply Multiplicative.toAdd.injective
  rw [← ofAdd_toAdd x, app_colsOf, app_colsOf, h]

@[expose] noncomputable def toOC (α : ↥Oq) : OC :=
  have hq : ∀ v, q (app (colsOf α) v) = q v := fun v => by rw [← app_colsOf]; exact α.2 v
  have h1 : ∀ j, q (colsOf α j) = q (idc j) := fun j => by rw [← app_idc (colsOf α) j, hq]
  have h2 : ∀ i j, q (colsOf α i + colsOf α j) = q (idc i + idc j) := fun i j => by
    rw [← app_idc (colsOf α) i, ← app_idc (colsOf α) j, ← app_add, hq]
  ⟨⟨colsOf α 0, (h1 0).trans (by decide)⟩,
    ⟨⟨colsOf α 1, (h1 1).trans (by decide), (h2 0 1).trans (by decide)⟩,
      ⟨⟨colsOf α 2, (h1 2).trans (by decide), (h2 0 2).trans (by decide),
        (h2 1 2).trans (by decide)⟩,
        ⟨colsOf α 3, (h1 3).trans (by decide), (h2 0 3).trans (by decide),
          (h2 1 3).trans (by decide), (h2 2 3).trans (by decide)⟩⟩⟩⟩

theorem toOC_cols (α : ↥Oq) : (toOC α).cols = colsOf α := by
  funext j
  fin_cases j <;> rfl

theorem toOC_injective : Function.Injective toOC := by
  intro α β h
  have := congrArg OC.cols h
  rw [toOC_cols, toOC_cols] at this
  exact Subtype.ext (colsOf_injective this)

@[expose] noncomputable def ofOC (x : OC) : MulAut (Multiplicative V4) :=
  let f : Multiplicative V4 →* Multiplicative V4 :=
    { toFun := fun v => Multiplicative.ofAdd (app x.cols (Multiplicative.toAdd v))
      map_one' := by
        show Multiplicative.ofAdd (app x.cols 0) = 1
        rw [app_zero]
        rfl
      map_mul' := fun v w => by
        show Multiplicative.ofAdd (app x.cols (Multiplicative.toAdd v + Multiplicative.toAdd w)) = _
        rw [app_add]
        rfl }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have h0 : app x.cols (Multiplicative.toAdd v) = 0 := congrArg Multiplicative.toAdd hv
    have := (OC_props x).2 _ h0
    exact Multiplicative.toAdd.injective (by rw [this]; rfl)
  MulEquiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)

theorem ofOC_mem (x : OC) : ofOC x ∈ Oq := by
  intro v
  show q (app x.cols (Multiplicative.toAdd (Multiplicative.ofAdd v))) = q v
  exact (OC_props x).1 v

theorem colsOf_ofOC (x : OC) : colsOf (ofOC x) = x.cols := by
  funext j
  show app x.cols (idc j) = x.cols j
  exact app_idc _ _

theorem toOC_surjective : Function.Surjective toOC := by
  intro x
  refine ⟨⟨ofOC x, ofOC_mem x⟩, ?_⟩
  have hcols : (toOC ⟨ofOC x, ofOC_mem x⟩).cols = x.cols := by
    rw [toOC_cols]
    exact colsOf_ofOC x
  obtain ⟨⟨a0, ha0⟩, ⟨a1, ha1⟩, ⟨a2, ha2⟩, ⟨a3, ha3⟩⟩ := x
  generalize hy : toOC ⟨ofOC _, ofOC_mem _⟩ = y at hcols
  obtain ⟨⟨b0, hb0⟩, ⟨b1, hb1⟩, ⟨b2, hb2⟩, ⟨b3, hb3⟩⟩ := y
  have e0 : b0 = a0 := congrFun hcols 0
  have e1 : b1 = a1 := congrFun hcols 1
  have e2 : b2 = a2 := congrFun hcols 2
  have e3 : b3 = a3 := congrFun hcols 3
  subst e0 e1 e2 e3
  rfl

theorem card_Oq : Nat.card Oq = 72 := by
  rw [← card_OC, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.ofBijective _ ⟨toOC_injective, toOC_surjective⟩)


theorem toOC_mk_cols (α : MulAut (Multiplicative V4)) (h : α ∈ Oq) :
    (toOC ⟨α, h⟩).cols = colsOf α :=
  toOC_cols _

theorem colsOf_eq_iff {α β : MulAut (Multiplicative V4)} : colsOf α = colsOf β ↔ α = β :=
  colsOf_injective.eq_iff

theorem ord3_colsOf_iff (α : MulAut (Multiplicative V4)) :
    Ord3 (colsOf α) ↔ α ≠ 1 ∧ α ^ 3 = 1 := by
  unfold Ord3
  simp only [← colsOf_one, ← colsOf_mul, ne_eq, colsOf_eq_iff, pow_three]

theorem invC_colsOf_iff (c t : MulAut (Multiplicative V4)) :
    InvC (colsOf c) (colsOf t) ↔ t ≠ 1 ∧ t * t = 1 ∧ t * c = c * t := by
  unfold InvC
  simp only [← colsOf_one, ← colsOf_mul, ne_eq, colsOf_eq_iff]

theorem normC_colsOf_iff (c a : MulAut (Multiplicative V4)) :
    NormC (colsOf c) (colsOf a) ↔ a * c = c * a ∨ a * c = c * c * a := by
  unfold NormC
  simp only [← colsOf_mul, colsOf_eq_iff]

@[expose] def InSA (t₁ t₂ x : MulAut (Multiplicative V4)) : Prop :=
  x = 1 ∨ x = t₁ ∨ x = t₂ ∨ x = t₁ * t₂ ∨ x = t₂ * t₁ ∨ x = t₁ * (t₂ * t₁)

theorem inS_colsOf_iff (t₁ t₂ x : MulAut (Multiplicative V4)) :
    InS (colsOf t₁) (colsOf t₂) (colsOf x) ↔ InSA t₁ t₂ x := by
  unfold InS InSA
  simp only [← colsOf_one, ← colsOf_mul, colsOf_eq_iff]

theorem conjIn_colsOf_iff (t₁ t₂ a : MulAut (Multiplicative V4)) :
    ConjIn (colsOf t₁) (colsOf t₂) (colsOf a) ↔ InSA t₁ t₂ (a * t₁ * a⁻¹) := by
  unfold ConjIn InSA
  simp only [← colsOf_one, ← colsOf_mul, colsOf_eq_iff]
  simp only [mul_inv_eq_iff_eq_mul]

theorem normalizes_S3_aut {c t₁ t₂ a : MulAut (Multiplicative V4)} (hc : c ∈ Oq)
    (h₁ : t₁ ∈ Oq) (h₂ : t₂ ∈ Oq) (ha : a ∈ Oq) (h3 : c ≠ 1 ∧ c ^ 3 = 1)
    (ht₁ : t₁ ≠ 1 ∧ t₁ * t₁ = 1 ∧ t₁ * c = c * t₁) (ht₂ : t₂ ≠ 1 ∧ t₂ * t₂ = 1 ∧ t₂ * c = c * t₂)
    (h12 : t₁ * t₂ ≠ 1 ∧ (t₁ * t₂) ^ 3 = 1) (hac : a * c = c * a ∨ a * c = c * c * a) :
    InSA t₁ t₂ (a * t₁ * a⁻¹) := by
  have key := normalizes_S3 (toOC ⟨c, hc⟩)
    (by rw [toOC_mk_cols, ord3_colsOf_iff]; exact h3) (toOC ⟨t₁, h₁⟩)
    (by rw [toOC_mk_cols, toOC_mk_cols, invC_colsOf_iff]; exact ht₁) (toOC ⟨t₂, h₂⟩)
    (by rw [toOC_mk_cols, toOC_mk_cols, invC_colsOf_iff]; exact ht₂)
    (by rw [toOC_mk_cols, toOC_mk_cols, ← colsOf_mul, ord3_colsOf_iff]; exact h12) (toOC ⟨a, ha⟩)
    (by rw [toOC_mk_cols, toOC_mk_cols, normC_colsOf_iff]; exact hac)
  rwa [toOC_mk_cols, toOC_mk_cols, toOC_mk_cols, conjIn_colsOf_iff] at key

theorem centralizer_S3_aut {c t₁ t₂ b : MulAut (Multiplicative V4)} (hc : c ∈ Oq)
    (h₁ : t₁ ∈ Oq) (h₂ : t₂ ∈ Oq) (hb : b ∈ Oq) (h3 : c ≠ 1 ∧ c ^ 3 = 1)
    (ht₁ : t₁ ≠ 1 ∧ t₁ * t₁ = 1 ∧ t₁ * c = c * t₁) (ht₂ : t₂ ≠ 1 ∧ t₂ * t₂ = 1 ∧ t₂ * c = c * t₂)
    (h12 : t₁ * t₂ ≠ 1 ∧ (t₁ * t₂) ^ 3 = 1) (hbc : b * c = c * b) :
    InSA t₁ t₂ b ∨ InSA t₁ t₂ (c * c * b) ∨ InSA t₁ t₂ (c * b) := by
  have key := centralizer_S3 (toOC ⟨c, hc⟩)
    (by rw [toOC_mk_cols, ord3_colsOf_iff]; exact h3) (toOC ⟨t₁, h₁⟩)
    (by rw [toOC_mk_cols, toOC_mk_cols, invC_colsOf_iff]; exact ht₁) (toOC ⟨t₂, h₂⟩)
    (by rw [toOC_mk_cols, toOC_mk_cols, invC_colsOf_iff]; exact ht₂)
    (by rw [toOC_mk_cols, toOC_mk_cols, ← colsOf_mul, ord3_colsOf_iff]; exact h12) (toOC ⟨b, hb⟩)
    (by rw [toOC_mk_cols, toOC_mk_cols, ← colsOf_mul, ← colsOf_mul, colsOf_eq_iff]; exact hbc)
  rw [toOC_mk_cols, toOC_mk_cols, toOC_mk_cols, toOC_mk_cols] at key
  unfold InCS at key
  rwa [← colsOf_mul, ← colsOf_mul, ← colsOf_mul, inS_colsOf_iff, inS_colsOf_iff,
    inS_colsOf_iff] at key

theorem card_centralizer_aut {c : MulAut (Multiplicative V4)} (hc : c ∈ Oq)
    (h3 : c ≠ 1 ∧ c ^ 3 = 1) :
    Nat.card ↥(Oq ⊓ Subgroup.centralizer ({c} : Set (MulAut (Multiplicative V4)))) = 18 := by
  set c0 := toOC ⟨c, hc⟩ with hc0
  have e1 : ↥(Oq ⊓ Subgroup.centralizer ({c} : Set (MulAut (Multiplicative V4)))) ≃
      {α : ↥Oq // (α : MulAut (Multiplicative V4)) * c = c * α} :=
    { toFun := fun β => ⟨⟨β, β.2.1⟩, Subgroup.mem_centralizer_singleton_iff.mp β.2.2⟩
      invFun := fun α => ⟨α.1, α.1.2, Subgroup.mem_centralizer_singleton_iff.mpr α.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e2 : {α : ↥Oq // (α : MulAut (Multiplicative V4)) * c = c * α} ≃
      {x : OC // comp x.cols c0.cols = comp c0.cols x.cols} :=
    Equiv.subtypeEquiv (Equiv.ofBijective toOC ⟨toOC_injective, toOC_surjective⟩) fun α => by
      show _ ↔ comp (toOC α).cols c0.cols = comp c0.cols (toOC α).cols
      rw [toOC_cols, hc0, toOC_mk_cols, ← colsOf_mul, ← colsOf_mul, colsOf_eq_iff]
  rw [Nat.card_congr (e1.trans e2), Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_centralizer c0 (by rw [hc0, toOC_mk_cols, ord3_colsOf_iff]; exact h3)

end CFSG.Quasithin.H13.A5.Orth

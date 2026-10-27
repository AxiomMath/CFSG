module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.Actions

import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.Quasithin

open scoped Pointwise

namespace XMod

variable (A : Type*) [Group A] {Q : Type*} [CommGroup Q] [MulDistribMulAction A Q]

@[expose] def IsInv (L : Subgroup Q) : Prop := ∀ a : A, ∀ l ∈ L, a • l ∈ L

@[expose] def fixed (L : Subgroup Q) : Subgroup Q where
  carrier := {l | l ∈ L ∧ ∀ a : A, a • l = l}
  one_mem' := ⟨L.one_mem, fun a => smul_one a⟩
  mul_mem' := fun {x y} hx hy => ⟨L.mul_mem hx.1 hy.1, fun a => by rw [smul_mul', hx.2 a, hy.2 a]⟩
  inv_mem' := fun {x} hx => ⟨L.inv_mem hx.1, fun a => by rw [smul_inv', hx.2 a]⟩

@[expose] def commOf (L : Subgroup Q) : Subgroup Q :=
  Subgroup.closure {c | ∃ a : A, ∃ l ∈ L, c = (a • l) * l⁻¹}

@[expose] def IsIrrSec (C L : Subgroup Q) : Prop :=
  C < L ∧ ∀ J : Subgroup Q, IsInv A J → C ≤ J → J ≤ L → J = C ∨ J = L

@[expose] def IsIrr (L : Subgroup Q) : Prop := IsInv A L ∧ IsIrrSec A ⊥ L

@[expose] def IsIrrPlus (I : Subgroup Q) : Prop :=
  IsInv A I ∧ commOf A I = I ∧ IsIrrSec A (fixed A I) I

@[expose] def Iso (L L' : Subgroup Q) : Prop :=
  ∃ φ : ↥L ≃* ↥L', ∀ (a : A) (l l' : ↥L), a • (l : Q) = (l' : Q) →
    a • ((φ l : ↥L') : Q) = ((φ l' : ↥L') : Q)

@[expose] def IsHomComp (M L : Subgroup Q) : Prop :=
  IsIrr A L ∧ L ≤ M ∧ ∀ L' : Subgroup Q, L' ≤ M → IsIrr A L' → Iso A L' L → L' ≤ L

@[expose] def IsTwoReduced (L : Subgroup Q) : Prop :=
  ∀ D : Subgroup A, D.Normal → (∀ d ∈ D, ∃ k : ℕ, ∀ l ∈ L, (d ^ 2 ^ k) • l = l) →
    ∀ d ∈ D, ∀ l ∈ L, d • l = l

variable {A}

theorem mem_fixed {L : Subgroup Q} {q : Q} : q ∈ fixed A L ↔ q ∈ L ∧ ∀ a : A, a • q = q := Iff.rfl

theorem fixed_le (L : Subgroup Q) : fixed A L ≤ L := fun _ h => h.1

theorem fixed_mono {L L' : Subgroup Q} (h : L ≤ L') : fixed A L ≤ fixed A L' :=
  fun _ hq => ⟨h hq.1, hq.2⟩

theorem fixed_top_eq_top_iff : fixed A (⊤ : Subgroup Q) = ⊤ ↔ ∀ (a : A) (q : Q), a • q = q := by
  constructor
  · intro h a q
    have : q ∈ fixed A (⊤ : Subgroup Q) := by rw [h]; trivial
    exact this.2 a
  · intro h
    rw [eq_top_iff]
    exact fun q _ => ⟨trivial, fun a => h a q⟩

theorem isInv_fixed (L : Subgroup Q) : IsInv A (fixed A L) := fun a l hl => by
  rw [hl.2 a]; exact hl

theorem isInv_top : IsInv A (⊤ : Subgroup Q) := fun _ _ _ => trivial

theorem isInv_bot : IsInv A (⊥ : Subgroup Q) := fun a l hl => by
  rw [Subgroup.mem_bot] at hl ⊢; rw [hl]; exact smul_one a

theorem IsInv.inf {L L' : Subgroup Q} (h : IsInv A L) (h' : IsInv A L') : IsInv A (L ⊓ L') :=
  fun a l hl => ⟨h a l hl.1, h' a l hl.2⟩

theorem IsInv.sup {L L' : Subgroup Q} (h : IsInv A L) (h' : IsInv A L') : IsInv A (L ⊔ L') := by
  intro a l hl
  obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hl
  rw [smul_mul']
  exact Subgroup.mul_mem_sup (h a x hx) (h' a y hy)

theorem isInv_iSup {ι : Sort*} {L : ι → Subgroup Q} (h : ∀ i, IsInv A (L i)) :
    IsInv A (⨆ i, L i) := by
  intro a l hl
  refine Subgroup.iSup_induction L (C := fun x => a • x ∈ ⨆ i, L i) hl
    (fun i x hx => Subgroup.mem_iSup_of_mem i (h i a x hx)) ?_ ?_
  · rw [smul_one]; exact one_mem _
  · intro x y hx hy
    rw [smul_mul']
    exact mul_mem hx hy

theorem mem_commOf_of_mem {L : Subgroup Q} (a : A) {l : Q} (hl : l ∈ L) :
    (a • l) * l⁻¹ ∈ commOf A L :=
  Subgroup.subset_closure ⟨a, l, hl, rfl⟩

theorem commOf_mono {L L' : Subgroup Q} (h : L ≤ L') : commOf A L ≤ commOf A L' :=
  Subgroup.closure_mono fun _ ⟨a, l, hl, hc⟩ => ⟨a, l, h hl, hc⟩

theorem commOf_le_of_isInv {L : Subgroup Q} (h : IsInv A L) : commOf A L ≤ L := by
  rw [commOf, Subgroup.closure_le]
  rintro _ ⟨a, l, hl, rfl⟩
  exact L.mul_mem (h a l hl) (L.inv_mem hl)

theorem commOf_le_iff {L M : Subgroup Q} :
    commOf A L ≤ M ↔ ∀ (a : A), ∀ l ∈ L, (a • l) * l⁻¹ ∈ M := by
  rw [commOf, Subgroup.closure_le]
  exact ⟨fun h a l hl => h ⟨a, l, hl, rfl⟩, fun h _ ⟨a, l, hl, hc⟩ => hc ▸ h a l hl⟩

theorem commOf_eq_bot_iff {L : Subgroup Q} :
    commOf A L = ⊥ ↔ L ≤ fixed A ⊤ := by
  rw [← le_bot_iff, commOf_le_iff]
  refine ⟨fun h l hl => ⟨trivial, fun a => ?_⟩, fun h a l hl => ?_⟩
  · have := h a l hl
    rwa [Subgroup.mem_bot, mul_inv_eq_one] at this
  · rw [Subgroup.mem_bot, mul_inv_eq_one]
    exact (h hl).2 a

theorem isInv_commOf (L : Subgroup Q) : IsInv A (commOf A L) := by
  intro a c hc
  induction hc using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨b, l, hl, rfl⟩ := hc
    have h1 : a • ((b • l) * l⁻¹) = (((a * b) • l) * l⁻¹) * ((a • l) * l⁻¹)⁻¹ := by
      rw [smul_mul', smul_inv', mul_smul]
      group
    rw [h1]
    exact mul_mem (mem_commOf_of_mem _ hl) (inv_mem (mem_commOf_of_mem _ hl))
  | one => rw [smul_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [smul_mul']; exact mul_mem hx hy
  | inv x _ hx => rw [smul_inv']; exact inv_mem hx

theorem Iso.refl (L : Subgroup Q) : Iso A L L := ⟨MulEquiv.refl _, fun _ _ _ h => h⟩

theorem Iso.trans {L L' L'' : Subgroup Q} (h : Iso A L L') (h' : Iso A L' L'') : Iso A L L'' := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨ψ, hψ⟩ := h'
  exact ⟨φ.trans ψ, fun a l l₂ hl => hψ a _ _ (hφ a l l₂ hl)⟩

theorem Iso.symm {L L' : Subgroup Q} (hL : IsInv A L) (h : Iso A L L') : Iso A L' L := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.symm, fun a l' l₂' hl => ?_⟩
  have hx : a • ((φ.symm l' : ↥L) : Q) ∈ L := hL a _ (φ.symm l').2
  have h1 := hφ a (φ.symm l') ⟨a • ((φ.symm l' : ↥L) : Q), hx⟩ rfl
  rw [MulEquiv.apply_symm_apply] at h1
  have h3 : φ ⟨a • ((φ.symm l' : ↥L) : Q), hx⟩ = l₂' := Subtype.ext (h1.symm.trans hl)
  have h4 : (⟨a • ((φ.symm l' : ↥L) : Q), hx⟩ : ↥L) = φ.symm l₂' := by
    rw [← h3, MulEquiv.symm_apply_apply]
  exact congrArg Subtype.val h4

theorem isHomComp_self {L : Subgroup Q} (hL : IsIrr A L) : IsHomComp A L L :=
  ⟨hL, le_rfl, fun _ hL' _ _ => hL'⟩

theorem commOf_sup_eq_of_le_fixed {L C : Subgroup Q} (hC : C ≤ fixed A ⊤) :
    commOf A (L ⊔ C) = commOf A L := by
  refine le_antisymm ?_ (commOf_mono le_sup_left)
  rw [commOf_le_iff]
  intro a l hl
  obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hl
  have hy' : a • y = y := (hC hy).2 a
  have h1 : (a • (x * y)) * (x * y)⁻¹ = (a • x) * x⁻¹ := by
    rw [smul_mul', hy']
    group
  rw [h1]
  exact mem_commOf_of_mem a hx

instance instSMulQuotFixed (L : Subgroup Q) : SMul A (Q ⧸ fixed A L) where
  smul a := QuotientGroup.map (fixed A L) (fixed A L) (MulDistribMulAction.toMonoidHom Q a)
    (fun n hn => by
      rw [Subgroup.mem_comap]
      change a • n ∈ fixed A L
      rw [hn.2 a]
      exact hn)

theorem smul_quotMk (L : Subgroup Q) (a : A) (q : Q) :
    a • (QuotientGroup.mk q : Q ⧸ fixed A L) = QuotientGroup.mk (a • q) := rfl

instance instMulDistribMulActionQuotFixed (L : Subgroup Q) :
    MulDistribMulAction A (Q ⧸ fixed A L) where
  one_smul q := QuotientGroup.induction_on q fun x => by rw [smul_quotMk, one_smul]
  mul_smul a b q := QuotientGroup.induction_on q fun x => by
    rw [smul_quotMk, smul_quotMk, smul_quotMk, mul_smul]
  smul_mul a p q := QuotientGroup.induction_on p fun x => QuotientGroup.induction_on q fun y => by
    rw [← QuotientGroup.mk_mul, smul_quotMk, smul_quotMk, smul_quotMk, smul_mul',
      QuotientGroup.mk_mul]
  smul_one a := by
    rw [← QuotientGroup.mk_one, smul_quotMk, smul_one]

end XMod

section Concrete

variable {G : Type*} [Group G] {V : Type*} [CommGroup V] [MulDistribMulAction G V]

abbrev modFix (X : Subgroup G) (W : Subgroup V) : Subgroup V := XMod.fixed ↥X W

abbrev modComm (X : Subgroup G) (W : Subgroup V) : Subgroup V := XMod.commOf ↥X W

abbrev IsModInv (X : Subgroup G) (W : Subgroup V) : Prop := XMod.IsInv ↥X W

@[expose] def Irr (X : Subgroup G) (W : Subgroup V) : Set (Subgroup V) :=
  {I | I ≤ W ∧ XMod.IsIrr ↥X I}

@[expose] def IrrPlus (X : Subgroup G) (W : Subgroup V) : Set (Subgroup V) :=
  {I | I ≤ W ∧ XMod.IsIrrPlus ↥X I}

@[expose] def tilde (X : Subgroup G) (W I : Subgroup V) : Subgroup (V ⧸ modFix X W) :=
  I.map (QuotientGroup.mk' (modFix X W))

@[expose] def IrrPlusOn (X : Subgroup G) (W : Subgroup V) (Y : Subgroup G) :
    Set (Subgroup V) :=
  {I | I ∈ IrrPlus X W ∧
    XMod.IsHomComp ↥X (tilde X W (⨆ y ∈ Y, y • I)) (tilde X W I)}

end Concrete

section Twist

variable {G : Type*} [Group G] {V : Type*} [CommGroup V] [MulDistribMulAction G V]
  {X : Subgroup G} {g : G}

theorem conj_mem_of_mem_normalizer (hg : g ∈ Subgroup.normalizer (X : Set G)) {x : G}
    (hx : x ∈ X) : g * x * g⁻¹ ∈ X :=
  (Subgroup.mem_normalizer_iff.1 hg x).1 hx

theorem inv_conj_mem_of_mem_normalizer (hg : g ∈ Subgroup.normalizer (X : Set G)) {x : G}
    (hx : x ∈ X) : g⁻¹ * x * g ∈ X :=
  (Subgroup.mem_normalizer_iff''.1 hg x).1 hx

theorem smul_smul_conj (g x : G) (q : V) : x • g • q = g • (g⁻¹ * x * g) • q := by
  rw [smul_smul, smul_smul]
  congr 1
  group

theorem inv_smul_smul_conj (g x : G) (q : V) : g⁻¹ • x • q = (g⁻¹ * x * g) • g⁻¹ • q := by
  rw [smul_smul, smul_smul]
  congr 1
  group

theorem fixes_iff_of_mem_normalizer (hg : g ∈ Subgroup.normalizer (X : Set G)) (q : V) :
    (∀ x : X, x • g⁻¹ • q = g⁻¹ • q) ↔ ∀ x : X, x • q = q := by
  constructor
  · intro h x
    have h1 := h ⟨g⁻¹ * x * g, inv_conj_mem_of_mem_normalizer hg x.2⟩
    have h2 : (g⁻¹ * (x : G) * g) • g⁻¹ • q = g⁻¹ • q := h1
    show (x : G) • q = q
    have h3 := smul_smul_conj g (x : G) (g⁻¹ • q)
    rw [smul_inv_smul, h2, smul_inv_smul] at h3
    exact h3
  · intro h x
    have h1 := h ⟨g * x * g⁻¹, conj_mem_of_mem_normalizer hg x.2⟩
    have h2 : (g * (x : G) * g⁻¹) • q = q := h1
    show (x : G) • g⁻¹ • q = g⁻¹ • q
    have h3 := smul_smul_conj g⁻¹ (x : G) q
    rw [inv_inv, h2] at h3
    exact h3

theorem smul_modFix (hg : g ∈ Subgroup.normalizer (X : Set G)) (W : Subgroup V) :
    g • modFix X W = modFix X (g • W) := by
  ext q
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, XMod.mem_fixed, XMod.mem_fixed,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, fixes_iff_of_mem_normalizer hg]

theorem isModInv_smul (hg : g ∈ Subgroup.normalizer (X : Set G)) {W : Subgroup V}
    (hW : IsModInv X W) : IsModInv X (g • W) := by
  intro x q hq
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq ⊢
  change g⁻¹ • (x : G) • q ∈ W
  rw [inv_smul_smul_conj]
  exact hW ⟨_, inv_conj_mem_of_mem_normalizer hg x.2⟩ _ hq

theorem smul_modComm (hg : g ∈ Subgroup.normalizer (X : Set G)) (W : Subgroup V) :
    g • modComm X W = modComm X (g • W) := by
  apply le_antisymm
  · intro q hq
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq
    have hM : modComm X W ≤
        (modComm X (g • W)).comap (MulDistribMulAction.toMonoidHom V g) := by
      rw [XMod.commOf_le_iff]
      intro x w hw
      rw [Subgroup.mem_comap]
      have h1 : (MulDistribMulAction.toMonoidHom V g) ((x • w) * w⁻¹) =
          ((⟨g * x * g⁻¹, conj_mem_of_mem_normalizer hg x.2⟩ : X) • (g • w)) * (g • w)⁻¹ := by
        change g • ((x : G) • w * w⁻¹) = ((g * x * g⁻¹ : G) • g • w) * (g • w)⁻¹
        rw [smul_mul', smul_inv', smul_smul, smul_smul]
        congr 2
        group
      rw [h1]
      exact XMod.mem_commOf_of_mem _ (Subgroup.smul_mem_pointwise_smul _ _ _ hw)
    have h2 := hM hq
    rw [Subgroup.mem_comap] at h2
    simpa using h2
  · rw [XMod.commOf_le_iff]
    intro x l hl
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hl
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have h1 : g⁻¹ • ((x • l) * l⁻¹) =
        ((⟨g⁻¹ * x * g, inv_conj_mem_of_mem_normalizer hg x.2⟩ : X) • (g⁻¹ • l)) *
          (g⁻¹ • l)⁻¹ := by
      change g⁻¹ • ((x : G) • l * l⁻¹) = ((g⁻¹ * x * g : G) • g⁻¹ • l) * (g⁻¹ • l)⁻¹
      rw [smul_mul', smul_inv', smul_smul, smul_smul]
      congr 2
      group
    rw [h1]
    exact XMod.mem_commOf_of_mem _ hl

end Twist

end CFSG.Quasithin

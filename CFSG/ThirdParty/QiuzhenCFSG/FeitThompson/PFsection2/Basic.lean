module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_7_Core
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.CharacterValues
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Index

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 2: basic notation

This file records the common formal vocabulary for Peterfalvi, Section 2,
`The Dade Isometry`.  The definitions are intentionally book-facing: PF
works only with a finite group `G`, a subset `A ⊆ G#`, a subgroup
`L ≤ N_G(A)`, and the auxiliary centralizer factors `H(a)`.

No result from BG is imported here.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section2

universe u

@[expose] public def conjBy {G : Type u} [Group G] (x g : G) : G :=
  x * g * x⁻¹

@[expose] public def conjugateIn {G : Type u} [Group G] (a b : G) : Prop :=
  ∃ x : G, conjBy x a = b

@[expose] public def conjugateInSubgroup {G : Type u} [Group G]
    (L : Subgroup G) (a b : G) : Prop :=
  ∃ x : L, conjBy (x : G) a = b

@[expose] public def conjugateSet {G : Type u} [Group G] (S : Set G) : Set G :=
  {g | ∃ s ∈ S, conjugateIn s g}

@[expose] public def rightTranslateSet {G : Type u} [Mul G] (S : Set G) (x : G) : Set G :=
  {g | ∃ s ∈ S, g = s * x}

@[expose] public def conjugateImage {G : Type u} [Group G] (S : Set G) (x : G) : Set G :=
  {g | ∃ s ∈ S, g = conjBy x s}

@[expose] public def conjugateSubgroup {G : Type u} [Group G]
    (x : G) (K : Subgroup G) : Subgroup G where
  carrier := {g | ∃ k ∈ K, g = conjBy x k}
  one_mem' := by
    refine ⟨1, K.one_mem, ?_⟩
    simp [conjBy]
  mul_mem' := by
    intro a b ha hb
    rcases ha with ⟨ka, hka, rfl⟩
    rcases hb with ⟨kb, hkb, rfl⟩
    refine ⟨ka * kb, K.mul_mem hka hkb, ?_⟩
    simp [conjBy, mul_assoc]
  inv_mem' := by
    intro a ha
    rcases ha with ⟨ka, hka, rfl⟩
    refine ⟨ka⁻¹, K.inv_mem hka, ?_⟩
    simp [conjBy, mul_assoc]

@[expose] public def normalizesSet {G : Type u} [Group G] (S : Set G) (x : G) : Prop :=
  ∀ g : G, conjBy x g ∈ S ↔ g ∈ S

public theorem normalizesSet_one {G : Type u} [Group G] (S : Set G) :
    normalizesSet S 1 := by
  intro g
  simp [conjBy]

public theorem normalizesSet_mul {G : Type u} [Group G] {S : Set G} {x y : G}
    (hx : normalizesSet S x) (hy : normalizesSet S y) :
    normalizesSet S (x * y) := by
  intro g
  calc
    conjBy (x * y) g ∈ S
        ↔ conjBy x (conjBy y g) ∈ S := by
            simp [conjBy, mul_assoc]
    _ ↔ conjBy y g ∈ S := hx (conjBy y g)
    _ ↔ g ∈ S := hy g

public theorem normalizesSet_inv {G : Type u} [Group G] {S : Set G} {x : G}
    (hx : normalizesSet S x) :
    normalizesSet S x⁻¹ := by
  intro g
  have h := hx (conjBy x⁻¹ g)
  have hconj : conjBy x (conjBy x⁻¹ g) = g := by
    simp [conjBy, mul_assoc]
  simpa [hconj] using h.symm

@[expose] public def setNormalizer {G : Type u} [Group G] (S : Set G) : Subgroup G where
  carrier := {x | normalizesSet S x}
  one_mem' := normalizesSet_one S
  mul_mem' := by
    intro x y hx hy
    exact normalizesSet_mul hx hy
  inv_mem' := by
    intro x hx
    exact normalizesSet_inv hx

@[expose] public def elementCentralizer {G : Type u} [Group G] (a : G) : Subgroup G :=
  Subgroup.centralizer ({a} : Set G)

@[expose] public def centralizerIn {G : Type u} [Group G] (L : Subgroup G) (a : G) :
    Subgroup G :=
  L ⊓ elementCentralizer a

@[expose] public def setProduct {G : Type u} [Mul G] (S T : Set G) : Set G :=
  {g | ∃ s ∈ S, ∃ t ∈ T, g = s * t}

@[expose] public def cosetProduct {G : Type u} [Group G] (a : G) (H : Subgroup G) : Set G :=
  setProduct ({a} : Set G) H

@[expose] public def IsTISubset {G : Type u} [Group G] (A : Set G) : Prop :=
  ∀ g : G, (A ∩ conjugateImage A g).Nonempty → normalizesSet A g

@[expose] public def IsTISubsetWithNormalizer {G : Type u} [Group G]
    (A : Set G) (L : Subgroup G) : Prop :=
  A.Nonempty ∧ (∀ a ∈ A, a ≠ 1) ∧ IsTISubset A ∧ setNormalizer A = L

/-- `C = H × K` as an internal direct product inside the ambient group. -/
public structure IsInternalDirectProduct {G : Type u} [Group G]
    (C H K : Subgroup G) : Prop where
  left_le : H ≤ C
  right_le : K ≤ C
  commute : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h
  inf_eq_bot : H ⊓ K = ⊥
  mul_surjective : ∀ c ∈ C, ∃ h ∈ H, ∃ k ∈ K, c = h * k

/-- `C = H ⋊ K` as an internal semidirect product. -/
public structure IsInternalSemidirectProduct {G : Type u} [Group G]
    (C H K : Subgroup G) : Prop where
  left_le : H ≤ C
  right_le : K ≤ C
  right_normalizes_left : ∀ k ∈ K, ∀ h ∈ H, conjBy k h ∈ H
  inf_eq_bot : H ⊓ K = ⊥
  mul_surjective : ∀ c ∈ C, ∃ h ∈ H, ∃ k ∈ K, c = h * k

/-- The factors in an internal semidirect product are complementary subgroups
inside the product subgroup. -/
public theorem internalSemidirectProduct_isComplement
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : IsInternalSemidirectProduct C H K) :
    (H.subgroupOf C).IsComplement' (K.subgroupOf C) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxH hxK
    apply Subtype.ext
    have hxInf : (x : G) ∈ H ⊓ K := Subgroup.mem_inf.mpr ⟨hxH, hxK⟩
    have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
      simpa [h.inf_eq_bot] using hxInf
    simpa using hxBot
  · rw [Set.eq_univ_iff_forall]
    intro x
    rcases h.mul_surjective (x : G) x.2 with ⟨h0, hh0, k0, hk0, hx⟩
    refine ⟨(⟨h0, h.left_le hh0⟩ : C), hh0,
      (⟨k0, h.right_le hk0⟩ : C), hk0, ?_⟩
    apply Subtype.ext
    simpa using hx.symm

/-- In an internal semidirect product `C = H ⋊ K`, the relative index of
`H` in `C` is the order of the complement `K`. -/
public theorem internalSemidirectProduct_left_relIndex_eq_card_right
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : IsInternalSemidirectProduct C H K) :
    H.relIndex C = Nat.card K := by
  have hcomp := internalSemidirectProduct_isComplement
    (C := C) (H := H) (K := K) h
  calc
    H.relIndex C = Nat.card (K.subgroupOf C) := by
      simpa [Subgroup.relIndex] using hcomp.symm.index_eq_card
    _ = Nat.card K := by
      simpa using
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (H := K) (K := C) h.right_le).toEquiv

/-- Peterfalvi Hypothesis (2.2). -/
public structure Hypothesis2 {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G) : Prop where
  subset_punctured : ∀ a ∈ A, a ≠ 1
  subset_L : ∀ a ∈ A, a ∈ L
  L_le_normalizer : L ≤ setNormalizer A
  G_conjugate_imp_L_conjugate :
    ∀ {a b : G}, a ∈ A → b ∈ A → conjugateIn a b → conjugateInSubgroup L a b
  centralizer_eq_product :
    ∀ {a : G}, a ∈ A →
      IsInternalSemidirectProduct (elementCentralizer a) (H a) (centralizerIn L a)
  coprime_orders :
    ∀ {a b : G}, a ∈ A → b ∈ A →
      Nat.Coprime (Nat.card (H a)) (Nat.card (centralizerIn L b))

public theorem hypothesis2_of_subset {G : Type u} [Group G] [Finite G]
    {A A1 : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) (hsub : A1 ⊆ A)
    (hnorm : L ≤ setNormalizer A1) :
    Hypothesis2 A1 L H where
  subset_punctured a ha := h.subset_punctured a (hsub ha)
  subset_L a ha := h.subset_L a (hsub ha)
  L_le_normalizer := hnorm
  G_conjugate_imp_L_conjugate ha hb hconj :=
    h.G_conjugate_imp_L_conjugate (hsub ha) (hsub hb) hconj
  centralizer_eq_product ha := h.centralizer_eq_product (hsub ha)
  coprime_orders ha hb := h.coprime_orders (hsub ha) (hsub hb)

@[expose] public def CFOn {G : Type u} [Group G] (L : Subgroup G) (A : Set G)
    (α : Section1.ClassFunction L) : Prop :=
  Section1.IsClassFunction α ∧ ∀ l : L, (l : G) ∉ A → α l = 0

@[expose] public def virtualCharacterOn {G : Type u} [Group G] [Finite G]
    (L : Subgroup G) [Finite L] (A : Set G) (α : Section1.ClassFunction L) : Prop :=
  Theory.Character.IsVirtualCharacter α ∧ ∀ l : L, (l : G) ∉ A → α l = 0

@[expose] public def virtualCharacterOfG {G : Type u} [Group G] [Finite G]
    (χ : Section1.ClassFunction G) : Prop :=
  Theory.Character.IsVirtualCharacter χ

@[expose] public def dadeSupport {G : Type u} [Group G]
    (A : Set G) (H : G → Subgroup G) : Set G :=
  {g | ∃ a ∈ A, ∃ h ∈ H a, conjugateIn g (a * h)}

/--
The class function `α^τ` from (2.5).  The value is selected from the unique
`L`-class supplied by (2.4.b); the corresponding value lemma is recorded in
the section statement file.
-/
@[expose] public noncomputable def dadeTransform {G : Type u} [Group G]
    {A : Set G} {L : Subgroup G} (H : G → Subgroup G)
    (hAL : ∀ a ∈ A, a ∈ L) (α : Section1.ClassFunction L) :
    Section1.ClassFunction G := by
  classical
  intro g
  exact
    if hg : ∃ a ∈ A, ∃ h ∈ H a, conjugateIn g (a * h) then
      let a : G := Classical.choose hg
      let ha : a ∈ A := (Classical.choose_spec hg).1
      α ⟨a, hAL a ha⟩
    else
      0

/-- The Dade transform as a linear map. -/
@[expose] public noncomputable def dadeTransformLinear {G : Type u} [Group G]
    {A : Set G} {L : Subgroup G} (H : G → Subgroup G)
    (hAL : ∀ a ∈ A, a ∈ L) :
    Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G where
  toFun := dadeTransform H hAL
  map_add' := by
    intro α β
    ext g
    by_cases hg : ∃ a ∈ A, ∃ h ∈ H a, conjugateIn g (a * h)
    · simp [dadeTransform, hg]
    · simp [dadeTransform, hg]
  map_smul' := by
    intro c α
    ext g
    by_cases hg : ∃ a ∈ A, ∃ h ∈ H a, conjugateIn g (a * h)
    · simp [dadeTransform, hg]
    · simp [dadeTransform, hg]

public theorem dadeTransformLinear_apply {G : Type u} [Group G]
    {A : Set G} {L : Subgroup G} (H : G → Subgroup G)
    (hAL : ∀ a ∈ A, a ∈ L) (α : Section1.ClassFunction L) :
    dadeTransformLinear H hAL α = dadeTransform H hAL α :=
  rfl

@[expose] public def HInter {G : Type u} [Group G]
    (H : G → Subgroup G) (B : Set G) : Subgroup G :=
  ⨅ b : B, H (b : G)

@[expose] public def normalizerIn {G : Type u} [Group G]
    (L : Subgroup G) (B : Set G) : Subgroup G :=
  L ⊓ setNormalizer B

@[expose] public def MOfSet {G : Type u} [Group G]
    (H : G → Subgroup G) (L : Subgroup G) (B : Set G) : Subgroup G :=
  HInter H B ⊔ normalizerIn L B

public theorem hInter_le_of_mem {G : Type u} [Group G]
    (H : G → Subgroup G) {B : Set G} {a : G} (ha : a ∈ B) :
    HInter H B ≤ H a := by
  intro x hx
  exact (show x ∈ H (⟨a, ha⟩ : B) from (Subgroup.mem_iInf.mp hx) ⟨a, ha⟩)

public theorem hInter_mul_normalizer_mem_MOfSet {G : Type u} [Group G]
    (H : G → Subgroup G) (L : Subgroup G) (B : Set G)
    {h x : G} (hh : h ∈ HInter H B) (hx : x ∈ normalizerIn L B) :
    h * x ∈ MOfSet H L B := by
  exact Subgroup.mul_mem _
    (show h ∈ MOfSet H L B from (show HInter H B ≤ MOfSet H L B from le_sup_left) hh)
    (show x ∈ MOfSet H L B from (show normalizerIn L B ≤ MOfSet H L B from le_sup_right) hx)

/-! ## Peterfalvi (2.1) notation -/


@[expose] public def subgroupCosetByElement {G : Type u} [Group G]
    (H : Subgroup G) (g : G) : Set G :=
  rightTranslateSet (H : Set G) g

@[expose] public def conjugateCosetPiece {G : Type u} [Group G]
    (H : Subgroup G) (g x : G) : Set G :=
  conjugateImage (subgroupCosetByElement (centralizerIn H g) g) x

@[expose] public def finiteDisjointUnionOfConjugatePieces {G : Type u} [Group G]
    (S : Set G) (H : Subgroup G) (g : G) (n : ℕ) : Prop :=
  ∃ reps : Finset G,
    reps.card = n ∧
      (∀ x ∈ reps, x ∈ H) ∧
      (∀ x ∈ reps, ∀ y ∈ reps, x ≠ y →
        Disjoint (conjugateCosetPiece H g x) (conjugateCosetPiece H g y)) ∧
      S = {z | ∃ x ∈ reps, z ∈ conjugateCosetPiece H g x}

/--
Specification of the function `α_B` in Peterfalvi (2.9).  It records the
defining equation on the product decomposition `M(B)=H(B)N_L(B)`.
-/
@[expose] public def alphaBSpec {G : Type u} [Group G]
    {L : Subgroup G} (H : G → Subgroup G)
    (α : Section1.ClassFunction L) (B : Set G)
    (αB : Section1.ClassFunction (MOfSet H L B)) : Prop :=
  ∀ ⦃h x : G⦄, (hh : h ∈ HInter H B) → (hx : x ∈ normalizerIn L B) →
    αB ⟨h * x, hInter_mul_normalizer_mem_MOfSet H L B hh hx⟩ =
      α ⟨x, (show x ∈ L from (Subgroup.mem_inf.mp hx).1)⟩

@[expose] public def setConjugateBy {G : Type u} [Group G] (x : G) (B : Set G) : Set G :=
  {g | ∃ b ∈ B, g = conjBy x b}

@[expose] public def LConjugateSubsets {G : Type u} [Group G]
    (L : Subgroup G) (B C : Set G) : Prop :=
  ∃ x : L, C = setConjugateBy (x : G) B

@[expose] public def IsRepresentativeSystemForNonemptySubsets {G : Type u} [Group G]
    (A : Set G) (L : Subgroup G) (reps : Finset (Set G)) : Prop :=
  (∀ B ∈ reps, B.Nonempty ∧ B ⊆ A) ∧
    ∀ C : Set G, C.Nonempty → C ⊆ A →
      ∃ B ∈ reps, LConjugateSubsets L B C ∧
        ∀ D ∈ reps, LConjugateSubsets L D C → D = B

@[expose] public def transporterSet {G : Type u} [Group G]
    (g : G) (X : Set G) : Set G :=
  {x | conjBy x⁻¹ g ∈ X}

end CFSG.Section2

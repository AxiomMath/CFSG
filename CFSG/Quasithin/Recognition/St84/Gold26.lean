module

public import CFSG.Quasithin.Recognition.St84.Basic
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TreeBasic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.GetD
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3TSlide
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Frattini

public section

namespace CFSG.Quasithin.St84

open scoped Pointwise

open SimpleGraph CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace AltWord

section Word

variable {P₁ P₂ : Subgroup G}

private def altLetter (P₁ P₂ : Subgroup G) : Set G :=
  {x | (x ∈ P₁ ∧ x ∉ P₁ ⊓ P₂) ∨ (x ∈ P₂ ∧ x ∉ P₁ ⊓ P₂)}

@[simp] private theorem mem_altLetter {x : G} :
    x ∈ altLetter P₁ P₂ ↔ (x ∈ P₁ ∧ x ∉ P₁ ⊓ P₂) ∨ (x ∈ P₂ ∧ x ∉ P₁ ⊓ P₂) :=
  Iff.rfl

private def DiffSide (P₁ P₂ : Subgroup G) (x y : G) : Prop :=
  (x ∈ P₁ ∧ y ∉ P₁) ∨ (x ∉ P₁ ∧ y ∈ P₁)

private theorem DiffSide.symm {x y : G} (h : DiffSide P₁ P₂ x y) : DiffSide P₁ P₂ y x :=
  h.elim (fun ⟨a, b⟩ => Or.inr ⟨b, a⟩) fun ⟨a, b⟩ => Or.inl ⟨b, a⟩

private theorem not_mem_inf_of_mem_altLetter {x : G} (hx : x ∈ altLetter P₁ P₂) : x ∉ P₁ ⊓ P₂ :=
  hx.elim (fun h => h.2) fun h => h.2

private theorem mem_right_of_mem_altLetter {x : G} (hx : x ∈ altLetter P₁ P₂) (h : x ∉ P₁) : x ∈ P₂ :=
  hx.elim (fun h' => absurd h'.1 h) fun h' => h'.1

private theorem not_mem_left_of_mem_altLetter {x : G} (hx : x ∈ altLetter P₁ P₂) (h : x ∈ P₂) : x ∉ P₁ :=
  fun h1 => not_mem_inf_of_mem_altLetter hx (Subgroup.mem_inf.mpr ⟨h1, h⟩)

private theorem not_mem_right_of_mem_altLetter {x : G} (hx : x ∈ altLetter P₁ P₂) (h : x ∈ P₁) : x ∉ P₂ :=
  fun h2 => not_mem_inf_of_mem_altLetter hx (Subgroup.mem_inf.mpr ⟨h, h2⟩)

private theorem altLetter_comm {x : G} : x ∈ altLetter P₁ P₂ ↔ x ∈ altLetter P₂ P₁ := by
  rw [mem_altLetter, mem_altLetter, inf_comm P₂ P₁]
  exact or_comm

private theorem DiffSide.swap {x y : G} (hx : x ∈ altLetter P₁ P₂) (hy : y ∈ altLetter P₁ P₂)
    (h : DiffSide P₁ P₂ x y) : DiffSide P₂ P₁ x y := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨not_mem_right_of_mem_altLetter hx h1, mem_right_of_mem_altLetter hy h2⟩
  · exact Or.inl ⟨mem_right_of_mem_altLetter hx h1, not_mem_right_of_mem_altLetter hy h2⟩

private def IsAlt (P₁ P₂ : Subgroup G) : List G → Prop
  | [] => False
  | [x] => x ∈ altLetter P₁ P₂
  | x :: y :: l => x ∈ altLetter P₁ P₂ ∧ DiffSide P₁ P₂ x y ∧ IsAlt P₁ P₂ (y :: l)

@[simp] private theorem isAlt_singleton {x : G} : IsAlt P₁ P₂ [x] ↔ x ∈ altLetter P₁ P₂ :=
  Iff.rfl

@[simp] private theorem isAlt_cons_cons {x y : G} {l : List G} :
    IsAlt P₁ P₂ (x :: y :: l) ↔
      x ∈ altLetter P₁ P₂ ∧ DiffSide P₁ P₂ x y ∧ IsAlt P₁ P₂ (y :: l) :=
  Iff.rfl

private theorem isAlt_nil : ¬ IsAlt P₁ P₂ [] := id

private theorem IsAlt.head_mem {x : G} {l : List G} (h : IsAlt P₁ P₂ (x :: l)) :
    x ∈ altLetter P₁ P₂ := by
  cases l with
  | nil => exact isAlt_singleton.mp h
  | cons y l' => exact (isAlt_cons_cons.mp h).1

private theorem IsAlt.mem_getElem {L : List G} (hL : IsAlt P₁ P₂ L) {k : ℕ} (hk : k < L.length) :
    L[k] ∈ altLetter P₁ P₂ := by
  induction L generalizing k with
  | nil => simp at hk
  | cons x t ih =>
    cases k with
    | zero =>
      cases t with
      | nil => simpa using hL
      | cons y l => exact (isAlt_cons_cons.mp hL).1
    | succ k =>
      cases t with
      | nil => simp at hk
      | cons y l =>
        rw [List.getElem_cons_succ]
        exact ih (isAlt_cons_cons.mp hL).2.2 (k := k) (by simpa using hk)

private theorem IsAlt.diffSide_getElem {L : List G} (hL : IsAlt P₁ P₂ L) {k : ℕ}
    (hk : k + 1 < L.length) : DiffSide P₁ P₂ (L[k]) (L[k + 1]) := by
  induction L generalizing k with
  | nil => simp at hk
  | cons x t ih =>
    cases k with
    | zero =>
      cases t with
      | nil => simp at hk
      | cons y l => exact (isAlt_cons_cons.mp hL).2.1
    | succ k =>
      cases t with
      | nil => simp at hk
      | cons y l =>
        rw [List.getElem_cons_succ, List.getElem_cons_succ]
        exact ih (isAlt_cons_cons.mp hL).2.2 (k := k) (by simpa using hk)

private theorem IsAlt.swap : ∀ {L : List G}, IsAlt P₁ P₂ L → IsAlt P₂ P₁ L
  | [], h => h
  | [x], h => altLetter_comm.mp h
  | _x :: y :: l, h => by
    obtain ⟨hx, hd, ht⟩ := isAlt_cons_cons.mp h
    exact isAlt_cons_cons.mpr
      ⟨altLetter_comm.mp hx, DiffSide.swap hx (IsAlt.head_mem ht) hd, IsAlt.swap ht⟩

private def IsGood (P₁ P₂ : Subgroup G) (x : G) : Prop :=
  x ∈ P₁ ⊓ P₂ ∨ ∃ L : List G, IsAlt P₁ P₂ L ∧ L.prod = x

private theorem IsGood.swap {x : G} (h : IsGood P₁ P₂ x) : IsGood P₂ P₁ x := by
  rcases h with h | ⟨L, hL, rfl⟩
  · exact Or.inl (by simpa [inf_comm] using h)
  · exact Or.inr ⟨L, IsAlt.swap hL, rfl⟩

private theorem isGood_one : IsGood P₁ P₂ (1 : G) :=
  Or.inl (one_mem _)

private theorem isGood_of_mem {x : G} (hx : x ∈ P₁ ∨ x ∈ P₂) : IsGood P₁ P₂ x := by
  by_cases hD : x ∈ P₁ ⊓ P₂
  · exact Or.inl hD
  · refine Or.inr ⟨[x], ?_, by simp⟩
    rcases hx with h | h
    · exact isAlt_singleton.mpr (mem_altLetter.mpr (Or.inl ⟨h, hD⟩))
    · exact isAlt_singleton.mpr (mem_altLetter.mpr (Or.inr ⟨h, hD⟩))

private theorem isGood_mul_cons {z x : G} {l : List G} (hz : z ∈ P₁) (hxP₂ : x ∈ P₂)
    (hl : IsAlt P₁ P₂ (x :: l)) : IsGood P₁ P₂ (z * (x :: l).prod) := by
  have hxA : x ∈ altLetter P₁ P₂ := IsAlt.head_mem hl
  have hxP₁ : x ∉ P₁ := not_mem_left_of_mem_altLetter hxA hxP₂
  by_cases hzD : z ∈ P₁ ⊓ P₂
  ·
    have hzxP₂ : z * x ∈ P₂ := mul_mem (Subgroup.mem_inf.mp hzD).2 hxP₂
    by_cases hzxD : z * x ∈ P₁ ⊓ P₂
    ·
      rcases l with _ | ⟨y, l'⟩
      · exact Or.inl (by simpa using hzxD)
      · obtain ⟨hyA, hxy, htail⟩ := isAlt_cons_cons.mp hl
        have hyP₁ : y ∈ P₁ := by
          rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact absurd h1 hxP₁
          · exact h2
        have hyP₂ : y ∉ P₂ := not_mem_right_of_mem_altLetter (IsAlt.head_mem htail) hyP₁
        have hzxyP₁ : z * x * y ∈ P₁ := mul_mem (Subgroup.mem_inf.mp hzxD).1 hyP₁
        have hzxyD : z * x * y ∉ P₁ ⊓ P₂ := by
          intro h
          refine hyP₂ ?_
          have h1 : (z * x)⁻¹ * (z * x * y) ∈ P₂ :=
            mul_mem (inv_mem (Subgroup.mem_inf.mp hzxD).2) (Subgroup.mem_inf.mp h).2
          simpa [mul_assoc] using h1
        have hzxyA : z * x * y ∈ altLetter P₁ P₂ := mem_altLetter.mpr (Or.inl ⟨hzxyP₁, hzxyD⟩)
        rcases l' with _ | ⟨w, l''⟩
        · refine Or.inr ⟨[z * x * y], isAlt_singleton.mpr hzxyA, ?_⟩
          simp [mul_assoc]
        · obtain ⟨_, hyw, htail'⟩ := isAlt_cons_cons.mp htail
          have hwP₁ : w ∉ P₁ := by
            rcases hyw with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact h2
            · exact absurd hyP₁ h1
          refine Or.inr ⟨(z * x * y) :: w :: l'', isAlt_cons_cons.mpr
            ⟨hzxyA, Or.inl ⟨hzxyP₁, hwP₁⟩, htail'⟩, ?_⟩
          simp [mul_assoc]
    ·
      rcases l with _ | ⟨y, l'⟩
      · refine Or.inr ⟨[z * x], isAlt_singleton.mpr (mem_altLetter.mpr (Or.inr ⟨hzxP₂, hzxD⟩)),
          ?_⟩
        simp
      · obtain ⟨hyA, hxy, htail⟩ := isAlt_cons_cons.mp hl
        have hyP₁ : y ∈ P₁ := by
          rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact absurd h1 hxP₁
          · exact h2
        have hzxP₁ : z * x ∉ P₁ := fun h => hzxD (Subgroup.mem_inf.mpr ⟨h, hzxP₂⟩)
        refine Or.inr ⟨(z * x) :: y :: l', isAlt_cons_cons.mpr
          ⟨mem_altLetter.mpr (Or.inr ⟨hzxP₂, hzxD⟩), Or.inr ⟨hzxP₁, hyP₁⟩, htail⟩, ?_⟩
        simp [mul_assoc]
  ·
    exact Or.inr ⟨z :: x :: l,
      isAlt_cons_cons.mpr ⟨mem_altLetter.mpr (Or.inl ⟨hz, hzD⟩), Or.inl ⟨hz, hxP₁⟩, hl⟩, rfl⟩

private theorem isGood_mul_prod_left {y : G} (hy : y ∈ P₁) {L : List G} (hL : IsAlt P₁ P₂ L) :
    IsGood P₁ P₂ (y * L.prod) := by
  rcases L with _ | ⟨x₁, t⟩
  · exact (isAlt_nil hL).elim
  rcases t with _ | ⟨x₂, l⟩
  ·
    by_cases h1 : x₁ ∈ P₁
    · simpa using isGood_of_mem (Or.inl (mul_mem hy h1))
    · exact isGood_mul_cons hy (mem_right_of_mem_altLetter (IsAlt.head_mem hL) h1) hL
  · obtain ⟨hx₁, hd, htail⟩ := isAlt_cons_cons.mp hL
    have hx₂A : x₂ ∈ altLetter P₁ P₂ := IsAlt.head_mem htail
    by_cases h1 : x₁ ∈ P₁
    ·
      have hx₂P₂ : x₂ ∈ P₂ := by
        rcases hd with ⟨a, b⟩ | ⟨a, b⟩
        · exact mem_right_of_mem_altLetter hx₂A b
        · exact absurd h1 a
      have hres := isGood_mul_cons (z := y * x₁) (mul_mem hy h1) hx₂P₂ htail
      have heq : (y * x₁) * (x₂ :: l).prod = y * (x₁ :: x₂ :: l).prod := by
        simp [mul_assoc]
      rwa [heq] at hres
    · have hx₁P₂ : x₁ ∈ P₂ := mem_right_of_mem_altLetter hx₁ h1
      by_cases hyD : y ∈ P₁ ⊓ P₂
      ·
        exact isGood_mul_cons (z := y) (Subgroup.mem_inf.mp hyD).1 hx₁P₂ hL
      ·
        exact Or.inr ⟨y :: x₁ :: x₂ :: l, isAlt_cons_cons.mpr
          ⟨mem_altLetter.mpr (Or.inl ⟨hy, hyD⟩), Or.inl ⟨hy, h1⟩, hL⟩, rfl⟩

private theorem isGood_mul {a b : G} (ha : a ∈ P₁ ∨ a ∈ P₂) (hb : IsGood P₁ P₂ b) :
    IsGood P₁ P₂ (a * b) := by
  rcases hb with hD | ⟨L, hL, rfl⟩
  · rcases ha with h1 | h2
    · exact isGood_of_mem (Or.inl (mul_mem h1 (Subgroup.mem_inf.mp hD).1))
    · exact isGood_of_mem (Or.inr (mul_mem h2 (Subgroup.mem_inf.mp hD).2))
  · rcases ha with h1 | h2
    · exact isGood_mul_prod_left h1 hL
    · exact IsGood.swap (isGood_mul_prod_left (P₁ := P₂) (P₂ := P₁) h2 (IsAlt.swap hL))

private theorem isGood_of_mem_sup {x : G} (hx : x ∈ P₁ ⊔ P₂) : IsGood P₁ P₂ x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction_left (s := (P₁ : Set G) ∪ (P₂ : Set G))
    (p := fun x _ => IsGood P₁ P₂ x) isGood_one ?_ ?_ hx
  · intro a ha b _ hb
    exact isGood_mul ((Set.mem_union a P₁ P₂).mp ha) hb
  · intro a ha b _ hb
    exact isGood_mul ((Set.mem_union a P₁ P₂).mp ha |>.elim (fun h => Or.inl (inv_mem h))
      fun h => Or.inr (inv_mem h)) hb

end Word

private noncomputable def aVOf (P₁ : Subgroup G) (α₁ α₂ : V) (x : G) : V := by
  classical
  exact if x ∈ P₁ then α₁ else α₂

private noncomputable def cVOf (P₁ : Subgroup G) (α₁ α₂ : V) (x : G) : V := by
  classical
  exact if x ∈ P₁ then α₂ else α₁

section Vertex

variable {α₁ α₂ : V} {P₁ P₂ : Subgroup G}

local notation "aV" x:max => aVOf P₁ α₁ α₂ x
local notation "cV" x:max => cVOf P₁ α₁ α₂ x

private theorem aV_of_mem {x : G} (h : x ∈ P₁) : aV x = α₁ := by
  simp [aVOf, h]

private theorem aV_of_not_mem {x : G} (h : x ∉ P₁) : aV x = α₂ := by
  simp [aVOf, h]

private theorem cV_of_mem {x : G} (h : x ∈ P₁) : cV x = α₂ := by
  simp [cVOf, h]

private theorem cV_of_not_mem {x : G} (h : x ∉ P₁) : cV x = α₁ := by
  simp [cVOf, h]

private theorem aV_ne_cV {x : G} (h : α₁ ≠ α₂) : aV x ≠ cV x := by
  by_cases hx : x ∈ P₁
  · rw [aV_of_mem hx, cV_of_mem hx]; exact h
  · rw [aV_of_not_mem hx, cV_of_not_mem hx]; exact h.symm

private theorem aV_mem_pair (x : G) : aV x ∈ ({α₁, α₂} : Set V) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_cases h : x ∈ P₁
  · exact Or.inl (aV_of_mem h)
  · exact Or.inr (aV_of_not_mem h)

private theorem pair_subset_aV_cV (x : G) : ({α₁, α₂} : Set V) ⊆ ({aV x, cV x} : Set V) := by
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
  rcases hz with rfl | rfl
  · by_cases h : x ∈ P₁
    · exact Or.inl (aV_of_mem h).symm
    · exact Or.inr (cV_of_not_mem h).symm
  · by_cases h : x ∈ P₁
    · exact Or.inr (cV_of_mem h).symm
    · exact Or.inl (aV_of_not_mem h).symm

end Vertex

section Walk

variable {α₁ α₂ : V} {P₁ P₂ : Subgroup G}

local notation "aV" x:max => aVOf P₁ α₁ α₂ x
local notation "cV" x:max => cVOf P₁ α₁ α₂ x

private theorem aV_fixed {x : G} (hP₁ : P₁ ≤ MulAction.stabilizer G α₁)
    (hP₂ : P₂ ≤ MulAction.stabilizer G α₂) (hx : x ∈ altLetter P₁ P₂) :
    x • aV x = aV x := by
  by_cases h : x ∈ P₁
  · rw [aV_of_mem h, MulAction.mem_stabilizer_iff.mp (hP₁ h)]
  · rw [aV_of_not_mem h, MulAction.mem_stabilizer_iff.mp (hP₂ (mem_right_of_mem_altLetter hx h))]

private theorem cV_moved {x : G} (h₁ : P₁ ⊓ MulAction.stabilizer G α₂ = P₁ ⊓ P₂)
    (h₂ : P₂ ⊓ MulAction.stabilizer G α₁ = P₁ ⊓ P₂) (hx : x ∈ altLetter P₁ P₂) :
    x • cV x ≠ cV x := by
  by_cases h : x ∈ P₁
  · intro hc
    rw [cV_of_mem h] at hc
    have hmem : x ∈ P₁ ⊓ MulAction.stabilizer G α₂ :=
      Subgroup.mem_inf.mpr ⟨h, MulAction.mem_stabilizer_iff.mpr hc⟩
    rw [h₁] at hmem
    exact not_mem_inf_of_mem_altLetter hx hmem
  · intro hc
    rw [cV_of_not_mem h] at hc
    have hmem : x ∈ P₂ ⊓ MulAction.stabilizer G α₁ :=
      Subgroup.mem_inf.mpr ⟨mem_right_of_mem_altLetter hx h, MulAction.mem_stabilizer_iff.mpr hc⟩
    rw [h₂] at hmem
    exact not_mem_inf_of_mem_altLetter hx hmem

private theorem adj_aV_cV (h12 : Γ.Adj α₁ α₂) {x : G} (hx : x ∈ altLetter P₁ P₂) :
    Γ.Adj (aV x) (cV x) := by
  by_cases h : x ∈ P₁
  · rw [aV_of_mem h, cV_of_mem h]; exact h12
  · rw [aV_of_not_mem h, cV_of_not_mem h]; exact h12.symm

private theorem cV_eq_aV {x y : G} (hx : x ∈ altLetter P₁ P₂) (hy : y ∈ altLetter P₁ P₂)
    (hd : DiffSide P₁ P₂ x y) : cV x = aV y := by
  rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [cV_of_mem h1, aV_of_not_mem h2]
  · rw [cV_of_not_mem h1, aV_of_mem h2]

private theorem aV_eq_cV {x y : G} (hx : x ∈ altLetter P₁ P₂) (hy : y ∈ altLetter P₁ P₂)
    (hd : DiffSide P₁ P₂ x y) : aV x = cV y :=
  (cV_eq_aV hy hx hd.symm).symm

private theorem same_side_of_diff {x y z : G} (hxy : DiffSide P₁ P₂ x y) (hyz : DiffSide P₁ P₂ y z) :
    (x ∈ P₁ ↔ z ∈ P₁) := by
  rcases hxy with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases hyz with ⟨c, d⟩ | ⟨c, d⟩
  · exact ⟨fun _ => absurd c b, fun _ => absurd c b⟩
  · exact ⟨fun _ => d, fun _ => a⟩
  · exact ⟨fun h => absurd h a, fun h => absurd h d⟩
  · exact ⟨fun _ => absurd b c, fun _ => absurd b c⟩

private theorem cV_eq_cV {x z : G} (hxz : x ∈ P₁ ↔ z ∈ P₁) : cV x = cV z := by
  by_cases h : x ∈ P₁
  · rw [cV_of_mem h, cV_of_mem (hxz.mp h)]
  · rw [cV_of_not_mem h, cV_of_not_mem (fun h' => h (hxz.mpr h'))]

private noncomputable def walkVOf (P₁ : Subgroup G) (α₁ α₂ : V) (L : List G) (k : ℕ) : V :=
  match k with
  | 0 => aVOf P₁ α₁ α₂ (L.getD 0 1)
  | k + 1 => (L.take (k + 1)).prod • cVOf P₁ α₁ α₂ (L.getD k 1)

local notation "walkV" L:max k:max => walkVOf P₁ α₁ α₂ L k

@[simp] private theorem walkV_zero (L : List G) : walkV L 0 = aV (L.getD 0 1) := rfl

@[simp] private theorem walkV_succ (L : List G) (k : ℕ) :
    walkV L (k + 1) = (L.take (k + 1)).prod • cV (L.getD k 1) := rfl

private theorem walkV_adj (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (h12 : Γ.Adj α₁ α₂) (hP₁ : P₁ ≤ MulAction.stabilizer G α₁)
    (hP₂ : P₂ ≤ MulAction.stabilizer G α₂) {L : List G} (hL : IsAlt P₁ P₂ L) :
    ∀ k, k + 1 ≤ L.length → Γ.Adj (walkV L k) (walkV L (k + 1)) := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h0 : L.getD 0 1 = L[0] := List.getD_eq_getElem L (1 : G) (by omega)
    have hx : L[0] ∈ altLetter P₁ P₂ := hL.mem_getElem (by omega)
    have hp : (L.take 1).prod = L[0] := by
      have := List.prod_take_succ L 0 (by omega)
      simpa using this
    rw [walkV_zero, walkV_succ, h0, hp]
    have h := (hadj (L[0]) (aV (L[0])) (cV (L[0]))).mpr (adj_aV_cV h12 hx)
    rwa [aV_fixed hP₁ hP₂ hx] at h
  | succ k ih =>
    intro hk
    have hk1 : k + 1 < L.length := by omega
    have hk0 : k < L.length := by omega
    have e0 : L.getD k 1 = L[k] := List.getD_eq_getElem L (1 : G) hk0
    have e1 : L.getD (k + 1) 1 = L[k + 1] := List.getD_eq_getElem L (1 : G) hk1
    have hx0 : L[k] ∈ altLetter P₁ P₂ := hL.mem_getElem hk0
    have hx1 : L[k + 1] ∈ altLetter P₁ P₂ := hL.mem_getElem hk1
    have hd : DiffSide P₁ P₂ (L[k]) (L[k + 1]) := hL.diffSide_getElem (by omega)
    have hp : (L.take ((k + 1) + 1)).prod = (L.take (k + 1)).prod * L[k + 1] :=
      List.prod_take_succ L (k + 1) hk1
    rw [walkV_succ, walkV_succ, e0, e1, hp, mul_smul]
    refine (hadj ((L.take (k + 1)).prod) _ _).mpr ?_
    rw [cV_eq_aV hx0 hx1 hd]
    have h := (hadj (L[k + 1]) (aV (L[k + 1])) (cV (L[k + 1]))).mpr (adj_aV_cV h12 hx1)
    rwa [aV_fixed hP₁ hP₂ hx1] at h

private theorem walkV_nb (hP₁ : P₁ ≤ MulAction.stabilizer G α₁)
    (hP₂ : P₂ ≤ MulAction.stabilizer G α₂)
    (h₁ : P₁ ⊓ MulAction.stabilizer G α₂ = P₁ ⊓ P₂)
    (h₂ : P₂ ⊓ MulAction.stabilizer G α₁ = P₁ ⊓ P₂)
    {L : List G} (hL : IsAlt P₁ P₂ L) :
    ∀ k, k + 2 ≤ L.length → walkV L k ≠ walkV L (k + 2) := by
  intro k
  induction k with
  | zero =>
    intro hk
    show walkV L 0 ≠ walkV L (1 + 1)
    have h0 : L.getD 0 1 = L[0] := List.getD_eq_getElem L (1 : G) (by omega)
    have h1 : L.getD 1 1 = L[1] := List.getD_eq_getElem L (1 : G) (by omega)
    have hA0 : L[0] ∈ altLetter P₁ P₂ := hL.mem_getElem (by omega)
    have hA1 : L[1] ∈ altLetter P₁ P₂ := hL.mem_getElem (by omega)
    have hd : DiffSide P₁ P₂ (L[0]) (L[1]) := hL.diffSide_getElem (by omega)
    have hp1 : (L.take 1).prod = L[0] := by
      have := List.prod_take_succ L 0 (by omega)
      simpa using this
    have hp2 : (L.take (1 + 1)).prod = (L.take 1).prod * L[1] :=
      List.prod_take_succ L 1 (by omega)
    rw [walkV_zero, walkV_succ, h0, h1, hp2, hp1]
    intro hcontra
    rw [mul_smul] at hcontra
    have hfix : L[0] • aV (L[0]) = aV (L[0]) := aV_fixed hP₁ hP₂ hA0
    rw [← hfix] at hcontra
    have h2 : aV (L[0]) = L[1] • cV (L[1]) := MulAction.injective (L[0]) hcontra
    rw [aV_eq_cV hA0 hA1 hd] at h2
    exact cV_moved h₁ h₂ hA1 h2.symm
  | succ k ih =>
    intro hk
    show walkV L (k + 1) ≠ walkV L ((k + 2) + 1)
    have hk0 : k < L.length := by omega
    have hk1 : k + 1 < L.length := by omega
    have hk2 : k + 2 < L.length := by omega
    have e0 : L.getD k 1 = L[k] := List.getD_eq_getElem L (1 : G) hk0
    have e2 : L.getD (k + 2) 1 = L[k + 2] := List.getD_eq_getElem L (1 : G) hk2
    have hA0 : L[k] ∈ altLetter P₁ P₂ := hL.mem_getElem hk0
    have hA1 : L[k + 1] ∈ altLetter P₁ P₂ := hL.mem_getElem hk1
    have hA2 : L[k + 2] ∈ altLetter P₁ P₂ := hL.mem_getElem hk2
    have hd01 : DiffSide P₁ P₂ (L[k]) (L[k + 1]) := hL.diffSide_getElem (by omega)
    have hd12' : DiffSide P₁ P₂ (L[k + 1]) (L[(k + 1) + 1]) := hL.diffSide_getElem (by omega)
    have hd12 : DiffSide P₁ P₂ (L[k + 1]) (L[k + 2]) := by
      have helem : L[(k + 1) + 1] = L[k + 2] := getElem_congr_idx (by omega)
      rw [← helem]
      exact hd12'
    have hp1 : (L.take (k + 2)).prod = (L.take (k + 1)).prod * L[k + 1] := by
      have := List.prod_take_succ L (k + 1) hk1
      simpa using this
    have hp2 : (L.take ((k + 2) + 1)).prod = (L.take (k + 2)).prod * L[k + 2] :=
      List.prod_take_succ L (k + 2) hk2
    rw [walkV_succ, walkV_succ, e0, e2, hp2, hp1, mul_smul, mul_smul]
    intro hcontra
    have h2 : cV (L[k]) = L[k + 1] • (L[k + 2] • cV (L[k + 2])) :=
      MulAction.injective ((L.take (k + 1)).prod) hcontra
    have hc : cV (L[k + 2]) = cV (L[k]) :=
      cV_eq_cV (same_side_of_diff hd01 hd12).symm
    have hfix : L[k + 1] • cV (L[k]) = cV (L[k]) := by
      rw [cV_eq_aV hA0 hA1 hd01]; exact aV_fixed hP₁ hP₂ hA1
    have hmv : L[k + 2] • cV (L[k]) ≠ cV (L[k]) := by
      have hm := cV_moved h₁ h₂ hA2
      rwa [hc] at hm
    rw [hc] at h2
    have h4 : L[k + 1] • (L[k + 2] • cV (L[k])) ≠ cV (L[k]) := by
      intro h5
      have h6 : L[k + 1] • (L[k + 2] • cV (L[k])) = L[k + 1] • cV (L[k]) := by
        rw [h5, hfix]
      exact hmv ((smul_left_cancel_iff (L[k + 1])).mp h6)
    exact h4 h2.symm

private theorem dist_walkV (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (h12 : Γ.Adj α₁ α₂) (hP₁ : P₁ ≤ MulAction.stabilizer G α₁)
    (hP₂ : P₂ ≤ MulAction.stabilizer G α₂)
    (h₁ : P₁ ⊓ MulAction.stabilizer G α₂ = P₁ ⊓ P₂)
    (h₂ : P₂ ⊓ MulAction.stabilizer G α₁ = P₁ ⊓ P₂)
    {L : List G} (hL : IsAlt P₁ P₂ L) {k : ℕ} (hk : k ≤ L.length) :
    Γ.dist (walkV L 0) (walkV L k) = k := by
  let P : Arc Γ L.length :=
    { vert := fun i => walkV L i
      adj := fun i hi => walkV_adj hadj h12 hP₁ hP₂ hL i (by omega)
      nb := fun i hi => walkV_nb hP₁ hP₂ h₁ h₂ hL i (by omega) }
  exact Arc.dist_eq hT P k hk

private theorem dist_le_one_pair (h12 : Γ.Adj α₁ α₂) {z w : V} (hz : z ∈ ({α₁, α₂} : Set V))
    (hw : w ∈ ({α₁, α₂} : Set V)) : Γ.dist z w ≤ 1 := by
  have hmem : ∀ {z : V}, z ∈ ({α₁, α₂} : Set V) → z = α₁ ∨ z = α₂ := by
    intro z hz
    simpa using hz
  obtain (rfl | rfl) := hmem hz <;> obtain (rfl | rfl) := hmem hw
  · simp
  · rw [dist_eq_one_iff_adj.mpr h12]
  · rw [SimpleGraph.dist_comm, dist_eq_one_iff_adj.mpr h12]
  · simp

private theorem walkV_notMem (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (h12 : Γ.Adj α₁ α₂) (hP₁ : P₁ ≤ MulAction.stabilizer G α₁)
    (hP₂ : P₂ ≤ MulAction.stabilizer G α₂)
    (h₁ : P₁ ⊓ MulAction.stabilizer G α₂ = P₁ ⊓ P₂)
    (h₂ : P₂ ⊓ MulAction.stabilizer G α₁ = P₁ ⊓ P₂)
    {L : List G} (hL : IsAlt P₁ P₂ L) {k : ℕ} (hk1 : 1 ≤ k)
    (hkn : k ≤ L.length) : walkV L k ∉ ({α₁, α₂} : Set V) := by
  rcases Nat.eq_or_lt_of_le hk1 with hk | hk
  · subst hk
    show walkV L (0 + 1) ∉ ({α₁, α₂} : Set V)
    have h0 : L.getD 0 1 = L[0] := List.getD_eq_getElem L (1 : G) (by omega)
    have hA : L[0] ∈ altLetter P₁ P₂ := hL.mem_getElem (by omega)
    have hp1 : (L.take 1).prod = L[0] := by
      have := List.prod_take_succ L 0 (by omega)
      simpa using this
    rw [walkV_succ, h0, hp1]
    intro hmem
    have hmem' : L[0] • cV (L[0]) = aV (L[0]) ∨ L[0] • cV (L[0]) = cV (L[0]) := by
      have := pair_subset_aV_cV (P₁ := P₁) (α₁ := α₁) (α₂ := α₂) (L[0]) hmem
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    rcases hmem' with h | h
    · have hinj : cV (L[0]) = aV (L[0]) := by
        refine (smul_left_cancel_iff (L[0])).mp ?_
        rw [h, aV_fixed hP₁ hP₂ hA]
      exact aV_ne_cV h12.ne hinj.symm
    · exact cV_moved h₁ h₂ hA h
  · have hk2 : 2 ≤ k := hk
    intro hmem
    have hdist : Γ.dist (walkV L 0) (walkV L k) = k :=
      dist_walkV hT hadj h12 hP₁ hP₂ h₁ h₂ hL hkn
    have h0 : walkV L 0 ∈ ({α₁, α₂} : Set V) := by
      rw [walkV_zero]
      exact aV_mem_pair (L.getD 0 1)
    have hle := dist_le_one_pair h12 h0 hmem
    omega

private theorem alt_prod_not_mem_stabilizer (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (h12 : Γ.Adj α₁ α₂) (hP₁ : P₁ ≤ MulAction.stabilizer G α₁)
    (hP₂ : P₂ ≤ MulAction.stabilizer G α₂)
    (h₁ : P₁ ⊓ MulAction.stabilizer G α₂ = P₁ ⊓ P₂)
    (h₂ : P₂ ⊓ MulAction.stabilizer G α₁ = P₁ ⊓ P₂)
    {L : List G} (hL : IsAlt P₁ P₂ L) (hn : 2 ≤ L.length) :
    L.prod ∉ MulAction.stabilizer G α₁ ∧ L.prod ∉ MulAction.stabilizer G α₂ := by
  have hn1 : 1 ≤ L.length := by omega
  have hkl : L.length - 1 < L.length := by omega
  have hkl2 : L.length - 2 < L.length := by omega
  have hx : L[L.length - 1] ∈ altLetter P₁ P₂ := hL.mem_getElem hkl
  have hy : L[L.length - 2] ∈ altLetter P₁ P₂ := hL.mem_getElem hkl2
  have hd' : DiffSide P₁ P₂ (L[L.length - 2]) (L[(L.length - 2) + 1]) :=
    hL.diffSide_getElem (by omega)
  have hd : DiffSide P₁ P₂ (L[L.length - 2]) (L[L.length - 1]) := by
    have helem : L[(L.length - 2) + 1] = L[L.length - 1] := getElem_congr_idx (by omega)
    rw [← helem]
    exact hd'
  have hlast : L.getD (L.length - 1) 1 = L[L.length - 1] := List.getD_eq_getElem L (1 : G) hkl
  have hprev : L.getD (L.length - 2) 1 = L[L.length - 2] := List.getD_eq_getElem L (1 : G) hkl2
  have hvn : walkV L L.length = L.prod • cV (L[L.length - 1]) := by
    have h : walkV L (L.length - 1 + 1) =
        (L.take (L.length - 1 + 1)).prod • cV (L.getD (L.length - 1) 1) :=
      walkV_succ L (L.length - 1)
    rw [Nat.sub_add_cancel hn1] at h
    rw [h, hlast, List.take_length]
  have hvn1 : walkV L (L.length - 1) = L.prod • aV (L[L.length - 1]) := by
    have h : walkV L (L.length - 2 + 1) =
        (L.take (L.length - 2 + 1)).prod • cV (L.getD (L.length - 2) 1) :=
      walkV_succ L (L.length - 2)
    rw [show L.length - 2 + 1 = L.length - 1 from by omega] at h
    rw [h, hprev, cV_eq_aV hy hx hd]
    have hsplit : L.prod = (L.take (L.length - 1)).prod * L[L.length - 1] := by
      have h2 := List.prod_take_succ L (L.length - 1) hkl
      rwa [Nat.sub_add_cancel hn1, List.take_length] at h2
    rw [hsplit, mul_smul, aV_fixed hP₁ hP₂ hx]
  have key : ∀ z : V, z ∈ ({α₁, α₂} : Set V) → L.prod • z ∉ ({α₁, α₂} : Set V) := by
    intro z hz
    have hout1 : walkV L (L.length - 1) ∉ ({α₁, α₂} : Set V) :=
      walkV_notMem hT hadj h12 hP₁ hP₂ h₁ h₂ hL (by omega) (by omega)
    have hout2 : walkV L L.length ∉ ({α₁, α₂} : Set V) :=
      walkV_notMem hT hadj h12 hP₁ hP₂ h₁ h₂ hL (by omega) (by omega)
    have hz' : z = aV (L[L.length - 1]) ∨ z = cV (L[L.length - 1]) := by
      have h := pair_subset_aV_cV (P₁ := P₁) (α₁ := α₁) (α₂ := α₂) (L[L.length - 1]) hz
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
    rcases hz' with rfl | rfl
    · rwa [← hvn1]
    · rwa [← hvn]
  constructor
  · intro hstab
    exact key α₁ (by simp) (by rw [MulAction.mem_stabilizer_iff.mp hstab]; simp)
  · intro hstab
    exact key α₂ (by simp) (by rw [MulAction.mem_stabilizer_iff.mp hstab]; simp)

end Walk

end AltWord

theorem inf_sup_stabilizer_eq_left (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {α₁ α₂ : V} (h12 : Γ.Adj α₁ α₂) {P₁ P₂ : Subgroup G}
    (hP₁ : P₁ ≤ MulAction.stabilizer G α₁) (hP₂ : P₂ ≤ MulAction.stabilizer G α₂)
    (h₁ : P₁ ⊓ MulAction.stabilizer G α₂ = P₁ ⊓ P₂)
    (h₂ : P₂ ⊓ MulAction.stabilizer G α₁ = P₁ ⊓ P₂) :
    (P₁ ⊔ P₂) ⊓ MulAction.stabilizer G α₁ = P₁ := by
  refine le_antisymm ?_ ?_
  · rintro h ⟨hsup, hstab⟩
    rcases AltWord.isGood_of_mem_sup hsup with hD | ⟨L, hL, hprod⟩
    · exact (Subgroup.mem_inf.mp hD).1
    · subst h
      rcases L with _ | ⟨x₁, t⟩
      · exact (AltWord.isAlt_nil hL).elim
      rcases t with _ | ⟨x₂, l⟩
      · by_cases h1 : x₁ ∈ P₁
        · simpa using h1
        · have hmem : x₁ ∈ P₂ ⊓ MulAction.stabilizer G α₁ :=
            Subgroup.mem_inf.mpr ⟨AltWord.mem_right_of_mem_altLetter (AltWord.IsAlt.head_mem hL) h1,
              by simpa using hstab⟩
          rw [h₂] at hmem
          exact absurd hmem (AltWord.not_mem_inf_of_mem_altLetter (AltWord.IsAlt.head_mem hL))
      · exact absurd hstab
          (AltWord.alt_prod_not_mem_stabilizer hT hadj h12 hP₁ hP₂ h₁ h₂ hL (by simp)).1
  · intro h hh
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hh, hP₁ hh⟩

theorem sup_inf_stabilizer_eq (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {α₁ α₂ : V} (h12 : Γ.Adj α₁ α₂) {P₁ P₂ : Subgroup G}
    (hP₁ : P₁ ≤ MulAction.stabilizer G α₁) (hP₂ : P₂ ≤ MulAction.stabilizer G α₂)
    (h₁ : P₁ ⊓ MulAction.stabilizer G α₂ = P₁ ⊓ P₂)
    (h₂ : P₂ ⊓ MulAction.stabilizer G α₁ = P₁ ⊓ P₂) :
    (P₁ ⊔ P₂) ⊓ MulAction.stabilizer G α₁ = P₁ ∧
      (P₁ ⊔ P₂) ⊓ MulAction.stabilizer G α₂ = P₂ := by
  constructor
  · exact inf_sup_stabilizer_eq_left hT hadj h12 hP₁ hP₂ h₁ h₂
  · have h := inf_sup_stabilizer_eq_left (P₁ := P₂) (P₂ := P₁) (α₁ := α₂) (α₂ := α₁)
      hT hadj h12.symm hP₂ hP₁ (by rw [inf_comm P₂ P₁]; exact h₂)
      (by rw [inf_comm P₂ P₁]; exact h₁)
    rwa [sup_comm] at h

section TwoFive

variable {α₁ α₂ : V} {N₁ N₂ : Subgroup G}

private def edgeStab (α₁ α₂ : V) : Subgroup G :=
  MulAction.stabilizer G α₁ ⊓ MulAction.stabilizer G α₂

private def pOne (N₁ N₂ : Subgroup G) (α₁ α₂ : V) : Subgroup G :=
  N₁ ⊔ (edgeStab α₁ α₂ ⊓ N₂)

private def pTwo (N₁ N₂ : Subgroup G) (α₁ α₂ : V) : Subgroup G :=
  N₂ ⊔ (edgeStab α₁ α₂ ⊓ N₁)

private def dSub (N₁ N₂ : Subgroup G) (α₁ α₂ : V) : Subgroup G :=
  (edgeStab α₁ α₂ ⊓ N₁) ⊔ (edgeStab α₁ α₂ ⊓ N₂)

private theorem pOne_le {N₁ N₂ : Subgroup G} {α₁ α₂ : V}
    (hN₁ : N₁ ≤ MulAction.stabilizer G α₁) : pOne N₁ N₂ α₁ α₂ ≤ MulAction.stabilizer G α₁ :=
  sup_le hN₁ (le_trans inf_le_left inf_le_left)

private theorem pTwo_le {N₁ N₂ : Subgroup G} {α₁ α₂ : V}
    (hN₂ : N₂ ≤ MulAction.stabilizer G α₂) : pTwo N₁ N₂ α₁ α₂ ≤ MulAction.stabilizer G α₂ :=
  sup_le hN₂ (le_trans inf_le_left inf_le_right)

private theorem sup_inf_of_normal {A B E : Subgroup G} {α β : V}
    (hA : A ≤ MulAction.stabilizer G α) (hEα : E ≤ MulAction.stabilizer G α)
    (hEβ : E ≤ MulAction.stabilizer G β)
    (hGE : MulAction.stabilizer G α ⊓ MulAction.stabilizer G β ≤ E)
    (hnA : (A.subgroupOf (MulAction.stabilizer G α)).Normal) :
    (A ⊔ (E ⊓ B)) ⊓ MulAction.stabilizer G β = (E ⊓ A) ⊔ (E ⊓ B) := by
  have hAnorm : MulAction.stabilizer G α ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA).mp hnA
  have hBnorm : E ⊓ B ≤ Subgroup.normalizer (A : Set G) :=
    (inf_le_left.trans hEα).trans hAnorm
  refine le_antisymm ?_ ?_
  ·
    intro x hx
    obtain ⟨hxA, hxG⟩ := Subgroup.mem_inf.mp hx
    have hprod : (↑(A ⊔ (E ⊓ B)) : Set G) = (A : Set G) * ↑(E ⊓ B) :=
      Subgroup.coe_mul_of_right_le_normalizer_left A (E ⊓ B) hBnorm
    have hx' : x ∈ (A : Set G) * ↑(E ⊓ B) := by
      rw [← hprod]
      exact hxA
    obtain ⟨a, ha, b, hb, hab⟩ := hx'
    have hbE : b ∈ E := (Subgroup.mem_inf.mp hb).1
    have hbG : b ∈ MulAction.stabilizer G β := hEβ hbE
    have haG : a ∈ MulAction.stabilizer G β := by
      have : a = x * b⁻¹ := by rw [← hab]; simp
      rw [this]
      exact mul_mem hxG (inv_mem hbG)
    have haE : a ∈ E := hGE (Subgroup.mem_inf.mpr ⟨hA ha, haG⟩)
    rw [← hab]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨haE, ha⟩))
      (Subgroup.mem_sup_right hb)
  ·
    refine le_inf (sup_le ?_ ?_) (sup_le ?_ ?_)
    · exact le_trans inf_le_right le_sup_left
    · exact le_sup_right
    · exact le_trans inf_le_left hEβ
    · exact le_trans inf_le_left hEβ

private theorem pOne_inf_stabRight {α₁ α₂ : V} {N₁ N₂ : Subgroup G}
    (hN₁ : N₁ ≤ MulAction.stabilizer G α₁)
    (hn₁ : (N₁.subgroupOf (MulAction.stabilizer G α₁)).Normal) :
    pOne N₁ N₂ α₁ α₂ ⊓ MulAction.stabilizer G α₂ = dSub N₁ N₂ α₁ α₂ := by
  have h := sup_inf_of_normal (A := N₁) (B := N₂) (E := edgeStab α₁ α₂) (α := α₁) (β := α₂)
    hN₁ inf_le_left inf_le_right le_rfl hn₁
  simpa only [pOne, dSub] using h

private theorem pTwo_inf_stabLeft {α₁ α₂ : V} {N₁ N₂ : Subgroup G}
    (hN₂ : N₂ ≤ MulAction.stabilizer G α₂)
    (hn₂ : (N₂.subgroupOf (MulAction.stabilizer G α₂)).Normal) :
    pTwo N₁ N₂ α₁ α₂ ⊓ MulAction.stabilizer G α₁ = dSub N₁ N₂ α₁ α₂ := by
  have h := sup_inf_of_normal (A := N₂) (B := N₁) (E := edgeStab α₁ α₂) (α := α₂) (β := α₁)
    hN₂ inf_le_right inf_le_left ?_ hn₂
  · simpa only [pTwo, dSub, sup_comm] using h
  · show MulAction.stabilizer G α₂ ⊓ MulAction.stabilizer G α₁ ≤ edgeStab α₁ α₂
    rw [inf_comm]
    exact le_rfl

private theorem pOne_inf_pTwo {α₁ α₂ : V} {N₁ N₂ : Subgroup G}
    (hN₁ : N₁ ≤ MulAction.stabilizer G α₁) (hN₂ : N₂ ≤ MulAction.stabilizer G α₂)
    (hn₁ : (N₁.subgroupOf (MulAction.stabilizer G α₁)).Normal) :
    pOne N₁ N₂ α₁ α₂ ⊓ pTwo N₁ N₂ α₁ α₂ = dSub N₁ N₂ α₁ α₂ := by
  refine le_antisymm ?_ ?_
  ·
    calc pOne N₁ N₂ α₁ α₂ ⊓ pTwo N₁ N₂ α₁ α₂
        ≤ pOne N₁ N₂ α₁ α₂ ⊓ MulAction.stabilizer G α₂ :=
          le_inf inf_le_left (le_trans inf_le_right (pTwo_le hN₂))
      _ = dSub N₁ N₂ α₁ α₂ := pOne_inf_stabRight hN₁ hn₁
  ·
    refine le_inf (sup_le ?_ ?_) (sup_le ?_ ?_)
    · exact le_trans inf_le_right le_sup_left
    · exact le_sup_right
    · exact le_sup_right
    · exact le_trans inf_le_right le_sup_left

private theorem sup_pOne_pTwo_eq_top (h : Hyp30 Γ G) {α₁ α₂ : V} (h12 : Γ.Adj α₁ α₂)
    {N₁ N₂ : Subgroup G} (hN₁ : N₁ ≤ MulAction.stabilizer G α₁)
    (hN₂ : N₂ ≤ MulAction.stabilizer G α₂)
    (hn₁ : (N₁.subgroupOf (MulAction.stabilizer G α₁)).Normal)
    (hn₂ : (N₂.subgroupOf (MulAction.stabilizer G α₂)).Normal)
    (ht₁ : ∀ a b : V, Γ.Adj α₁ a → Γ.Adj α₁ b → ∃ g ∈ N₁, g • a = b)
    (ht₂ : ∀ a b : V, Γ.Adj α₂ a → Γ.Adj α₂ b → ∃ g ∈ N₂, g • a = b) :
    pOne N₁ N₂ α₁ α₂ ⊔ pTwo N₁ N₂ α₁ α₂ = ⊤ := by
  have hst₁ : MulAction.stabilizer G α₁ ≤ Subgroup.normalizer (N₁ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN₁).mp hn₁
  have hst₂ : MulAction.stabilizer G α₂ ≤ Subgroup.normalizer (N₂ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN₂).mp hn₂
  have htrans : EdgeTransitive Γ (pOne N₁ N₂ α₁ α₂ ⊔ pTwo N₁ N₂ α₁ α₂) := by
    refine edgeTransitive_of_locTrans h.isTree.connected h.adj_smul _ h12 ?_ ?_
    · intro a b ha hb
      obtain ⟨g, hg, hgab⟩ := ht₁ a b ha hb
      exact ⟨g, Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_left hg), hN₁ hg⟩, hgab⟩
    · intro a b ha hb
      obtain ⟨g, hg, hgab⟩ := ht₂ a b ha hb
      exact ⟨g, Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_sup_right (Subgroup.mem_sup_left hg), hN₂ hg⟩, hgab⟩
  have hsup : (pOne N₁ N₂ α₁ α₂ ⊔ pTwo N₁ N₂ α₁ α₂) ⊔ edgeStab α₁ α₂ = ⊤ :=
    sup_eq_top_of_edgeTransitive h.adj_smul h.preservesParts h12 htrans
  have hE₁ : edgeStab α₁ α₂ ≤ Subgroup.normalizer (N₁ : Set G) := inf_le_left.trans hst₁
  have hE₂ : edgeStab α₁ α₂ ≤ Subgroup.normalizer (N₂ : Set G) := inf_le_right.trans hst₂
  have hE_in₁ : edgeStab α₁ α₂ ≤
      Subgroup.normalizer ((edgeStab α₁ α₂ ⊓ N₁ : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro e he n hn
    obtain ⟨hnE, hnN⟩ := Subgroup.mem_inf.mp hn
    exact Subgroup.mem_inf.mpr
      ⟨mul_mem (mul_mem he hnE) (inv_mem he),
        (Subgroup.mem_normalizer_iff.mp (hE₁ he) n).mp hnN⟩
  have hE_in₂ : edgeStab α₁ α₂ ≤
      Subgroup.normalizer ((edgeStab α₁ α₂ ⊓ N₂ : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro e he n hn
    obtain ⟨hnE, hnN⟩ := Subgroup.mem_inf.mp hn
    exact Subgroup.mem_inf.mpr
      ⟨mul_mem (mul_mem he hnE) (inv_mem he),
        (Subgroup.mem_normalizer_iff.mp (hE₂ he) n).mp hnN⟩
  have hP₁ : edgeStab α₁ α₂ ≤
      Subgroup.normalizer ((pOne N₁ N₂ α₁ α₂ : Subgroup G) : Set G) :=
    (le_inf hE₁ hE_in₂).trans
      (Subgroup.inf_normalizer_le_normalizer_sup N₁ (edgeStab α₁ α₂ ⊓ N₂))
  have hP₂ : edgeStab α₁ α₂ ≤
      Subgroup.normalizer ((pTwo N₁ N₂ α₁ α₂ : Subgroup G) : Set G) :=
    (le_inf hE₂ hE_in₁).trans
      (Subgroup.inf_normalizer_le_normalizer_sup N₂ (edgeStab α₁ α₂ ⊓ N₁))
  have hN : edgeStab α₁ α₂ ≤ Subgroup.normalizer
      (((pOne N₁ N₂ α₁ α₂ ⊔ pTwo N₁ N₂ α₁ α₂) : Subgroup G) : Set G) :=
    (le_inf hP₁ hP₂).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hnormal : (pOne N₁ N₂ α₁ α₂ ⊔ pTwo N₁ N₂ α₁ α₂).Normal := by
    refine Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr ?_)
    rw [← hsup]
    exact sup_le Subgroup.le_normalizer hN
  exact h.minimal _ hnormal htrans

private theorem two_five_facts (h : Hyp30 Γ G) {α₁ α₂ : V} (h12 : Γ.Adj α₁ α₂)
    {N₁ N₂ : Subgroup G} (hN₁ : N₁ ≤ MulAction.stabilizer G α₁)
    (hN₂ : N₂ ≤ MulAction.stabilizer G α₂)
    (hn₁ : (N₁.subgroupOf (MulAction.stabilizer G α₁)).Normal)
    (hn₂ : (N₂.subgroupOf (MulAction.stabilizer G α₂)).Normal)
    (ht₁ : ∀ a b : V, Γ.Adj α₁ a → Γ.Adj α₁ b → ∃ g ∈ N₁, g • a = b)
    (ht₂ : ∀ a b : V, Γ.Adj α₂ a → Γ.Adj α₂ b → ∃ g ∈ N₂, g • a = b) :
    MulAction.stabilizer G α₁ = pOne N₁ N₂ α₁ α₂ ∧
      MulAction.stabilizer G α₂ = pTwo N₁ N₂ α₁ α₂ ∧
      edgeStab α₁ α₂ = dSub N₁ N₂ α₁ α₂ := by
  have htop := sup_pOne_pTwo_eq_top h h12 hN₁ hN₂ hn₁ hn₂ ht₁ ht₂
  have hD₁ : pOne N₁ N₂ α₁ α₂ ⊓ MulAction.stabilizer G α₂ =
      pOne N₁ N₂ α₁ α₂ ⊓ pTwo N₁ N₂ α₁ α₂ := by
    rw [pOne_inf_stabRight hN₁ hn₁, pOne_inf_pTwo hN₁ hN₂ hn₁]
  have hD₂ : pTwo N₁ N₂ α₁ α₂ ⊓ MulAction.stabilizer G α₁ =
      pOne N₁ N₂ α₁ α₂ ⊓ pTwo N₁ N₂ α₁ α₂ := by
    rw [pTwo_inf_stabLeft hN₂ hn₂, pOne_inf_pTwo hN₁ hN₂ hn₁]
  obtain ⟨hleft, hright⟩ := sup_inf_stabilizer_eq h.isTree h.adj_smul h12
    (pOne_le hN₁) (pTwo_le hN₂) hD₁ hD₂
  have hleft' : MulAction.stabilizer G α₁ = pOne N₁ N₂ α₁ α₂ := by
    rw [← hleft, htop, top_inf_eq]
  have hright' : MulAction.stabilizer G α₂ = pTwo N₁ N₂ α₁ α₂ := by
    rw [← hright, htop, top_inf_eq]
  refine ⟨hleft', hright', ?_⟩
  show MulAction.stabilizer G α₁ ⊓ MulAction.stabilizer G α₂ = dSub N₁ N₂ α₁ α₂
  rw [hleft', pOne_inf_stabRight hN₁ hn₁]

end TwoFive

theorem inf_stabilizer_eq_sup (h : Hyp30 Γ G) {α₁ α₂ : V} (h12 : Γ.Adj α₁ α₂)
    {N₁ N₂ : Subgroup G} (hN₁ : N₁ ≤ MulAction.stabilizer G α₁)
    (hN₂ : N₂ ≤ MulAction.stabilizer G α₂)
    (hn₁ : (N₁.subgroupOf (MulAction.stabilizer G α₁)).Normal)
    (hn₂ : (N₂.subgroupOf (MulAction.stabilizer G α₂)).Normal)
    (ht₁ : ∀ a b : V, Γ.Adj α₁ a → Γ.Adj α₁ b → ∃ g ∈ N₁, g • a = b)
    (ht₂ : ∀ a b : V, Γ.Adj α₂ a → Γ.Adj α₂ b → ∃ g ∈ N₂, g • a = b) :
    MulAction.stabilizer G α₁ ⊓ MulAction.stabilizer G α₂ =
      (MulAction.stabilizer G α₁ ⊓ MulAction.stabilizer G α₂ ⊓ N₁) ⊔
        (MulAction.stabilizer G α₁ ⊓ MulAction.stabilizer G α₂ ⊓ N₂) :=
  (two_five_facts h h12 hN₁ hN₂ hn₁ hn₂ ht₁ ht₂).2.2

theorem stabilizer_eq_sup_left (h : Hyp30 Γ G) {α₁ α₂ : V} (h12 : Γ.Adj α₁ α₂)
    {N₁ N₂ : Subgroup G} (hN₁ : N₁ ≤ MulAction.stabilizer G α₁)
    (hN₂ : N₂ ≤ MulAction.stabilizer G α₂)
    (hn₁ : (N₁.subgroupOf (MulAction.stabilizer G α₁)).Normal)
    (hn₂ : (N₂.subgroupOf (MulAction.stabilizer G α₂)).Normal)
    (ht₁ : ∀ a b : V, Γ.Adj α₁ a → Γ.Adj α₁ b → ∃ g ∈ N₁, g • a = b)
    (ht₂ : ∀ a b : V, Γ.Adj α₂ a → Γ.Adj α₂ b → ∃ g ∈ N₂, g • a = b) :
    MulAction.stabilizer G α₁ =
      N₁ ⊔ (MulAction.stabilizer G α₁ ⊓ MulAction.stabilizer G α₂ ⊓ N₂) :=
  (two_five_facts h h12 hN₁ hN₂ hn₁ hn₂ ht₁ ht₂).1

end CFSG.Quasithin.St84

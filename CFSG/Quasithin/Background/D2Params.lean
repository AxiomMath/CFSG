module

public import CFSG.Quasithin.Background.D2Basic
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

@[expose] def IsA2 (X A : Subgroup (MulAut V)) : Prop := A ≤ X ∧ A ≠ ⊥ ∧ IsElemAbelian2 A

@[expose] noncomputable def rAV (A : Subgroup (MulAut V)) : ℚ :=
  (rkIdx (fixV A) : ℚ) / (rk A : ℚ)

@[expose] def Rle (X : Subgroup (MulAut V)) (r : ℚ) : Set (Subgroup (MulAut V)) :=
  {A | IsA2 X A ∧ rAV A ≤ r}

@[expose] def Req (X : Subgroup (MulAut V)) (r : ℚ) : Set (Subgroup (MulAut V)) :=
  {A | IsA2 X A ∧ rAV A = r}

@[expose] def RPlus (X : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {A | IsA2 X A ∧ ∀ B : Subgroup (MulAut V), B ≠ ⊥ → B ≤ A → rAV A ≤ rAV B}

@[expose] def kRle (X : Subgroup (MulAut V)) (k : ℕ) (r : ℚ) : Set (Subgroup (MulAut V)) :=
  {A | A ∈ Rle X r ∧ commSeries A k = ⊥}

@[expose] def kReq (X : Subgroup (MulAut V)) (k : ℕ) (r : ℚ) : Set (Subgroup (MulAut V)) :=
  {A | A ∈ Req X r ∧ commSeries A k = ⊥}

@[expose] def RPlusLe (X : Subgroup (MulAut V)) (r : ℚ) : Set (Subgroup (MulAut V)) :=
  Rle X r ∩ RPlus X

@[expose] def kRPlusLe (X : Subgroup (MulAut V)) (k : ℕ) (r : ℚ) : Set (Subgroup (MulAut V)) :=
  kRle X k r ∩ RPlus X

@[expose] def RPlusEq (X : Subgroup (MulAut V)) (r : ℚ) : Set (Subgroup (MulAut V)) :=
  Req X r ∩ RPlus X

@[expose] def kRPlusEq (X : Subgroup (MulAut V)) (k : ℕ) (r : ℚ) : Set (Subgroup (MulAut V)) :=
  kReq X k r ∩ RPlus X

@[expose] def kqValues (X : Subgroup (MulAut V)) (k : ℕ) : Set ℚ :=
  {s | ∃ A, IsA2 X A ∧ commSeries A k = ⊥ ∧ rAV A = s}

theorem kqValues_finite [Finite V] (X : Subgroup (MulAut V)) (k : ℕ) :
    (kqValues X k).Finite := by
  refine (Set.finite_range (fun A : Subgroup (MulAut V) => rAV A)).subset ?_
  rintro s ⟨A, -, -, rfl⟩
  exact ⟨A, rfl⟩

@[expose] noncomputable def kq [Finite V] (X : Subgroup (MulAut V)) (k : ℕ) : WithTop ℚ :=
  (kqValues_finite X k).toFinset.min

@[expose] noncomputable def qOf [Finite V] (X : Subgroup (MulAut V)) : WithTop ℚ := kq X 2

@[expose] noncomputable def qhatOf [Finite V] (X : Subgroup (MulAut V)) : WithTop ℚ := kq X 3

@[expose] def Qset (X : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) := kRle X 2 2

@[expose] def Qhat (X : Subgroup (MulAut V)) (s : ℚ) : Set (Subgroup (MulAut V)) := kRle X 3 s

@[expose] def QhatStar [Finite V] (X : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {A | ∃ r : ℚ, qhatOf X = (r : WithTop ℚ) ∧ r ≤ 2 ∧ A ∈ kRle X 3 r ∧
    ∀ B ∈ kRle X 3 r, B ≤ A → B = A}

@[expose] def Jhat [Finite V] (X : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  ⨆ A ∈ QhatStar X, A

theorem IsA2.mono {X A B : Subgroup (MulAut V)} (h : IsA2 X A) (hB : B ≤ A) (hne : B ≠ ⊥) :
    IsA2 X B :=
  ⟨hB.trans h.1, hne, fun a ha b hb => h.2.2.1 a (hB ha) b (hB hb),
    fun a ha => h.2.2.2 a (hB ha)⟩

theorem IsA2.le {X A : Subgroup (MulAut V)} (h : IsA2 X A) : A ≤ X := h.1

theorem IsA2.ne_bot {X A : Subgroup (MulAut V)} (h : IsA2 X A) : A ≠ ⊥ := h.2.1

theorem IsA2.isElemAbelian2 {X A : Subgroup (MulAut V)} (h : IsA2 X A) : IsElemAbelian2 A :=
  h.2.2

theorem IsElemAbelian2.isPGroup {A : Subgroup (MulAut V)} (h : IsElemAbelian2 A) :
    IsPGroup 2 A :=
  fun a => ⟨1, Subtype.ext (by simpa using h.2 (a : MulAut V) a.2)⟩

theorem IsElemAbelian2.rk_pos [Finite V] {A : Subgroup (MulAut V)} (h : IsElemAbelian2 A)
    (hne : A ≠ ⊥) : 0 < rk A := by
  rcases Nat.eq_zero_or_pos (rk A) with h0 | h0
  · exact absurd ((rk_eq_zero_iff_of_isPGroup h.isPGroup).mp h0) hne
  · exact h0

theorem IsA2.rk_pos [Finite V] {X A : Subgroup (MulAut V)} (h : IsA2 X A) : 0 < rk A :=
  h.2.2.rk_pos h.2.1

theorem IsA2.rAV_mul [Finite V] {X A : Subgroup (MulAut V)} (h : IsA2 X A) :
    rAV A * (rk A : ℚ) = (rkIdx (fixV A) : ℚ) := by
  unfold rAV
  have : (rk A : ℚ) ≠ 0 := by exact_mod_cast h.rk_pos.ne'
  field_simp

section KqApi

variable [Finite V]

theorem kq_le_iff {X : Subgroup (MulAut V)} {k : ℕ} {r : ℚ} :
    kq X k ≤ (r : WithTop ℚ) ↔ ∃ A, IsA2 X A ∧ commSeries A k = ⊥ ∧ rAV A ≤ r := by
  constructor
  · intro h
    by_cases htop : kq X k = ⊤
    · rw [htop] at h
      exact absurd h (by simp)
    · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp htop
      have hmem : a ∈ (kqValues_finite X k).toFinset := Finset.mem_of_min ha.symm
      rw [Set.Finite.mem_toFinset] at hmem
      obtain ⟨A, hA, hAk, rfl⟩ := hmem
      rw [← ha] at h
      exact ⟨A, hA, hAk, WithTop.coe_le_coe.mp h⟩
  · rintro ⟨A, hA, hAk, hr⟩
    refine (Finset.min_le (a := rAV A) ?_).trans (WithTop.coe_le_coe.mpr hr)
    rw [Set.Finite.mem_toFinset]
    exact ⟨A, hA, hAk, rfl⟩

theorem le_kq_iff {X : Subgroup (MulAut V)} {k : ℕ} {r : ℚ} :
    (r : WithTop ℚ) ≤ kq X k ↔ ∀ A, IsA2 X A → commSeries A k = ⊥ → r ≤ rAV A := by
  unfold kq
  rw [Finset.le_min_iff]
  constructor
  · intro h A hA hAk
    have := h (rAV A) (by rw [Set.Finite.mem_toFinset]; exact ⟨A, hA, hAk, rfl⟩)
    exact WithTop.coe_le_coe.mp this
  · intro h s hs
    rw [Set.Finite.mem_toFinset] at hs
    obtain ⟨A, hA, hAk, rfl⟩ := hs
    exact WithTop.coe_le_coe.mpr (h A hA hAk)

theorem kq_lt_iff {X : Subgroup (MulAut V)} {k : ℕ} {r : ℚ} :
    kq X k < (r : WithTop ℚ) ↔ ∃ A, IsA2 X A ∧ commSeries A k = ⊥ ∧ rAV A < r := by
  rw [← not_le, le_kq_iff]
  push Not
  rfl

theorem lt_kq_iff {X : Subgroup (MulAut V)} {k : ℕ} {r : ℚ} :
    (r : WithTop ℚ) < kq X k ↔ ∀ A, IsA2 X A → commSeries A k = ⊥ → r < rAV A := by
  rw [← not_le, kq_le_iff]
  push Not
  rfl

theorem kq_eq_top_iff {X : Subgroup (MulAut V)} {k : ℕ} :
    kq X k = ⊤ ↔ ¬ ∃ A, IsA2 X A ∧ commSeries A k = ⊥ := by
  unfold kq
  rw [Finset.min_eq_top, Finset.eq_empty_iff_forall_notMem]
  constructor
  · rintro h ⟨A, hA, hAk⟩
    exact h (rAV A) (by rw [Set.Finite.mem_toFinset]; exact ⟨A, hA, hAk, rfl⟩)
  · intro h s hs
    rw [Set.Finite.mem_toFinset] at hs
    obtain ⟨A, hA, hAk, -⟩ := hs
    exact h ⟨A, hA, hAk⟩

theorem kq_eq_coe_iff {X : Subgroup (MulAut V)} {k : ℕ} {r : ℚ} :
    kq X k = (r : WithTop ℚ) ↔
      (∃ A, IsA2 X A ∧ commSeries A k = ⊥ ∧ rAV A = r) ∧
        ∀ A, IsA2 X A → commSeries A k = ⊥ → r ≤ rAV A := by
  constructor
  · intro h
    have h1 := kq_le_iff.mp h.le
    have h2 := le_kq_iff.mp h.ge
    obtain ⟨A, hA, hAk, hAr⟩ := h1
    exact ⟨⟨A, hA, hAk, le_antisymm hAr (h2 A hA hAk)⟩, h2⟩
  · rintro ⟨⟨A, hA, hAk, hAr⟩, h2⟩
    exact le_antisymm (kq_le_iff.mpr ⟨A, hA, hAk, hAr.le⟩) (le_kq_iff.mpr h2)

theorem qOf_le_iff {X : Subgroup (MulAut V)} {r : ℚ} :
    qOf X ≤ (r : WithTop ℚ) ↔ ∃ A, IsA2 X A ∧ IsQuadratic A ∧ rAV A ≤ r := by
  unfold qOf
  rw [kq_le_iff]
  simp only [isQuadratic_iff_commSeries_two]

end KqApi

theorem QhatStar_spec [Finite V] {X A : Subgroup (MulAut V)} (hA : A ∈ QhatStar X) :
    ∃ r : ℚ, qhatOf X = (r : WithTop ℚ) ∧ r ≤ 2 ∧ A ∈ kReq X 3 r ∧
      ∀ B ∈ kRle X 3 r, B ≤ A → B = A := by
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hAk⟩, hmin⟩ := hA
  have h1 : (r : WithTop ℚ) ≤ kq X 3 := hr.ge
  have h3 := le_kq_iff.mp h1 A hA2 hAk
  exact ⟨r, hr, hr2, ⟨⟨hA2, le_antisymm hAr h3⟩, hAk⟩, hmin⟩

end CFSG.Quasithin

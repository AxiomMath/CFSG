module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped Pointwise commutatorElement

variable {K K' : Type*} [Group K] [Group K']

@[expose] noncomputable def fratSub (R : Subgroup K) : Subgroup K := (frattini ↥R).map R.subtype

@[expose] def fratGen (q : ℕ) (A : Subgroup K) : Subgroup K :=
  ⁅A, A⁆ ⊔ Subgroup.closure {x | ∃ a ∈ A, x = a ^ q}

theorem fratSub_le (R : Subgroup K) : fratSub R ≤ R := Subgroup.map_subtype_le _

theorem map_fratGen (q : ℕ) (f : K →* K') (A : Subgroup K) :
    (fratGen q A).map f = fratGen q (A.map f) := by
  unfold fratGen
  rw [Subgroup.map_sup, Subgroup.map_commutator, MonoidHom.map_closure]
  congr 2
  ext x
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨f a, ⟨a, ha, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a ^ q, ⟨a, ha, rfl⟩, by simp⟩

@[expose] def IsPiece (q : ℕ) (S R : Subgroup K) : Prop :=
  R ≠ ⊥ ∧ IsPGroup q ↥R ∧ S ≤ normalizer (R : Set K) ∧
    ∀ Z : Subgroup K, Z ≤ R → S ≤ normalizer (Z : Set K) → Z ≤ fratSub R ∨ Z = R

section Finite

variable [Finite K]

theorem fratSub_eq_fratGen {q : ℕ} (hq : q.Prime) {A : Subgroup K} (hA : IsPGroup q ↥A) :
    fratSub A = fratGen q A := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (IsPGroup q ↥A) := ⟨hA⟩
  unfold fratSub fratGen
  rw [CFSG.frattini_eq_closure_commutator_union_powers (R := ↥A) (p := q), MonoidHom.map_closure,
    Set.image_union, Subgroup.closure_union]
  congr 1
  · have h1 : Subgroup.map A.subtype ⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆ = ⁅A, A⁆ := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← Subgroup.coe_map, Subgroup.closure_eq]
    exact h1
  · congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, y.2, by simp⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨_, ⟨⟨a, ha⟩, rfl⟩, by simp⟩

theorem eq_of_sup_fratSub_eq {R Z : Subgroup K} (hZR : Z ≤ R) (h : Z ⊔ fratSub R = R) : Z = R := by
  have h1 : Z.subgroupOf R ⊔ frattini ↥R = ⊤ := by
    apply Subgroup.map_injective R.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hZR, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact h
  exact le_antisymm hZR (Subgroup.subgroupOf_eq_top.mp (frattini_nongenerating h1))

theorem fratSub_lt {R : Subgroup K} (hR : R ≠ ⊥) : fratSub R < R :=
  lt_of_le_of_ne (fratSub_le R) fun h =>
    hR (eq_of_sup_fratSub_eq bot_le (by rw [bot_sup_eq]; exact h)).symm

theorem isPGroup_map {q : ℕ} (f : K →* K') {A : Subgroup K} (hA : IsPGroup q ↥A) :
    IsPGroup q ↥(A.map f) :=
  hA.of_surjective (f.subgroupMap A) (f.subgroupMap_surjective A)

theorem map_fratSub [Finite K'] {q : ℕ} (hq : q.Prime) (f : K →* K') {A : Subgroup K}
    (hA : IsPGroup q ↥A) :
    (fratSub A).map f = fratSub (A.map f) := by
  rw [fratSub_eq_fratGen hq hA, fratSub_eq_fratGen hq (isPGroup_map f hA), map_fratGen]

theorem mem_normalizer_fratSub {q : ℕ} (hq : q.Prime) {A : Subgroup K} (hA : IsPGroup q ↥A)
    {g : K} (hg : g ∈ normalizer (A : Set K)) : g ∈ normalizer (fratSub A : Set K) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  rw [map_fratSub hq _ hA, hg]

end Finite

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

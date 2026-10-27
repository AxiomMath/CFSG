module

public import CFSG.Sporadic.Co2Smith.HPCount
public import CFSG.Sporadic.Co2Smith.HPRep

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

@[expose] noncomputable def cE
    (e n : ℕ) : Cz := ⟨cElt e n, cElt_mem e n⟩

@[expose] noncomputable def zCz : Cz := ⟨z0, z0_mem_Cz⟩

@[expose] def RepC (y : Cz) (R : Array ℕ) : Prop :=
  Native.validM R = true ∧ ((y : K)).val.val = rowsMatrix 22 R

theorem RepC.mul
    {y y' : Cz} {R R' : Array ℕ} (h : RepC y R) (h' : RepC y' R') :
    RepC (y * y') (Native.mulRowsF R R') := by
  refine ⟨?_, ?_⟩
  · rw [mulRowsF_eq]
    exact validM_mulRows h.1 h'.1
  · rw [mulRowsF_eq, rowsMatrix_mulRows, Subgroup.coe_mul, val_val_mul, h.2, h'.2]

theorem RepC.eq
    {y y' : Cz} {R : Array ℕ} (h : RepC y R) (h' : RepC y' R) : y = y' :=
  Subtype.ext (eq_of_val_eq (h.2.trans h'.2.symm))

theorem RepC.unique
    {y : Cz} {R R' : Array ℕ} (h : RepC y R) (h' : RepC y R') : R = R' :=
  eq_of_rowsMatrix_eq h.1 h'.1 (h.2.symm.trans h'.2)

theorem RepC.eq_iff
    {y y' : Cz} {R R' : Array ℕ} (h : RepC y R) (h' : RepC y' R') :
    y = y' ↔ R = R' := by
  constructor
  · rintro rfl
    exact h.unique h'
  · rintro rfl
    exact h.eq h'

theorem repC_one : RepC 1 (idRows 22) :=
  ⟨validM_idRows, by rw [Subgroup.coe_one, val_val_one, rowsMatrix_idRows]⟩

theorem cE_injOn
    {e e' n n' : ℕ} (he : e < 512) (he' : e' < 512) (hn : n < 1451520)
    (hn' : n' < 1451520) (h : cE e n = cE e' n') : e = e' ∧ n = n' :=
  cElt_injOn he he' hn hn' (congrArg Subtype.val h)

theorem exists_cE
    (y : Cz) : ∃ e < 512, ∃ n < 1451520, cE e n = y := by
  obtain ⟨e, he, n, hn, h⟩ := exists_cElt y.2
  exact ⟨e, he, n, hn, Subtype.ext h⟩

open Classical in
theorem card_eq_cnt_aux {α : Type*} (M N : ℕ) (f : ℕ → ℕ → α)
    (hsurj : ∀ y, ∃ e < M, ∃ n < N, f e n = y)
    (hinj : ∀ e e' n n', e < M → e' < M → n < N → n' < N → f e n = f e' n' → e = e' ∧ n = n')
    (P : α → Prop) (c : ℕ → ℕ → Bool) (g : ℕ → Bool)
    (hg : ∀ e < M, ∀ n < N, P (f e n) → g n = true)
    (hP : ∀ e < M, ∀ n < N, g n = true → (c e n = true ↔ P (f e n))) :
    Nat.card {y : α // P y} =
      (((List.range N).filter g).map fun n =>
        ((List.range M).filter fun e => c e n).length).sum := by
  have hinj' : Set.InjOn (fun p : ℕ × ℕ => f p.1 p.2)
      (↑((Finset.range M) ×ˢ (Finset.range N)) : Set (ℕ × ℕ)) := by
    rintro ⟨e, n⟩ hp ⟨e', n'⟩ hp' h
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio] at hp hp'
    obtain ⟨h1, h2⟩ := hinj e e' n n' hp.1 hp'.1 hp.2 hp'.2 h
    rw [h1, h2]
  have himg : ∀ y : α, P y ↔ y ∈ (((Finset.range M) ×ˢ (Finset.range N)).filter
      fun p => P (f p.1 p.2)).image (fun p : ℕ × ℕ => f p.1 p.2) := by
    intro y
    constructor
    · intro hy
      obtain ⟨e, he, n, hn, rfl⟩ := hsurj y
      exact Finset.mem_image.mpr ⟨(e, n), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr he, Finset.mem_range.mpr hn⟩, hy⟩, rfl⟩
    · intro hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hp).2
  have hcard : Nat.card {y : α // P y} =
      (((Finset.range M) ×ˢ (Finset.range N)).filter fun p => P (f p.1 p.2)).card := by
    rw [← Finset.card_image_of_injOn
      (hinj'.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight himg)
  rw [hcard, sum_filter_range, Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' := Finset.mem_range.mp hn
  by_cases hgn : g n
  · rw [ite_eq_left hgn, length_filter_range, Finset.card_filter]
    refine Finset.sum_congr rfl fun e he => ?_
    have he' := Finset.mem_range.mp he
    simp only [hP e he' n hn' hgn]
  · rw [ite_eq_right hgn]
    refine Finset.sum_eq_zero fun e he => ?_
    have he' := Finset.mem_range.mp he
    rw [ite_eq_right fun h => hgn (hg e he' n hn' h)]

end CFSG.Sporadic.Co2Smith

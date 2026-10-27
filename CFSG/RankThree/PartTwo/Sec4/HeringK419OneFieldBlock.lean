module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringOF

open Matrix
open scoped _root_.Classical commutatorElement

theorem commutator_eq_top_of_simple_nonabelian {P : Type*} [Group P] (hs : IsSimpleGroup P)
    (hnc : ∃ a b : P, a * b ≠ b * a) : commutator P = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator P) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have hmem : ⁅a, b⁆ ∈ commutator P := Subgroup.commutator_mem_commutator
      (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at hmem
    exact hab (commutatorElement_eq_one_iff_mul_comm.mp hmem)
  · exact h

theorem eq_one_of_perfect {P : Type*} [Group P] (hP : commutator P = ⊤) {A : Type*} [CommGroup A]
    (f : P →* A) (p : P) : f p = 1 := by
  have hle : commutator P ≤ f.ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.mpr
      (mul_comm _ _)]
  rw [hP] at hle
  exact (MonoidHom.mem_ker.mp (hle (Subgroup.mem_top p)))

section Block

variable {E : Type*} [Field E] {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → E)
  {P : Type*} [Group P] (M : P →* Matrix ι ι E)
  (hblock : ∀ (p : P) (i j : ι), μ i ≠ μ j → M p i j = 0)

include hblock in
@[expose] noncomputable def blk (l : E) : P →* Matrix {j // μ j = l} {j // μ j = l} E where
  toFun p := (M p).submatrix Subtype.val Subtype.val
  map_one' := by
    ext i j
    simp [Matrix.one_apply, Subtype.ext_iff]
  map_mul' p q := by
    ext i j
    have h1 : (M (p * q)) i j = ∑ k, M p i k * M q k j := by
      rw [map_mul, Matrix.mul_apply]
    have h2 : ∑ k, M p i k * M q k j =
        ∑ k : {k // μ k = l}, M p i k * M q k j := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun k => μ k = l)]
      have : ∑ k : {k // ¬ μ k = l}, M p i k * M q k j = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        have hk : μ i ≠ μ k := by
          rw [i.2]
          exact fun h => k.2 h.symm
        rw [hblock p i k hk, zero_mul]
      rw [this, add_zero]
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    rw [h1, h2]

theorem blk_apply (hblock : ∀ (p : P) (i j : ι), μ i ≠ μ j → M p i j = 0) (l : E) (p : P)
    (i j : {j // μ j = l}) : blk μ M hblock l p i j = M p i j := rfl

end Block

theorem exists_injective_slTwo_of_blockDiagonal {E : Type} [Field E] {ι : Type} [Fintype ι]
    [DecidableEq ι] (μ : ι → E) {P : Type} [Group P] (hs : IsSimpleGroup P)
    (hnc : ∃ a b : P, a * b ≠ b * a) (M : P →* Matrix ι ι E) (hM : Function.Injective M)
    (hblock : ∀ (p : P) (i j : ι), μ i ≠ μ j → M p i j = 0)
    (hbound : ∀ i : ι, Fintype.card {j // μ j = μ i} ≤ 2) :
    ∃ f : P →* SpecialLinearGroup (Fin 2) E, Function.Injective f := by
  classical
  have hperf := commutator_eq_top_of_simple_nonabelian hs hnc
  have hex : ∃ i₀ : ι, Function.Injective (blk μ M hblock (μ i₀)) := by
    by_contra hcon
    push Not at hcon
    have hker : ∀ i : ι, (blk μ M hblock (μ i)).ker = ⊤ := by
      intro i
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (blk μ M hblock (μ i)).ker with h | h
      · exact absurd ((MonoidHom.ker_eq_bot_iff _).mp h) (hcon i)
      · exact h
    have hone : ∀ p : P, M p = 1 := by
      intro p
      ext i j
      by_cases hij : μ i = μ j
      · have h1 : blk μ M hblock (μ i) p = 1 := by
          have : p ∈ (blk μ M hblock (μ i)).ker := by rw [hker i]; exact Subgroup.mem_top p
          exact this
        have h2 := congrFun (congrFun h1 ⟨i, rfl⟩) ⟨j, hij.symm⟩
        simpa [blk_apply, Matrix.one_apply, Subtype.ext_iff] using h2
      · rw [hblock p i j hij, Matrix.one_apply_ne]
        rintro rfl
        exact hij rfl
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have ha : a = 1 := hM (by rw [hone a, map_one])
    have hb : b = 1 := hM (by rw [hone b, map_one])
    rw [ha, hb]
  obtain ⟨i₀, hinj⟩ := hex
  have hcard2 : Fintype.card {j : ι // μ j = μ i₀} = 2 := by
    have hle := hbound i₀
    have hpos : 0 < Fintype.card {j : ι // μ j = μ i₀} :=
      Fintype.card_pos_iff.mpr ⟨⟨i₀, rfl⟩⟩
    rcases (show Fintype.card {j : ι // μ j = μ i₀} = 1 ∨ Fintype.card {j : ι // μ j = μ i₀} = 2
      by omega) with h1 | h2
    · exfalso
      have hsub : Subsingleton {j : ι // μ j = μ i₀} :=
        Fintype.card_le_one_iff_subsingleton.mp h1.le
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      apply hinj
      rw [map_mul, map_mul]
      ext i j
      have hij : j = i := Subsingleton.elim j i
      subst hij
      simp only [Matrix.mul_apply]
      rw [Finset.sum_eq_single j (fun x _ hx => absurd (Subsingleton.elim x j) hx)
          (fun h => absurd (Finset.mem_univ _) h),
        Finset.sum_eq_single j (fun x _ hx => absurd (Subsingleton.elim x j) hx)
          (fun h => absurd (Finset.mem_univ _) h)]
      rw [mul_comm]
    · exact h2
  let e : {j : ι // μ j = μ i₀} ≃ Fin 2 := Fintype.equivFinOfCardEq hcard2
  let R : Matrix {j : ι // μ j = μ i₀} {j : ι // μ j = μ i₀} E ≃ₐ[E] Matrix (Fin 2) (Fin 2) E :=
    Matrix.reindexAlgEquiv E E e
  have hdet : ∀ p : P, (blk μ M hblock (μ i₀) p).det = 1 := by
    intro p
    have h0 := eq_one_of_perfect hperf
      ((Matrix.detMonoidHom : Matrix {j : ι // μ j = μ i₀} {j : ι // μ j = μ i₀} E →* E).comp
        (blk μ M hblock (μ i₀))).toHomUnits p
    have h1 := congrArg Units.val h0
    simpa using h1
  let g : P → SpecialLinearGroup (Fin 2) E := fun p => ⟨R (blk μ M hblock (μ i₀) p), by
    change (Matrix.reindex e e (blk μ M hblock (μ i₀) p)).det = 1
    rw [Matrix.det_reindex_self, hdet p]⟩
  have hcoe : ∀ p, ((g p : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
      R (blk μ M hblock (μ i₀) p) := fun p => rfl
  refine ⟨{ toFun := g, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · apply Subtype.ext
    change ((g 1 : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) = 1
    rw [hcoe, map_one, map_one]
  · intro p q
    apply Subtype.ext
    change ((g (p * q) : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
      ((g p : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) *
        ((g q : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E)
    rw [hcoe, hcoe, hcoe, map_mul, map_mul]
  · intro p q hpq
    have h := congrArg Subtype.val hpq
    change ((g p : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
      ((g q : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) at h
    rw [hcoe, hcoe] at h
    exact hinj (R.injective h)

end CFSG.RankThree.PartTwo.Sec4.HeringOF

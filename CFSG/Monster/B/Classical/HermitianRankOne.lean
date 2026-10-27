module

public import CFSG.Monster.B.Classical.PlaneIncidence
import all CFSG.Fischer.F4
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Monster.B.Classical.Plane

open CFSG.Fischer
open scoped LinearAlgebra.Projectivization

@[expose] noncomputable def R (p : ℙ F4 (Fin 3 → F4)) : Matrix (Fin 3) (Fin 3) F4 :=
  Matrix.vecMulVec p.rep fun i => p.rep i ^ 2

theorem cube_eq_one_of_ne_zero : ∀ a : F4, a ≠ 0 → a * a ^ 2 = 1 := by decide

theorem R_mk (v : Fin 3 → F4) (hv : v ≠ 0) :
    R (Projectivization.mk F4 v hv) = Matrix.vecMulVec v fun i => v i ^ 2 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F4 v hv
  rw [R, ← ha]
  ext r c
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Units.smul_def, smul_eq_mul]
  have h := cube_eq_one_of_ne_zero (a : F4) a.ne_zero
  linear_combination (v r * v c ^ 2) * h

@[expose] def ωsq : F4 := ⟨3⟩

theorem ωsq_eq : ωsq = F4.ω ^ 2 := by decide

@[expose] def RTbl : Fin 21 → Matrix (Fin 3) (Fin 3) F4 :=
  ![!![0, 0, 0; 0, 0, 0; 0, 0, 1],
    !![0, 0, 0; 0, 1, 0; 0, 0, 0],
    !![0, 0, 0; 0, 1, 1; 0, 1, 1],
    !![0, 0, 0; 0, 1, ωsq; 0, F4.ω, 1],
    !![0, 0, 0; 0, 1, F4.ω; 0, ωsq, 1],
    !![1, 0, 0; 0, 0, 0; 0, 0, 0],
    !![1, 0, 1; 0, 0, 0; 1, 0, 1],
    !![1, 0, ωsq; 0, 0, 0; F4.ω, 0, 1],
    !![1, 0, F4.ω; 0, 0, 0; ωsq, 0, 1],
    !![1, 1, 0; 1, 1, 0; 0, 0, 0],
    !![1, 1, 1; 1, 1, 1; 1, 1, 1],
    !![1, 1, ωsq; 1, 1, ωsq; F4.ω, F4.ω, 1],
    !![1, 1, F4.ω; 1, 1, F4.ω; ωsq, ωsq, 1],
    !![1, ωsq, 0; F4.ω, 1, 0; 0, 0, 0],
    !![1, ωsq, 1; F4.ω, 1, F4.ω; 1, ωsq, 1],
    !![1, ωsq, ωsq; F4.ω, 1, 1; F4.ω, 1, 1],
    !![1, ωsq, F4.ω; F4.ω, 1, ωsq; ωsq, F4.ω, 1],
    !![1, F4.ω, 0; ωsq, 1, 0; 0, 0, 0],
    !![1, F4.ω, 1; ωsq, 1, ωsq; 1, F4.ω, 1],
    !![1, F4.ω, ωsq; ωsq, 1, F4.ω; F4.ω, ωsq, 1],
    !![1, F4.ω, F4.ω; ωsq, 1, 1; ωsq, 1, 1]]

theorem RTbl_spec : ∀ i : Fin 21, (Matrix.vecMulVec (Ω i) fun k => Ω i k ^ 2) = RTbl i := by
  decide +kernel

theorem R_Ωproj (i : Fin 21) : R (Ωproj i) = RTbl i := by
  rw [Ωproj_apply, R_mk, RTbl_spec]

theorem sum_ne_zero_one : ∀ x₀ : Fin 21, RTbl x₀ ≠ 0 := by decide +kernel

theorem sum_ne_zero_two : ∀ x₀ x₁ : Fin 21, x₀ < x₁ → RTbl x₀ + RTbl x₁ ≠ 0 := by
  decide +kernel

theorem sum_ne_zero_three : ∀ x₀ x₁ : Fin 21, x₀ < x₁ → ∀ x₂ : Fin 21, x₁ < x₂ →
    RTbl x₀ + RTbl x₁ + RTbl x₂ ≠ 0 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem sum_ne_zero_four : ∀ x₀ x₁ : Fin 21, x₀ < x₁ → ∀ x₂ : Fin 21, x₁ < x₂ →
    ∀ x₃ : Fin 21, x₂ < x₃ → RTbl x₀ + RTbl x₁ + RTbl x₂ + RTbl x₃ ≠ 0 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
theorem sum_eq_zero_five_iff : ∀ x₀ x₁ : Fin 21, x₀ < x₁ → ∀ x₂ : Fin 21, x₁ < x₂ →
    ∀ x₃ : Fin 21, x₂ < x₃ → ∀ x₄ : Fin 21, x₃ < x₄ →
      (RTbl x₀ + RTbl x₁ + RTbl x₂ + RTbl x₃ + RTbl x₄ = 0 ↔
        ∃ a : Fin 21, 2 ^ (x₀ : ℕ) + 2 ^ (x₁ : ℕ) + 2 ^ (x₂ : ℕ) + 2 ^ (x₃ : ℕ) + 2 ^ (x₄ : ℕ) =
          lineMask a) := by
  decide +kernel

theorem sum_orderEmbOfFin {β : Type*} [AddCommMonoid β] (T : Finset (Fin 21)) {k : ℕ}
    (hk : T.card = k) (f : Fin 21 → β) :
    ∑ i ∈ T, f i = ∑ j : Fin k, f (T.orderEmbOfFin hk j) := by
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ T hk]
  rw [Finset.sum_map]
  rfl

theorem mask_eq_sum_orderEmbOfFin (T : Finset (Fin 21)) {k : ℕ} (hk : T.card = k) :
    mask T = ∑ j : Fin k, 2 ^ (T.orderEmbOfFin hk j : ℕ) :=
  sum_orderEmbOfFin T hk _

theorem eq_projLine_iff_mask (T : Finset (Fin 21)) (a : Fin 21) :
    T = projLine a ↔ mask T = lineMask a := by
  rw [← mask_projLine]
  exact ⟨fun h => h ▸ rfl, fun h => mask_injective h⟩

theorem sum_RTbl_eq_zero_iff (T : Finset (Fin 21)) (h1 : 1 ≤ T.card) (h5 : T.card ≤ 5) :
    ∑ i ∈ T, RTbl i = 0 ↔ T.card = 5 ∧ ∃ a, T = projLine a := by
  have hlt : ∀ {k} (hk : T.card = k) (j l : Fin k), j < l →
      T.orderEmbOfFin hk j < T.orderEmbOfFin hk l := fun hk j l h =>
    (T.orderEmbOfFin hk).strictMono h
  obtain hk | hk | hk | hk | hk : T.card = 1 ∨ T.card = 2 ∨ T.card = 3 ∨ T.card = 4 ∨
      T.card = 5 := by omega
  · rw [sum_orderEmbOfFin T hk, Fin.sum_univ_one]
    exact iff_of_false (sum_ne_zero_one _) (by omega)
  · rw [sum_orderEmbOfFin T hk, Fin.sum_univ_two]
    exact iff_of_false (sum_ne_zero_two _ _ (hlt hk 0 1 (by decide))) (by omega)
  · rw [sum_orderEmbOfFin T hk, Fin.sum_univ_three]
    exact iff_of_false (sum_ne_zero_three _ _ (hlt hk 0 1 (by decide)) _
      (hlt hk 1 2 (by decide))) (by omega)
  · rw [sum_orderEmbOfFin T hk, Fin.sum_univ_four]
    exact iff_of_false (sum_ne_zero_four _ _ (hlt hk 0 1 (by decide)) _
      (hlt hk 1 2 (by decide)) _ (hlt hk 2 3 (by decide))) (by omega)
  · rw [sum_orderEmbOfFin T hk, Fin.sum_univ_five, sum_eq_zero_five_iff _ _
      (hlt hk 0 1 (by decide)) _ (hlt hk 1 2 (by decide)) _ (hlt hk 2 3 (by decide)) _
      (hlt hk 3 4 (by decide))]
    simp only [hk, true_and, eq_projLine_iff_mask, mask_eq_sum_orderEmbOfFin T hk,
      Fin.sum_univ_five]

theorem linearIndependent_Ω_pair : ∀ p q : Fin 21, p ≠ q → ∀ s t : F4,
    s • Ω p + t • Ω q = 0 → s = 0 ∧ t = 0 := by
  decide +kernel

theorem mem_span_pair_Ω_iff : ∀ p q i : Fin 21, p ≠ q →
    ((∃ s t : F4, s • Ω p + t • Ω q = Ω i) ↔ IsOn (join p q) i) := by
  decide +kernel

theorem exists_two_isOn : ∀ a : Fin 21, ∃ p q : Fin 21, p ≠ q ∧ IsOn a p ∧ IsOn a q := by
  decide +kernel

theorem finrank_span_Ω_pair {p q : Fin 21} (hpq : p ≠ q) :
    Module.finrank F4 (Submodule.span F4 {Ω p, Ω q}) = 2 := by
  have hli : LinearIndependent F4 ![Ω p, Ω q] :=
    LinearIndependent.pair_iff.2 (linearIndependent_Ω_pair p q hpq)
  have := finrank_span_eq_card hli
  rwa [Fintype.card_fin, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
    Set.union_empty, Set.singleton_union] at this

theorem mem_span_Ω_pair_iff {p q : Fin 21} (hpq : p ≠ q) (i : Fin 21) :
    Ω i ∈ Submodule.span F4 {Ω p, Ω q} ↔ IsOn (join p q) i := by
  rw [Submodule.mem_span_pair, mem_span_pair_Ω_iff p q i hpq]

theorem exists_projLine_iff (T : Finset (Fin 21)) :
    (∃ a, T = projLine a) ↔ ∃ W : Submodule F4 (Fin 3 → F4), Module.finrank F4 W = 2 ∧
      ∀ i, i ∈ T ↔ Ω i ∈ W := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨p, q, hpq, hp, hq⟩ := exists_two_isOn a
    have ha : a = join p q := join_unique p q a hpq hp hq
    refine ⟨Submodule.span F4 {Ω p, Ω q}, finrank_span_Ω_pair hpq, fun i => ?_⟩
    rw [mem_projLine, mem_span_Ω_pair_iff hpq, ha]
  · rintro ⟨W, hW, hT⟩
    let b := Module.finBasisOfFinrankEq F4 W hW
    have hmemW : ∀ x : Fin 3 → F4, x ∈ W ↔ ∃ s t : F4, s • (b 0 : Fin 3 → F4) +
        t • (b 1 : Fin 3 → F4) = x := by
      intro x
      constructor
      · intro hx
        refine ⟨b.repr ⟨x, hx⟩ 0, b.repr ⟨x, hx⟩ 1, ?_⟩
        have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
        rw [Fin.sum_univ_two] at this
        simpa using this
      · rintro ⟨s, t, rfl⟩
        exact W.add_mem (W.smul_mem s (b 0).2) (W.smul_mem t (b 1).2)
    have hne : ∀ j, (b j : Fin 3 → F4) ≠ 0 := fun j h =>
      b.ne_zero j (Subtype.ext h)
    obtain ⟨c₀, hc₀, h₀⟩ := exists_smul_Ω_normIdx _ (hne 0)
    obtain ⟨c₁, hc₁, h₁⟩ := exists_smul_Ω_normIdx _ (hne 1)
    set q₀ := normIdx (b 0 : Fin 3 → F4)
    set q₁ := normIdx (b 1 : Fin 3 → F4)
    have hq : q₀ ≠ q₁ := by
      intro hq
      have hli := Fintype.linearIndependent_iff.1 b.linearIndependent ![c₁, -c₀] (by
        rw [Fin.sum_univ_two]
        apply Subtype.ext
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Submodule.coe_add,
          Submodule.coe_smul, Submodule.coe_zero]
        rw [h₀, h₁, ← hq, smul_smul, smul_smul, mul_comm c₁ c₀, neg_mul, neg_smul,
          add_neg_cancel])
      exact hc₁ (by simpa using hli 0)
    refine ⟨join q₀ q₁, ?_⟩
    ext i
    rw [hT, mem_projLine, ← mem_span_Ω_pair_iff hq, hmemW, Submodule.mem_span_pair]
    constructor
    · rintro ⟨s, t, h⟩
      refine ⟨s * c₀, t * c₁, ?_⟩
      rw [← h, h₀, h₁, smul_smul, smul_smul]
    · rintro ⟨s, t, h⟩
      refine ⟨s * c₀⁻¹, t * c₁⁻¹, ?_⟩
      rw [← h, h₀, h₁, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hc₀, mul_one,
        mul_assoc, inv_mul_cancel₀ hc₁, mul_one]

theorem submodule_Ωproj_le_iff (i : Fin 21) (W : Submodule F4 (Fin 3 → F4)) :
    (Ωproj i).submodule ≤ W ↔ Ω i ∈ W := by
  rw [Ωproj_apply, Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]

theorem rank_one_hermitian_small_dependencies :
    (∀ (v : Fin 3 → F4) (hv : v ≠ 0),
      R (Projectivization.mk F4 v hv) = Matrix.vecMulVec v fun i => v i ^ 2) ∧
    ∀ (k : ℕ) (p : Fin k → ℙ F4 (Fin 3 → F4)), Function.Injective p → 1 ≤ k → k ≤ 5 →
      (∑ i, R (p i) = 0 ↔ k = 5 ∧ ∃ W : Submodule F4 (Fin 3 → F4), Module.finrank F4 W = 2 ∧
        ∀ q, q ∈ Set.range p ↔ q.submodule ≤ W) := by
  refine ⟨R_mk, fun k p hp h1 h5 => ?_⟩
  set T : Finset (Fin 21) := Finset.univ.image fun i => Ωproj.symm (p i)
  have hinj : Function.Injective fun i => Ωproj.symm (p i) := Ωproj.symm.injective.comp hp
  have hT : T.card = k := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hsum : ∑ i, R (p i) = ∑ j ∈ T, RTbl j := by
    rw [Finset.sum_image fun i _ j _ h => hinj h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← R_Ωproj, Equiv.apply_symm_apply]
  have hmemT : ∀ j, j ∈ T ↔ Ωproj j ∈ Set.range p := by
    intro j
    simp only [T, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, by rw [Equiv.apply_symm_apply]⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, by rw [hi, Equiv.symm_apply_apply]⟩
  rw [hsum, sum_RTbl_eq_zero_iff T (by omega) (by omega), hT, exists_projLine_iff]
  refine and_congr_right fun _ => exists_congr fun W => and_congr_right fun _ => ?_
  constructor
  · intro h q
    rw [← Ωproj.apply_symm_apply q, ← hmemT, h, submodule_Ωproj_le_iff]
  · intro h j
    rw [hmemT, h, submodule_Ωproj_le_iff]

end CFSG.Monster.B.Classical.Plane

module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKLinStab
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open Matrix
open scoped commutatorElement

variable {F : Type} [Field F]

private def stabPerf_Dl (a : F) (ha : a ≠ 0) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0; 0, a, 0; 0, 0, a⁻¹], by simp [Matrix.det_fin_three, mul_inv_cancel₀ ha]⟩

private def stabPerf_Uel (u : Fin 2 → F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, u 0, u 1; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

private def stabPerf_Lel (X : SpecialLinearGroup (Fin 2) F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0; 0, (X : Matrix (Fin 2) (Fin 2) F) 0 0, (X : Matrix (Fin 2) (Fin 2) F) 0 1;
      0, (X : Matrix (Fin 2) (Fin 2) F) 1 0, (X : Matrix (Fin 2) (Fin 2) F) 1 1], by
    have hX := Matrix.SpecialLinearGroup.det_coe X
    rw [Matrix.det_fin_two] at hX
    simp [Matrix.det_fin_three]
    linear_combination hX⟩

private def stabPerf_E01 : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

private def stabPerf_E02 : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

private theorem coe_stabPerf_Dl {a : F} (ha : a ≠ 0) :
    ((stabPerf_Dl a ha : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, a, 0; 0, 0, a⁻¹] := rfl

private theorem coe_stabPerf_Uel (u : Fin 2 → F) :
    ((stabPerf_Uel u : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, u 0, u 1; 0, 1, 0; 0, 0, 1] := rfl

private theorem coe_stabPerf_Lel (X : SpecialLinearGroup (Fin 2) F) :
    ((stabPerf_Lel X : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, (X : Matrix (Fin 2) (Fin 2) F) 0 0, (X : Matrix (Fin 2) (Fin 2) F) 0 1;
        0, (X : Matrix (Fin 2) (Fin 2) F) 1 0, (X : Matrix (Fin 2) (Fin 2) F) 1 1] := rfl

private theorem coe_stabPerf_E01 :
    ((stabPerf_E01 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 1, 0; 0, 1, 0; 0, 0, 1] := rfl

private theorem coe_stabPerf_E02 :
    ((stabPerf_E02 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 1; 0, 1, 0; 0, 0, 1] := rfl

private def stabPerf_Lhom : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 3) F where
  toFun := stabPerf_Lel
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_stabPerf_Lel, Matrix.SpecialLinearGroup.coe_one]
  map_mul' X Y := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_stabPerf_Lel, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two, Fin.sum_univ_three] <;> ring

private theorem stabPerf_Lhom_apply (X : SpecialLinearGroup (Fin 2) F) :
    stabPerf_Lhom X = stabPerf_Lel X := rfl

private theorem stabPerf_exists_mulVec_e0_of_zero_ne {v : Fin 3 → F} (hv : v 0 ≠ 0) :
    ∃ g : SpecialLinearGroup (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = ![1, 0, 0] := by
  refine ⟨⟨!![1 / v 0, 0, 0; -v 1, v 0, 0; -v 2 / v 0, 0, 1], ?_⟩, ?_⟩
  · simp [Matrix.det_fin_three, hv]
  · ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv] <;> field_simp <;>
      ring

private theorem stabPerf_exists_mulVec_e0 {w : Fin 3 → F} (hw : w ≠ 0) :
    ∃ g : SpecialLinearGroup (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w = ![1, 0, 0] := by
  obtain ⟨E, hE⟩ : ∃ E : SpecialLinearGroup (Fin 3) F,
      ((E : Matrix (Fin 3) (Fin 3) F) *ᵥ w) 0 ≠ 0 := by
    by_cases h0 : w 0 = 0
    · by_cases h1 : w 1 = 0
      · refine ⟨stabPerf_E02, ?_⟩
        have h2 : w 2 ≠ 0 := by
          intro h2
          apply hw
          ext i
          fin_cases i <;> simp [h0, h1, h2]
        rw [coe_stabPerf_E02]
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0] using h2
      · refine ⟨stabPerf_E01, ?_⟩
        rw [coe_stabPerf_E01]
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0] using h1
    · exact ⟨1, by simpa using h0⟩
  obtain ⟨g, hg⟩ := stabPerf_exists_mulVec_e0_of_zero_ne hE
  refine ⟨g * E, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hg]

private theorem stabPerf_entries_of_mem {g : SpecialLinearGroup (Fin 3) F}
    (hg : g ∈ stabVec (![1, 0, 0] : Fin 3 → F)) :
    (g : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
  have h := mem_stabVec.mp hg
  refine ⟨?_, ?_, ?_⟩
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun h 0
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun h 1
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun h 2

private theorem stabPerf_Uel_mem_stab (u : Fin 2 → F) :
    stabPerf_Uel u ∈ stabVec (![1, 0, 0] : Fin 3 → F) := by
  rw [mem_stabVec, coe_stabPerf_Uel]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem stabPerf_Dl_mem_stab {a : F} (ha : a ≠ 0) :
    stabPerf_Dl a ha ∈ stabVec (![1, 0, 0] : Fin 3 → F) := by
  rw [mem_stabVec, coe_stabPerf_Dl]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem stabPerf_decomp (M : SpecialLinearGroup (Fin 3) F)
    (h00 : (M : Matrix (Fin 3) (Fin 3) F) 0 0 = 1) (h10 : (M : Matrix (Fin 3) (Fin 3) F) 1 0 = 0)
    (h20 : (M : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) :
    ∃ (v : Fin 2 → F) (X : SpecialLinearGroup (Fin 2) F),
      M = stabPerf_Uel v * stabPerf_Lel X := by
  have hdet := Matrix.SpecialLinearGroup.det_coe M
  rw [Matrix.det_fin_three, h00, h10, h20] at hdet
  have hXdet : (!![(M : Matrix (Fin 3) (Fin 3) F) 1 1, (M : Matrix (Fin 3) (Fin 3) F) 1 2;
      (M : Matrix (Fin 3) (Fin 3) F) 2 1, (M : Matrix (Fin 3) (Fin 3) F) 2 2] :
      Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two]
    simp
    linear_combination hdet
  obtain ⟨X, hX⟩ : ∃ X : SpecialLinearGroup (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) = !![(M : Matrix (Fin 3) (Fin 3) F) 1 1,
        (M : Matrix (Fin 3) (Fin 3) F) 1 2; (M : Matrix (Fin 3) (Fin 3) F) 2 1,
        (M : Matrix (Fin 3) (Fin 3) F) 2 2] :=
    ⟨⟨_, hXdet⟩, rfl⟩
  refine ⟨![(M : Matrix (Fin 3) (Fin 3) F) 0 1 * (M : Matrix (Fin 3) (Fin 3) F) 2 2 -
      (M : Matrix (Fin 3) (Fin 3) F) 0 2 * (M : Matrix (Fin 3) (Fin 3) F) 2 1,
      -((M : Matrix (Fin 3) (Fin 3) F) 0 1 * (M : Matrix (Fin 3) (Fin 3) F) 1 2) +
      (M : Matrix (Fin 3) (Fin 3) F) 0 2 * (M : Matrix (Fin 3) (Fin 3) F) 1 1], X, ?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_stabPerf_Uel, coe_stabPerf_Lel, hX]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h00, h10, h20]
  all_goals first
    | linear_combination (-((M : Matrix (Fin 3) (Fin 3) F) 0 1)) * hdet
    | linear_combination (-((M : Matrix (Fin 3) (Fin 3) F) 0 2)) * hdet

private theorem stabPerf_Lel_mem_commutator {a : F} (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1)
    (X : SpecialLinearGroup (Fin 2) F) :
    stabPerf_Lel X ∈ ⁅stabVec (![1, 0, 0] : Fin 3 → F), stabVec (![1, 0, 0] : Fin 3 → F)⁆ := by
  have hS : Subgroup.map stabPerf_Lhom (⊤ : Subgroup (SpecialLinearGroup (Fin 2) F)) ≤
      stabVec (![1, 0, 0] : Fin 3 → F) := by
    rintro _ ⟨Y, -, rfl⟩
    rw [mem_stabVec, stabPerf_Lhom_apply, coe_stabPerf_Lel]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hcomm : Subgroup.map stabPerf_Lhom (commutator (SpecialLinearGroup (Fin 2) F)) ≤
      ⁅stabVec (![1, 0, 0] : Fin 3 → F), stabVec (![1, 0, 0] : Fin 3 → F)⁆ := by
    rw [commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono hS hS
  have hX : X ∈ commutator (SpecialLinearGroup (Fin 2) F) := by
    rw [Matrix.SL2.commutator_eq_top ha hasq]
    exact Subgroup.mem_top X
  exact hcomm (Subgroup.mem_map_of_mem stabPerf_Lhom hX)

private theorem stabPerf_exists_ne_zero_one_neg_one [Fintype F] (h4 : 4 ≤ Fintype.card F) :
    ∃ a : F, a ≠ 0 ∧ a ≠ 1 ∧ a ≠ -1 := by
  classical
  by_contra hcon
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1, -1} := by
    intro a _
    by_cases h0 : a = 0
    · simp [h0]
    by_cases h1 : a = 1
    · simp [h1]
    have h2 : a = -1 := by
      by_contra h2
      exact hcon ⟨a, h0, h1, h2⟩
    simp [h2]
  have h5 := Finset.card_le_card hsub
  rw [Finset.card_univ] at h5
  have h6 : ({0, 1, -1} : Finset F).card ≤ 3 := Finset.card_le_three
  omega

private theorem stabPerf_sq_ne_one {a : F} (h1 : a ≠ 1) (h2 : a ≠ -1) : a ^ 2 ≠ 1 := by
  intro h
  have h' : (a - 1) * (a + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h3 | h3
  · exact h1 (sub_eq_zero.mp h3)
  · exact h2 (eq_neg_of_add_eq_zero_left h3)

private theorem stabPerf_commutator_Uel {a : F} (ha0 : a ≠ 0) {u v : Fin 2 → F}
    (hu0 : u 0 * (a⁻¹ - 1) = v 0) (hu1 : u 1 * (a - 1) = v 1) :
    ⁅stabPerf_Dl a ha0, stabPerf_Uel u⁆ = stabPerf_Uel v := by
  have hinv : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0
  have hmul : stabPerf_Dl a ha0 * stabPerf_Uel u =
      stabPerf_Uel v * stabPerf_Uel u * stabPerf_Dl a ha0 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, coe_stabPerf_Dl, coe_stabPerf_Uel,
        Matrix.mul_fin_three]
    all_goals first
      | linear_combination a * hu0 - u 0 * hinv
      | linear_combination -(a * hu0 - u 0 * hinv)
      | linear_combination a⁻¹ * hu1 - u 1 * hinv
      | linear_combination -(a⁻¹ * hu1 - u 1 * hinv)
  rw [commutatorElement_def, hmul]
  group

private theorem stabPerf_Uel_mem_commutator {a : F} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (v : Fin 2 → F) :
    stabPerf_Uel v ∈ ⁅stabVec (![1, 0, 0] : Fin 3 → F), stabVec (![1, 0, 0] : Fin 3 → F)⁆ := by
  have hsub : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  have hsubinv : a⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (fun h => ha1 (inv_eq_one.mp h))
  obtain ⟨u, hu0, hu1⟩ : ∃ u : Fin 2 → F, u 0 * (a⁻¹ - 1) = v 0 ∧ u 1 * (a - 1) = v 1 :=
    ⟨![v 0 / (a⁻¹ - 1), v 1 / (a - 1)], div_mul_cancel₀ _ hsubinv, div_mul_cancel₀ _ hsub⟩
  have hcomm := Subgroup.commutator_mem_commutator (stabPerf_Dl_mem_stab ha0)
    (stabPerf_Uel_mem_stab u)
  rwa [stabPerf_commutator_Uel ha0 hu0 hu1] at hcomm

private theorem stabPerf_e0_le [Fintype F] (h4 : 4 ≤ Fintype.card F) :
    stabVec (![1, 0, 0] : Fin 3 → F) ≤
      ⁅stabVec (![1, 0, 0] : Fin 3 → F), stabVec (![1, 0, 0] : Fin 3 → F)⁆ := by
  obtain ⟨a, ha0, ha1, ha2⟩ := stabPerf_exists_ne_zero_one_neg_one h4
  have hasq : a ^ 2 ≠ 1 := stabPerf_sq_ne_one ha1 ha2
  intro g hg
  obtain ⟨h00, h10, h20⟩ := stabPerf_entries_of_mem hg
  obtain ⟨v, X, rfl⟩ := stabPerf_decomp g h00 h10 h20
  exact mul_mem (stabPerf_Uel_mem_commutator ha0 ha1 v) (stabPerf_Lel_mem_commutator ha0 hasq X)

theorem stabVec_perfect [Fintype F] (h4 : 4 ≤ Fintype.card F) {w : Fin 3 → F} (hw : w ≠ 0) :
    ⁅stabVec w, stabVec w⁆ = stabVec w := by
  obtain ⟨g₀, hg₀⟩ := stabPerf_exists_mulVec_e0 hw
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  · intro g hg
    let ψ : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F :=
      (MulAut.conj g₀⁻¹).toMonoidHom
    have hψ : ∀ x, ψ x = g₀⁻¹ * x * g₀ := fun x => by simp [ψ]
    have hw' : ((g₀⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        (![1, 0, 0] : Fin 3 → F) = w := by
      rw [← hg₀, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    have hk : g₀ * g * g₀⁻¹ ∈ stabVec (![1, 0, 0] : Fin 3 → F) := by
      rw [mem_stabVec, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hw', mem_stabVec.mp hg, hg₀]
    have hmapS : Subgroup.map ψ (stabVec (![1, 0, 0] : Fin 3 → F)) ≤ stabVec w := by
      rintro _ ⟨s, hs, rfl⟩
      rw [hψ, mem_stabVec, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg₀, mem_stabVec.mp hs, hw']
    have h1 : ψ (g₀ * g * g₀⁻¹) ∈
        Subgroup.map ψ ⁅stabVec (![1, 0, 0] : Fin 3 → F), stabVec (![1, 0, 0] : Fin 3 → F)⁆ :=
      Subgroup.mem_map_of_mem ψ (stabPerf_e0_le h4 hk)
    rw [Subgroup.map_commutator] at h1
    have h2 := Subgroup.commutator_mono hmapS hmapS h1
    rwa [hψ, show g₀⁻¹ * (g₀ * g * g₀⁻¹) * g₀ = g by group] at h2

end CFSG.Quasithin.H13.Ch4.CentK

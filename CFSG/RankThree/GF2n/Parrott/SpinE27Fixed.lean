module

public import CFSG.LinearAlgebra.F2CubeMatrix
public import CFSG.RankThree.GF2n.Parrott.SpinE27Classes
public import CFSG.RankThree.GF2n.Parrott.SpinRigidity
public import CFSG.RankThree.GF2n.Parrott.FixCardConj

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.RankThree.GF2n.Parrott.SpinRigid
open CFSG.LinearAlgebra.F2Cube (C3 FixedFreeRep fixedCount fixedDim)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)

theorem eq_zero_of_fixedCount_eq_one {M : Mat8} (h : fixedCount M = 1) {v : Fin 8 → ZMod 2}
    (hv : M.mulVec v = v) : v = 0 := by
  have h0 : M.mulVec (0 : Fin 8 → ZMod 2) = 0 := Matrix.mulVec_zero M
  have h1 := Fintype.card_le_one_iff.1 h.le ⟨v, hv⟩ ⟨0, h0⟩
  exact congrArg Subtype.val h1

theorem fixedCount_eq_count (M : Mat8) :
    fixedCount M = ((Finset.range 256).filter fun m => bapply (colsOf M) m = m).card := by
  unfold fixedCount
  rw [Fintype.card_subtype]
  symm
  refine Finset.card_bij (fun m _ => vecOfNat m) (fun m hm => ?_) (fun m₁ h₁ m₂ h₂ h => ?_)
    (fun v hv => ?_)
  · simp only [Finset.mem_filter, Finset.mem_range] at hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply bitmask_injective
    rw [← bapply_colsOf, bitmask_vecOfNat m hm.1, hm.2]
  · simp only [Finset.mem_filter, Finset.mem_range] at h₁ h₂
    rw [← bitmask_vecOfNat m₁ h₁.1, ← bitmask_vecOfNat m₂ h₂.1, h]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    refine ⟨bitmask v, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨bitmask_lt v, by rw [bapply_colsOf, hv]⟩
    · apply bitmask_injective
      exact bitmask_vecOfNat _ (bitmask_lt v)

theorem fixedCount_apply_of_isConj (ρ : A45 →* GL8) {a b : A45} (h : IsConj a b) :
    fixedCount ((ρ a : GL8) : Mat8) = fixedCount ((ρ b : GL8) : Mat8) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [← hc, map_mul, map_mul, map_inv]
  exact (fixCard_conj (ρ c) (ρ a)).symm

theorem fixedDim_apply_of_isConj (ρ : A45 →* GL8) {a b : A45} (h : IsConj a b) :
    fixedDim ((ρ a : GL8) : Mat8) = fixedDim ((ρ b : GL8) : Mat8) := by
  unfold fixedDim
  rw [fixedCount_apply_of_isConj ρ h]

theorem spinE27Elt_mem (t : C3) : spinE27Elt t ∈ spinE27 :=
  (mem_spinE27_iff _).2 ⟨t, rfl⟩

theorem spinE27Elt_ne_one {t : C3} (ht : t ≠ 0) : spinE27Elt t ≠ 1 := fun h =>
  ht (spinE27Elt_injective (h.trans spinE27Elt_zero.symm))

theorem spinE27Elt_one_zero_zero : spinE27Elt (1, 0, 0) = spinE27a := by
  simp [spinE27Elt]

theorem spinE27Elt_zero_one_zero : spinE27Elt (0, 1, 0) = spinE27b := by
  simp [spinE27Elt]

theorem spinE27Elt_one_one_zero : spinE27Elt (1, 1, 0) = spinE27a * spinE27b := by
  simp [spinE27Elt]

theorem fixedCount_eq_on_spinE27 (ρ₁ ρ₂ : A45 →* GL8)
    (h₁ : fixedCount ((ρ₁ spinE27a : GL8) : Mat8) = fixedCount ((ρ₂ spinE27a : GL8) : Mat8))
    (h₂ : fixedCount ((ρ₁ (spinE27a * spinE27b) : GL8) : Mat8) =
      fixedCount ((ρ₂ (spinE27a * spinE27b) : GL8) : Mat8))
    (h₃ : fixedCount ((ρ₁ (spinE27a * spinE27b⁻¹) : GL8) : Mat8) =
      fixedCount ((ρ₂ (spinE27a * spinE27b⁻¹) : GL8) : Mat8))
    {g : A45} (hg : g ∈ spinE27) (hne : g ≠ 1) :
    fixedCount ((ρ₁ g : GL8) : Mat8) = fixedCount ((ρ₂ g : GL8) : Mat8) := by
  obtain ⟨L₁, L₂, L₃, -, -, -, -, -, -, hmem, c1, c2, c3, -, -, -⟩ := spinE27_classes
  rcases (hmem g).1 ⟨hg, hne⟩ with h | h | h
  · rw [← fixedCount_apply_of_isConj ρ₁ (c1 g h), ← fixedCount_apply_of_isConj ρ₂ (c1 g h), h₁]
  · rw [← fixedCount_apply_of_isConj ρ₁ (c2 g h), ← fixedCount_apply_of_isConj ρ₂ (c2 g h), h₂]
  · rw [← fixedCount_apply_of_isConj ρ₁ (c3 g h), ← fixedCount_apply_of_isConj ρ₂ (c3 g h), h₃]

theorem sum_fixedDim_spinE27 (ρ : A45 →* GL8) :
    ∑ t ∈ Finset.univ.filter (fun t : C3 => t ≠ 0), fixedDim ((ρ (spinE27Elt t) : GL8) : Mat8) =
      8 * fixedDim ((ρ spinE27a : GL8) : Mat8) +
        6 * fixedDim ((ρ (spinE27a * spinE27b) : GL8) : Mat8) +
        12 * fixedDim ((ρ (spinE27a * spinE27b⁻¹) : GL8) : Mat8) := by
  obtain ⟨L₁, L₂, L₃, h1, h2, h3, d12, d13, d23, hmem, c1, c2, c3, -, -, -⟩ := spinE27_classes
  let d : A45 → ℕ := fun g => fixedDim ((ρ g : GL8) : Mat8)
  have himg : (Finset.univ.filter (fun t : C3 => t ≠ 0)).image spinE27Elt = L₁ ∪ L₂ ∪ L₃ := by
    ext g
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact or_assoc.2 ((hmem _).1 ⟨spinE27Elt_mem t, spinE27Elt_ne_one ht⟩)
    · intro hg
      obtain ⟨hg1, hg2⟩ := (hmem g).2 (or_assoc.1 hg)
      obtain ⟨t, rfl⟩ := (mem_spinE27_iff g).1 hg1
      exact ⟨t, fun h0 => hg2 (by rw [h0, spinE27Elt_zero]), rfl⟩
  show ∑ t ∈ Finset.univ.filter (fun t : C3 => t ≠ 0), d (spinE27Elt t) =
    8 * d spinE27a + 6 * d (spinE27a * spinE27b) + 12 * d (spinE27a * spinE27b⁻¹)
  rw [← Finset.sum_image (f := d) (fun s _ t _ h => spinE27Elt_injective h), himg,
    Finset.sum_union (Finset.disjoint_union_left.2 ⟨d13, d23⟩), Finset.sum_union d12]
  have e1 : ∑ g ∈ L₁, d g = 8 * d spinE27a := by
    rw [Finset.sum_congr rfl (fun g hg => (fixedDim_apply_of_isConj ρ (c1 g hg)).symm),
      Finset.sum_const, h1, smul_eq_mul]
  have e2 : ∑ g ∈ L₂, d g = 6 * d (spinE27a * spinE27b) := by
    rw [Finset.sum_congr rfl (fun g hg => (fixedDim_apply_of_isConj ρ (c2 g hg)).symm),
      Finset.sum_const, h2, smul_eq_mul]
  have e3 : ∑ g ∈ L₃, d g = 12 * d (spinE27a * spinE27b⁻¹) := by
    rw [Finset.sum_congr rfl (fun g hg => (fixedDim_apply_of_isConj ρ (c3 g hg)).symm),
      Finset.sum_const, h3, smul_eq_mul]
  rw [e1, e2, e3]

@[expose] def spinE27FixedFreeRep (ρ : A45 →* GL8)
    (hρ : ∀ v : Fin 8 → ZMod 2,
      (∀ t, ((ρ (spinE27Elt t) : GL8) : Mat8).mulVec v = v) → v = 0) : FixedFreeRep 8 where
  toFun t := ((ρ (spinE27Elt t) : GL8) : Mat8)
  map_zero := by rw [spinE27Elt_zero, map_one, Units.val_one]
  map_add s t := by rw [← spinE27Elt_mul, map_mul, Units.val_mul]
  eq_zero_of_fixed := hρ

theorem exists_conj_on_spinE27 (ρ₁ ρ₂ : A45 →* GL8)
    (hρ₁ : ∀ v : Fin 8 → ZMod 2,
      (∀ t, ((ρ₁ (spinE27Elt t) : GL8) : Mat8).mulVec v = v) → v = 0)
    (hρ₂ : ∀ v : Fin 8 → ZMod 2,
      (∀ t, ((ρ₂ (spinE27Elt t) : GL8) : Mat8).mulVec v = v) → v = 0)
    (h₁ : fixedCount ((ρ₁ spinE27a : GL8) : Mat8) = fixedCount ((ρ₂ spinE27a : GL8) : Mat8))
    (h₂ : fixedCount ((ρ₁ (spinE27a * spinE27b) : GL8) : Mat8) =
      fixedCount ((ρ₂ (spinE27a * spinE27b) : GL8) : Mat8))
    (h₃ : fixedCount ((ρ₁ (spinE27a * spinE27b⁻¹) : GL8) : Mat8) =
      fixedCount ((ρ₂ (spinE27a * spinE27b⁻¹) : GL8) : Mat8)) :
    ∃ P : GL8, ∀ g ∈ spinE27, ρ₁ g = P * ρ₂ g * P⁻¹ := by
  obtain ⟨E, F, hFE, hEF, hconj⟩ := (spinE27FixedFreeRep ρ₁ hρ₁).exists_conj
    (spinE27FixedFreeRep ρ₂ hρ₂) (fun t ht =>
      fixedCount_eq_on_spinE27 ρ₁ ρ₂ h₁ h₂ h₃ (spinE27Elt_mem t) (spinE27Elt_ne_one ht))
  refine ⟨⟨F, E, hFE, hEF⟩, fun g hg => ?_⟩
  obtain ⟨t, rfl⟩ := (mem_spinE27_iff g).1 hg
  apply Units.ext
  have h1 : E * ((ρ₁ (spinE27Elt t) : GL8) : Mat8) = ((ρ₂ (spinE27Elt t) : GL8) : Mat8) * E :=
    hconj t
  show ((ρ₁ (spinE27Elt t) : GL8) : Mat8) = F * ((ρ₂ (spinE27Elt t) : GL8) : Mat8) * E
  calc ((ρ₁ (spinE27Elt t) : GL8) : Mat8) = (F * E) * ((ρ₁ (spinE27Elt t) : GL8) : Mat8) := by
        rw [hFE, Matrix.one_mul]
    _ = F * (E * ((ρ₁ (spinE27Elt t) : GL8) : Mat8)) := by rw [Matrix.mul_assoc]
    _ = F * (((ρ₂ (spinE27Elt t) : GL8) : Mat8) * E) := by rw [h1]
    _ = F * ((ρ₂ (spinE27Elt t) : GL8) : Mat8) * E := by rw [Matrix.mul_assoc]

theorem colsOf_rhoA_spinE27a : colsOf ((rhoA spinE27a : GL8) : Mat8) = gb 2 :=
  colsOf_spinMat_G5 2

theorem colsOf_rhoA_spinE27b : colsOf ((rhoA spinE27b : GL8) : Mat8) = gb 3 :=
  colsOf_spinMat_G5 3

theorem fixedCount_rhoA_spinE27a : fixedCount ((rhoA spinE27a : GL8) : Mat8) = 4 := by
  rw [fixedCount_eq_count, colsOf_rhoA_spinE27a]
  decide +kernel

theorem fixedCount_rhoA_spinE27ab :
    fixedCount ((rhoA (spinE27a * spinE27b) : GL8) : Mat8) = 1 := by
  rw [fixedCount_eq_count, map_mul, Units.val_mul, colsOf_mul, colsOf_rhoA_spinE27a,
    colsOf_rhoA_spinE27b]
  decide +kernel

theorem fixedCount_rhoA_spinE27abinv :
    fixedCount ((rhoA (spinE27a * spinE27b⁻¹) : GL8) : Mat8) = 16 := by
  rw [fixedCount_eq_count, spinE27b_inv, map_mul, Units.val_mul, colsOf_mul, map_pow,
    Units.val_pow_eq_pow_val, colsOf_pow, colsOf_rhoA_spinE27a, colsOf_rhoA_spinE27b]
  decide +kernel

theorem rhoA_eq_zero_of_fixed : ∀ v : Fin 8 → ZMod 2,
    (∀ t, ((rhoA (spinE27Elt t) : GL8) : Mat8).mulVec v = v) → v = 0 := by
  intro v hv
  have h1 := hv (1, 1, 0)
  rw [spinE27Elt_one_one_zero] at h1
  exact eq_zero_of_fixedCount_eq_one fixedCount_rhoA_spinE27ab h1

end CFSG.RankThree.GF2n.Parrott

module

public import CFSG.RankThree.PartOne.KF.U4Group
public import CFSG.RankThree.PartOne.LSTD.Basic

public section

namespace CFSG.RankThree.PartOne.U5LIFT

open Matrix CFSG CFSG.RankThree.PartOne.KFU CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryCoord
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.LSTD

variable {f : ℕ} {K : Type} [Field K]

@[expose] def fixVec (a b l : Fin 5) (ζ : Kˣ) : Fin 5 → Kˣ := torusElt a l ζ * torusElt b l ζ

theorem fixVec_apply_a {a b l : Fin 5} (hab : a ≠ b) (hal : a ≠ l) (ζ : Kˣ) :
    fixVec a b l ζ a = ζ := by
  simp [fixVec, torusElt_apply_left hal, torusElt_apply_other hab hal]

theorem fixVec_apply_b {a b l : Fin 5} (hab : a ≠ b) (hbl : b ≠ l) (ζ : Kˣ) :
    fixVec a b l ζ b = ζ := by
  simp [fixVec, torusElt_apply_left hbl, torusElt_apply_other hab.symm hbl]

theorem fixVec_apply_l {a b l : Fin 5} (hal : a ≠ l) (hbl : b ≠ l) (ζ : Kˣ) :
    fixVec a b l ζ l = ζ⁻¹ * ζ⁻¹ := by
  simp [fixVec, torusElt_apply_right hal, torusElt_apply_right hbl]

theorem fixVec_apply_other {a b l k : Fin 5} (hka : k ≠ a) (hkb : k ≠ b) (hkl : k ≠ l) (ζ : Kˣ) :
    fixVec a b l ζ k = 1 := by
  simp [fixVec, torusElt_apply_other hka hkl, torusElt_apply_other hkb hkl]

theorem fixVec_mem {a b l : Fin 5} (hal : a ≠ l) (hbl : b ≠ l) {ζ : Kˣ} (hζ : ζ ^ 5 = 1) :
    fixVec a b l ζ ∈ torusVec 5 5 K :=
  Subgroup.mul_mem _ (torusElt_mem hal hζ) (torusElt_mem hbl hζ)

theorem isBlockDiag_of_comm_fix {a b : Fin 5} {ζ : Kˣ} (hζ : ζ⁻¹ * ζ⁻¹ ≠ ζ) (hab : a ≠ b)
    {y : GL (Fin 5) K}
    (hy : ∀ l, l ≠ a → l ≠ b → y * diagU (fixVec a b l ζ) = diagU (fixVec a b l ζ) * y) :
    IsBlockDiag a b (y : Matrix (Fin 5) (Fin 5) K) := by
  intro k m hkm
  have key : ∀ l, l ≠ a → l ≠ b →
      (y : Matrix (Fin 5) (Fin 5) K) k m * ((fixVec a b l ζ m : Kˣ) : K) =
        ((fixVec a b l ζ k : Kˣ) : K) * (y : Matrix (Fin 5) (Fin 5) K) k m := by
    intro l hla hlb
    have h1 := congrArg (fun z : GL (Fin 5) K => (z : Matrix (Fin 5) (Fin 5) K) k m)
      (hy l hla hlb)
    simpa [Units.val_mul, diagU_val, Matrix.mul_diagonal, Matrix.diagonal_mul] using h1
  have hζK : ((ζ⁻¹ * ζ⁻¹ : Kˣ) : K) ≠ (ζ : K) := fun h' => hζ (Units.ext h')
  by_cases hk : k = a ∨ k = b
  · have hm : ¬ (m = a ∨ m = b) := hkm.mp hk
    have hma : m ≠ a := fun h' => hm (Or.inl h')
    have hmb : m ≠ b := fun h' => hm (Or.inr h')
    have h2 := key m hma hmb
    have hkv : fixVec a b m ζ k = ζ := by
      rcases hk with rfl | rfl
      · exact fixVec_apply_a hab hma.symm ζ
      · exact fixVec_apply_b hab hmb.symm ζ
    rw [hkv, fixVec_apply_l hma.symm hmb.symm] at h2
    have h3 : (y : Matrix (Fin 5) (Fin 5) K) k m * (((ζ⁻¹ * ζ⁻¹ : Kˣ) : K) - (ζ : K)) = 0 := by
      linear_combination h2
    exact (mul_eq_zero.mp h3).resolve_right (sub_ne_zero.mpr hζK)
  · have hm : m = a ∨ m = b := by
      by_contra hm
      exact hk (hkm.mpr hm)
    have hka : k ≠ a := fun h' => hk (Or.inl h')
    have hkb : k ≠ b := fun h' => hk (Or.inr h')
    have h2 := key k hka hkb
    have hmv : fixVec a b k ζ m = ζ := by
      rcases hm with rfl | rfl
      · exact fixVec_apply_a hab hka.symm ζ
      · exact fixVec_apply_b hab hkb.symm ζ
    rw [hmv, fixVec_apply_l hka.symm hkb.symm] at h2
    have h3 : (y : Matrix (Fin 5) (Fin 5) K) k m * ((ζ : K) - ((ζ⁻¹ * ζ⁻¹ : Kˣ) : K)) = 0 := by
      linear_combination h2
    exact (mul_eq_zero.mp h3).resolve_right (sub_ne_zero.mpr hζK.symm)

theorem conj_mem_blk_of_comm_fix (h : UnitaryFieldData 2 f K) {a b : Fin 5} (hab : a ≠ b)
    {ζ : Kˣ} (hζ : ζ⁻¹ * ζ⁻¹ ≠ ζ) {y : GL (Fin 5) K}
    (hyU : y ∈ primeFormUnitary h (idGram K 5))
    (hy : ∀ l, l ≠ a → l ≠ b → y * diagU (fixVec a b l ζ) = diagU (fixVec a b l ζ) * y)
    {g : GL (Fin 5) K} (hg : g ∈ blk h hab) : y * g * y⁻¹ ∈ blk h hab := by
  refine conj_mem_blk (h := h) hab hyU (isBlockDiag_of_comm_fix hζ hab hy) ?_ hg
  refine isBlockDiag_of_comm_fix hζ hab fun l hla hlb => ?_
  have := Commute.inv_left (show Commute y (diagU (fixVec a b l ζ)) from hy l hla hlb)
  exact this.eq

theorem trace_fixVec [CharP K 2] {a b l : Fin 5} (hab : a ≠ b) (hal : a ≠ l) (hbl : b ≠ l)
    (ζ : Kˣ) :
    Matrix.trace ((diagU (fixVec a b l ζ) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      ((ζ⁻¹ * ζ⁻¹ : Kˣ) : K) := by
  have hv : ∀ k : Fin 5, ((fixVec a b l ζ k : Kˣ) : K) = 1 + (if k = a then (ζ : K) - 1 else 0) +
      (if k = b then (ζ : K) - 1 else 0) + (if k = l then ((ζ⁻¹ * ζ⁻¹ : Kˣ) : K) - 1 else 0) := by
    intro k
    by_cases hka : k = a
    · subst hka
      simp [fixVec_apply_a hab hal, hab, hal]
    · by_cases hkb : k = b
      · subst hkb
        simp [fixVec_apply_b hab hbl, hka, hbl]
      · by_cases hkl : k = l
        · subst hkl
          simp [fixVec_apply_l hal hbl, hka, hkb]
        · simp [fixVec_apply_other hka hkb hkl, hka, hkb, hkl]
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  simp only [Matrix.trace, Matrix.diag, diagU_val, Matrix.diagonal_apply_eq, hv]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, nsmul_eq_mul, mul_one]
  push_cast
  linear_combination (1 + (ζ : K)) * h2

theorem scalar_eq_one_of_conj {g x : GL (Fin 5) K} {κ : Kˣ}
    (h : g * x * g⁻¹ = diagU (fun _ => κ) * x)
    (htr : Matrix.trace (x : Matrix (Fin 5) (Fin 5) K) ≠ 0) : κ = 1 := by
  have h1 := congrArg (fun z : GL (Fin 5) K => Matrix.trace (z : Matrix (Fin 5) (Fin 5) K)) h
  simp only [Units.val_mul] at h1
  rw [Matrix.trace_units_conj g (x : Matrix (Fin 5) (Fin 5) K)] at h1
  have h2 : ((diagU (fun _ => κ) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
      (x : Matrix (Fin 5) (Fin 5) K) = (κ : K) • (x : Matrix (Fin 5) (Fin 5) K) := by
    rw [diagU_val, ← Matrix.smul_eq_diagonal_mul]
  rw [h2, Matrix.trace_smul, smul_eq_mul] at h1
  have h3 : ((κ : K) - 1) * Matrix.trace (x : Matrix (Fin 5) (Fin 5) K) = 0 := by
    linear_combination -h1
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact Units.ext (by simpa [sub_eq_zero] using h4)
  · exact absurd h4 htr

end CFSG.RankThree.PartOne.U5LIFT

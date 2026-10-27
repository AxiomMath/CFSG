module

public import CFSG.OddTranspositions.PartThree.Eleven.Five.Refl
import CFSG.OddTranspositions.PartThree.Eleven.FiveMinus.Spinor
import CFSG.OddTranspositions.PartThree.Eleven.FiveMinus.Thirteen
import Mathlib.Data.Fin.SuccPred

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

private theorem fiveForm_eq_dotProduct' (n : ℕ) (ε : Bool) (x y : Fin (n + 1) → ZMod 5) :
    fiveForm n ε x y = x ⬝ᵥ fiveFormVec n ε y := by
  unfold fiveForm fiveFormVec dotProduct
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.castSucc_ne_last, ↓reduceIte]
  ring

private theorem fiveFormVec_neg (n : ℕ) (ε : Bool) (y : Fin (n + 1) → ZMod 5) :
    fiveFormVec n ε (-y) = -fiveFormVec n ε y := by
  funext j
  simp only [fiveFormVec, Pi.neg_apply]
  split_ifs <;> ring_nf

private theorem fiveForm_add_left' (n : ℕ) (ε : Bool) (x y z : Fin (n + 1) → ZMod 5) :
    fiveForm n ε (x + y) z = fiveForm n ε x z + fiveForm n ε y z := by
  simp only [fiveForm_eq_dotProduct', add_dotProduct]

private theorem fiveForm_neg_right' (n : ℕ) (ε : Bool) (x y : Fin (n + 1) → ZMod 5) :
    fiveForm n ε x (-y) = -fiveForm n ε x y := by
  calc fiveForm n ε x (-y) = x ⬝ᵥ fiveFormVec n ε (-y) :=
        fiveForm_eq_dotProduct' n ε x (-y)
    _ = x ⬝ᵥ -fiveFormVec n ε y := by rw [fiveFormVec_neg]
    _ = -(x ⬝ᵥ fiveFormVec n ε y) := dotProduct_neg x (fiveFormVec n ε y)
    _ = -fiveForm n ε x y := by rw [fiveForm_eq_dotProduct' n ε x y]

private theorem fiveForm_sub_left' (n : ℕ) (ε : Bool) (x y z : Fin (n + 1) → ZMod 5) :
    fiveForm n ε (x - y) z = fiveForm n ε x z - fiveForm n ε y z := by
  simp only [fiveForm_eq_dotProduct', sub_dotProduct]

private theorem fiveForm_smul_left' (n : ℕ) (ε : Bool) (c : ZMod 5)
    (x y : Fin (n + 1) → ZMod 5) :
    fiveForm n ε (c • x) y = c * fiveForm n ε x y := by
  simp only [fiveForm_eq_dotProduct', smul_dotProduct, smul_eq_mul]

private theorem fiveForm_neg_neg' (n : ℕ) (ε : Bool) (x y : Fin (n + 1) → ZMod 5) :
    fiveForm n ε (-x) (-y) = fiveForm n ε x y := by
  calc fiveForm n ε (-x) (-y) = (-x) ⬝ᵥ fiveFormVec n ε (-y) :=
        fiveForm_eq_dotProduct' n ε (-x) (-y)
    _ = (-x) ⬝ᵥ -fiveFormVec n ε y := by rw [fiveFormVec_neg]
    _ = x ⬝ᵥ fiveFormVec n ε y := neg_dotProduct_neg x (fiveFormVec n ε y)
    _ = fiveForm n ε x y := (fiveForm_eq_dotProduct' n ε x y).symm

private theorem two_ne_zero_zmodFive : (2 : ZMod 5) ≠ 0 := by
  intro h
  have hdvd := (ZMod.natCast_eq_zero_iff 2 5).mp h
  omega

private theorem neg_one_ne_zero_zmodFive : (-(1 : ZMod 5)) ≠ 0 := by
  intro h
  have h1 : (1 : ZMod 5) = 0 := neg_eq_zero.mp h
  have hdvd := (ZMod.natCast_eq_zero_iff 1 5).mp h1
  omega

theorem eq_fiveReflOf_of_neg_eigenline {t : GL (Fin 5) (ZMod 5)}
    (hform : ∀ x y, fiveForm 4 true ((t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x)
      ((t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ y) = fiveForm 4 true x y)
    (ht : t * t = 1) {w : Fin 5 → ZMod 5} (hw : w ≠ 0)
    (hline : ∀ x, (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x = -x ↔ ∃ a : ZMod 5, x = a • w) :
    fiveForm 4 true w w ≠ 0 ∧ t = fiveReflOf 4 true w := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have htM : (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) * t = 1 := by
    have h := congrArg (fun u : GL (Fin 5) (ZMod 5) =>
      (u : Matrix (Fin 5) (Fin 5) (ZMod 5))) ht
    simpa using h
  have htapply : ∀ x, (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ
      ((t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, htM, Matrix.one_mulVec]
  have htw : (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w = -w :=
    (hline w).mpr ⟨1, by simp⟩
  have hstep1 : ∀ x, fiveForm 4 true
      (x + (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x) w = 0 := by
    intro x
    have hfix : (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ
        (x + (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x) =
        x + (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x := by
      rw [Matrix.mulVec_add, htapply x, add_comm]
    have h := hform (x + (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x) w
    rw [hfix, htw] at h
    have hneg : fiveForm 4 true (x + (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x) (-w) =
        -fiveForm 4 true (x + (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x) w :=
      fiveForm_neg_right' 4 true (x + (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x) w
    rw [hneg] at h
    have h2 : (2 : ZMod 5) * fiveForm 4 true
        (x + (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x) w = 0 := by
      rw [two_mul]
      exact (neg_eq_iff_add_eq_zero).mp h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 two_ne_zero_zmodFive
    · exact h3
  have htw_eq : ∀ x, fiveForm 4 true
      ((t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x) w = -fiveForm 4 true x w := by
    intro x
    have h := hstep1 x
    rw [fiveForm_add_left'] at h
    exact ((neg_eq_iff_add_eq_zero).mpr h).symm
  have hsub : ∀ x, fiveForm 4 true
      (x - (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x) w =
      2 * fiveForm 4 true x w := by
    intro x
    rw [fiveForm_sub_left', htw_eq x, two_mul]
    abel
  have hmem : ∀ x, (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ
      (x - (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x) =
      -(x - (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x) := by
    intro x
    rw [Matrix.mulVec_sub, htapply x]
    abel
  have hrel : ∀ x, ∃ b : ZMod 5,
      x - (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x = b • w := by
    intro x
    exact (hline (x - (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x)).mp (hmem x)
  have hQQ : fiveForm 4 true w w ≠ 0 := by
    intro hQ0
    have horth : ∀ x, fiveForm 4 true x w = 0 := by
      intro x
      obtain ⟨b, hb⟩ := hrel x
      have hbQ : b * fiveForm 4 true w w = 2 * fiveForm 4 true x w := by
        have h := hsub x
        rw [hb, fiveForm_smul_left'] at h
        exact h
      rw [hQ0, mul_zero] at hbQ
      have h2 : (2 : ZMod 5) * fiveForm 4 true x w = 0 := hbQ.symm
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 two_ne_zero_zmodFive
      · exact h3
    have hvec : ∀ i, fiveFormVec 4 true w i = 0 := by
      intro i
      have hi := horth (Pi.single i 1)
      rw [fiveForm_eq_dotProduct', single_dotProduct] at hi
      simpa using hi
    have hw0 : w = 0 := by
      funext i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · have := hvec j.castSucc
        simpa only [fiveFormVec, Fin.castSucc_ne_last, ↓reduceIte, Pi.zero_apply] using this
      · have := hvec (Fin.last 4)
        simp only [fiveFormVec, ↓reduceIte] at this
        have hne := neg_one_ne_zero_zmodFive
        exact (mul_eq_zero.mp this).resolve_left hne
    exact hw hw0
  refine ⟨hQQ, ?_⟩
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [fiveReflOf_mulVec]
  obtain ⟨b, hb⟩ := hrel (Pi.single i 1)
  have hbQ : b * fiveForm 4 true w w =
      2 * fiveForm 4 true (Pi.single i 1) w := by
    have h := hsub (Pi.single i 1)
    rw [hb, fiveForm_smul_left'] at h
    exact h
  have hbval : b = 2 * fiveForm 4 true (Pi.single i 1) w *
      (fiveForm 4 true w w)⁻¹ := by
    have h := congrArg (fun z => z * (fiveForm 4 true w w)⁻¹) hbQ
    rw [mul_assoc, mul_inv_cancel₀ hQQ, mul_one] at h
    exact h
  have htx : (t : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ (Pi.single i 1) =
      Pi.single i 1 - b • w := by
    rw [← hb]
    abel
  rw [htx, hbval]

theorem mem_fiveReflections_four_true_false_of_dvd_card_centralizer
    {t : fiveReflectionGroup 4 true false} (ht : orderOf t = 2)
    (hdet : Matrix.GeneralLinearGroup.det (t : GL (Fin 5) (ZMod 5)) ≠ 1)
    (h13 : 13 ∣ Nat.card
      (Subgroup.centralizer ({t} : Set (fiveReflectionGroup 4 true false)))) :
    (t : GL (Fin 5) (ZMod 5)) ∈ fiveReflections 4 true false := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨c, hc13⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.centralizer ({t} : Set (fiveReflectionGroup 4 true false))) 13 h13
  let cGL : GL (Fin 5) (ZMod 5) :=
    ((c : fiveReflectionGroup 4 true false) : GL (Fin 5) (ZMod 5))
  have hcGL_order : orderOf cGL = 13 := by
    dsimp only [cGL]
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc13]
  have hcGL_pow : cGL ^ 13 = 1 := by
    rw [← hcGL_order]
    exact pow_orderOf_eq_one cGL
  have hcGL_ne : cGL ≠ 1 := by
    intro h
    have h1 : orderOf cGL = 1 := by rw [h, orderOf_one]
    rw [hcGL_order] at h1
    omega
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht, pow_two] at h
    exact h
  have ht2GL : (t : GL (Fin 5) (ZMod 5)) * (t : GL (Fin 5) (ZMod 5)) = 1 := by
    have h := congrArg (fun u : fiveReflectionGroup 4 true false =>
      (u : GL (Fin 5) (ZMod 5))) ht2
    simpa using h
  have htc : (t : GL (Fin 5) (ZMod 5)) * cGL =
      cGL * (t : GL (Fin 5) (ZMod 5)) := by
    have hc : (c : fiveReflectionGroup 4 true false) * t =
        t * (c : fiveReflectionGroup 4 true false) :=
      Subgroup.mem_centralizer_singleton_iff.mp c.2
    have h := congrArg (fun u : fiveReflectionGroup 4 true false =>
      (u : GL (Fin 5) (ZMod 5))) hc
    have h' : cGL * (t : GL (Fin 5) (ZMod 5)) =
        (t : GL (Fin 5) (ZMod 5)) * cGL := by simpa [cGL] using h
    exact h'.symm
  rcases eq_one_or_eq_neg_one_or_exists_eigenline_of_commute ht2GL hcGL_pow hcGL_ne htc with
    h1 | hneg1 | hnegline | hposline
  · exfalso
    have htone : t = 1 := Subtype.ext h1
    rw [htone, orderOf_one] at ht
    omega
  · exfalso
    exact neg_one_notMem_fiveReflectionGroup_four_true_false (hneg1 ▸ t.2)
  · obtain ⟨w, hw, hline⟩ := hnegline
    have hform : ∀ x y, fiveForm 4 true
        (((t : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x)
        (((t : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ y) =
        fiveForm 4 true x y :=
      fiveForm_mulVec_of_mem t.2
    obtain ⟨hQ, ht_eq⟩ := eq_fiveReflOf_of_neg_eigenline hform ht2GL hw hline
    have hnotsq : ¬ IsSquare (fiveForm 4 true w w) := by
      intro hsq
      have hrw : fiveReflOf 4 true w ∈ fiveReflections 4 true true :=
        fiveReflOf_mem hQ (by simp [hsq])
      have hrwR : fiveReflOf 4 true w ∈ fiveReflectionGroup 4 true false := by
        rw [← ht_eq]
        exact t.2
      exact (notMem_fiveReflectionGroup_four_true_false_of_mem_fiveReflections_true
        hrw) hrwR
    rw [ht_eq]
    exact fiveReflOf_mem hQ (by simp [hnotsq])
  · obtain ⟨w, hw, hline⟩ := hposline
    exfalso
    have hneg_apply : ∀ x, (((-(t : GL (Fin 5) (ZMod 5))) :
        Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x) =
        -(((t : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x) := by
      intro x
      rw [Matrix.neg_mulVec]
    have hform_neg : ∀ x y, fiveForm 4 true
        (((-(t : GL (Fin 5) (ZMod 5))) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x)
        (((-(t : GL (Fin 5) (ZMod 5))) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ y) =
        fiveForm 4 true x y := by
      intro x y
      rw [hneg_apply x, hneg_apply y, fiveForm_neg_neg']
      exact fiveForm_mulVec_of_mem t.2 x y
    have hneg2 : (-(t : GL (Fin 5) (ZMod 5))) * (-(t : GL (Fin 5) (ZMod 5))) = 1 := by
      rw [neg_mul_neg, ht2GL]
    have hline_neg : ∀ x, (((-(t : GL (Fin 5) (ZMod 5))) :
        Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x = -x ↔ ∃ a : ZMod 5, x = a • w) := by
      intro x
      rw [hneg_apply x]
      constructor
      · intro hx
        exact (hline x).mp (neg_injective hx)
      · intro hx
        exact congrArg Neg.neg ((hline x).mpr hx)
    obtain ⟨hQ, ht_neg_eq⟩ :=
      eq_fiveReflOf_of_neg_eigenline (t := -(t : GL (Fin 5) (ZMod 5)))
        hform_neg hneg2 hw hline_neg
    have ht_eq_neg : (t : GL (Fin 5) (ZMod 5)) = -(fiveReflOf 4 true w) := by
      rw [← ht_neg_eq, neg_neg]
    apply hdet
    rw [ht_eq_neg]
    have hmul : (-(fiveReflOf 4 true w) : GL (Fin 5) (ZMod 5)) =
        (-1 : GL (Fin 5) (ZMod 5)) * fiveReflOf 4 true w := by
      rw [neg_mul, one_mul]
    have hdet_neg_one :
        Matrix.GeneralLinearGroup.det (-1 : GL (Fin 5) (ZMod 5)) = -1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_neg, Units.val_one,
        Matrix.det_neg, Matrix.det_one, Fintype.card_fin, Units.coe_neg_one]
      ring
    rw [hmul, map_mul, hdet_neg_one, det_fiveReflOf (n := 4) (ε := true) hQ]
    simp

end CFSG.OddTranspositions.PartThree

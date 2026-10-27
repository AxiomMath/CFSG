module

public import CFSG.Quasithin.Background.SzG11M12Syl
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut

public section

namespace CFSG.Quasithin.G11.SzG11S

namespace M12Syl

open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier M12Data
open CFSG.ComponentClassification.M12Cover

@[expose] def letterP (d : ℕ) : Equiv.Perm (Fin 12) :=
  if d = 1 then m12gA else if d = 2 then m12bp else if d = 3 then m12bp⁻¹ else 1

@[expose] def evalP : ℕ → ℕ → Equiv.Perm (Fin 12)
  | 0, _ => 1
  | n + 1, w => if w = 0 then 1 else letterP (w % 4) * evalP n (w / 4)

theorem tbl_gp : tbl m12bp = tBp := by decide +kernel

theorem tbl_gpi : tbl m12bp⁻¹ = tBpi := by decide +kernel

theorem tbl_letterP (d : ℕ) : tbl (letterP d) = letterT tBp tBpi d := by
  unfold letterP letterT
  split_ifs
  · exact tbl_gA
  · exact tbl_gp
  · exact tbl_gpi
  · exact tbl_one

theorem tbl_evalP : ∀ n w : ℕ, tbl (evalP n w) = evalN tBp tBpi n w
  | 0, w => by simp [evalP, evalN, tbl_one]
  | n + 1, w => by
    by_cases hw : w = 0
    · simp [evalP, evalN, hw, tbl_one]
    · simp only [evalP, evalN, hw, ite_false]
      rw [tbl_mul, tbl_letterP, tbl_evalP n]

theorem beta_evalM :
    ∀ n w : ℕ, ((beta (evalM n w) : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) = evalP n w
  | 0, w => by simp [evalM, evalP]
  | n + 1, w => by
    by_cases hw : w = 0
    · simp [evalM, evalP, hw]
    · simp only [evalM, evalP, hw, ite_false, map_mul, Subgroup.coe_mul]
      rw [beta_evalM n]
      congr 1
      unfold letterM letterP
      split_ifs
      · rw [beta_m12a]
      · exact beta_m12b
      · rw [map_inv, Subgroup.coe_inv, beta_m12b]
      · simp

@[expose] def PresD (σ : Equiv.Perm (Fin 12)) (i j : Fin 12) : Prop :=
  (σ i = i ∧ σ j = j) ∨ (σ i = j ∧ σ j = i)

theorem outer_no_stab
    (g : ↥NativeSporadic.M12) {i j : Fin 12} (hij : i ≠ j)
    (h : ∀ s : ↥NativeSporadic.M12, PresD (s : Equiv.Perm (Fin 12)) i j →
      PresD ((g * beta s * g⁻¹ : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) i j) : False := by
  obtain ⟨m, hm0, hm1⟩ := exists_smul_eq_two m12_hyp (by decide) (by norm_num) i j hij
  have hm0' : (m : Equiv.Perm (Fin 12)) 0 = i := hm0
  have hm1' : (m : Equiv.Perm (Fin 12)) 1 = j := hm1
  obtain ⟨hs0, hs1⟩ := outer_swap
  have e0 := tbl_evalM fuel outerWord
  have hs0' : ((evalM fuel outerWord : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) 0 = 1 := by
    have := tbl_getD ((evalM fuel outerWord : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) 0
    rw [e0] at this
    simp only [Fin.val_zero] at this
    rw [hs0] at this
    exact Fin.ext this.symm
  have hs1' : ((evalM fuel outerWord : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) 1 = 0 := by
    have := tbl_getD ((evalM fuel outerWord : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) 1
    rw [e0] at this
    simp only [Fin.val_one] at this
    rw [hs1] at this
    exact Fin.ext this.symm
  set s₀ : ↥NativeSporadic.M12 := evalM fuel outerWord with hs₀
  have hspres : PresD ((m * s₀ * m⁻¹ : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) i j := by
    right
    have hi : (m⁻¹ : ↥NativeSporadic.M12).1 i = 0 := by
      rw [← hm0']; simp
    have hj : (m⁻¹ : ↥NativeSporadic.M12).1 j = 1 := by
      rw [← hm1']; simp
    constructor
    · simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply]
      rw [hi, hs0', hm1']
    · simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply]
      rw [hj, hs1', hm0']
  have h1 := h _ hspres
  have hq : g * beta (m * s₀ * m⁻¹) * g⁻¹ = (g * beta m) * beta s₀ * (g * beta m)⁻¹ := by
    simp [map_mul, map_inv, mul_assoc]
  rw [hq] at h1
  set Q : Equiv.Perm (Fin 12) := ((g * beta m : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12))
    with hQ
  set r : Equiv.Perm (Fin 12) := ((beta s₀ : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) with hr
  have hrP : r = evalP fuel outerWord := beta_evalM fuel outerWord
  have hfree := outer_free
  have hrt : tbl r = evalN tBp tBpi fuel outerWord := by rw [hrP, tbl_evalP]
  have hr1 : ∀ x : Fin 12, r x ≠ x := by
    intro x hx
    have h2 := (hfree x x.2).1
    have h3 := tbl_getD r x
    rw [hrt, hx] at h3
    exact h2 h3
  have hr2 : ∀ x : Fin 12, r (r x) ≠ x := by
    intro x hx
    have h2 := (hfree x x.2).2
    have h3 := tbl_getD (r * r) x
    rw [tbl_mul, hrt, Equiv.Perm.mul_apply, hx] at h3
    exact h2 h3
  have hconj : ((Q * r * Q⁻¹ : Equiv.Perm (Fin 12))) =
      ((g * beta m * beta s₀ * (g * beta m)⁻¹ : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) := by
    simp [hQ, hr, Subgroup.coe_mul]
  rw [← hconj] at h1
  rcases h1 with ⟨h1, -⟩ | ⟨h1, h2⟩
  · have h3 : Q (r (Q⁻¹ i)) = Q (Q⁻¹ i) := by
      have : (Q * r * Q⁻¹) i = i := h1
      simpa [Equiv.Perm.mul_apply] using this
    exact hr1 (Q⁻¹ i) (Q.injective h3)
  · have h3 : (Q * r * Q⁻¹) ((Q * r * Q⁻¹) i) = i := by rw [h1, h2]
    have h4 : Q (r (r (Q⁻¹ i))) = Q (Q⁻¹ i) := by simpa [Equiv.Perm.mul_apply] using h3
    exact hr2 (Q⁻¹ i) (Q.injective h4)

end M12Syl

end CFSG.Quasithin.G11.SzG11S

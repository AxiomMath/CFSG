module

public import CFSG.RankThree.PartOne.SEITZ5.UTrans

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2
open CFSG.RankThree.PartOne.CTP (u2 l2 u2_coe)

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

@[expose] def dg (s : fixSub σ) (hs : s ≠ 0) : SpecialLinearGroup (Fin 2) (fixSub σ) :=
  ⟨!![s, 0; 0, s⁻¹], by rw [Matrix.det_fin_two_of]; field_simp; simp⟩

theorem ent_dg_zero_zero (s : fixSub σ) (hs : s ≠ 0) : ent (dg s hs) 0 0 = (s : K) := by
  simp [ent, dg]

theorem ent_dg_zero_one (s : fixSub σ) (hs : s ≠ 0) : ent (dg s hs) 0 1 = 0 := by
  simp [ent, dg]

theorem ent_dg_one_zero (s : fixSub σ) (hs : s ≠ 0) : ent (dg s hs) 1 0 = 0 := by
  simp [ent, dg]

theorem ent_dg_one_one (s : fixSub σ) (hs : s ≠ 0) : ent (dg s hs) 1 1 = ((s : K))⁻¹ := by
  simp [ent, dg]

theorem coe_dg (s : fixSub σ) (hs : s ≠ 0) :
    ((dg s hs : SpecialLinearGroup (Fin 2) (fixSub σ)) : Matrix (Fin 2) (Fin 2) (fixSub σ)) =
      !![s, 0; 0, s⁻¹] := rfl

theorem dg_mul (s s' : fixSub σ) (hs : s ≠ 0) (hs' : s' ≠ 0) :
    dg s hs * dg s' hs' = dg (s * s') (mul_ne_zero hs hs') := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_dg, coe_dg, coe_dg]
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

theorem dg_mul_u2_mul_inv (s : fixSub σ) (hs : s ≠ 0) (c : fixSub σ) :
    dg s hs * u2 c * (dg s hs)⁻¹ = u2 (s * s * c) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, coe_dg, u2_coe, u2_coe, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem Aff.conj_dg {P : Frame σ n} {g t : SUid σ n} {s : fixSub σ} (hs : s ≠ 0) {τ₁ τ₂ : K}
    {c : fixSub σ} (hg : Aff P g (dg s hs) τ₁ τ₂) (ht : Aff P t (u2 c) 0 0) :
    Aff P (g * t * g⁻¹) (u2 (s * s * c)) 0 ((s : K) * c * τ₁) := by
  have := (hg.mul ht).mul hg.inv
  rw [dg_mul_u2_mul_inv] at this
  obtain ⟨h00, h01, h10, h11⟩ := ent_u2 (σ := σ) c
  have hs' : (s : K) ≠ 0 := fun h => hs (Subtype.ext h)
  simp only [h00, h01, h10, h11, ent_inv_zero_zero, ent_inv_zero_one, ent_inv_one_zero,
    ent_inv_one_one, ent_dg_zero_zero, ent_dg_zero_one, ent_dg_one_zero, ent_dg_one_one] at this
  exact this.congr (by field_simp; ring) (by field_simp; ring)

theorem cocycle_mem {P : Frame σ n} {H : Subgroup (SUid σ n)} {s s' : fixSub σ} (hs : s ≠ 0)
    (hs' : s' ≠ 0) {g g' g'' : SUid σ n} (hg : g ∈ affGroup P H) (hg' : g' ∈ affGroup P H)
    (hg'' : g'' ∈ affGroup P H) {a₁ a₂ b₁ b₂ c₁ c₂ : K} (h : Aff P g (dg s hs) a₁ a₂)
    (h' : Aff P g' (dg s' hs') b₁ b₂) (h'' : Aff P g'' (dg (s * s') (mul_ne_zero hs hs')) c₁ c₂) :
    ((s' : K) * a₁ + b₁ - c₁, ((s' : K))⁻¹ * a₂ + b₂ - c₂) ∈ xTrans P H := by
  have hm := h.mul h'
  rw [dg_mul] at hm
  simp only [ent_dg_zero_zero, ent_dg_zero_one, ent_dg_one_zero, ent_dg_one_one] at hm
  have := sub_mem_xTrans ((affGroup P H).mul_mem hg hg') hg'' hm h''
  simpa using this

end CFSG.RankThree.PartOne.SEITZ5

module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieLocB
public import CFSG.LocalAnalysis.EvenBN.U5.ModelSylowRank
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieDefs

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

@[expose] def sylSY : Subgroup (hypPSU h 2 1) := (Ssub h).map (hypProj h 2 1)

variable {h}

theorem syl_mat_levHom_ee (B : SpecialLinearGroup (Fin 2) h.fixedField) (i j : Fin 2) :
    mat (levHom h B) (.inl i) (.inl j) = slM B i j := by
  rw [levHom_eq_lev, mat_lev]
  simp [oddDiag]

theorem syl_eq_one_of_proj_eq {B : SpecialLinearGroup (Fin 2) h.fixedField} {s : hypSU h 2 1}
    (hs : s ∈ Ssub h) (e : hypProj h 2 1 s = hypProj h 2 1 (levHom h B)) : B = 1 := by
  have hch : CharP K 2 := h.charP
  have hz : s⁻¹ * levHom h B ∈ hypScalars h 2 1 := by
    rw [← ker_hypProj, MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]
  obtain ⟨c, -, hc⟩ := exists_scalar_of_mem_hypScalars hz
  have hL : levHom h B = s * (s⁻¹ * levHom h B) := (mul_inv_cancel_left s _).symm
  obtain ⟨-, x, C, hxC⟩ := hs
  have hent : ∀ i j : Fin 2, slM B i j = (1 : Matrix (Fin 2) (Fin 2) K) i j * c := by
    intro i j
    rw [← syl_mat_levHom_ee, hL, mat_mul, Matrix.mul_apply]
    simp only [hc, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hxC,
      oddUni_apply_ee]
  have h00 : slM B 0 0 = c := by rw [hent]; simp
  have h11 : slM B 1 1 = c := by rw [hent]; simp
  have h01 : slM B 0 1 = 0 := by rw [hent]; simp
  have h10 : slM B 1 0 = 0 := by rw [hent]; simp
  have hdet := det_slM B
  rw [Matrix.det_fin_two, h00, h11, h01, h10] at hdet
  have hcc : c * c = 1 := by linear_combination hdet
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hc1 : c = 1 := by
    have : (c - 1) ^ 2 = 0 := by linear_combination hcc + (1 - c) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  ext i j
  have := hent i j
  rw [slM_apply, hc1, mul_one] at this
  rw [this]
  fin_cases i <;> fin_cases j <;> simp

theorem syl_proj_levHom_injective : Function.Injective ((hypProj h 2 1).comp (levHom h)) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  exact syl_eq_one_of_proj_eq (one_mem _) (by rw [map_one]; exact hB.symm)

theorem syl_lY_eq_range : lY h = ((hypProj h 2 1).comp (levHom h)).range := by
  rw [MonoidHom.range_comp, lY, L0]

theorem syl_sY_inf_lY : sylSY h ⊓ lY h = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨⟨s, hs, rfl⟩, ⟨g, ⟨B, rfl⟩, hg⟩⟩
  have hB : B = 1 := syl_eq_one_of_proj_eq hs hg.symm
  rw [Subgroup.mem_bot, ← hg, hB, map_one, map_one]

theorem syl_conj_mem_sY {y x : hypPSU h 2 1} (hy : y ∈ lY h) (hx : x ∈ sylSY h) :
    y * x * y⁻¹ ∈ sylSY h := by
  obtain ⟨g, ⟨B, rfl⟩, rfl⟩ := hy
  obtain ⟨s, hs, rfl⟩ := hx
  refine ⟨levHom h B * s * (levHom h B)⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  rw [levHom_eq_lev]
  exact lev_conj_mem_Ssub _ _ hs

theorem syl_lY_le_normalizer : lY h ≤ Subgroup.normalizer (sylSY h : Set (hypPSU h 2 1)) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨syl_conj_mem_sY hy, fun hx => ?_⟩
  have := syl_conj_mem_sY (inv_mem hy) hx
  have e : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
  rwa [e] at this

theorem syl_card_sY : Nat.card (sylSY h) = (2 ^ f) ^ 8 := by
  rw [sylSY, card_map_hypProj Ssub_le_Usub, card_Ssub]

theorem syl_card_lY : Nat.card (lY h) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have := h.finite
  rw [syl_lY_eq_range, ← Nat.card_congr (MonoidHom.ofInjective syl_proj_levHom_injective).toEquiv,
    CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two, h.card_fixedField]

theorem syl_card_sup_lY :
    Nat.card (sylSY h ⊔ lY h : Subgroup (hypPSU h 2 1)) =
      (2 ^ f) ^ 8 * (2 ^ f * ((2 ^ f) ^ 2 - 1)) := by
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
    syl_lY_le_normalizer (disjoint_iff.2 syl_sY_inf_lY), syl_card_sY, syl_card_lY]

end CFSG.Quasithin.H13.F431.Un.L5

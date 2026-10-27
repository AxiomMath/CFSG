module

public import CFSG.LocalAnalysis.EvenBN.U5.ModelSylowRank
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Stab
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsUnitBorel

public section

namespace CFSG.Quasithin.H13.Sec53F.Unit

open scoped Pointwise commutatorElement
open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem mem_hypScalars_of_torus {t : hypSU h 2 1} (ht : t ∈ Isub h)
    (hχ : ∀ a, mat t a a = mat t ιe₁ ιe₁) : t ∈ hypScalars h 2 1 := by
  have hdiag : mat t = Matrix.diagonal fun _ => mat t ιe₁ ιe₁ := by
    rw [torus_mat ht]
    congr 1
    funext a
    exact hχ a
  have hne : mat t ιe₁ ιe₁ ≠ 0 := torus_ne_zero ht ιe₁
  have hnorm : h.norm (mat t ιe₁ ιe₁) = 1 := by
    have := torus_bar_mul ht ιe₁
    rw [show hypPartner ιe₁ = ιf₁ from rfl, hχ ιf₁] at this
    rw [UnitaryFieldData.norm]
    linear_combination this
  have hdet : (mat t ιe₁ ιe₁) ^ 5 = 1 := by
    have h1 : ((t : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K).det = 1 :=
      t.2.2
    have h2 : (mat t).det = 1 := h1
    rw [hdiag, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      show Fintype.card (HypIndex 2 1) = 5 from by simp [HypIndex]] at h2
    exact h2
  refine ⟨Units.mk0 _ hne, hnorm, Units.ext hdet, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  exact hdiag

theorem mul_eq_of_centralizes {b : hypSU h 2 1} (hb : b ∈ hypBorel h 2 1)
    (hx : hypProj h 2 1 b ∈ Subgroup.centralizer
      (hypProjUnitriangular h 2 1 : Set (hypPSU h 2 1))) :
    ∀ u ∈ hypUnitriangular h 2 1, b * u * b⁻¹ = u := by
  intro u hu
  have hbN : b ∈ Subgroup.normalizer (hypUnitriangular h 2 1 : Set (hypSU h 2 1)) := by
    rw [UnitaryHigher.normalizer_hypUnitriangular h (by norm_num) (by norm_num)]
    exact hb
  have h1 : b * u * b⁻¹ ∈ hypUnitriangular h 2 1 := (Subgroup.mem_normalizer_iff.mp hbN u).mp hu
  have hc := Subgroup.mem_centralizer_iff.mp hx (hypProj h 2 1 u) ⟨u, hu, rfl⟩
  have hZ : b * u * b⁻¹ * u⁻¹ ∈ hypScalars h 2 1 := by
    rw [← ker_hypProj, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [mul_inv_eq_one, ← hc, mul_inv_cancel_right]
  have hU : b * u * b⁻¹ * u⁻¹ ∈ hypUnitriangular h 2 1 := mul_mem h1 (inv_mem hu)
  have hmem : b * u * b⁻¹ * u⁻¹ ∈ (⊥ : Subgroup (hypSU h 2 1)) := by
    rw [← hypUnitriangular_inf_hypScalars h (r := 2) (ε := 1) (by norm_num) (by norm_num)]
    exact ⟨hU, hZ⟩
  rw [Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact hmem

theorem conj_U_superdiag {u₀ u : hypSU h 2 1} (hu₀ : u₀ ∈ hypUnitriangular h 2 1)
    (hu : u ∈ hypUnitriangular h 2 1) :
    mat (u₀⁻¹ * u * u₀) ιe₁ ιe₂ = mat u ιe₁ ιe₂ ∧ mat (u₀⁻¹ * u * u₀) ιe₂ ιz = mat u ιe₂ ιz ∧
      mat (u₀⁻¹ * u * u₀) ιz ιf₂ = mat u ιz ιf₂ ∧
      mat (u₀⁻¹ * u * u₀) ιf₂ ιf₁ = mat u ιf₂ ιf₁ := by
  have hi := inv_mem hu₀
  have hm := mul_mem hi hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e := mul_e₁e₂ hi hu₀
    rw [inv_mul_cancel, mat_one, one_apply_ne (by decide)] at e
    rw [mul_e₁e₂ hm hu₀, mul_e₁e₂ hi hu]
    linear_combination (-1 : K) * e
  · have e := mul_e₂z hi hu₀
    rw [inv_mul_cancel, mat_one, one_apply_ne (by decide)] at e
    rw [mul_e₂z hm hu₀, mul_e₂z hi hu]
    linear_combination (-1 : K) * e
  · have e := mul_zf₂ hi hu₀
    rw [inv_mul_cancel, mat_one, one_apply_ne (by decide)] at e
    rw [mul_zf₂ hm hu₀, mul_zf₂ hi hu]
    linear_combination (-1 : K) * e
  · have e := mul_f₂f₁ hi hu₀
    rw [inv_mul_cancel, mat_one, one_apply_ne (by decide)] at e
    rw [mul_f₂f₁ hm hu₀, mul_f₂f₁ hi hu]
    linear_combination (-1 : K) * e

theorem centralizer_le_map_ZPsub :
    Subgroup.centralizer (hypProjUnitriangular h 2 1 : Set (hypPSU h 2 1)) ≤
      (ZPsub h).map (hypProj h 2 1) := by
  intro x hx
  have hxN := Subgroup.centralizer_le_normalizer _ hx
  rw [normalizer_hypProjUnitriangular h (by norm_num) (by norm_num)] at hxN
  obtain ⟨b, hb, rfl⟩ := hxN
  have hbN : b ∈ Subgroup.normalizer (hypUnitriangular h 2 1 : Set (hypSU h 2 1)) := by
    rw [UnitaryHigher.normalizer_hypUnitriangular h (by norm_num) (by norm_num)]
    exact hb
  obtain ⟨u₀, hu₀, t₀, ht₀, rfl⟩ := normalizer_eq_mul h (r := 2) (ε := 1) (by norm_num)
    (by norm_num) hbN
  have hcomm := mul_eq_of_centralizes hb hx
  have htu : ∀ u ∈ hypUnitriangular h 2 1, t₀ * u * t₀⁻¹ = u₀⁻¹ * u * u₀ := by
    intro u hu
    calc t₀ * u * t₀⁻¹ = u₀⁻¹ * ((u₀ * t₀) * u * (u₀ * t₀)⁻¹) * u₀ := by group
      _ = u₀⁻¹ * u * u₀ := by rw [hcomm u hu]
  have key : ∀ u ∈ hypUnitriangular h 2 1, ∀ a b : HypIndex 2 1,
      mat (u₀⁻¹ * u * u₀) a b = mat u a b → mat u a b ≠ 0 → mat t₀ a a = mat t₀ b b := by
    intro u hu a b hsd hne
    have e : mat (t₀ * u * t₀⁻¹) a b = mat (u₀⁻¹ * u * u₀) a b := by rw [htu u hu]
    rw [torus_conj_apply ht₀, hsd] at e
    have hb := torus_ne_zero ht₀ b
    have e' : mat t₀ a a * mat u a b = mat t₀ b b * mat u a b := by
      calc mat t₀ a a * mat u a b
          = (mat t₀ a a * mat u a b * (mat t₀ b b)⁻¹) * mat t₀ b b := by
            rw [mul_assoc, inv_mul_cancel₀ hb, mul_one]
        _ = mat u a b * mat t₀ b b := by rw [e]
        _ = mat t₀ b b * mat u a b := mul_comm _ _
    exact mul_right_cancel₀ hne e'
  obtain ⟨y, hy, hya⟩ := exists_rootI₁ h 1
  obtain ⟨c, hc⟩ := trace_surj (hK := h) (a := 1 * h.bar 1) (by simp)
  obtain ⟨y', hy', hyu, -⟩ := exists_rootI₂ h hc
  obtain ⟨hyU, -⟩ := mem_patSub_sI₁.1 hy
  obtain ⟨hyU', -⟩ := mem_patSub_sI₂.1 hy'
  have r1 : mat y ιf₂ ιf₁ = 1 := by rw [(U_rel hyU).1, hya, map_one]
  have r2 : mat y' ιz ιf₂ = 1 := by rw [(U_rel hyU').2.1, hyu, map_one]
  obtain ⟨s1, s2, s3, s4⟩ := conj_U_superdiag hu₀ hyU
  obtain ⟨s1', s2', s3', s4'⟩ := conj_U_superdiag hu₀ hyU'
  have E1 := key y hyU ιe₁ ιe₂ s1 (by rw [hya]; exact one_ne_zero)
  have E2 := key y hyU ιf₂ ιf₁ s4 (by rw [r1]; exact one_ne_zero)
  have E3 := key y' hyU' ιe₂ ιz s2' (by rw [hyu]; exact one_ne_zero)
  have E4 := key y' hyU' ιz ιf₂ s3' (by rw [r2]; exact one_ne_zero)
  have hχ : ∀ a, mat t₀ a a = mat t₀ ιe₁ ιe₁ := by
    intro a
    have F2 := E3.symm.trans E1.symm
    have F3 := E4.symm.trans F2
    rcases hypIndex_cases a with rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact E1.symm
    · exact F2
    · exact F3
    · exact E2.symm.trans F3
  have hts : t₀ ∈ hypScalars h 2 1 := mem_hypScalars_of_torus ht₀ hχ
  have hπ : hypProj h 2 1 (u₀ * t₀) = hypProj h 2 1 u₀ := by
    have : hypProj h 2 1 t₀ = 1 := by
      rw [← MonoidHom.mem_ker, ker_hypProj]
      exact hts
    rw [map_mul, this, mul_one]
  rw [hπ] at hx ⊢
  have hcomm' := mul_eq_of_centralizes (hypUnitriangular_le_hypBorel h hu₀) hx
  have hcen : u₀ ∈ CFSG.centerIn (hypUnitriangular h 2 1) :=
    ⟨hu₀, Subgroup.mem_centralizer_iff.2 fun y hy => by
      have := hcomm' y hy
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm⟩
  rw [centerIn_U] at hcen
  exact ⟨u₀, hcen, rfl⟩

end CFSG.Quasithin.H13.Sec53F.Unit

module

public import CFSG.RankThree.GF2n.Tim79aRootStatements
public import CFSG.Timmesfeld.Transvection.ModelSpRadical
public import CFSG.Timmesfeld.Transvection.ModelGeometry

public section

namespace CFSG.RankThree.GF2n.Tim79a

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank

theorem rootIrrModel_sp {n : ℕ} {F : Type} [Field F] [CharP F 2] (hcore : SpCoreStmt n F)
    {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0) {T : Subgroup (StatedSp n F)}
    (hT : CFSG.Timmesfeld.ARS.CaseM.IsTransGroup a T) : RootIrrModel (StatedSp n F) T := by
  intro R hTR hRP hRnorm
  rw [hcore ha hT] at hRP ⊢
  rw [normalizer_eq_spLine ha hT] at hRnorm
  by_cases hRT : R ≤ T
  · exact Or.inl (le_antisymm hRT hTR)
  right
  obtain ⟨x, hxR, hxT⟩ := SetLike.not_le_iff_exists.1 hRT
  obtain ⟨w, l, haw, hxw⟩ := exists_param_of_mem_spRad ha (hRP hxR)
  have hw : ∀ c : F, w ≠ c • a := fun c hc =>
    hxT ((hT.1 x).2 ⟨l, mat_eq_spTrans_of_param hxw hc⟩)
  refine le_antisymm hRP fun y hy => ?_
  obtain ⟨w', l', haw', hyw⟩ := exists_param_of_mem_spRad ha hy
  by_cases hw' : ∃ c : F, w' = c • a
  · obtain ⟨c, hc⟩ := hw'
    exact hTR ((hT.1 y).2 ⟨l', mat_eq_spTrans_of_param hyw hc⟩)
  push Not at hw'
  obtain ⟨g, hga, c, hgw⟩ := exists_mat_mulVec_eq_mod haw haw' hw hw'
  have hgx : g * x * g⁻¹ ∈ R := hRnorm g ⟨1, one_ne_zero, by rw [hga, one_smul]⟩ x hxR
  obtain ⟨t, ht⟩ := hT.2 (l + l')
  have hagw : spForm a (SpExtras.mat n F g *ᵥ w) = 0 := by
    have h := spForm_mat_mulVec g a w
    rw [hga] at h
    rw [h, haw]
  have hzy : g * x * g⁻¹ * t = y := by
    refine eq_of_mat_mulVec_eq fun v => ?_
    rw [mat_mul_mulVec_of_param hagw (spForm_zero_right a) (mat_conj_mulVec_of_param hxw hga)
      (fun v => by rw [ht]; exact spTrans_mulVec_param a v (l + l')) v, hyw, hgw]
    simp only [add_zero, spForm_add_left, spForm_smul_left', spForm_zero_right, mul_zero]
    have h2 := two_smul_vec_eq_zero ((c * spForm a v + l * spForm a v) • a)
    linear_combination (norm := module) h2
  rw [← hzy]
  exact R.mul_mem hgx (hTR ((hT.1 t).2 ⟨_, ht⟩))

theorem rootInnerModel_sp_of_s2 {n : ℕ} {F : Type} [Field F] [CharP F 2] (hcore : SpCoreStmt n F)
    {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0) {T : Subgroup (StatedSp n F)}
    (hT : CFSG.Timmesfeld.ARS.CaseM.IsTransGroup a T)
    (hS2 : RootS2Model (StatedSp n F) T) : RootInnerModel (StatedSp n F) T := by
  intro α hαT hαN
  obtain ⟨s, hsP, rfl⟩ :=
    hS2 α hαT fun b hb => hαN b (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hb)
  refine ⟨s, ?_, rfl⟩
  rw [hcore ha hT] at hsP
  obtain ⟨w, l, haw, hsw⟩ := exists_param_of_mem_spRad ha hsP
  have himp : ∀ u, spForm a u = 0 → spForm w u = 0 := by
    intro u hu
    obtain ⟨g, hg⟩ := exists_mat_eq_spTrans u (1 : F)
    have hga : SpExtras.mat n F g *ᵥ a = a := by
      rw [hg, spTrans_mulVec, spForm_eq_zero_comm hu, mul_zero, zero_smul, add_zero]
    have hgN : g⁻¹ ∈ Subgroup.normalizer (T : Set (StatedSp n F)) := by
      rw [normalizer_eq_spLine ha hT]
      exact inv_mem (show g ∈ spLine a from ⟨1, one_ne_zero, by rw [hga, one_smul]⟩)
    have h1 := hαN g⁻¹ hgN
    rw [MulAut.conj_apply, inv_inv] at h1
    obtain ⟨e, he⟩ := (hT.1 _).1 h1
    have hcs : g * (s * g⁻¹ * s⁻¹) * s = g * s * g⁻¹ := by group
    have hp₁ := mat_conj_mulVec_of_param hsw hga
    have hp₂ : ∀ v, SpExtras.mat n F (g * s * g⁻¹) *ᵥ v = v + spForm a v • (0 + w) +
        spForm (0 + w) v • a + ((e + l + spForm 0 w) * spForm a v) • a := by
      rw [← hcs]
      exact mat_mul_mulVec_of_param (spForm_zero_right a) haw
        (fun v => by rw [he]; exact spTrans_mulVec_param a v e) hsw
    obtain ⟨d, hd⟩ := exists_eq_add_smul_of_param ha hp₁ hp₂
    rw [hg, spTrans_mulVec, one_mul, zero_add] at hd
    have hd' : spForm u w • u = d • a := add_left_cancel hd
    have h3 := congrArg (spForm w) hd'
    rw [spForm_smul_right', spForm_smul_right', spForm_eq_zero_comm haw, mul_zero, spForm_comm,
      CharTwo.neg_eq] at h3
    exact mul_self_eq_zero.1 h3
  obtain ⟨c, hc⟩ := exists_eq_smul_of_spForm_imp himp
  exact (hT.1 s).2 ⟨l, mat_eq_spTrans_of_param hsw hc⟩

end CFSG.RankThree.GF2n.Tim79a

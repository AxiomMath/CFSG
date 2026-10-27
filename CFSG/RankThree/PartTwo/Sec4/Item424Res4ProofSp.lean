module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res4ProofKill
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.CoverCentKit

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.RankThree.PartOne.KCSpComm
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.ComponentClassification.PresentationLocal (sympFour commutatorEquivAlternating
  isSimpleGroup_commutator_sympFour isPerfect_commutator_sympFour)
open scoped MatrixGroups commutatorElement

namespace Item424Res4

section E9

variable {k : Type} [Field k]

theorem exists_sl_two_pow_three :
    ∃ M : SL(2, k), M ^ 3 = 1 ∧ (M : Matrix (Fin 2) (Fin 2) k) 0 1 = 1 := by
  set M : SL(2, k) := ⟨!![0, 1; -1, -1], by simp [Matrix.det_fin_two]⟩ with hM
  have hMc : (M : Matrix (Fin 2) (Fin 2) k) = !![0, 1; -1, -1] := rfl
  refine ⟨M, ?_, by rw [hMc]; rfl⟩
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_pow, hMc, pow_three, Matrix.mul_fin_two, Matrix.mul_fin_two,
    Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

theorem mat_longBlock_inl_inr {r : ℕ} (j : Fin r) (A : SL(2, k)) :
    mat r k (longBlock k r j A) (Sum.inl j) (Sum.inr j) = (A : Matrix (Fin 2) (Fin 2) k) 0 1 := by
  rw [mat_longBlock]
  simp [CFSG.LieType.Steinberg.Sp.blockMat]

theorem mat_longBlock_inl_inr_of_ne {r : ℕ} {j l : Fin r} (hjl : j ≠ l) (A : SL(2, k)) :
    mat r k (longBlock k r j A) (Sum.inl l) (Sum.inr l) = 0 := by
  rw [mat_longBlock, blockMat_apply_of_not_mem]
  · exact Matrix.one_apply_ne Sum.inl_ne_inr
  · rintro ⟨h1, -⟩
    rcases mem_coords.1 h1 with h | h
    · exact hjl (Sum.inl_injective h).symm
    · exact Sum.inl_ne_inr h

theorem mat_eq_zero_of_mem_spScalars {r : ℕ} [NeZero r] {z : StatedSp r k}
    (hz : z ∈ spScalars r k) {a b : Fin r ⊕ Fin r} (hab : a ≠ b) : mat r k z a b = 0 := by
  obtain ⟨c, -, hc⟩ := exists_scalar_of_mem_spScalars hz
  rw [mat_apply, hc, Matrix.GeneralLinearGroup.coe_scalar]
  simp [hab]

theorem exists_e9_psp {r : ℕ} (hr : 2 ≤ r) :
    ∃ x y : StatedProj (StatedSp r k), x ≠ 1 ∧ x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = y * x ∧
      y ∉ Subgroup.zpowers x := by
  have : NeZero r := ⟨by omega⟩
  obtain ⟨M, hM3, hM01⟩ := exists_sl_two_pow_three (k := k)
  set i₀ : Fin r := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin r := ⟨1, by omega⟩ with hi₁
  have hi : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
  set u := longBlock k r i₀ M with hu
  set v := longBlock k r i₁ M with hv
  refine ⟨proj r k u, proj r k v, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have hz : u ∈ spScalars r k := by
      rw [← ker_proj]
      exact h
    have h1 := mat_eq_zero_of_mem_spScalars hz
      (Sum.inl_ne_inr : (Sum.inl i₀ : Fin r ⊕ Fin r) ≠ Sum.inr i₀)
    rw [hu, mat_longBlock_inl_inr (k := k) i₀ M, hM01] at h1
    exact one_ne_zero h1
  · rw [← map_pow, hu, ← map_pow, hM3, map_one, map_one]
  · rw [← map_pow, hv, ← map_pow, hM3, map_one, map_one]
  · rw [← map_mul, ← map_mul, (commute_longRootSp2 hi ⟨M, rfl⟩ ⟨M, rfl⟩ : Commute u v).eq]
  · intro hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← map_zpow] at hn
    have hz : (u ^ n)⁻¹ * v ∈ spScalars r k := by
      rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, hn, inv_mul_cancel]
    have h2 : mat r k v = mat r k (u ^ n) * mat r k ((u ^ n)⁻¹ * v) := by
      rw [← map_mul, mul_inv_cancel_left]
    have h3 := congrFun (congrFun h2 (Sum.inl i₁)) (Sum.inr i₁)
    rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr i₁)] at h3
    · have hun : u ^ n = longBlock k r i₀ (M ^ n) := by rw [hu, map_zpow]
      rw [hun, mat_longBlock_inl_inr_of_ne (k := k) hi, zero_mul, hv,
        mat_longBlock_inl_inr (k := k) i₁ M, hM01] at h3
      exact one_ne_zero h3
    · intro b _ hb
      rw [mat_eq_zero_of_mem_spScalars hz hb, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

end E9

theorem not_hasType424_sympFour : ¬ Sec11.KS11Lie2Proof.HasType424 sympFour := by
  have hs : IsSimpleGroup (commutator sympFour) := isSimpleGroup_commutator_sympFour
  refine Census.Karpilovsky.Proving.not_hasType424_of_normal_simple (commutator sympFour) ?_ ?_ ?_
  · have : Group.IsPerfect (commutator sympFour) := isPerfect_commutator_sympFour
    have : Nontrivial (commutator sympFour) := hs.toNontrivial
    exact CFSG.LieType.SteinbergBR.not_isSolvable_of_isPerfect
  · have h := (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := commutator sympFour)).mpr le_rfl
    exact Group.isSolvable_of_comm h.is_comm.comm
  · intro hT
    exact Census.Karpilovsky.Proving.not_isType424_alt_six
      (Sec11.isType424_of_mulEquiv commutatorEquivAlternating.symm hT)

theorem not_hasType424_psp {r : ℕ} (hr : 2 ≤ r) {k : Type} [Field k] [Finite k] :
    ¬ Sec11.KS11Lie2Proof.HasType424 (StatedProj (StatedSp r k)) := by
  by_cases hex : r = 2 ∧ Nat.card k = 2
  · obtain ⟨rfl, hk⟩ := hex
    intro h
    exact not_hasType424_sympFour (h.of_mulEquiv (statedProjEquivSympFour hk))
  · obtain ⟨hs, -⟩ := simple_perfect_statedProj (k := k) hr hex
    have : IsSimpleGroup (⊤ : Subgroup (StatedProj (StatedSp r k))) :=
      Subgroup.topEquiv.isSimpleGroup
    obtain ⟨x, y, hx1, hx3, hy3, hxy, hyx⟩ := exists_e9_psp (k := k) hr
    have hc : ⁅x, y⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr hxy
    exact Sec11.KS11Lie2Proof.not_hasType424_of_simple ⊤ (fun _ _ => Subgroup.mem_top _)
      (Subgroup.mem_top x) (Subgroup.mem_top y) hx1 hx3 hy3
      (by rw [hc]; exact Commute.one_left x) (by rw [hc]; exact Commute.one_left y) hyx

theorem nonempty_fixSub_fieldAut_equiv {r : ℕ} [NeZero r] {F : Type} [Field F] {σ : F ≃+* F}
    (hσ3 : σ ^ 3 = 1) :
    Nonempty (StatedProj (StatedSp r (descentField σ)) ≃* Item426.fixSub (fieldAut r F σ)) := by
  have hrange : (subfieldInj (r := r) σ).range = Item426.fixSub (fieldAut r F σ) := by
    rw [range_subfieldInj, ← spFixedGroup_fieldAut_eq_range (p := 3) ⟨1, rfl⟩ hσ3]
    ext x
    exact Iff.rfl
  exact ⟨(MonoidHom.ofInjective (subfieldInj_injective σ)).trans (MulEquiv.subgroupCongr hrange)⟩

theorem not_hasType424_fixSub_fieldAut {r : ℕ} (hr : 2 ≤ r) {F : Type} [Field F] [Finite F]
    {σ : F ≃+* F} (hσ3 : σ ^ 3 = 1) :
    ¬ Sec11.KS11Lie2Proof.HasType424 (Item426.fixSub (fieldAut r F σ)) := by
  have : NeZero r := ⟨by omega⟩
  have : Finite (descentField σ) := Subtype.finite
  obtain ⟨e⟩ := nonempty_fixSub_fieldAut_equiv (r := r) hσ3
  exact fun h => not_hasType424_psp hr (h.of_mulEquiv e.symm)

theorem pow_three_eq_one_of_conj_fieldAut {r : ℕ} (hr : 1 ≤ r) {F : Type} [Field F] [Finite F]
    {σ : F ≃+* F} {d : MulAut (StatedProj (StatedSp r F))}
    (h3 : (d * fieldAut r F σ * d⁻¹) ^ 3 = 1) : σ ^ 3 = 1 := by
  rw [conj_pow, mul_inv_eq_one, mul_eq_left, ← map_pow] at h3
  exact (KFacts.fieldAut_mem_range_conjAut_iff hr).mp (by rw [h3]; exact one_mem _)

end Item424Res4

open Item424Res4

theorem k424FieldCentSymplectic_holds :
    K424FieldCentSymplectic := by
  refine ⟨fun G _ _ L K c r F _ _ hr h hc3 hK => ?_, fun G _ _ L K c F _ _ _ h hc3 hK => ?_⟩
  · obtain ⟨e, hcN, _, ⟨σ, rfl⟩, -, d, -, hτ⟩ := h
    have hr2 : 2 ≤ r := by omega
    have hσ3 : σ ^ 3 = 1 := pow_three_eq_one_of_conj_fieldAut (r := r) (by omega)
      (by rw [← hτ]; exact KFacts.inducedAutHom_pow_eq_one L e hcN hc3)
    exact not_isType424_of_inducedAut_eq e hcN hc3 hK hτ (not_hasType424_fixSub_fieldAut hr2 hσ3)
  · obtain ⟨e, hcN, _, ⟨σ, rfl⟩, -, d, -, hτ⟩ := h
    have hσ3 : σ ^ 3 = 1 := pow_three_eq_one_of_conj_fieldAut (r := 2) (by norm_num)
      (by rw [← hτ]; exact KFacts.inducedAutHom_pow_eq_one L e hcN hc3)
    exact not_isType424_of_inducedAut_eq e hcN hc3 hK hτ
      (not_hasType424_fixSub_fieldAut le_rfl hσ3)

end CFSG.RankThree.PartTwo.Sec4

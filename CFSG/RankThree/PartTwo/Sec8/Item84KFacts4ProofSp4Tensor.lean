module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLevi
public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofTools
import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item84KFacts4

open Matrix hiding gram gram_apply
open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

section Group

variable {G : Type*} [Group G]

theorem commutator_eq_of_commute {t s t' s' : G} (h1 : Commute t s) (h2 : Commute t s')
    (h3 : Commute t t') (h4 : Commute t' s) (h5 : Commute t' s') :
    t * s * (t' * s') * (t * s)⁻¹ * (t' * s')⁻¹ = s * s' * s⁻¹ * s'⁻¹ := by
  have ht : Commute t (s * (t' * s') * s⁻¹) :=
    (h1.mul_right (h3.mul_right h2)).mul_right h1.inv_right
  have ht' : Commute t' (s * s' * s⁻¹ * s'⁻¹) :=
    ((h4.mul_right h5).mul_right h4.inv_right).mul_right h5.inv_right
  calc t * s * (t' * s') * (t * s)⁻¹ * (t' * s')⁻¹
      = t * (s * (t' * s') * s⁻¹) * t⁻¹ * (t' * s')⁻¹ := by group
    _ = s * (t' * s') * s⁻¹ * (t' * s')⁻¹ := by rw [ht.eq, mul_inv_cancel_right]
    _ = s * t' * s' * s⁻¹ * s'⁻¹ * t'⁻¹ := by group
    _ = t' * s * s' * s⁻¹ * s'⁻¹ * t'⁻¹ := by rw [← h4.eq]
    _ = t' * (s * s' * s⁻¹ * s'⁻¹) * t'⁻¹ := by group
    _ = s * s' * s⁻¹ * s'⁻¹ := by rw [ht'.eq, mul_inv_cancel_right]

end Group

variable {F : Type} [Field F] [CharP F 2]

section Matrices

variable (F) in
@[expose] def wMat : Matrix (Fin 2) (Fin 2) F := !![0, 1; 1, 0]

variable (F) in
@[expose] def yTMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks 0 (wMat F) (wMat F) 1

theorem yTMat_symplectic : (yTMat F)ᵀ * gram F 2 * yTMat F = gram F 2 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [yTMat, wMat, gram_apply, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      CharTwo.neg_eq, CharTwo.add_self_eq_zero]

variable (F) in
@[expose] noncomputable def yT : StatedSp 2 F := ofSymplecticMat (yTMat F) yTMat_symplectic

theorem mat_yT : mat 2 F (yT F) = yTMat F := rfl

theorem mat_levi_apply (B : SL(2, F)) (r c : Fin 2 ⊕ Fin 2) :
    mat 2 F (leviEmbedSL F 2 B) r c =
      fromBlocks (B : Matrix (Fin 2) (Fin 2) F) 0 0
        !![(B : Matrix (Fin 2) (Fin 2) F) 1 1, (B : Matrix (Fin 2) (Fin 2) F) 1 0;
          (B : Matrix (Fin 2) (Fin 2) F) 0 1, (B : Matrix (Fin 2) (Fin 2) F) 0 0] r c := by
  rw [mat_leviEmbedSL, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  congr 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq]

theorem levi_mul_yT (B : SL(2, F)) :
    mat 2 F (leviEmbedSL F 2 B) * yTMat F = yTMat F * mat 2 F (leviEmbedSL F 2 B) := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [mat_levi_apply, yTMat, wMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem range_levi_le_centralizer :
    (leviEmbedSL F 2).range ≤ Subgroup.centralizer ({yT F} : Set (StatedSp 2 F)) := by
  rintro _ ⟨B, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply mat_injective
  rw [map_mul, map_mul, mat_yT]
  exact levi_mul_yT B

end Matrices

section Centralizer

theorem decomp_aux {p00 p01 p10 p11 u v w z : F}
    (e00 : p11 * u + p01 * w = 1 + (p00 * p11 + p01 * p10) + (u * z + v * w))
    (e11 : p10 * v + p00 * z = 1 + (p00 * p11 + p01 * p10) + (u * z + v * w))
    (e10 : p00 * w + p10 * u = 0) (e01 : p01 * z + p11 * v = 0) :
    (u = 0 ∧ v = 0 ∧ w = 0 ∧ z = 0 ∧ p00 * p11 + p01 * p10 = 1) ∨
      (u * z + v * w ≠ 0 ∧ ∃ l : F,
        p00 = l * u ∧ p01 = l * v ∧ p10 = l * w ∧ p11 = l * z) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set c := 1 + (p00 * p11 + p01 * p10) + (u * z + v * w) with hc
  by_cases hD : u * z + v * w = 0
  · left
    have hc2 : c * c = (p00 * p11 + p01 * p10) * (u * z + v * w) := by
      linear_combination (-(p10 * v + p00 * z)) * e00 - c * e11 - (p00 * w + p10 * u) * e01 +
        (p10 * p11 * u * v + p00 * p01 * w * z) * h2
    rw [hD, mul_zero] at hc2
    have hc0 : c = 0 := mul_self_eq_zero.mp hc2
    have hdet : p00 * p11 + p01 * p10 = 1 := by linear_combination hc0 - hD - h2 - hc
    refine ⟨?_, ?_, ?_, ?_, hdet⟩
    · linear_combination p00 * e00 + p00 * hc0 + p01 * e10 - (p00 * p01 * w) * h2 - u * hdet
    · linear_combination p01 * e11 + p01 * hc0 + p00 * e01 - (p00 * p01 * z) * h2 - v * hdet
    · linear_combination p10 * e00 + p10 * hc0 + p11 * e10 - (p10 * p11 * u) * h2 - w * hdet
    · linear_combination p11 * e11 + p11 * hc0 + p10 * e01 - (p10 * p11 * v) * h2 - z * hdet
  · right
    have h1 : p00 * (u * z + v * w) = c * u := by
      linear_combination u * e11 + v * e10 - (p10 * u * v) * h2
    have h3 : p01 * (u * z + v * w) = c * v := by
      linear_combination u * e01 + v * e00 - (p11 * u * v) * h2
    have h4 : p10 * (u * z + v * w) = c * w := by
      linear_combination z * e10 + w * e11 - (p00 * w * z) * h2
    have h5 : p11 * (u * z + v * w) = c * z := by
      linear_combination z * e00 + w * e01 - (p01 * w * z) * h2
    refine ⟨hD, c / (u * z + v * w), ?_, ?_, ?_, ?_⟩ <;>
      rw [div_mul_eq_mul_div, eq_div_iff hD]
    · exact h1
    · exact h3
    · exact h4
    · exact h5

theorem exists_decomp_of_mem_centralizer_yT [Finite F] {x : StatedSp 2 F}
    (hx : x ∈ Subgroup.centralizer ({yT F} : Set (StatedSp 2 F))) :
    ∃ (α β : F) (B : SL(2, F)),
      mat 2 F x = (α • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) + β • yTMat F) *
        mat 2 F (leviEmbedSL F 2 B) := by
  have hXY : mat 2 F x * yTMat F = yTMat F * mat 2 F x := by
    have := congrArg (mat 2 F) (Subgroup.mem_centralizer_singleton_iff.mp hx)
    rwa [map_mul, map_mul, mat_yT] at this
  have hS := mat_transpose_mul_gram_mul x
  generalize mat 2 F x = X at hXY hS ⊢
  have r : ∀ i j, (X * yTMat F) i j = (yTMat F * X) i j := fun i j => by rw [hXY]
  have r1 := r (Sum.inl 0) (Sum.inl 0)
  have r2 := r (Sum.inl 0) (Sum.inl 1)
  have r3 := r (Sum.inl 0) (Sum.inr 0)
  have r4 := r (Sum.inl 0) (Sum.inr 1)
  have r5 := r (Sum.inl 1) (Sum.inl 0)
  have r6 := r (Sum.inl 1) (Sum.inl 1)
  have r7 := r (Sum.inl 1) (Sum.inr 0)
  have r8 := r (Sum.inl 1) (Sum.inr 1)
  simp [yTMat, wMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at r1 r2 r3 r4
  simp [yTMat, wMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at r5 r6 r7 r8
  have s : ∀ i j, (Xᵀ * gram F 2 * X) i j = gram F 2 i j := fun i j => by rw [hS]
  have s00 := s (Sum.inl 0) (Sum.inr 0)
  have s11 := s (Sum.inl 1) (Sum.inr 1)
  have s01 := s (Sum.inl 0) (Sum.inr 1)
  have s10 := s (Sum.inl 1) (Sum.inr 0)
  simp only [transpose_mul_gram_mul_apply] at s00 s11 s01 s10
  simp [Fintype.sum_sum_type, Fin.sum_univ_two, gram_apply] at s00 s11 s01 s10
  set p00 := X (.inl 0) (.inl 0) with hp00
  set p01 := X (.inl 0) (.inl 1) with hp01
  set p10 := X (.inl 1) (.inl 0) with hp10
  set p11 := X (.inl 1) (.inl 1) with hp11
  set u := X (.inl 0) (.inr 1) with hu'
  set v := X (.inl 0) (.inr 0) with hv'
  set w := X (.inl 1) (.inr 1) with hw'
  set z := X (.inl 1) (.inr 0) with hz'
  have e00 : p11 * u + p01 * w = 1 + (p00 * p11 + p01 * p10) + (u * z + v * w) := by grind
  have e11 : p10 * v + p00 * z = 1 + (p00 * p11 + p01 * p10) + (u * z + v * w) := by grind
  have e10 : p00 * w + p10 * u = 0 := by grind
  have e01 : p01 * z + p11 * v = 0 := by grind
  clear r s hXY hS
  rcases decomp_aux e00 e11 e10 e01 with ⟨hu, hv, hw, hz, hdet⟩ | ⟨hD, l, h00, h01, h10, h11⟩
  · refine ⟨1, 0, mkSL !![p00, p01; p10, p11] (by rw [det_fin_two_of]; grind), ?_⟩
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [mat_levi_apply, yTMat, wMat, Matrix.mul_apply, Matrix.one_apply] <;> grind
  · obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' (u * z + v * w)
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      exact hD (by rw [hμ, mul_zero])
    have hμ' : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ0
    refine ⟨μ * l, μ, mkSL (μ⁻¹ • !![u, v; w, z]) ?_, ?_⟩
    · rw [det_smul, det_fin_two_of, Fintype.card_fin]
      grind
    · ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
        simp [mat_levi_apply, yTMat, wMat, Matrix.mul_apply, Fintype.sum_sum_type,
          Fin.sum_univ_two, Matrix.one_apply] <;> grind

omit [CharP F 2] in
theorem commute_of_mat {g h : StatedSp 2 F} (hgh : mat 2 F g * mat 2 F h = mat 2 F h * mat 2 F g) :
    Commute g h :=
  mat_injective (by rw [map_mul, map_mul, hgh])

theorem commute_poly_levi (α β : F) (B : SL(2, F)) :
    Commute (α • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) + β • yTMat F)
      (mat 2 F (leviEmbedSL F 2 B)) := by
  have hc : Commute (yTMat F) (mat 2 F (leviEmbedSL F 2 B)) := (levi_mul_yT B).symm
  exact ((Commute.one_left _).smul_left α).add_left (hc.smul_left β)

omit [CharP F 2] in
theorem commute_poly_poly (α β α' β' : F) :
    Commute (α • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) + β • yTMat F)
      (α' • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) + β' • yTMat F) := by
  have hY : Commute (α • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) + β • yTMat F)
      (yTMat F) := ((Commute.one_left _).smul_left α).add_left ((Commute.refl _).smul_left β)
  exact ((Commute.one_right _).smul_right α').add_right (hY.smul_right β')

theorem commutator_mem_range_levi [Finite F] {x y : StatedSp 2 F}
    (hx : x ∈ Subgroup.centralizer ({yT F} : Set (StatedSp 2 F)))
    (hy : y ∈ Subgroup.centralizer ({yT F} : Set (StatedSp 2 F))) :
    x * y * x⁻¹ * y⁻¹ ∈ (leviEmbedSL F 2).range := by
  obtain ⟨α, β, B, hB⟩ := exists_decomp_of_mem_centralizer_yT hx
  obtain ⟨α', β', B', hB'⟩ := exists_decomp_of_mem_centralizer_yT hy
  set s := leviEmbedSL F 2 B with hs
  set s' := leviEmbedSL F 2 B' with hs'
  set t := x * s⁻¹ with ht
  set t' := y * s'⁻¹ with ht'
  have hmat : ∀ (u v : StatedSp 2 F) (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F),
      mat 2 F u = A * mat 2 F v → mat 2 F (u * v⁻¹) = A := by
    intro u v A h
    rw [map_mul, h, Matrix.mul_assoc, ← map_mul, mul_inv_cancel, map_one, Matrix.mul_one]
  have hmt := hmat x s _ hB
  have hmt' := hmat y s' _ hB'
  rw [← ht] at hmt
  rw [← ht'] at hmt'
  have c1 : Commute t s := commute_of_mat (by rw [hmt]; exact commute_poly_levi α β B)
  have c2 : Commute t s' := commute_of_mat (by rw [hmt]; exact commute_poly_levi α β B')
  have c3 : Commute t t' := commute_of_mat (by rw [hmt, hmt']; exact commute_poly_poly α β α' β')
  have c4 : Commute t' s := commute_of_mat (by rw [hmt']; exact commute_poly_levi α' β' B)
  have c5 : Commute t' s' := commute_of_mat (by rw [hmt']; exact commute_poly_levi α' β' B')
  have hx' : x = t * s := by rw [ht, inv_mul_cancel_right]
  have hy' : y = t' * s' := by rw [ht', inv_mul_cancel_right]
  rw [hx', hy', commutator_eq_of_commute c1 c2 c3 c4 c5]
  exact ⟨B * B' * B⁻¹ * B'⁻¹, by simp [hs, hs']⟩

theorem inSubgroup_perfectResidual_centralizer_yT_eq [Finite F] (hF : 4 ≤ Nat.card F) :
    inSubgroup perfectResidual (Subgroup.centralizer ({yT F} : Set (StatedSp 2 F))) =
      (leviEmbedSL F 2).range := by
  have : Group.IsPerfect SL(2, F) := by
    classical
    apply CFSG.LinearGroups.special_linear_dimension_two_perfect
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF)
    exact ⟨s, hs⟩
  have hperf : Group.IsPerfect (leviEmbedSL F 2).range :=
    Group.IsPerfect.ofSurjective (f := (leviEmbedSL F 2).rangeRestrict)
      (leviEmbedSL F 2).rangeRestrict_surjective
  exact Sec21.Item228Census3Proof.inSubgroup_perfectResidual_eq_of_commutator
    range_levi_le_centralizer (Subgroup.isPerfect_iff.mp hperf)
    (fun x hx y hy => commutator_mem_range_levi hx hy)

theorem nonempty_perfectResidual_centralizer_conj_yT [Finite F] (hF : 4 ≤ Nat.card F)
    (g : StatedSp 2 F) :
    Nonempty (inSubgroup perfectResidual (Subgroup.centralizer
      ({g * yT F * g⁻¹} : Set (StatedSp 2 F))) ≃* SL(2, F)) := by
  have e1 := Sec21.Item228Census3Proof.perfectResidualCentralizerEquiv (MulAut.conj g) (yT F)
  rw [MulAut.conj_apply] at e1
  exact ⟨e1.symm.trans
    ((MulEquiv.subgroupCongr (inSubgroup_perfectResidual_centralizer_yT_eq hF)).trans
      (MonoidHom.ofInjective (leviEmbedSL_injective (K := F) (n := 2))).symm)⟩

end Centralizer

end CFSG.RankThree.PartTwo.Sec8.Item84KFacts4

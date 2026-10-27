module

import CFSG.ClassicalGroups.Orthogonal.MinusLeviBlocks
import CFSG.Adapters.StatedQuasisimple
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalOrthogonalBlocks
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open Matrix
open CFSG.ComponentClassification.UnbalancingLocal.OrthogonalBlocks
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin.Twisted
open CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven

private noncomputable abbrev k328r3f_ι {F : Type} [Field F] (b c : F) :
    GL (Fin 3) F →* GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F :=
  (HypForm.tail 3 (Fin 2) (planeNorm b c)).rho

private theorem k328r3f_ι_isometry {F : Type} [Field F] (b c : F) (A : GL (Fin 3) F)
    (v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :
    StatedQuadMinus 4 F b c ((k328r3f_ι b c A : Matrix _ _ F) *ᵥ v) =
      StatedQuadMinus 4 F b c v := by
  have h := (HypForm.tail 3 (Fin 2) (planeNorm b c)).rho_isometry A v
  have hQ : ∀ w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F,
      (HypForm.tail 3 (Fin 2) (planeNorm b c)).Q w = StatedQuadMinus 4 F b c w := by
    intro w
    rw [statedQuadMinus_eq_sum_planeNorm (n := 4)]
    simp [HypForm.Q, HypForm.tail, Matrix.fromCols_mulVec, dotProduct]
    rfl
  rw [← hQ, ← hQ]
  exact h

private noncomputable abbrev k328r3f_Y {F : Type} [Field F] (b c : F) :
    Subgroup (GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :=
  (StatedSL 3 F).map (k328r3f_ι b c)

private theorem k328r3f_Y_perfect {F : Type} [Field F] (b c : F) :
    ⁅k328r3f_Y b c, k328r3f_Y b c⁆ = k328r3f_Y b c := by
  rw [← Subgroup.map_commutator,
    commutator_self_of_perfect
      (StatedAPI.isQuasisimple_statedSL_of_two_le (m := 2) (by norm_num) F).1.1]

private theorem k328r3f_Y_le {F : Type} [Field F] (b c : F) :
    k328r3f_Y b c ≤ StatedOmega (StatedQuadMinus 4 F b c) := by
  have hY : ∀ g ∈ k328r3f_Y b c, ∀ v, StatedQuadMinus 4 F b c ((g : Matrix _ _ F) *ᵥ v) =
      StatedQuadMinus 4 F b c v := by
    rintro _ ⟨A, -, rfl⟩ v
    exact k328r3f_ι_isometry b c A v
  have hle : k328r3f_Y b c ≤ Subgroup.closure
      {A : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F |
        ∀ v, StatedQuadMinus 4 F b c ((A : Matrix _ _ F) *ᵥ v) = StatedQuadMinus 4 F b c v} :=
    fun g hg => Subgroup.subset_closure (hY g hg)
  rw [← k328r3f_Y_perfect b c]
  exact Subgroup.commutator_mono hle hle

private theorem k328r3f_two_eq_zero {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4) :
    (2 : F) = 0 := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have h2 : ringChar F = 2 := by
    have hdvd : ringChar F ∣ 2 ^ 2 := by
      have : ringChar F ∣ ringChar F ^ (n : ℕ) := dvd_pow_self _ n.ne_zero
      rw [← hn, hF] at this
      simpa using this
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
  have : CharP F 2 := ringChar.of_eq h2
  exact_mod_cast CharP.cast_eq_zero F 2

private theorem k328r3f_omega_facts {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    (ω : F) (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 0 ∧ ω ≠ 1 ∧ ω ^ 2 ≠ ω ∧ ω ^ 3 = 1 := by
  have h2 := k328r3f_two_eq_zero (F := F) hF
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, by linear_combination (ω - 1) * hω⟩
  · rw [h] at hω
    exact one_ne_zero (by linear_combination hω)
  · rw [h] at hω
    exact one_ne_zero (by linear_combination hω - h2)
  · exact one_ne_zero (by linear_combination hω - h - ω * h2)

private theorem k328r3f_diag_mem_Y {F : Type} [Field F] (b c : F) (d : Fin 3 → Fˣ)
    (hd : d 0 * d 1 * d 2 = 1) : diagGL (torusEntMinus 3 F d) ∈ k328r3f_Y b c := by
  refine ⟨diagGL d, Subgroup.subset_closure ?_, rho_diagGL (planeNorm b c) d⟩
  show ((diagGL d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1
  rw [coe_diagGL, Matrix.det_diagonal, Fin.prod_univ_three]
  simpa using congrArg Units.val hd

private theorem k328r3f_z_eq {F : Type} [Field F] {ω : F} (hω0 : ω ≠ 0) (h3 : ω ^ 3 = 1)
    {z₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (hz : (z₀ : Matrix _ _ F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] (Sum.elim ![ω ^ 2, ω ^ 2, ω ^ 2] ![1, 1]))) :
    z₀ = diagGL (torusEntMinus 3 F fun _ => Units.mk0 ω hω0) := by
  have hinv : ω⁻¹ = ω ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact h3)
  apply Units.ext
  rw [hz, coe_diagGL]
  congr 1
  funext i
  rcases i with i | i | i <;> fin_cases i <;> simp [torusEntMinus, hinv]

private theorem k328r3f_t_eq {F : Type} [Field F] {ω : F} (hω0 : ω ≠ 0) (h3 : ω ^ 3 = 1)
    {t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (ht : (t₀ : Matrix _ _ F) =
      Matrix.diagonal (Sum.elim ![ω, ω ^ 2, 1] (Sum.elim ![ω ^ 2, ω, 1] ![1, 1]))) :
    t₀ = diagGL (torusEntMinus 3 F
      ![Units.mk0 ω hω0, Units.mk0 (ω ^ 2) (pow_ne_zero 2 hω0), 1]) := by
  have hinv : ω⁻¹ = ω ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact h3)
  have hinv2 : (ω ^ 2)⁻¹ = ω := inv_eq_of_mul_eq_one_left (by rw [← pow_succ']; exact h3)
  apply Units.ext
  rw [ht, coe_diagGL]
  congr 1
  funext i
  rcases i with i | i | i <;> fin_cases i <;> simp [torusEntMinus, hinv, hinv2]

private theorem k328r3f_pow_three {F : Type} [Field F] (d : Fin 3 → Fˣ) (h : ∀ i, d i ^ 3 = 1) :
    (diagGL (torusEntMinus 3 F d) : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) ^ 3 = 1 := by
  rw [← map_pow, ← map_one (diagGL (ι := Fin 3 ⊕ Fin 3 ⊕ Fin 2) (K := F))]
  congr 1
  funext j
  rcases j with i | i | i <;> simp [torusEntMinus, inv_pow, h]

private theorem k328r3f_orderOf_three {F : Type} [Field F] {ω : F} (hω1 : ω ≠ 1)
    {g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F} (h3 : g ^ 3 = 1)
    (h : (g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (Sum.inl 0) (Sum.inl 0) =
      ω) :
    orderOf g = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime h3 fun h1 => hω1 ?_
  rw [h1] at h
  simpa using h.symm

private theorem k328r3f_not_mem {F : Type} [Field F] {ω : F} (hω0 : ω ≠ 0) (hω2 : ω ^ 2 ≠ ω)
    {z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (hz : z₀ = diagGL (torusEntMinus 3 F fun _ => Units.mk0 ω hω0))
    (ht : (t₀ : Matrix _ _ F) =
      Matrix.diagonal (Sum.elim ![ω, ω ^ 2, 1] (Sum.elim ![ω ^ 2, ω, 1] ![1, 1]))) :
    t₀ ∉ Subgroup.zpowers z₀ := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have e : ∀ i : Fin 3, ((z₀ ^ k : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
      Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (Sum.inl i) (Sum.inl i) =
      ω ^ k := fun i => by
    rw [hz, ← map_zpow, coe_diagGL, Matrix.diagonal_apply_eq]
    show (((torusEntMinus 3 F fun _ => Units.mk0 ω hω0) ^ k) (Sum.inl i) : F) = ω ^ k
    rw [Pi.pow_apply, Units.val_zpow_eq_zpow_val]
    rfl
  have h0 := congrArg (fun g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F =>
    (g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (Sum.inl 0) (Sum.inl 0)) hk
  have h1 := congrArg (fun g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F =>
    (g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (Sum.inl 1) (Sum.inl 1)) hk
  simp only [e, ht] at h0 h1
  simp at h0 h1
  exact hω2 (h1.symm.trans h0)

private theorem k328r3f_Y_le_stdComp {F : Type} [Field F] (b c : F) {ω : F} (hω0 : ω ≠ 0)
    {z₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (hz : z₀ = diagGL (torusEntMinus 3 F fun _ => Units.mk0 ω hω0)) :
    k328r3f_Y b c ≤ stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀ := by
  have hzι : z₀ = k328r3f_ι b c (diagGL fun _ : Fin 3 => Units.mk0 ω hω0) :=
    hz.trans (rho_diagGL (planeNorm b c) _).symm
  have hYC : k328r3f_Y b c ≤
      StatedOmega (StatedQuadMinus 4 F b c) ⊓ Subgroup.centralizer {z₀} := by
    refine le_inf (k328r3f_Y_le b c) ?_
    rintro _ ⟨A, -, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hzι, ← map_mul, ← map_mul]
    congr 1
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_diagGL]
    show (A : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal (fun _ => ω) =
      Matrix.diagonal (fun _ => ω) * (A : Matrix (Fin 3) (Fin 3) F)
    rw [← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
  have h := Subgroup.commutator_mono hYC hYC
  rwa [k328r3f_Y_perfect] at h

theorem row3_facts (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 4) (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : (z₀ : Matrix _ _ F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] (Sum.elim ![ω ^ 2, ω ^ 2, ω ^ 2] ![1, 1])))
    (ht : (t₀ : Matrix _ _ F) =
      Matrix.diagonal (Sum.elim ![ω, ω ^ 2, 1] (Sum.elim ![ω ^ 2, ω, 1] ![1, 1]))) :
    FactsLeaf (StatedOmega (StatedQuadMinus 4 F b c)) z₀ t₀ := by
  have _ := hbc
  obtain ⟨hω0, hω1, hω2, hω3⟩ := k328r3f_omega_facts hF ω hω
  have hzE := k328r3f_z_eq hω0 hω3 hz
  have htE := k328r3f_t_eq hω0 hω3 ht
  have hzY : z₀ ∈ k328r3f_Y b c := by
    rw [hzE]
    exact k328r3f_diag_mem_Y b c _ (Units.ext (by simpa [pow_succ] using hω3))
  have htY : t₀ ∈ k328r3f_Y b c := by
    rw [htE]
    exact k328r3f_diag_mem_Y b c _ (Units.ext (by simp; linear_combination hω3))
  have hYstd := k328r3f_Y_le_stdComp b c hω0 hzE
  have hz3 : z₀ ^ 3 = 1 := by
    rw [hzE]
    exact k328r3f_pow_three _ fun i => Units.ext (by simpa using hω3)
  have ht3 : t₀ ^ 3 = 1 := by
    rw [htE]
    refine k328r3f_pow_three _ fun i => Units.ext ?_
    fin_cases i
    · simpa using hω3
    · simp
      linear_combination (ω ^ 3 + 1) * hω3
    · simp
  refine ⟨k328r3f_Y_le b c hzY, hYstd hzY, hYstd htY, k328r3f_orderOf_three hω1 hz3 (by simp [hz]),
    k328r3f_orderOf_three hω1 ht3 (by simp [ht]), ?_, k328r3f_not_mem hω0 hω2 hzE ht⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hz, ht, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

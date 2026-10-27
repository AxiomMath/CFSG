module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGStep
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoFlagBase
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoCard
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSmall
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeModelII

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition

private def rckRPb5_form {F : Type} [Field F] (σ : F →+* F) {n : ℕ}
    (x y : Fin n → F) : F :=
  Matrix.vecMul (fun i => σ (x i)) (Unitary.antidiag n) ⬝ᵥ y

private lemma rckRPb5_form_apply {F : Type} [Field F] (σ : F →+* F) {n : ℕ}
    (x y : Fin n → F) :
    rckRPb5_form σ x y = ∑ i, σ (x i) * y (Fin.rev i) := by
  rw [rckRPb5_form, ← Matrix.dotProduct_mulVec]
  simp [dotProduct, GGOppRadSpU.antidiag_mulVec_apply]

private lemma rckRPb5_form_add_right {F : Type} [Field F] (σ : F →+* F) {n : ℕ}
    (x y y' : Fin n → F) :
    rckRPb5_form σ x (y + y') = rckRPb5_form σ x y + rckRPb5_form σ x y' := by
  simp only [rckRPb5_form_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma rckRPb5_form_smul_right {F : Type} [Field F] (σ : F →+* F) {n : ℕ}
    (c : F) (x y : Fin n → F) :
    rckRPb5_form σ x (c • y) = c * rckRPb5_form σ x y := by
  simp only [rckRPb5_form_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private lemma rckRPb5_form_linear_right {F : Type} [Field F] (σ : F →+* F) {n : ℕ}
    (a b : F) (x y z : Fin n → F) :
    rckRPb5_form σ x (a • y + b • z) =
      a * rckRPb5_form σ x y + b * rckRPb5_form σ x z := by
  rw [rckRPb5_form_add_right, rckRPb5_form_smul_right, rckRPb5_form_smul_right]

private lemma rckRPb5_form_swap {F : Type} [Field F] (σ : F ≃+* F)
    (hσ : ∀ c, σ (σ c) = c) {n : ℕ} (x y : Fin n → F) :
    rckRPb5_form σ.toRingHom y x = σ (rckRPb5_form σ.toRingHom x y) := by
  rw [rckRPb5_form_apply, rckRPb5_form_apply]
  exact GGOppRadSpU.sum_σ_mul_rev_symm σ hσ x y

private lemma rckRPb5_linearIndependent_of_pairings {F : Type} [Field F]
    (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {x y x' y' : Fin n → F}
    (hxy' : rckRPb5_form σ.toRingHom x y' = 1)
    (hyx' : rckRPb5_form σ.toRingHom y x' = 1)
    (hxx' : rckRPb5_form σ.toRingHom x x' = 0)
    (hyy' : rckRPb5_form σ.toRingHom y y' = 0) :
    LinearIndependent F ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro a b hz
  have h1 : rckRPb5_form σ.toRingHom y' (a • x + b • y) = 0 := by
    rw [hz]
    simp [rckRPb5_form]
  rw [rckRPb5_form_linear_right] at h1
  have hy'x : rckRPb5_form σ.toRingHom y' x = 1 := by
    rw [rckRPb5_form_swap σ hσ, hxy', map_one]
  have hy'y : rckRPb5_form σ.toRingHom y' y = 0 := by
    rw [rckRPb5_form_swap σ hσ, hyy', map_zero]
  rw [hy'x, hy'y, mul_one, mul_zero, add_zero] at h1
  have h2 : rckRPb5_form σ.toRingHom x' (a • x + b • y) = 0 := by
    rw [hz]
    simp [rckRPb5_form]
  rw [rckRPb5_form_linear_right] at h2
  have hx'x : rckRPb5_form σ.toRingHom x' x = 0 := by
    rw [rckRPb5_form_swap σ hσ, hxx', map_zero]
  have hx'y : rckRPb5_form σ.toRingHom x' y = 1 := by
    rw [rckRPb5_form_swap σ hσ, hyx', map_one]
  rw [hx'x, hx'y, mul_zero, mul_one, zero_add] at h2
  exact ⟨h1, h2⟩

private noncomputable abbrev rckRPb5_F (g : ℕ) : Type := GaloisField 2 (2 * (g + 1))

private noncomputable abbrev rckRPb5_σ (g : ℕ) : rckRPb5_F g ≃+* rckRPb5_F g :=
  CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)

private lemma rckRPb5_σ_involutive (g : ℕ) :
    ∀ c, rckRPb5_σ g (rckRPb5_σ g c) = c := by
  have hFcard : Nat.card (rckRPb5_F g) = (2 ^ (g + 1)) ^ 2 := by
    change Nat.card (GaloisField 2 (2 * (g + 1))) = (2 ^ (g + 1)) ^ 2
    rw [GaloisField.card 2 (2 * (g + 1)) (by omega), ← pow_mul, mul_comm]
  exact CFSG.LieType.BorelTits.unitaryInvolution_involutive hFcard

private lemma rckRPb5_glGeoFlag_of_rootGroup_eq_unitPairGroup
    {F : Type} [Field F] (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c) {n : ℕ}
    {R : Subgroup (GL (Fin n) F)} {v w v₂ w₂ : Fin n → F}
    (hR : R = unitPairGroup σ.toRingHom (Unitary.antidiag n) v w)
    (h12 : rckRPb5_form σ.toRingHom v w₂ = 1)
    (h21 : rckRPb5_form σ.toRingHom w v₂ = 1)
    (hvv : rckRPb5_form σ.toRingHom v v = 0)
    (hww : rckRPb5_form σ.toRingHom w w = 0)
    (hvw : rckRPb5_form σ.toRingHom v w = 0)
    (hvv₂ : rckRPb5_form σ.toRingHom v v₂ = 0)
    (hww₂ : rckRPb5_form σ.toRingHom w w₂ = 0) :
    GLGeoFlag none R := by
  rw [hR]
  have hG : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) F).det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  have hli : LinearIndependent F ![v, w] :=
    rckRPb5_linearIndependent_of_pairings σ hσ h12 h21 hvv₂ hww₂
  have hwv : rckRPb5_form σ.toRingHom w v = 0 := by
    rw [rckRPb5_form_swap σ hσ]
    rw [show rckRPb5_form σ.toRingHom v w = 0 from hvw]
    rw [map_zero]
  exact glGeoFlag_unitPairGroup σ.toRingHom hG hli hvv hww hvw hwv

private lemma rckRPb5_normalized_PSL
    {G : Type} [Group G] {k g : ℕ}
    (ι : (ggU .PSL (k + 1) (2 * (g + 1))).K →* G)
    (hq : CFSG.Assembly.IsQuasisimple ↥ι.range) :
    RCKNormalizedModel .PSL (k + 1) (2 * (g + 1)) := by
  refine ⟨by simp [GGPosTag], ?_⟩
  exact rckRP_admissible_PSL_of_quasisimple_range (k := k) (f := 2 * (g + 1))
    (by omega) ι hq

theorem rckRP_flaggedModel_PSU_dualPair
    (n g : ℕ) (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hSU : ∀ s ∈ S, Unitary.conjTr
    (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
    (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * Unitary.antidiag n *
      (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hpair : formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e ≠ e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e < 2)
    {J' : Subgroup
      ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype)
      S (e + formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e),
      glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S
        (e + formAdj
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag n) e)⁆) :
    RCKRPFlaggedModel
      (Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype
      none J' := by
  classical
  obtain ⟨k, ι, β₀, hk, hconj, hlong, hcenter, hrange, h4n, hvec⟩ :=
    exists_blockModel_dualPair_PSU_explicitModel n g S hSU hS he hpair hdeg hJe
  obtain ⟨v₁, w₁, v₂, w₂, h12, h21, hiso_pair, hroot1, hroot2⟩ := hvec
  obtain ⟨hv1v1, hw1w1, hv2v2, hw2w2, hv1w1, hv1v2, hw1w2, hv2w2⟩ := hiso_pair
  have hq : CFSG.Assembly.IsQuasisimple ↥ι.range := by
    rw [hrange]
    exact hJe.2.2
  have hnorm : RCKNormalizedModel .PSL (k + 1) (2 * (g + 1)) :=
    rckRPb5_normalized_PSL ι hq
  have hflag₀ : GLGeoFlag none
      ((((ggU .PSL (k + 1) (2 * (g + 1))).D.rootGroup β₀).map ι).map
        (Unitary.SU (rckRPb5_σ g) n).subtype) :=
    rckRPb5_glGeoFlag_of_rootGroup_eq_unitPairGroup (rckRPb5_σ g)
      (rckRPb5_σ_involutive g) hroot1 h12 h21 hv1v1 hw1w1 hv1w1 hv1v2 hw1w2
  have hnot : ¬ ((CFSG.Open.StatedLieTag.PSL = CFSG.Open.StatedLieTag.PSp ∧ k + 1 = 2) ∨
      CFSG.Open.StatedLieTag.PSL = CFSG.Open.StatedLieTag.F4) := by simp
  have hβ₀root : β₀ ∈ (ggU .PSL (k + 1) (2 * (g + 1))).D.roots := ggLongRoot_mem_roots hlong
  refine ⟨.PSL, k + 1, 2 * (g + 1), ι, hnorm, hrange, hcenter, ?_⟩
  exact rckRP_rootFlags_of_long (Unitary.SU (rckRPb5_σ g) n).subtype
    (fun _ b hb => absurd hb (by simp [Option.mem_def])) hnorm hnot ι
    hβ₀root hlong hflag₀

theorem rckRP_modelBig_PSU_dualPair
    (n g : ℕ) (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hSU : ∀ s ∈ S, Unitary.conjTr
    (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
    (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * Unitary.antidiag n *
      (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hpair : formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e ≠ e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e < 2)
    {J' : Subgroup
      ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype)
      S (e + formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e),
      glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S
        (e + formAdj
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag n) e)⁆) :
    RCKRPModelBig J' := by
  classical
  obtain ⟨k, ι, _, _, _, _, hcenter, hrange, _, _⟩ :=
    exists_blockModel_dualPair_PSU_explicitModel n g S hSU hS he hpair hdeg hJe
  have hq : CFSG.Assembly.IsQuasisimple ↥ι.range := by
    rw [hrange]
    exact hJe.2.2
  exact rckRP_modelBig_of_PSL (by omega) ι (rckRPb5_normalized_PSL ι hq) hrange hcenter

end CFSG.StandardType.RCKRP

module

public import CFSG.RankThree.PartOne.D4RC.Gram6
import CFSG.RankThree.PartOne.KLCE.A2Model
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.ClassicalGroups.Unitary.Transitivity
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
import CFSG.RankThree.PartOne.KD4T.Certs
import CFSG.RankThree.PartOne.KE.StabGeneral
import CFSG.RankThree.PartOne.KLCE.Descent

public noncomputable section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4 CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ7
  CFSG.SeitzReduction CFSG.Timmesfeld.ARS
open CFSG.RankThree.Classical2 (fixSubgroup unitarySet)

open scoped Matrix MatrixGroups Pointwise

open scoped CFSG.ConvolutionPoints

set_option linter.unusedSectionVars false

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section Lin

variable {L : Type} [Field L]

@[expose] def rsLieₗ : Matrix (Fin 3) (Fin 3) L →ₗ[L] RootModule Tag.D4 L where
  toFun := rsLie
  map_add' N N' := by
    simp only [rsLie, Matrix.add_apply, add_smul]
    abel
  map_smul' c N := by
    simp only [rsLie, Matrix.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add]

end Lin

abbrev rguU (R : Type) [Semiring R] : Fin 3 → R := Pi.single 0 1 + Pi.single 1 1

section Transitive

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem rgu_exists_unitary {f : ℕ} (hf : 1 ≤ f) {w : Fin 3 → L} (hw0 : w ≠ 0)
    (hwq : ∀ a, w a ^ (2 ^ f) ^ 2 = w a) (hiso : ∑ a, w a ^ 2 ^ f * w a = 0) :
    ∃ Y : GL (Fin 3) L, Y ∈ unitarySet (2 ^ f) 3 ∧
      (Y : Matrix (Fin 3) (Fin 3) L) *ᵥ rguU L = w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K₂, _, _, _, ι, hcard, hι⟩ :=
    CFSG.RankThree.PartOne.KLCE.exists_subfield_card (L := L) (n := 2 * f) (by omega)
  have hexp : (2 ^ f) ^ 2 = 2 ^ (2 * f) := by rw [← pow_mul, mul_comm]
  have hcard' : Nat.card K₂ = (2 ^ f) ^ 2 := by rw [hcard, hexp]
  have : Fintype K₂ := Fintype.ofFinite K₂
  have hpow : ∀ c : K₂, c ^ (2 ^ f) ^ 2 = c := fun c => by
    rw [← hcard', Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  set σ₂ := CFSG.LieType.BorelTits.unitaryInvolution K₂ 2 f with hσ₂def
  have hσ₂ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ₂ :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hcard'
  have hσa : ∀ c, σ₂ c = c ^ 2 ^ f := fun c =>
    CFSG.LieType.BorelTits.unitaryInvolution_apply K₂ 2 f c
  choose w₂ hw₂ using fun a => (hι (w a)).1 (by rw [← hexp]; exact hwq a)
  set u₂ : Fin 3 → K₂ := rguU K₂ with hu₂
  have hu0 : u₂ ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [hu₂] at this
  have hu : CFSG.ClassicalGroups.Unitary.herm σ₂ u₂ u₂ = 0 := by
    simp [CFSG.ClassicalGroups.Unitary.herm, hu₂, Fin.sum_univ_three, CharTwo.add_self_eq_zero]
  have hw0' : w₂ ≠ 0 := by
    intro h
    apply hw0
    funext a
    rw [← hw₂ a, h, Pi.zero_apply, map_zero, Pi.zero_apply]
  have hw : CFSG.ClassicalGroups.Unitary.herm σ₂ w₂ w₂ = 0 := by
    apply ι.injective
    rw [map_zero, CFSG.ClassicalGroups.Unitary.herm, map_sum]
    simp only [map_mul, hσa, map_pow, hw₂]
    exact hiso
  obtain ⟨t, -, ht⟩ :=
    CFSG.ClassicalGroups.Unitary.exists_mem_T_smul_eq_of_iso hσ₂ le_rfl hu0 hu hw0' hw
  obtain ⟨hdet, hct⟩ := t.2
  refine ⟨Matrix.GeneralLinearGroup.map ι (t : GL (Fin 3) K₂), ⟨fun a b => ?_, ?_, ?_⟩, ?_⟩
  · change ι _ ^ (2 ^ f) ^ 2 = ι _
    rw [← map_pow, hpow]
  · change (((t : GL (Fin 3) K₂) : Matrix (Fin 3) (Fin 3) K₂).map ι).det = 1
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
  · change ((((t : GL (Fin 3) K₂) : Matrix (Fin 3) (Fin 3) K₂).map ι).map (· ^ 2 ^ f))ᵀ *
      ((t : GL (Fin 3) K₂) : Matrix (Fin 3) (Fin 3) K₂).map ι = 1
    have e1 : ((((t : GL (Fin 3) K₂) : Matrix (Fin 3) (Fin 3) K₂).map ι).map (· ^ 2 ^ f))ᵀ =
        (CFSG.LieType.Universal.Unitary.conjTr σ₂
          ((t : GL (Fin 3) K₂) : Matrix (Fin 3) (Fin 3) K₂)).map ι := by
      ext a b
      simp [CFSG.LieType.Universal.Unitary.conjTr, hσa]
    rw [e1, ← Matrix.map_mul, hct, Matrix.map_one _ (map_zero ι) (map_one ι)]
  · funext a
    have h1 := RingHom.map_mulVec ι ((t : GL (Fin 3) K₂) : Matrix (Fin 3) (Fin 3) K₂) u₂ a
    have hu' : ι ∘ u₂ = rguU L := by
      funext b
      fin_cases b <;> simp [hu₂]
    have ht' : ((t : GL (Fin 3) K₂) : Matrix (Fin 3) (Fin 3) K₂) *ᵥ u₂ = w₂ :=
      (CFSG.ClassicalGroups.Unitary.smul_def σ₂ t u₂).symm.trans ht
    rw [hu', ht'] at h1
    rw [← hw₂ a, h1]
    rfl

end Transitive

section Conj

variable {L : Type} [Field L] [CharP L 2]

theorem rgu_conj_single {f : ℕ} {H X : SL(3, L)} {Y : GL (Fin 3) L}
    (hY : Y ∈ unitarySet (2 ^ f) 3)
    (hX : Matrix.SpecialLinearGroup.toGL X = Matrix.SpecialLinearGroup.toGL H * Y *
      (Matrix.SpecialLinearGroup.toGL H)⁻¹) :
    ((X * (H * Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : L)) :
      SL(3, L)) : Matrix (Fin 3) (Fin 3) L) * Matrix.single 0 1 1 *
      ((X * (H * Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : L)) :
        SL(3, L)) : Matrix (Fin 3) (Fin 3) L)⁻¹ =
      (H : Matrix (Fin 3) (Fin 3) L) * Matrix.vecMulVec ((Y : Matrix (Fin 3) (Fin 3) L) *ᵥ rguU L)
        (fun a => ((Y : Matrix (Fin 3) (Fin 3) L) *ᵥ rguU L) a ^ 2 ^ f) *
        (H : Matrix (Fin 3) (Fin 3) L)⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T : Matrix (Fin 3) (Fin 3) L := 1 + Matrix.single 1 0 1 with hTdef
  have hTm : ((Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : L) :
      SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = T := rfl
  have hTT : T * T = 1 := by
    have hss : Matrix.single (1 : Fin 3) (0 : Fin 3) (1 : L) *
        Matrix.single (1 : Fin 3) (0 : Fin 3) (1 : L) = 0 :=
      Matrix.single_mul_single_of_ne (1 : L) (1 : Fin 3) 0 1 (by decide) 1
    rw [hTdef, add_mul, one_mul, mul_add, mul_one, hss, add_zero, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  have hTinv : T⁻¹ = T := Matrix.inv_eq_right_inv hTT
  have hHinv : (H : Matrix (Fin 3) (Fin 3) L)⁻¹ * (H : Matrix (Fin 3) (Fin 3) L) = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [H.2]; exact isUnit_one)
  have hXm : (X : Matrix (Fin 3) (Fin 3) L) = (H : Matrix (Fin 3) (Fin 3) L) *
      (Y : Matrix (Fin 3) (Fin 3) L) * (H : Matrix (Fin 3) (Fin 3) L)⁻¹ := by
    have h := congrArg (fun A : GL (Fin 3) L => (A : Matrix (Fin 3) (Fin 3) L)) hX
    simp only [Units.val_mul, Matrix.coe_units_inv,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h
    exact h
  have hYinv : (Y : Matrix (Fin 3) (Fin 3) L)⁻¹ =
      ((Y : Matrix (Fin 3) (Fin 3) L).map (· ^ 2 ^ f))ᵀ := Matrix.inv_eq_left_inv hY.2.2
  have hM : ((X * (H * Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide)
      (1 : L)) : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
        (H : Matrix (Fin 3) (Fin 3) L) * (Y : Matrix (Fin 3) (Fin 3) L) * T := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hTm, hXm]
    calc (H : Matrix (Fin 3) (Fin 3) L) * (Y : Matrix (Fin 3) (Fin 3) L) *
          (H : Matrix (Fin 3) (Fin 3) L)⁻¹ * ((H : Matrix (Fin 3) (Fin 3) L) * T) =
        (H : Matrix (Fin 3) (Fin 3) L) * (Y : Matrix (Fin 3) (Fin 3) L) *
          ((H : Matrix (Fin 3) (Fin 3) L)⁻¹ * (H : Matrix (Fin 3) (Fin 3) L)) * T := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hHinv, Matrix.mul_one]
  have hkey : (Y : Matrix (Fin 3) (Fin 3) L) * (T * Matrix.single 0 1 1 * T) *
      ((Y : Matrix (Fin 3) (Fin 3) L).map (· ^ 2 ^ f))ᵀ =
        Matrix.vecMulVec ((Y : Matrix (Fin 3) (Fin 3) L) *ᵥ rguU L)
          (fun a => ((Y : Matrix (Fin 3) (Fin 3) L) *ᵥ rguU L) a ^ 2 ^ f) := by
    ext a b
    simp only [hTdef, Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, Matrix.map_apply, Pi.add_apply, Pi.single_apply]
    simp only [Fin.isValue, Fin.reduceEq, and_self, and_false, false_and, ↓reduceIte, mul_one,
      mul_zero, zero_mul, add_zero, zero_add]
    rw [add_pow_char_pow]
    ring
  rw [hM, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hTinv, hYinv, ← hkey]
  simp only [Matrix.mul_assoc]

end Conj

section Entry

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ε : ℤ}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

variable {F : RclFrame ℓ f K σ ε p L} {x : 𝒞[K, σ]} {i : Fin 4}

theorem rgu_exists_fix (D : RclAlgData F i) (hε : ε = -1) {Y : GL (Fin 3) L}
    (hY : Y ∈ unitarySet (ℓ ^ f) 3) :
    ∃ X : SL(3, L), X ∈ fixSubgroup D.Φ' ∧ Matrix.SpecialLinearGroup.toGL X =
      Matrix.SpecialLinearGroup.toGL D.H * Y * (Matrix.SpecialLinearGroup.toGL D.H)⁻¹ := by
  set Z : GL (Fin 3) L := Matrix.SpecialLinearGroup.toGL D.H * Y *
    (Matrix.SpecialLinearGroup.toGL D.H)⁻¹ with hZ
  have hdet : (Z : Matrix (Fin 3) (Fin 3) L).det = 1 := by
    rw [hZ, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, Matrix.coe_units_inv,
      Matrix.det_nonsing_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, D.H.2, hY.2.1,
      Ring.inverse_one, mul_one, one_mul]
  refine ⟨⟨Z, hdet⟩, (D.unit hε _).2 ⟨Y, hY, Units.ext rfl⟩, Units.ext rfl⟩

theorem rgu_entry (hε : ε = -1) (sp : RclSpecial F x i) (D : RclAlgData F i) {g : 𝒞[K, σ]}
    {κ : L}
    (hcol : ((F.g0⁻¹ * triEmb K σ L (sp.c * g) : ModGL d4 L) : Module.End L (RootModule d4 L))
      (Finsupp.single rgHi 1) = κ • ((D.ρ D.H' : ModGL d4 L) : Module.End L (RootModule d4 L))
        (rootVec d4 L (D.σ' 0 1)))
    (z : 𝒞[K, σ]) :
    ∃ C : Fin 3 → Fin 3 → L, ∀ Y : GL (Fin 3) L, Y ∈ unitarySet (ℓ ^ f) 3 →
      ∃ X : ↥(fixSubgroup D.Φ'),
      rgEntry ((triEmb K σ L (g⁻¹ * z * (rcaTheta sp D X : 𝒞[K, σ]) * g) : ModGL d4 L) :
        Module.End L (RootModule d4 L)) = ∑ a, ∑ b, C a b *
          (((Y : Matrix (Fin 3) (Fin 3) L) *ᵥ rguU L) a *
            ((Y : Matrix (Fin 3) (Fin 3) L) *ᵥ rguU L) b ^ ℓ ^ f) := by
  obtain rfl : ℓ = 2 := F.hℓ2
  obtain ⟨v, ε', -, hρ⟩ := rgt_rho_rootVec D
  set W : ModGL d4 L := (triEmb K σ L (sp.c * g))⁻¹ * triEmb K σ L (sp.c * z * sp.c⁻¹) * F.g0
    with hW
  set n := canonicalRep (coxeterSystem d4) L v with hn
  let Λ : Matrix (Fin 3) (Fin 3) L →ₗ[L] L :=
    (Finsupp.lapply rgLo) ∘ₗ (W : Module.End L (RootModule d4 L)) ∘ₗ
      (n : Module.End L (RootModule d4 L)) ∘ₗ rsLieₗ
  have hΛ : ∀ N, Λ N = ((W : Module.End L (RootModule d4 L))
      ((n : Module.End L (RootModule d4 L)) (rsLie N))) rgLo := fun N => rfl
  refine ⟨fun a b => κ * ε' * Λ ((D.H : Matrix (Fin 3) (Fin 3) L) * Matrix.single a b 1 *
    (D.H : Matrix (Fin 3) (Fin 3) L)⁻¹), fun Y hY => ?_⟩
  obtain ⟨X, hXF, hXY⟩ := rgu_exists_fix D hε hY
  refine ⟨⟨X, hXF⟩, ?_⟩
  set w := (Y : Matrix (Fin 3) (Fin 3) L) *ᵥ rguU L with hw
  have hsum : (D.H : Matrix (Fin 3) (Fin 3) L) *
      Matrix.vecMulVec w (fun a => w a ^ 2 ^ f) * (D.H : Matrix (Fin 3) (Fin 3) L)⁻¹ =
        ∑ a, ∑ b, (w a * w b ^ 2 ^ f) • ((D.H : Matrix (Fin 3) (Fin 3) L) *
          Matrix.single a b 1 * (D.H : Matrix (Fin 3) (Fin 3) L)⁻¹) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single (Matrix.vecMulVec w (fun a => w a ^ 2 ^ f))]
    simp only [Matrix.vecMulVec_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [show Matrix.single a b (w a * w b ^ 2 ^ f) = (w a * w b ^ 2 ^ f) • Matrix.single a b (1 : L)
      by rw [Matrix.smul_single, smul_eq_mul, mul_one], Matrix.mul_smul, Matrix.smul_mul]
  have e1 := rgt_entry_eq sp D hcol z ⟨X, hXF⟩
  rw [hρ, D.H'_unit hε] at e1
  change _ = κ * ((W : Module.End L (RootModule d4 L)) (ε' •
    (n : Module.End L (RootModule d4 L)) (rsLie (((X * (D.H *
      Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : L)) :
        SL(3, L)) : Matrix (Fin 3) (Fin 3) L) * Matrix.single 0 1 1 *
      ((X * (D.H * Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide)
        (1 : L)) : SL(3, L)) : Matrix (Fin 3) (Fin 3) L)⁻¹)))) rgLo at e1
  rw [rgu_conj_single hY hXY, hsum, map_smul, Finsupp.smul_apply, smul_eq_mul] at e1
  rw [e1]
  have h2 : ((W : Module.End L (RootModule d4 L)) ((n : Module.End L (RootModule d4 L))
      (rsLie (∑ a, ∑ b, (w a * w b ^ 2 ^ f) • ((D.H : Matrix (Fin 3) (Fin 3) L) *
        Matrix.single a b 1 * (D.H : Matrix (Fin 3) (Fin 3) L)⁻¹))))) rgLo =
      ∑ a, ∑ b, (w a * w b ^ 2 ^ f) * Λ ((D.H : Matrix (Fin 3) (Fin 3) L) *
        Matrix.single a b 1 * (D.H : Matrix (Fin 3) (Fin 3) L)⁻¹) := by
    rw [← hΛ, map_sum]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [h2]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end Entry

end CFSG.RankThree.PartOne.D4RC

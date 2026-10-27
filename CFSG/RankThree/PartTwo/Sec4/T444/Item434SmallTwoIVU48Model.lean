module

public import CFSG.RankThree.PartTwo.KFacts.KS21AutThreeU58
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven
import CFSG.LocalAnalysis.SectionRank.EvenCover.Unitary
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec21.Item22Statements
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K card_units_K)

abbrev σ4 : K ≃+* K := CFSG.LieType.BorelTits.unitaryInvolution K 2 3

abbrev SU4 : Type := ↥(SUid σ4 4)

theorem SU4_eq_stated : SUid σ4 4 = StatedSU 4 (2 ^ 3) K := SUid_eq_statedSU card_K 4

theorem SU4_eq_gramSU :
    SUid σ4 4 = gramSU hK ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  rw [SU4_eq_stated, Units.val_one]
  exact unitarySU_eq_gramSU hK 4

@[expose] def equivSU4 : projSU 4 2 3 ≃* SU4 :=
  ((CFSG.RankThree.PartTwo.Sec4.projSUEquivStatedProj 4 2 3).trans
    ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedSU_four_eq_bot (K := K)
        (2 ^ 3))).trans QuotientGroup.quotientBot)).trans
    (MulEquiv.subgroupCongr SU4_eq_stated.symm)

abbrev PU4 := primeFormP hK ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)

theorem normOneScalars_eq_bot4 :
    normOneScalars hK (gramSU hK ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) 4 = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨c, -, hc4, hg⟩
  have h63 : c ^ 63 = 1 := by rw [← card_units_K]; exact pow_card_eq_one'
  have hc1 : c = 1 := by
    have hdvd : orderOf c ∣ Nat.gcd 4 63 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc4) (orderOf_dvd_of_pow_eq_one h63)
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by simpa using hdvd))
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hg, hc1, map_one]
  rfl

@[expose] def ePU4 : PU4 ≃* SU4 :=
  ((QuotientGroup.quotientMulEquivOfEq normOneScalars_eq_bot4).trans
    QuotientGroup.quotientBot).trans (MulEquiv.subgroupCongr SU4_eq_gramSU.symm)

theorem coe_ePU4_mk (g : gramSU hK ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    ((ePU4 (g : PU4) : SU4) : GL (Fin 4) K) = g :=
  rfl

@[expose] def fieldSU4 (φ : K ≃+* K) : MulAut SU4 :=
  (MulEquiv.subgroupCongr SU4_eq_gramSU).trans
    ((primeFormFieldSU hK (isPrimeFormGram_one (n := 4)) φ).trans
      (MulEquiv.subgroupCongr SU4_eq_gramSU.symm))

theorem coe_fieldSU4 (φ : K ≃+* K) (g : SU4) :
    ((fieldSU4 φ g : SU4) : GL (Fin 4) K) = glAut φ (g : GL (Fin 4) K) :=
  rfl

theorem hn4 : 3 ≤ 4 := by norm_num

theorem hq4 : ¬(4 = 3 ∧ 2 ^ 3 = 2) := by norm_num

@[expose] def fieldFactor4 : MulAut SU4 →* (K ≃+* K) :=
  (primeFormFieldFactor hK (isPrimeFormGram_one (n := 4)) hn4 hq4).comp
    (MulAut.congr ePU4.symm).toMonoidHom

theorem exists_unitary_field4 (α : MulAut SU4) :
    ∃ A ∈ primeFormUnitary hK ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K),
      ∀ g : SU4, ((α g : SU4) : GL (Fin 4) K) =
        A * glAut (fieldFactor4 α) (g : GL (Fin 4) K) * A⁻¹ := by
  have hC := isPrimeFormGram_one (n := 4) (K := K)
  obtain ⟨-, -, -, -, huniq, hff, -, -, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization hK hC hn4 hq4
  set α' : MulAut PU4 := (MulAut.congr ePU4.symm) α with hα'
  obtain ⟨φ, ⟨A, hαA⟩, -⟩ := huniq α'
  have hφ : fieldFactor4 α = φ := by
    change primeFormFieldFactor hK hC hn4 hq4 α' = φ
    rw [hαA]
    exact hff A φ
  refine ⟨A, A.2, fun g => ?_⟩
  obtain ⟨g', hg'⟩ := QuotientGroup.mk_surjective (ePU4.symm g)
  have hgg' : (g : GL (Fin 4) K) = g' := by
    rw [← coe_ePU4_mk, hg', MulEquiv.apply_symm_apply]
  have hα : α g = ePU4 (α' (ePU4.symm g)) := by
    rw [hα', MulAut.congr_apply]
    simp
  rw [hα, ← hg', hαA, MulAut.mul_apply]
  change ((ePU4 (primeFormConjAut hK _ A (primeFormFieldAut hK hC φ (g' : PU4))) : SU4) :
    GL (Fin 4) K) = _
  rw [primeFormFieldAut_mk, primeFormConjAut_mk, coe_ePU4_mk, hgg', hφ]
  rfl

theorem det_pow_nine_of_mem4 {A : GL (Fin 4) K}
    (hA : A ∈ primeFormUnitary hK ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    GeneralLinearGroup.det A ^ 9 = 1 := by
  have h := congrArg Matrix.det (mem_primeFormUnitary.mp hA)
  rw [Units.val_one, Matrix.mul_one, det_mul, det_transpose, det_one] at h
  have hmap : ((A : Matrix (Fin 4) (Fin 4) K).map hK.bar).det =
      (A : Matrix (Fin 4) (Fin 4) K).det ^ 8 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, UnitaryFieldData.bar_apply]
    norm_num
  rw [hmap] at h
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, Units.val_one, pow_succ]
  exact h

theorem exists_SU4_conj_eq {A : GL (Fin 4) K}
    (hA : A ∈ primeFormUnitary hK ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    ∃ g₀ : SU4, ∀ x : GL (Fin 4) K,
      A * x * A⁻¹ = (g₀ : GL (Fin 4) K) * x * (g₀ : GL (Fin 4) K)⁻¹ := by
  set d := GeneralLinearGroup.det A with hd
  have hd9 := det_pow_nine_of_mem4 hA
  set c : Kˣ := (d ^ 7)⁻¹ with hc
  have hc9 : c ^ 9 = 1 := by
    rw [hc, inv_pow, ← pow_mul, mul_comm 7 9, pow_mul, hd9, one_pow, inv_one]
  set A' := GeneralLinearGroup.scalar (Fin 4) c * A with hA'
  have hcoe : ((A' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (c : K) • (A : Matrix (Fin 4) (Fin 4) K) := by
    rw [hA', Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, smul_eq_diagonal_mul]
  have hcd : c ^ 4 * d = 1 := by
    have h28 : (d ^ 7) ^ 4 = d ^ 9 * d ^ 9 * d ^ 9 * d := by
      rw [← pow_mul, ← pow_add, ← pow_add, ← pow_succ]
    rw [hc, inv_pow, h28, hd9, one_mul, one_mul, one_mul, inv_mul_cancel]
  have hA'mem : A' ∈ StatedSU 4 (2 ^ 3) K := by
    rw [mem_unitarySU_iff hK]
    constructor
    · rw [← GeneralLinearGroup.val_det_apply, hA', map_mul, GeneralLinearGroup.det_scalar,
        Fintype.card_fin, ← hd, hcd, Units.val_one]
    · have hU : ((A : Matrix (Fin 4) (Fin 4) K).map hK.bar)ᵀ * (A : Matrix (Fin 4) (Fin 4) K) =
          1 := by
        have := mem_primeFormUnitary.mp hA
        rwa [Units.val_one, Matrix.mul_one] at this
      have hbar : ((c : K) • (A : Matrix (Fin 4) (Fin 4) K)).map hK.bar =
          hK.bar (c : K) • (A : Matrix (Fin 4) (Fin 4) K).map hK.bar := by
        ext i j
        simp [map_mul]
      have hcc : hK.bar (c : K) * c = 1 := by
        rw [UnitaryFieldData.bar_apply, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_succ,
          show 2 ^ 3 + 1 = 9 from rfl, hc9, Units.val_one]
      rw [hcoe, hbar, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hU, hcc,
        one_smul]
  refine ⟨⟨A', by rw [SU4_eq_stated]; exact hA'mem⟩, fun x => ?_⟩
  have hcen : GeneralLinearGroup.scalar (Fin 4) c ∈ Subgroup.center (GL (Fin 4) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have hcomm := Subgroup.mem_center_iff.mp hcen
  change A * x * A⁻¹ = A' * x * A'⁻¹
  rw [hA', _root_.mul_inv_rev]
  calc A * x * A⁻¹ = A * x * A⁻¹ * GeneralLinearGroup.scalar (Fin 4) c *
        (GeneralLinearGroup.scalar (Fin 4) c)⁻¹ := by rw [mul_inv_cancel_right]
    _ = GeneralLinearGroup.scalar (Fin 4) c * (A * x * A⁻¹) *
        (GeneralLinearGroup.scalar (Fin 4) c)⁻¹ := by rw [hcomm (A * x * A⁻¹)]
    _ = _ := by simp only [mul_assoc]

theorem exists_conj_field4 (α : MulAut SU4) :
    ∃ g₀ : SU4, ∀ x : SU4, ((α x : SU4) : GL (Fin 4) K) =
      (g₀ : GL (Fin 4) K) * glAut (fieldFactor4 α) (x : GL (Fin 4) K) *
        (g₀ : GL (Fin 4) K)⁻¹ := by
  obtain ⟨A, hA, hα⟩ := exists_unitary_field4 α
  obtain ⟨g₀, hg₀⟩ := exists_SU4_conj_eq hA
  exact ⟨g₀, fun x => by rw [hα x, hg₀]⟩

theorem fieldFactor4_conj (g : SU4) : fieldFactor4 (MulAut.conj g) = 1 := by
  have hC := isPrimeFormGram_one (n := 4) (K := K)
  obtain ⟨-, -, -, -, -, hff, -⟩ :=
    unitary_prime_form_full_semilinear_realization hK hC hn4 hq4
  have hgm : (g : GL (Fin 4) K) ∈ gramSU hK ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [← SU4_eq_gramSU]
    exact g.2
  have hgu : (g : GL (Fin 4) K) ∈
      primeFormUnitary hK ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := hgm.1
  have key : (MulAut.congr ePU4.symm) (MulAut.conj g) =
      primeFormConjHom hK ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ⟨g, hgu⟩ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H z =>
      apply ePU4.injective
      change ePU4 (ePU4.symm ((MulAut.conj g) (ePU4 (z : PU4)))) = _
      rw [MulEquiv.apply_symm_apply, primeFormConjHom_mk]
      apply Subtype.ext
      rfl
  have h1 := hff ⟨g, hgu⟩ 1
  rw [map_one, mul_one] at h1
  change primeFormFieldFactor hK hC hn4 hq4 ((MulAut.congr ePU4.symm) (MulAut.conj g)) = 1
  rw [key]
  exact h1

theorem mem_range_conj_of_fieldFactor4_eq_one {α : MulAut SU4} (h : fieldFactor4 α = 1) :
    α ∈ (MulAut.conj : SU4 →* MulAut SU4).range := by
  obtain ⟨g₀, hg₀⟩ := exists_conj_field4 α
  refine ⟨g₀, MulEquiv.ext fun x => Subtype.ext ?_⟩
  rw [MulAut.conj_apply, hg₀ x, h]
  simp

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48

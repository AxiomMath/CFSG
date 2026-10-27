module

public import CFSG.LocalAnalysis.StandardType.KGLangTorAFields
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUUnitary
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
import CFSG.LocalAnalysis.StandardType.GGL45TGSU
import CFSG.Assembly.GL83StatedBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.FQMat

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

private theorem kgLangTorAUniAux_map_pow_frob {d n : ℕ} {F : Type} [Field F] [CharP F 2]
    (M : Matrix (Fin d) (Fin d) F) :
    M.map (· ^ 2 ^ n) = M.map ⇑(iterateFrobenius F 2 n) := by
  ext i j
  simp [Matrix.map_apply, iterateFrobenius_def]

private theorem kgLangTorAUniAux_coe_scalar_mul {d : ℕ} {F : Type} [Field F] (c : Fˣ)
    (x : GL (Fin d) F) :
    ((Matrix.GeneralLinearGroup.scalar (Fin d) c * x : GL (Fin d) F) :
      Matrix (Fin d) (Fin d) F) = (c : F) • (x : Matrix (Fin d) (Fin d) F) := by
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.smul_eq_diagonal_mul]

private theorem kgLangTorAUniAux_transpose_map_smul {d : ℕ} {F : Type} [Field F]
    (σ : F →+* F) (c : F) (M : Matrix (Fin d) (Fin d) F) :
    Matrix.transpose ((c • M).map σ) = σ c • Matrix.transpose (M.map σ) := by
  ext i j
  simp [Matrix.map_apply, map_mul]

theorem kgLangTorA_gu_scalar_mul {d n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) {B : GL (Fin d) F}
    (hB : B ∈ LargeEvenGUSet (Fin d) F (2 ^ n)) (c : Fˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin d) c * B ∈ LargeEvenGUSet (Fin d) F (2 ^ n) := by
  haveI : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hF
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨μ, hμ0, hμq, hμ⟩ := hB
  refine ⟨(c : F) ^ (2 ^ n + 1) * μ, ?_, ?_, ?_⟩
  · exact mul_ne_zero (pow_ne_zero _ c.ne_zero) hμ0
  · have hcard : (c : F) ^ ((2 ^ n) ^ 2) = (c : F) := by
      have h := FiniteField.pow_card (c : F)
      rwa [show Fintype.card F = (2 ^ n) ^ 2 by rw [← Nat.card_eq_fintype_card, hF]] at h
    rw [mul_pow, hμq, ← pow_mul]
    have hexp : (2 ^ n + 1) * 2 ^ n = (2 ^ n) ^ 2 + 2 ^ n := by ring
    rw [hexp, pow_add, hcard, ← pow_succ']
  · rw [kgLangTorAUniAux_coe_scalar_mul, kgLangTorAUniAux_map_pow_frob,
      kgLangTorAUniAux_transpose_map_smul, iterateFrobenius_def,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← kgLangTorAUniAux_map_pow_frob (B : Matrix (Fin d) (Fin d) F), hμ, smul_smul]
    congr 1
    rw [← pow_succ]

theorem kgLangTorA_gu_map {d n : ℕ} {F : Type} [Field F] (σ : F ≃+* F) {B : GL (Fin d) F}
    (hB : B ∈ LargeEvenGUSet (Fin d) F (2 ^ n)) :
    Matrix.GeneralLinearGroup.map (σ : F →+* F) B ∈ LargeEvenGUSet (Fin d) F (2 ^ n) := by
  obtain ⟨μ, hμ0, hμq, hμ⟩ := hB
  refine ⟨σ μ, ?_, ?_, ?_⟩
  · exact (map_ne_zero σ).mpr hμ0
  · rw [← map_pow, hμq]
  · have h1 : ((B : Matrix (Fin d) (Fin d) F).map σ).map (· ^ 2 ^ n) =
        ((B : Matrix (Fin d) (Fin d) F).map (· ^ 2 ^ n)).map σ := by
      ext i j
      simp [Matrix.map_apply, map_pow]
    change Matrix.transpose (((B : Matrix (Fin d) (Fin d) F).map σ).map (· ^ 2 ^ n)) *
      ((B : Matrix (Fin d) (Fin d) F).map σ) = σ μ • (1 : Matrix (Fin d) (Fin d) F)
    rw [h1, ← Matrix.transpose_map, ← Matrix.map_mul, hμ,
      Matrix.map_smul' ⇑σ μ (1 : Matrix (Fin d) (Fin d) F) (fun a b => map_mul σ a b),
      Matrix.map_one ⇑σ (map_zero σ) (map_one σ)]

theorem kgLangTorA_uni_scalar {d n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    {M : Subgroup.normalizer (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F))}
    (hM : TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n)) M = 1) :
    (M : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F := by
  exact TableBUE.mem_scalars_of_projConj_eq_one (unitaryFieldData_of_card hn hF) hF hd hdq
    (Nat.minFac_prime (n := 2 ^ n + 1) (by have := Nat.one_le_two_pow (n := n); omega))
    (Nat.minFac_dvd _) hM

theorem kgLangTorA_uni_field {d n p : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hq : ¬(d = 3 ∧ 2 ^ n = 2))
    {f₀ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))}
    (hf₀ : f₀ ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n))))
    (hf₀p : orderOf f₀ = p) :
    ∃ σ : F ≃+* F, orderOf σ = p ∧
      LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
        (fun g g' => ((g' : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
          ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map σ) f₀ := by
  have hd1 : 1 ≤ d := by omega
  let h : UnitaryFieldData 2 n F := unitaryFieldData_of_card hn hF
  obtain ⟨σ, hσc⟩ := RecipeFieldSU.congr_field_eq h hd1 hf₀
  refine ⟨σ, ?_, ?_⟩
  · have hinj : Function.Injective
        (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldHom h
          (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (K := F) (n := d))) :=
      RecipeFieldSpU.primeFormFieldHom_injective h hd hq
    have h1 := orderOf_injective
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldHom h
        (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (K := F) (n := d)))
      hinj σ
    have h2 := (MulAut.congr (InndiagSU.projEquiv h hd1)).orderOf_eq f₀
    rw [hσc] at h2
    rw [h1, hf₀p] at h2
    exact h2
  · have hf₀eq : f₀ = (MulAut.congr (InndiagSU.projEquiv h hd1)).symm
        (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldHom h
          (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (K := F) (n := d))
          σ) := by
      rw [← hσc, MulEquiv.symm_apply_apply]
    rw [hf₀eq]
    intro g g' hgg'
    rw [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
    change (InndiagSU.projEquiv h hd1).symm
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldAut h
        (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (K := F) (n := d)) σ
        (InndiagSU.projEquiv h hd1 (g : LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))))) =
      (g' : LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))
    rw [InndiagSU.projEquiv_mk,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldAut_mk,
      InndiagSU.projEquiv_symm_mk]
    congr 1
    apply Subtype.ext
    apply Units.ext
    change ((CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut σ (g : GL (Fin d) F) :
        GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = _
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut]
    exact hgg'.symm

private def kgLangTorAUniAux_smap {d n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData 2 n F) (σ : F ≃+* F)
    (g : LargeEvenSUGroup (Fin d) F (2 ^ n)) : LargeEvenSUGroup (Fin d) F (2 ^ n) :=
  ⟨Matrix.GeneralLinearGroup.map (σ : F →+* F) (g : GL (Fin d) F),
    GGL45TG.SU.map_mem_su h σ g.2⟩

private theorem kgLangTorAUniAux_smap_map {d n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData 2 n F) (σ : F ≃+* F)
    (g : LargeEvenSUGroup (Fin d) F (2 ^ n)) :
    (((kgLangTorAUniAux_smap h σ g : LargeEvenSUGroup (Fin d) F (2 ^ n)) : GL (Fin d) F) :
      Matrix (Fin d) (Fin d) F) = ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map σ :=
  rfl

private theorem kgLangTorAUniAux_eq_projConj_of_graph {d n : ℕ} {F : Type} [Field F]
    {B : GL (Fin d) F}
    (hBnorm : B ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)))
    {x : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))}
    (hx : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
      (fun g g' => (g' : GL (Fin d) F) = B * g * B⁻¹) x) :
    x = TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n)) ⟨B, hBnorm⟩ := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H g =>
    rw [TableB.projConj_mk]
    exact hx g ⟨B * (g : GL (Fin d) F) * B⁻¹,
      (Subgroup.mem_normalizer_iff.mp hBnorm g).mp g.2⟩ rfl

private theorem kgLangTorAUniAux_conj_field {d n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData 2 n F) {σ : F ≃+* F}
    {f₀ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))}
    (hf₀ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
      (fun g g' => ((g' : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map σ) f₀)
    {B : GL (Fin d) F}
    (hBnorm : B ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)))
    (hσBnorm : Matrix.GeneralLinearGroup.map (σ : F →+* F) B ∈
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F))) :
    f₀ * TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n)) ⟨B, hBnorm⟩ =
      TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n))
        ⟨Matrix.GeneralLinearGroup.map (σ : F →+* F) B, hσBnorm⟩ * f₀ := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H g =>
    change (f₀ * TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n)) ⟨B, hBnorm⟩)
        (↑g : LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))) =
      (TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n))
        ⟨Matrix.GeneralLinearGroup.map (σ : F →+* F) B, hσBnorm⟩ * f₀)
        (↑g : LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))
    have hL : (f₀ * TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n)) ⟨B, hBnorm⟩)
        (↑g : LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))) =
        ↑(kgLangTorAUniAux_smap h σ (Subgroup.normalizerMonoidHom _ ⟨B, hBnorm⟩ g) :
          LargeEvenSUGroup (Fin d) F (2 ^ n)) := by
      rw [MulAut.mul_apply, TableB.projConj_mk]
      exact hf₀ _ _ (kgLangTorAUniAux_smap_map h σ _)
    have hR : (TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n))
          ⟨Matrix.GeneralLinearGroup.map (σ : F →+* F) B, hσBnorm⟩ * f₀)
        (↑g : LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))) =
        ↑(Subgroup.normalizerMonoidHom _
            ⟨Matrix.GeneralLinearGroup.map (σ : F →+* F) B, hσBnorm⟩
            (kgLangTorAUniAux_smap h σ g) : LargeEvenSUGroup (Fin d) F (2 ^ n)) := by
      rw [MulAut.mul_apply]
      rw [show f₀ (↑g : LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))) =
          ↑(kgLangTorAUniAux_smap h σ g : LargeEvenSUGroup (Fin d) F (2 ^ n)) from
        hf₀ g (kgLangTorAUniAux_smap h σ g) (kgLangTorAUniAux_smap_map h σ g)]
      exact TableB.projConj_mk (LargeEvenSUGroup (Fin d) F (2 ^ n))
        ⟨Matrix.GeneralLinearGroup.map (σ : F →+* F) B, hσBnorm⟩ (kgLangTorAUniAux_smap h σ g)
    rw [hL, hR]
    congr 1
    apply Subtype.ext
    show Matrix.GeneralLinearGroup.map (σ : F →+* F) (B * (g : GL (Fin d) F) * B⁻¹) =
      Matrix.GeneralLinearGroup.map (σ : F →+* F) B *
        Matrix.GeneralLinearGroup.map (σ : F →+* F) (g : GL (Fin d) F) *
        (Matrix.GeneralLinearGroup.map (σ : F →+* F) B)⁻¹
    simp only [map_mul, map_inv]

theorem kgLangTorA_uni_semifixed {d n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    {σ : F ≃+* F} {f₀ x : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))}
    (hf₀ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
      (fun g g' => ((g' : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map σ) f₀)
    {B : GL (Fin d) F} (hB : B ∈ LargeEvenGUSet (Fin d) F (2 ^ n))
    (hx : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
      (fun g g' => (g' : GL (Fin d) F) = B * g * B⁻¹) x)
    (hcomm : f₀ * x = x * f₀) :
    ∃ c : Fˣ, Matrix.GeneralLinearGroup.map (σ : F →+* F) B =
      Matrix.GeneralLinearGroup.scalar (Fin d) c * B := by
  let h : UnitaryFieldData 2 n F := unitaryFieldData_of_card hn hF
  have hBnorm : B ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)) :=
    TableBUE.gu_subset_normalizer h hB
  have hσBnorm : Matrix.GeneralLinearGroup.map (σ : F →+* F) B ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)) :=
    TableBUE.gu_subset_normalizer h (kgLangTorA_gu_map σ hB)
  have hx_eq : x = TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n)) ⟨B, hBnorm⟩ :=
    kgLangTorAUniAux_eq_projConj_of_graph hBnorm hx
  have hconj := kgLangTorAUniAux_conj_field h hf₀ hBnorm hσBnorm
  have h1 : TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n))
        ⟨Matrix.GeneralLinearGroup.map (σ : F →+* F) B, hσBnorm⟩ =
      TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n)) ⟨B, hBnorm⟩ := by
    have hstep : f₀ * TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n)) ⟨B, hBnorm⟩ *
        f₀⁻¹ = TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n)) ⟨B, hBnorm⟩ := by
      rw [← hx_eq, hcomm]
      group
    rw [← hstep, hconj]
    group
  let M : Subgroup.normalizer
      (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)) :=
    ⟨Matrix.GeneralLinearGroup.map (σ : F →+* F) B, hσBnorm⟩ * ⟨B, hBnorm⟩⁻¹
  have hM : TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n)) M = 1 := by
    show TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n))
      (⟨Matrix.GeneralLinearGroup.map (σ : F →+* F) B, hσBnorm⟩ * ⟨B, hBnorm⟩⁻¹) = 1
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  obtain ⟨c, hc⟩ := kgLangTorA_uni_scalar hF hn hd hdq hM
  refine ⟨c, ?_⟩
  rw [hc]
  change Matrix.GeneralLinearGroup.map (σ : F →+* F) B =
    (Matrix.GeneralLinearGroup.map (σ : F →+* F) B * B⁻¹) * B
  group

private theorem kgLangTorAUniAux_map_pow_eq {F : Type} [Field F] [Finite F] {n p : ℕ}
    (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = (2 ^ n) ^ 2)
    {σ : F ≃+* F} (hσ : orderOf σ = p) (x : semilinearFixedSubfield σ) :
    (x : F) ^ (2 ^ (n / p)) = (x : F) ^ (2 ^ n) := by
  rw [← kgLangTorA_pow_eq_on_fixed hn hp hp2 hF hσ x]

private theorem kgLangTorAUniAux_map_pow_map_fix {d n : ℕ} {F : Type} [Field F]
    {σ : F ≃+* F} {M : Matrix (Fin d) (Fin d) F} (hM : M.map (σ : F →+* F) = M) :
    (M.map (· ^ 2 ^ n)).map (σ : F →+* F) = M.map (· ^ 2 ^ n) := by
  ext i j
  simp only [Matrix.map_apply, map_pow]
  have h : (M.map (σ : F →+* F)) i j = M i j := Matrix.ext_iff.mpr hM i j
  simp only [Matrix.map_apply] at h
  rw [h]

private theorem kgLangTorAUniAux_map_map_pow_mul {d n : ℕ} {F₀ F : Type} [Field F₀] [Field F]
    (ι : F₀ →+* F) (M : Matrix (Fin d) (Fin d) F₀) :
    (M.map (· ^ 2 ^ n)).map ι = (M.map ι).map (· ^ 2 ^ n) := by
  ext i j
  simp only [Matrix.map_apply, map_pow]

theorem kgLangTorA_uni_descend {d n p : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : F ≃+* F} (hσ : orderOf σ = p) {B : GL (Fin d) F}
    (hB : B ∈ LargeEvenGUSet (Fin d) F (2 ^ n))
    (hBσ : Matrix.GeneralLinearGroup.map (σ : F →+* F) B = B) :
    ∃ M : GL (Fin d) (semilinearFixedSubfield σ),
      M ∈ LargeEvenGUSet (Fin d) (semilinearFixedSubfield σ) (2 ^ (n / p)) ∧
      Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M = B := by
  obtain ⟨M, hM⟩ : ∃ M : GL (Fin d) (semilinearFixedSubfield σ),
      Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M = B :=
    CFSG.LocalAnalysis.GLTheoremA.FQ.exists_descend σ B hBσ
  refine ⟨M, ?_, hM⟩
  rcases isEmpty_or_nonempty (Fin d) with hempty | hne
  · exact ⟨1, one_ne_zero, one_pow _,
      Matrix.ext fun i _ => isEmptyElim i⟩
  · haveI : Nonempty (Fin d) := hne
    obtain ⟨μ, hμ0, hμq, hμ⟩ := hB
    have hBmat : (B : Matrix (Fin d) (Fin d) F).map (σ : F →+* F) =
        (B : Matrix (Fin d) (Fin d) F) := by
      have := congrArg (fun x : GL (Fin d) F => (x : Matrix (Fin d) (Fin d) F)) hBσ
      simpa using this
    have hμfix : σ μ = μ := by
      have hmap := congrArg (fun A : Matrix (Fin d) (Fin d) F => A.map (σ : F →+* F)) hμ
      rw [Matrix.map_mul, Matrix.transpose_map,
        kgLangTorAUniAux_map_pow_map_fix hBmat, hBmat,
        Matrix.map_smul' (σ : F →+* F) μ (1 : Matrix (Fin d) (Fin d) F)
          (fun a b => map_mul σ a b),
        Matrix.map_one (σ : F →+* F) (map_zero σ) (map_one σ)] at hmap
      rw [hμ] at hmap
      have h2 : Matrix.scalar (Fin d) μ = Matrix.scalar (Fin d) (σ μ) := by
        rw [Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
          ← Matrix.smul_one_eq_diagonal]
        exact hmap
      exact (Matrix.scalar_inj).mp h2.symm
    let μ₀ : semilinearFixedSubfield σ := ⟨μ, hμfix⟩
    have hμq₀ : μ₀ ^ (2 ^ (n / p)) = μ₀ := by
      apply Subtype.ext
      push_cast
      rw [← kgLangTorA_pow_eq_on_fixed hn hp hp2 hF hσ μ₀]
      simpa using hμq
    let ι : semilinearFixedSubfield σ →+* F := (semilinearFixedSubfield σ).subtype
    have hBmatM : (M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)).map ι =
        (B : Matrix (Fin d) (Fin d) F) := by
      have := congrArg (fun x : GL (Fin d) F => (x : Matrix (Fin d) (Fin d) F)) hM
      simpa [ι] using this
    have hBq : (B : Matrix (Fin d) (Fin d) F).map (· ^ 2 ^ (n / p)) =
        (B : Matrix (Fin d) (Fin d) F).map (· ^ 2 ^ n) := by
      ext i j
      simp only [Matrix.map_apply]
      have hBij : (B : Matrix (Fin d) (Fin d) F) i j =
          ((M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) i j : F) := by
        have h := Matrix.ext_iff.mpr hBmatM i j
        simpa [ι] using h.symm
      rw [hBij]
      exact kgLangTorAUniAux_map_pow_eq hn hp hp2 hF hσ _
    have hMeq : Matrix.transpose (((M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)).map
          (· ^ 2 ^ (n / p)))) * (M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) =
        μ₀ • (1 : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) := by
      apply Matrix.map_injective (semilinearFixedSubfield σ).subtype_injective
      change (Matrix.transpose (((M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)).map
          (· ^ 2 ^ (n / p)))) *
        (M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ))).map ι =
        (μ₀ • (1 : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ))).map ι
      rw [Matrix.map_mul, Matrix.transpose_map,
        kgLangTorAUniAux_map_map_pow_mul ι
          (M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)), hBmatM,
        Matrix.map_smul' (ι : semilinearFixedSubfield σ →+* F) μ₀
          (1 : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) (fun a b => map_mul ι a b),
        Matrix.map_one (ι : semilinearFixedSubfield σ →+* F) (map_zero ι) (map_one ι)]
      rw [hBq, hμ]
      rfl
    refine ⟨μ₀, ?_, hμq₀, hMeq⟩
    intro h
    apply hμ0
    have h' : (μ₀ : F) = 0 := by rw [h]; rfl
    change (μ₀ : F) = 0
    exact h'

end CFSG.StandardType

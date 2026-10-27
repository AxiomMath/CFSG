module

public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsUni
import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniSub
import CFSG.LocalAnalysis.StandardType.KGLangTorAUniLift
import CFSG.Open.StatedSUFieldChange
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.FQMat
import CFSG.Assembly.GL83StatedBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial

private theorem kgLangS1AUniTransferAux_glEquiv_eq_map
    {F₁ F₂ : Type} [Field F₁] [Field F₂] (e : F₁ ≃+* F₂) (n : ℕ)
    (A : GL (Fin n) F₁) :
    CFSG.Open.StatedSUFieldChange.glEquiv e n A =
      Matrix.GeneralLinearGroup.map (e : F₁ →+* F₂) A := by
  apply Units.ext
  ext i j
  rw [CFSG.Open.StatedSUFieldChange.glEquiv_coe, Matrix.map_apply,
    Matrix.GeneralLinearGroup.map_apply]
  rfl

private theorem kgLangS1AUniTransferAux_map_eq_glEquiv
    {F₁ F₂ : Type} [Field F₁] [Field F₂] (e : F₁ ≃+* F₂) (n : ℕ) :
    (Matrix.GeneralLinearGroup.map (e : F₁ →+* F₂) : GL (Fin n) F₁ →* GL (Fin n) F₂) =
      (CFSG.Open.StatedSUFieldChange.glEquiv e n).toMonoidHom := by
  apply MonoidHom.ext
  intro A
  exact (kgLangS1AUniTransferAux_glEquiv_eq_map e n A).symm

private theorem kgLangS1AUniTransferAux_map_normalizer
    {ι : Type} [Fintype ι] [DecidableEq ι] {F F' : Type} [Field F] [Field F']
    (e : F ≃+* F') {H : Subgroup (GL ι F)} {H' : Subgroup (GL ι F')}
    (hmap : H.map (Matrix.GeneralLinearGroup.map (e : F →+* F')) = H')
    {B : GL ι F} (hB : B ∈ Subgroup.normalizer (H : Set (GL ι F))) :
    Matrix.GeneralLinearGroup.map (e : F →+* F') B ∈
      Subgroup.normalizer (H' : Set (GL ι F')) := by
  rw [Subgroup.mem_normalizer_iff] at hB ⊢
  intro h
  constructor
  · intro hh
    rw [← hmap] at hh ⊢
    obtain ⟨k, hk, hkmap⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨B * k * B⁻¹, (hB k).mp hk, ?_⟩
    rw [Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_mul,
      Matrix.GeneralLinearGroup.map_inv, hkmap]
  · intro hh
    rw [← hmap] at hh ⊢
    obtain ⟨k, hk, hkmap⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨B⁻¹ * k * B, (hB (B⁻¹ * k * B)).mpr ?_, ?_⟩
    · rw [show B * (B⁻¹ * k * B) * B⁻¹ = k from by group]
      exact hk
    · rw [Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_mul,
        Matrix.GeneralLinearGroup.map_inv, hkmap]
      group

private theorem kgLangS1AUniTransferAux_statedProjSUEquiv_projConj
    {d m : ℕ} {F₀ E : Type} [Field F₀] [Field E] (τ : E ≃+* F₀)
    {B : GL (Fin d) E}
    (hB : B ∈ Subgroup.normalizer (CFSG.Open.StatedSU d (2 ^ m) E : Set (GL (Fin d) E)))
    (hB' : Matrix.GeneralLinearGroup.map (τ : E →+* F₀) B ∈
      Subgroup.normalizer (CFSG.Open.StatedSU d (2 ^ m) F₀ : Set (GL (Fin d) F₀))) :
    ∀ x : CFSG.Open.StatedProj (CFSG.Open.StatedSU d (2 ^ m) E),
      CFSG.Open.StatedSUFieldChange.statedProjSUEquiv τ d (2 ^ m)
          (TableB.projConj (CFSG.Open.StatedSU d (2 ^ m) E) ⟨B, hB⟩ x) =
        TableB.projConj (CFSG.Open.StatedSU d (2 ^ m) F₀)
          ⟨Matrix.GeneralLinearGroup.map (τ : E →+* F₀) B, hB'⟩
          (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv τ d (2 ^ m) x) := by
  intro x
  induction x using QuotientGroup.induction_on with
  | H y =>
    have step1 : CFSG.Open.StatedSUFieldChange.statedProjSUEquiv τ d (2 ^ m)
          (TableB.projConj (CFSG.Open.StatedSU d (2 ^ m) E) ⟨B, hB⟩
            (QuotientGroup.mk y)) =
        CFSG.Open.StatedSUFieldChange.statedProjSUEquiv τ d (2 ^ m)
          (QuotientGroup.mk (((CFSG.Open.StatedSU d (2 ^ m) E).normalizerMonoidHom
            ⟨B, hB⟩) y)) := by
      rw [TableB.projConj_mk]
    have step2 : CFSG.Open.StatedSUFieldChange.statedProjSUEquiv τ d (2 ^ m)
          (QuotientGroup.mk (((CFSG.Open.StatedSU d (2 ^ m) E).normalizerMonoidHom
            ⟨B, hB⟩) y)) =
        QuotientGroup.mk (CFSG.Open.StatedSUFieldChange.statedSUEquiv τ d (2 ^ m)
          (((CFSG.Open.StatedSU d (2 ^ m) E).normalizerMonoidHom ⟨B, hB⟩) y)) :=
      QuotientGroup.congr_mk _ _ _ _ _
    have step3 : (QuotientGroup.mk (CFSG.Open.StatedSUFieldChange.statedSUEquiv τ d (2 ^ m)
          (((CFSG.Open.StatedSU d (2 ^ m) E).normalizerMonoidHom ⟨B, hB⟩) y)) :
          CFSG.Open.StatedProj (CFSG.Open.StatedSU d (2 ^ m) F₀)) =
        (QuotientGroup.mk (((CFSG.Open.StatedSU d (2 ^ m) F₀).normalizerMonoidHom
          ⟨Matrix.GeneralLinearGroup.map (τ : E →+* F₀) B, hB'⟩)
          (CFSG.Open.StatedSUFieldChange.statedSUEquiv τ d (2 ^ m) y)) :
          CFSG.Open.StatedProj (CFSG.Open.StatedSU d (2 ^ m) F₀)) := by
      congr 1
      apply Subtype.ext
      show (CFSG.Open.StatedSUFieldChange.glEquiv τ d)
          (B * (y : GL (Fin d) E) * B⁻¹) =
        Matrix.GeneralLinearGroup.map (τ : E →+* F₀) B *
          (CFSG.Open.StatedSUFieldChange.glEquiv τ d) (y : GL (Fin d) E) *
          (Matrix.GeneralLinearGroup.map (τ : E →+* F₀) B)⁻¹
      rw [kgLangS1AUniTransferAux_glEquiv_eq_map,
        kgLangS1AUniTransferAux_glEquiv_eq_map]
      rw [Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_mul,
        Matrix.GeneralLinearGroup.map_inv]
    have step4 : (QuotientGroup.mk (((CFSG.Open.StatedSU d (2 ^ m) F₀).normalizerMonoidHom
          ⟨Matrix.GeneralLinearGroup.map (τ : E →+* F₀) B, hB'⟩)
          (CFSG.Open.StatedSUFieldChange.statedSUEquiv τ d (2 ^ m) y)) :
          CFSG.Open.StatedProj (CFSG.Open.StatedSU d (2 ^ m) F₀)) =
        TableB.projConj (CFSG.Open.StatedSU d (2 ^ m) F₀)
          ⟨Matrix.GeneralLinearGroup.map (τ : E →+* F₀) B, hB'⟩
          ((QuotientGroup.mk (CFSG.Open.StatedSUFieldChange.statedSUEquiv τ d (2 ^ m) y)) :
            CFSG.Open.StatedProj (CFSG.Open.StatedSU d (2 ^ m) F₀)) := by
      rw [TableB.projConj_mk]
    have step5 : TableB.projConj (CFSG.Open.StatedSU d (2 ^ m) F₀)
          ⟨Matrix.GeneralLinearGroup.map (τ : E →+* F₀) B, hB'⟩
          ((QuotientGroup.mk (CFSG.Open.StatedSUFieldChange.statedSUEquiv τ d (2 ^ m) y)) :
            CFSG.Open.StatedProj (CFSG.Open.StatedSU d (2 ^ m) F₀)) =
        TableB.projConj (CFSG.Open.StatedSU d (2 ^ m) F₀)
          ⟨Matrix.GeneralLinearGroup.map (τ : E →+* F₀) B, hB'⟩
          (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv τ d (2 ^ m)
            (QuotientGroup.mk y)) := by
      congr 1
    exact step1.trans (step2.trans (step3.trans (step4.trans step5)))

private theorem kgLangS1AUniTransferAux_field_mul_projConj
    {d m : ℕ} {F : Type} [Field F] {σ : F ≃+* F}
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ m)))}
    (hf : CFSG.LocalAnalysis.GLTheoremA.T156.Uni.Induced (2 ^ m) σ f)
    (X : Subgroup.normalizer (LargeEvenSUGroup (Fin d) F (2 ^ m) : Set (GL (Fin d) F)))
    (hσX : Matrix.GeneralLinearGroup.map (σ : F →+* F) (X : GL (Fin d) F) ∈
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) F (2 ^ m) : Set (GL (Fin d) F))) :
    f * TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ m)) X =
      TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ m))
        ⟨Matrix.GeneralLinearGroup.map (σ : F →+* F) (X : GL (Fin d) F), hσX⟩ * f := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H g =>
    rw [MulAut.mul_apply, TableB.projConj_mk]
    rw [hf (((LargeEvenSUGroup (Fin d) F (2 ^ m)).normalizerMonoidHom X) g)]
    rw [MulAut.mul_apply, hf g, TableB.projConj_mk]
    congr 1
    apply Subtype.ext
    show Matrix.GeneralLinearGroup.map (σ : F →+* F)
        ((X : GL (Fin d) F) * (g : GL (Fin d) F) * (X : GL (Fin d) F)⁻¹) =
      Matrix.GeneralLinearGroup.map (σ : F →+* F) (X : GL (Fin d) F) *
        Matrix.GeneralLinearGroup.map (σ : F →+* F) (g : GL (Fin d) F) *
        (Matrix.GeneralLinearGroup.map (σ : F →+* F) (X : GL (Fin d) F))⁻¹
    rw [Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_mul,
      Matrix.GeneralLinearGroup.map_inv]

private theorem kgLangS1AUniTransferAux_projConj_mul_inv_eq
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] (H : Subgroup (GL ι K))
    (A B : Subgroup.normalizer (H : Set (GL ι K))) :
    TableB.projConj H A * TableB.projConj H B * (TableB.projConj H A)⁻¹ =
      TableB.projConj H (A * B * A⁻¹) := by
  rw [← map_inv, ← map_mul, ← map_mul]

private theorem kgLangS1AUniTransferAux_scalar_comm
    {d : ℕ} {K : Type} [Field K] (u : Kˣ) (X : GL (Fin d) K) :
    Matrix.GeneralLinearGroup.scalar (Fin d) u * X =
      X * Matrix.GeneralLinearGroup.scalar (Fin d) u := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar]
  exact Matrix.scalar_comm (u : K) (fun r' => Commute.all (u : K) r')
    (X : Matrix (Fin d) (Fin d) K)

private theorem kgLangS1AUniTransferAux_exists_scalar_of_projConj_eq
    {d m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ m) ^ 2) (hm : 1 ≤ m) (hd : 3 ≤ d)
    (hdq : ¬(d = 3 ∧ 2 ^ m = 2)) {X Y : GL (Fin d) F}
    (hX : X ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin d) F (2 ^ m) : Set (GL (Fin d) F)))
    (hY : Y ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin d) F (2 ^ m) : Set (GL (Fin d) F)))
    (h : TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ m)) ⟨X, hX⟩ =
      TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ m)) ⟨Y, hY⟩) :
    ∃ u : Fˣ, X = Matrix.GeneralLinearGroup.scalar (Fin d) u * Y := by
  have h1 : TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ m))
      (⟨Y, hY⟩⁻¹ * ⟨X, hX⟩) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have hscal := kgLangTorA_uni_scalar hF hm hd (by
    rintro h'
    exact hdq (Prod.ext_iff.mp h')) h1
  rw [largeEvenScalars_def, MonoidHom.mem_range] at hscal
  obtain ⟨u, hu⟩ := hscal
  have hcoeeq : ((⟨Y, hY⟩⁻¹ * ⟨X, hX⟩ :
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) F (2 ^ m) : Set (GL (Fin d) F))) :
      GL (Fin d) F) = Y⁻¹ * X := rfl
  have hYX : Y⁻¹ * X = Matrix.GeneralLinearGroup.scalar (Fin d) u := by
    rw [← hcoeeq, ← hu]
  refine ⟨u, ?_⟩
  calc X = Y * (Y⁻¹ * X) := by group
    _ = Y * Matrix.GeneralLinearGroup.scalar (Fin d) u := by rw [hYX]
    _ = Matrix.GeneralLinearGroup.scalar (Fin d) u * Y :=
        (kgLangS1AUniTransferAux_scalar_comm u Y).symm

private theorem kgLangS1AUniTransferAux_commute_of_scalar_mul
    {d : ℕ} {K : Type} [Field K] {X Y : GL (Fin d) K} (u v : Kˣ)
    (h : (Matrix.GeneralLinearGroup.scalar (Fin d) u * X) *
        (Matrix.GeneralLinearGroup.scalar (Fin d) v * Y) =
      (Matrix.GeneralLinearGroup.scalar (Fin d) v * Y) *
        (Matrix.GeneralLinearGroup.scalar (Fin d) u * X)) :
    X * Y = Y * X := by
  have key1 : (Matrix.GeneralLinearGroup.scalar (Fin d) u * X) *
      (Matrix.GeneralLinearGroup.scalar (Fin d) v * Y) =
      Matrix.GeneralLinearGroup.scalar (Fin d) u *
        Matrix.GeneralLinearGroup.scalar (Fin d) v * (X * Y) := by
    calc (Matrix.GeneralLinearGroup.scalar (Fin d) u * X) *
          (Matrix.GeneralLinearGroup.scalar (Fin d) v * Y)
        = Matrix.GeneralLinearGroup.scalar (Fin d) u *
            (X * Matrix.GeneralLinearGroup.scalar (Fin d) v) * Y := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin d) u *
            (Matrix.GeneralLinearGroup.scalar (Fin d) v * X) * Y := by
          rw [← kgLangS1AUniTransferAux_scalar_comm v X]
      _ = Matrix.GeneralLinearGroup.scalar (Fin d) u *
            Matrix.GeneralLinearGroup.scalar (Fin d) v * (X * Y) := by group
  have key2 : (Matrix.GeneralLinearGroup.scalar (Fin d) v * Y) *
      (Matrix.GeneralLinearGroup.scalar (Fin d) u * X) =
      Matrix.GeneralLinearGroup.scalar (Fin d) v *
        Matrix.GeneralLinearGroup.scalar (Fin d) u * (Y * X) := by
    calc (Matrix.GeneralLinearGroup.scalar (Fin d) v * Y) *
          (Matrix.GeneralLinearGroup.scalar (Fin d) u * X)
        = Matrix.GeneralLinearGroup.scalar (Fin d) v *
            (Y * Matrix.GeneralLinearGroup.scalar (Fin d) u) * X := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin d) v *
            (Matrix.GeneralLinearGroup.scalar (Fin d) u * Y) * X := by
          rw [← kgLangS1AUniTransferAux_scalar_comm u Y]
      _ = Matrix.GeneralLinearGroup.scalar (Fin d) v *
            Matrix.GeneralLinearGroup.scalar (Fin d) u * (Y * X) := by group
  have h1 : Matrix.GeneralLinearGroup.scalar (Fin d) u *
      Matrix.GeneralLinearGroup.scalar (Fin d) v * (X * Y) =
      Matrix.GeneralLinearGroup.scalar (Fin d) v *
        Matrix.GeneralLinearGroup.scalar (Fin d) u * (Y * X) := by
    rw [← key1, h, key2]
  rw [show Matrix.GeneralLinearGroup.scalar (Fin d) v *
        Matrix.GeneralLinearGroup.scalar (Fin d) u =
      Matrix.GeneralLinearGroup.scalar (Fin d) u *
        Matrix.GeneralLinearGroup.scalar (Fin d) v from by
    rw [← map_mul, mul_comm v u, map_mul]] at h1
  exact mul_left_cancel h1

theorem kgLangS1A_uni_commute_transfer {d m : ℕ} {F₀ E : Type} [Field F₀] [Finite F₀] [Field E]
    [Finite E] (hd : 3 ≤ d) (hm : 1 ≤ m) (hF₀ : Nat.card F₀ = (2 ^ m) ^ 2)
    (hE : Nat.card E = (2 ^ m) ^ 2) (hdq : ¬(d = 3 ∧ 2 ^ m = 2))
    (ψ : LargeEvenProj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m)))
    {M N : Subgroup.normalizer (LargeEvenSUGroup (Fin d) F₀ (2 ^ m) : Set (GL (Fin d) F₀))}
    {g h : Subgroup.normalizer (LargeEvenSUGroup (Fin d) E (2 ^ m) : Set (GL (Fin d) E))}
    (hM : ∀ x, ψ (TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) M x) =
      TableB.projConj (LargeEvenSUGroup (Fin d) E (2 ^ m)) g (ψ x))
    (hN : ∀ x, ψ (TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) N x) =
      TableB.projConj (LargeEvenSUGroup (Fin d) E (2 ^ m)) h (ψ x))
    (hgh : (g : GL (Fin d) E) * h = h * g) :
    (M : GL (Fin d) F₀) * N = N * M := by
  classical
  have hd0 : 0 < d := by omega
  letI := Fintype.ofFinite F₀
  letI := Fintype.ofFinite E
  have hcard : Nat.card E = Nat.card F₀ := by rw [hE, hF₀]
  have hcard' : Fintype.card E = Fintype.card F₀ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard
  let τ : E ≃+* F₀ := FiniteField.ringEquivOfCardEq hcard'
  let T : LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m)) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) :=
    CFSG.Open.StatedSUFieldChange.statedProjSUEquiv τ d (2 ^ m)
  let Φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m))) := ψ.trans T
  obtain ⟨i, hi, f, hf, hif⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GField.uni_mem_mul_field hm hF₀ hd hdq Φ
  have hu : UnitaryFieldData 2 m F₀ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GField.unitaryData_two hm hF₀
  have hS : LargeEvenGUSet (Fin d) F₀ (2 ^ m) ⊆
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) F₀ (2 ^ m) : Set (GL (Fin d) F₀)) :=
    fun B hB => TableBUE.gu_subset_normalizer hu hB
  obtain ⟨A, hAGU, hi_eq⟩ := TableB.exists_eq_projConj hS hi
  obtain ⟨σ, hσ⟩ := CFSG.LocalAnalysis.GLTheoremA.T156.Uni.exists_induced hf
  let A₀ : Subgroup.normalizer (LargeEvenSUGroup (Fin d) F₀ (2 ^ m) :
      Set (GL (Fin d) F₀)) := ⟨A, hS hAGU⟩
  have hi_eq' : i = TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) A₀ := hi_eq
  have hmapτ : (LargeEvenSUGroup (Fin d) E (2 ^ m)).map
      (Matrix.GeneralLinearGroup.map (τ : E →+* F₀)) = LargeEvenSUGroup (Fin d) F₀ (2 ^ m) := by
    rw [kgLangS1AUniTransferAux_map_eq_glEquiv τ d]
    change (CFSG.Open.StatedSU d (2 ^ m) E).map
        (CFSG.Open.StatedSUFieldChange.glEquiv τ d).toMonoidHom =
      CFSG.Open.StatedSU d (2 ^ m) F₀
    exact CFSG.Open.StatedSUFieldChange.map_statedSU τ d (2 ^ m)
  have hmapσ : (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)).map
      (Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀)) = LargeEvenSUGroup (Fin d) F₀ (2 ^ m) := by
    rw [kgLangS1AUniTransferAux_map_eq_glEquiv σ d]
    change (CFSG.Open.StatedSU d (2 ^ m) F₀).map
        (CFSG.Open.StatedSUFieldChange.glEquiv σ d).toMonoidHom =
      CFSG.Open.StatedSU d (2 ^ m) F₀
    exact CFSG.Open.StatedSUFieldChange.map_statedSU σ d (2 ^ m)
  have hσM_norm : Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (M : GL (Fin d) F₀) ∈
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) F₀ (2 ^ m) : Set (GL (Fin d) F₀)) :=
    kgLangS1AUniTransferAux_map_normalizer σ hmapσ M.2
  have hσN_norm : Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (N : GL (Fin d) F₀) ∈
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) F₀ (2 ^ m) : Set (GL (Fin d) F₀)) :=
    kgLangS1AUniTransferAux_map_normalizer σ hmapσ N.2
  have hτg_norm : Matrix.GeneralLinearGroup.map (τ : E →+* F₀) (g : GL (Fin d) E) ∈
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) F₀ (2 ^ m) : Set (GL (Fin d) F₀)) :=
    kgLangS1AUniTransferAux_map_normalizer τ hmapτ g.2
  have hτh_norm : Matrix.GeneralLinearGroup.map (τ : E →+* F₀) (h : GL (Fin d) E) ∈
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) F₀ (2 ^ m) : Set (GL (Fin d) F₀)) :=
    kgLangS1AUniTransferAux_map_normalizer τ hmapτ h.2
  let σM : Subgroup.normalizer (LargeEvenSUGroup (Fin d) F₀ (2 ^ m) :
      Set (GL (Fin d) F₀)) :=
    ⟨Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (M : GL (Fin d) F₀), hσM_norm⟩
  let σN : Subgroup.normalizer (LargeEvenSUGroup (Fin d) F₀ (2 ^ m) :
      Set (GL (Fin d) F₀)) :=
    ⟨Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (N : GL (Fin d) F₀), hσN_norm⟩
  let τg : GL (Fin d) F₀ := Matrix.GeneralLinearGroup.map (τ : E →+* F₀) (g : GL (Fin d) E)
  let τh : GL (Fin d) F₀ := Matrix.GeneralLinearGroup.map (τ : E →+* F₀) (h : GL (Fin d) E)
  let Yn : Subgroup.normalizer (LargeEvenSUGroup (Fin d) F₀ (2 ^ m) :
      Set (GL (Fin d) F₀)) := A₀ * σM * A₀⁻¹
  let Yn' : Subgroup.normalizer (LargeEvenSUGroup (Fin d) F₀ (2 ^ m) :
      Set (GL (Fin d) F₀)) := A₀ * σN * A₀⁻¹
  have hfMulM := kgLangS1AUniTransferAux_field_mul_projConj hσ M hσM_norm
  have hfMulN := kgLangS1AUniTransferAux_field_mul_projConj hσ N hσN_norm
  have hfconjM : f * TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) M * f⁻¹ =
      TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) σM := by
    rw [hfMulM]; group; rfl
  have hfconjN : f * TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) N * f⁻¹ =
      TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) σN := by
    rw [hfMulN]; group; rfl
  have hΦM_lhs : Φ * TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) M * Φ⁻¹ =
      TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) Yn := by
    calc Φ * TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) M * Φ⁻¹
        = (i * f) * TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) M * (i * f)⁻¹ := by
          rw [hif]
      _ = i * (f * TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) M * f⁻¹) * i⁻¹ := by
          group
      _ = i * TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) σM * i⁻¹ := by
          rw [hfconjM]
      _ = TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) (A₀ * σM * A₀⁻¹) := by
          rw [hi_eq']
          exact kgLangS1AUniTransferAux_projConj_mul_inv_eq _ A₀ σM
      _ = TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) Yn := rfl
  have hΦN_lhs : Φ * TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) N * Φ⁻¹ =
      TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) Yn' := by
    calc Φ * TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) N * Φ⁻¹
        = (i * f) * TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) N * (i * f)⁻¹ := by
          rw [hif]
      _ = i * (f * TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) N * f⁻¹) * i⁻¹ := by
          group
      _ = i * TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) σN * i⁻¹ := by
          rw [hfconjN]
      _ = TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) (A₀ * σN * A₀⁻¹) := by
          rw [hi_eq']
          exact kgLangS1AUniTransferAux_projConj_mul_inv_eq _ A₀ σN
      _ = TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) Yn' := rfl
  have hTg : ∀ x, T (TableB.projConj (LargeEvenSUGroup (Fin d) E (2 ^ m)) g x) =
      TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) ⟨τg, hτg_norm⟩ (T x) :=
    kgLangS1AUniTransferAux_statedProjSUEquiv_projConj τ g.2 hτg_norm
  have hTh : ∀ x, T (TableB.projConj (LargeEvenSUGroup (Fin d) E (2 ^ m)) h x) =
      TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) ⟨τh, hτh_norm⟩ (T x) :=
    kgLangS1AUniTransferAux_statedProjSUEquiv_projConj τ h.2 hτh_norm
  have hΦM_rhs : Φ * TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) M * Φ⁻¹ =
      TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) ⟨τg, hτg_norm⟩ := by
    ext x
    rw [MulAut.mul_apply, MulAut.mul_apply]
    have hΦinv : Φ⁻¹ x = ψ.symm (T.symm x) := by
      change (ψ.trans T).symm x = ψ.symm (T.symm x)
      rw [MulEquiv.symm_trans_apply]
    rw [hΦinv]
    change (ψ.trans T) (TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) M
        (ψ.symm (T.symm x))) =
      TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) ⟨τg, hτg_norm⟩ x
    rw [MulEquiv.trans_apply, hM (ψ.symm (T.symm x)), MulEquiv.apply_symm_apply,
      hTg (T.symm x), MulEquiv.apply_symm_apply]
  have hΦN_rhs : Φ * TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) N * Φ⁻¹ =
      TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) ⟨τh, hτh_norm⟩ := by
    ext x
    rw [MulAut.mul_apply, MulAut.mul_apply]
    have hΦinv : Φ⁻¹ x = ψ.symm (T.symm x) := by
      change (ψ.trans T).symm x = ψ.symm (T.symm x)
      rw [MulEquiv.symm_trans_apply]
    rw [hΦinv]
    change (ψ.trans T) (TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) N
        (ψ.symm (T.symm x))) =
      TableB.projConj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m)) ⟨τh, hτh_norm⟩ x
    rw [MulEquiv.trans_apply, hN (ψ.symm (T.symm x)), MulEquiv.apply_symm_apply,
      hTh (T.symm x), MulEquiv.apply_symm_apply]
  obtain ⟨u, hu⟩ := kgLangS1AUniTransferAux_exists_scalar_of_projConj_eq hF₀ hm hd hdq
    hτg_norm Yn.2 (by rw [← hΦM_rhs, hΦM_lhs])
  obtain ⟨w, hw⟩ := kgLangS1AUniTransferAux_exists_scalar_of_projConj_eq hF₀ hm hd hdq
    hτh_norm Yn'.2 (by rw [← hΦN_rhs, hΦN_lhs])
  have hcommmap : τg * τh = τh * τg := by
    rw [← Matrix.GeneralLinearGroup.map_mul, ← Matrix.GeneralLinearGroup.map_mul, hgh]
  have hPQ : (Yn : GL (Fin d) F₀) * (Yn' : GL (Fin d) F₀) =
      (Yn' : GL (Fin d) F₀) * (Yn : GL (Fin d) F₀) := by
    refine kgLangS1AUniTransferAux_commute_of_scalar_mul u w ?_
    rw [← hu, ← hw]
    exact hcommmap
  have hPQex : (A * Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (M : GL (Fin d) F₀) * A⁻¹) *
      (A * Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (N : GL (Fin d) F₀) * A⁻¹) =
      (A * Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (N : GL (Fin d) F₀) * A⁻¹) *
      (A * Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (M : GL (Fin d) F₀) * A⁻¹) := by
    have h := hPQ
    change (A * Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (M : GL (Fin d) F₀) * A⁻¹) *
        (A * Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (N : GL (Fin d) F₀) * A⁻¹) =
      (A * Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (N : GL (Fin d) F₀) * A⁻¹) *
        (A * Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (M : GL (Fin d) F₀) * A⁻¹) at h
    exact h
  have hPQ' : Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (M : GL (Fin d) F₀) *
      Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (N : GL (Fin d) F₀) =
      Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (N : GL (Fin d) F₀) *
      Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (M : GL (Fin d) F₀) := by
    have h := hPQex
    rw [show A * Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (M : GL (Fin d) F₀) * A⁻¹ *
          (A * Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (N : GL (Fin d) F₀) * A⁻¹) =
        A * (Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (M : GL (Fin d) F₀) *
          Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (N : GL (Fin d) F₀)) * A⁻¹ from by group,
      show A * Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (N : GL (Fin d) F₀) * A⁻¹ *
          (A * Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (M : GL (Fin d) F₀) * A⁻¹) =
        A * (Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (N : GL (Fin d) F₀) *
          Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀) (M : GL (Fin d) F₀)) * A⁻¹ from by group]
      at h
    exact mul_left_cancel (mul_right_cancel h)
  have hMNmap :
      Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀)
        ((M : GL (Fin d) F₀) * (N : GL (Fin d) F₀)) =
      Matrix.GeneralLinearGroup.map (σ : F₀ →+* F₀)
        ((N : GL (Fin d) F₀) * (M : GL (Fin d) F₀)) := by
    rw [Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_mul, hPQ']
  exact Matrix.GeneralLinearGroup.map_injective σ.injective hMNmap

end CFSG.StandardType

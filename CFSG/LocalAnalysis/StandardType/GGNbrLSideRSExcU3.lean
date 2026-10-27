module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.FrameAct
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import Certificates.Certificate13659
import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL1Alg
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentPerm
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASplitAct
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
import CFSG.HardMathSupport.Timmesfeld.CrossChar.G2LongFrame
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuNHom
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped MatrixGroups

private lemma u3main_ker_ne_top
    {τ : Tag} {L : Type} [Field L] {ψ : SL(3, L) →* ModGL τ L}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) : ψ.ker ≠ ⊤ := by
  intro h
  have h01 : (⟨0, by omega⟩ : Fin 3) ≠ ⟨1, by omega⟩ := by simp
  obtain ⟨ε, hε⟩ := hψ.transv ⟨0, by omega⟩ ⟨1, by omega⟩ h01
  have h1 : Matrix.SpecialLinearGroup.transvection h01 (1 : L) ∈ ψ.ker := by
    rw [h]
    exact Subgroup.mem_top _
  rw [MonoidHom.mem_ker, hε, mul_one,
    ← pinnedX_zero τ L (σ ⟨0, by omega⟩ ⟨1, by omega⟩)] at h1
  exact Units.ne_zero ε (pinnedX_injective τ L _ h1)

theorem ggNbrLSideRSExc_frameAct_conj_eq_smul
    {τ : Tag} {L : Type} [Field L] {ψ : SL(3, L) →* ModGL τ L}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) {y z : ModGL τ L}
    {B H : GL (Fin 3) L} (hy : SLFrameAct ψ y B false) (hz : SLFrameAct ψ z H false)
    (X X' : SL(3, L))
    (h : ∀ g ∈ ψ.range, (y * (z * ψ X * z⁻¹) * y⁻¹) * g * (y * (z * ψ X * z⁻¹) * y⁻¹)⁻¹ =
      (z * ψ X' * z⁻¹) * g * (z * ψ X' * z⁻¹)⁻¹) :
    ∃ ζ : L, ζ ^ 3 = 1 ∧
      ((H⁻¹ * B * H : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * (X : Matrix (Fin 3) (Fin 3) L) *
        (((H⁻¹ * B * H)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
          ζ • (X' : Matrix (Fin 3) (Fin 3) L) := by
  classical
  let sC : GL (Fin 3) L →* MulAut SL(3, L) :=
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 L
  let U₁ : SL(3, L) := sC (B * H) X
  let U₂ : SL(3, L) := sC H X'
  have hU₁ : U₁ = sC (B * H) X := rfl
  have hU₂ : U₂ = sC H X' := rfl
  have hzX : z * ψ X * z⁻¹ = ψ (sC H X) := hz X
  have hzX' : z * ψ X' * z⁻¹ = ψ U₂ := by
    rw [hU₂]
    exact hz X'
  have hmul : sC (B * H) X = sC B (sC H X) := by
    rw [map_mul, MulAut.mul_apply]
  have hyBH : y * ψ (sC H X) * y⁻¹ = ψ U₁ := by
    have hh := hy (sC H X)
    rw [hU₁, hmul]
    exact hh
  have hconj1 : y * (z * ψ X * z⁻¹) * y⁻¹ = ψ U₁ := by
    rw [hzX]
    exact hyBH
  have hB : ∀ Y : SL(3, L), ψ (U₂⁻¹ * U₁) * ψ Y = ψ Y * ψ (U₂⁻¹ * U₁) := by
    intro Y
    have key := h (ψ Y) (MonoidHom.mem_range.mpr ⟨Y, rfl⟩)
    rw [hconj1, hzX'] at key
    calc ψ (U₂⁻¹ * U₁) * ψ Y = (ψ U₂)⁻¹ * ψ U₁ * ψ Y := by rw [map_mul, map_inv]
      _ = (ψ U₂)⁻¹ * (ψ U₁ * ψ Y * (ψ U₁)⁻¹) * ψ U₁ := by group
      _ = (ψ U₂)⁻¹ * (ψ U₂ * ψ Y * (ψ U₂)⁻¹) * ψ U₁ := by rw [key]
      _ = ψ Y * ((ψ U₂)⁻¹ * ψ U₁) := by group
      _ = ψ Y * ψ (U₂⁻¹ * U₁) := by rw [map_mul, map_inv]
  have hψker : ψ.ker ≠ ⊤ := u3main_ker_ne_top hψ
  have hcent : U₂⁻¹ * U₁ ∈ Subgroup.center SL(3, L) :=
    mem_center_SL_of_commute (ν := 3) (by norm_num) ψ hψker hB
  obtain ⟨ζ, hζ3pow, hζscalar⟩ := (Matrix.SpecialLinearGroup.mem_center_iff).mp hcent
  have hζ3 : ζ ^ 3 = 1 := by simpa using hζ3pow
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at hζ3
    exact one_ne_zero hζ3.symm
  let S : SL(3, L) := ⟨Matrix.scalar (Fin 3) ζ, by
    rw [Matrix.scalar_apply, Matrix.det_diagonal]
    simpa using hζ3⟩
  have hSU : S = U₂⁻¹ * U₁ := Subtype.ext hζscalar
  have hU1 : U₁ = U₂ * S := by
    rw [hSU]
    group
  have hGL : Matrix.SpecialLinearGroup.toGL U₁ =
      Matrix.SpecialLinearGroup.toGL U₂ * Matrix.SpecialLinearGroup.toGL S := by
    rw [hU1, map_mul]
  rw [hU₁, hU₂,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation] at hGL
  have hSGL : Matrix.SpecialLinearGroup.toGL S =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ζ hζ0) := Units.ext rfl
  have hScomm : (H⁻¹ : GL (Fin 3) L) * Matrix.SpecialLinearGroup.toGL S * H =
      Matrix.SpecialLinearGroup.toGL S := by
    have hcomm : Matrix.SpecialLinearGroup.toGL S * H = H * Matrix.SpecialLinearGroup.toGL S := by
      rw [hSGL]
      exact Matrix.GeneralLinearGroup.scalar_commute (Units.mk0 ζ hζ0) H
    calc (H⁻¹ : GL (Fin 3) L) * Matrix.SpecialLinearGroup.toGL S * H
        = (H⁻¹ : GL (Fin 3) L) * (Matrix.SpecialLinearGroup.toGL S * H) := by group
      _ = (H⁻¹ : GL (Fin 3) L) * (H * Matrix.SpecialLinearGroup.toGL S) := by rw [hcomm]
      _ = Matrix.SpecialLinearGroup.toGL S := by group
  have hconjGL : (H⁻¹ * B * H) * Matrix.SpecialLinearGroup.toGL X * (H⁻¹ * B * H)⁻¹ =
      Matrix.SpecialLinearGroup.toGL X' * Matrix.SpecialLinearGroup.toGL S := by
    calc (H⁻¹ * B * H) * Matrix.SpecialLinearGroup.toGL X * (H⁻¹ * B * H)⁻¹
        = (H⁻¹ : GL (Fin 3) L) *
            ((B * H) * Matrix.SpecialLinearGroup.toGL X * (B * H)⁻¹) * H := by group
      _ = (H⁻¹ : GL (Fin 3) L) *
            ((H * Matrix.SpecialLinearGroup.toGL X' * H⁻¹) *
              Matrix.SpecialLinearGroup.toGL S) * H := by rw [hGL]
      _ = Matrix.SpecialLinearGroup.toGL X' * Matrix.SpecialLinearGroup.toGL S := by
        rw [show (H⁻¹ : GL (Fin 3) L) *
              ((H * Matrix.SpecialLinearGroup.toGL X' * H⁻¹) *
                Matrix.SpecialLinearGroup.toGL S) * H =
            Matrix.SpecialLinearGroup.toGL X' *
              ((H⁻¹ : GL (Fin 3) L) * Matrix.SpecialLinearGroup.toGL S * H) from by group,
          hScomm]
  refine ⟨ζ, hζ3, ?_⟩
  have hv := congrArg (fun u : GL (Fin 3) L => (u : Matrix (Fin 3) (Fin 3) L)) hconjGL
  have hSmat : (Matrix.SpecialLinearGroup.toGL S : Matrix (Fin 3) (Fin 3) L) =
      Matrix.scalar (Fin 3) ζ := rfl
  have hscalar : Matrix.scalar (Fin 3) ζ = ζ • (1 : Matrix (Fin 3) (Fin 3) L) := by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  simpa [Units.val_mul, Units.val_inv_eq_inv_val, hSmat, hscalar,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.mul_smul, Matrix.mul_one] using hv

theorem ggNbrLSideRSExc_exists_smul_map_of_conj {L : Type} [Field L] [IsAlgClosed L] {Q : ℕ}
    (hQ2 : 2 ≤ Q) (hQ3 : 3 ∣ Q - 1) (σQ : L ≃+* L) (hσ : ∀ c, σQ c = c ^ Q) (C : GL (Fin 3) L)
    (hC : ∀ X : SL(3, ↥(fixSubfield σQ)), ∃ (X' : SL(3, ↥(fixSubfield σQ))) (ζ : L), ζ ^ 3 = 1 ∧
      (C : Matrix (Fin 3) (Fin 3) L) *
          (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X : Matrix (Fin 3) (Fin 3) L) *
          ((C⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
        ζ • (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X' :
          Matrix (Fin 3) (Fin 3) L)) :
    ∃ (M : GL (Fin 3) ↥(fixSubfield σQ)) (c : L), c ≠ 0 ∧
      (C : Matrix (Fin 3) (Fin 3) L) =
        c • (M : Matrix (Fin 3) (Fin 3) ↥(fixSubfield σQ)).map (fixSubfield σQ).subtype := by
  classical
  refine CFSG.RankThree.PartTwo.Sec4.E27.exists_rational_scalar_mul (k := ↥(fixSubfield σQ))
    (Ω := L) (q := Q) hQ2 σQ.toRingHom hσ ?_ ?_ C ?_
  · intro c
    rw [Subfield.algebraMap_ofSubfield]
    exact (mem_fixSubfield (σ := σQ)).mp c.2
  · intro z hz
    exact ⟨⟨z, (mem_fixSubfield (σ := σQ)).mpr hz⟩, rfl⟩
  · intro i j hij a b
    obtain ⟨X', ζ, hζ3, hXeq⟩ :=
      hC (Matrix.SpecialLinearGroup.transvection hij (1 : ↥(fixSubfield σQ)))
    have hX0 : (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype
        (Matrix.SpecialLinearGroup.transvection hij (1 : ↥(fixSubfield σQ))) :
          Matrix (Fin 3) (Fin 3) L) = 1 + Matrix.single i j (1 : L) := by
      rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.transvection_coe]
      ext p q
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
        Matrix.single_apply]
      split_ifs <;> simp
    have hζQ : ζ ^ Q = ζ := by
      obtain ⟨m, hm⟩ := hQ3
      have hQeq : Q = 3 * m + 1 := by omega
      calc ζ ^ Q = ζ ^ (3 * m + 1) := by rw [hQeq]
        _ = ζ ^ (3 * m) * ζ := by rw [pow_succ]
        _ = (ζ ^ 3) ^ m * ζ := by rw [pow_mul]
        _ = 1 ^ m * ζ := by rw [hζ3]
        _ = ζ := by rw [one_pow, one_mul]
    have hζfix : ζ ∈ fixSubfield σQ := (mem_fixSubfield (σ := σQ)).mpr (by rw [hσ, hζQ])
    have key : ((C : Matrix (Fin 3) (Fin 3) L) * (1 + Matrix.single i j (1 : L)) *
        ((C⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) a b =
        ζ * (((X' : Matrix (Fin 3) (Fin 3) ↥(fixSubfield σQ)) a b : ↥(fixSubfield σQ)) : L) := by
      rw [← hX0, hXeq]
      simp [Matrix.smul_apply, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply]
    refine ⟨⟨ζ, hζfix⟩ * (X' : Matrix (Fin 3) (Fin 3) ↥(fixSubfield σQ)) a b, ?_⟩
    rw [Subfield.algebraMap_ofSubfield, Subfield.subtype_apply, Subfield.coe_mul, key]

private lemma u3main_rootDiagUnit_pow_eq_one_of_forall {τ : Tag} {L : Type} [Field L] {p : ℕ}
    {a : Fin τ.rank → Lˣ} (hap : ∀ i, a i ^ p = 1) : rootDiagUnit τ a ^ p = 1 := by
  have key : ∀ n : ℕ, rootDiagUnit τ a ^ n = rootDiagUnit τ (a ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
    | succ n ih => rw [pow_succ, ih, ← rootDiagUnit_mul, ← pow_succ]
  rw [key p, show a ^ p = 1 from funext fun i => by simpa using hap i, rootDiagUnit_one]

private lemma u3main_frameAct_mul {τ : Tag} {L : Type} [Field L] {ψ : SL(3, L) →* ModGL τ L}
    {g g' : ModGL τ L} {B B' : GL (Fin 3) L} {ε : Bool}
    (hg : SLFrameAct ψ g B false) (hg' : SLFrameAct ψ g' B' ε) :
    SLFrameAct ψ (g * g') (B * B') ε := by
  intro X
  unfold SLFrameAct at hg hg'
  calc (g * g') * ψ X * (g * g')⁻¹
      = g * (g' * ψ X * g'⁻¹) * g⁻¹ := by group
    _ = g * ψ (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 L B'
          (if ε then CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 L X
            else X)) * g⁻¹ := by rw [hg' X]
    _ = ψ (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 L B
          (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 L B'
            (if ε then CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 L X
              else X))) := hg _
    _ = ψ (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 L (B * B')
          (if ε then CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 L X
            else X)) := by rw [map_mul, MulAut.mul_apply]

private lemma u3main_ker_le_center
    {τ : Tag} {L : Type} [Field L] {ψ : SL(3, L) →* ModGL τ L}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) :
    ψ.ker ≤ Subgroup.center SL(3, L) := by
  have hQ : CFSG.IsQuasisimple SL(3, L) :=
    CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (n := 3) (K := L) (by norm_num)
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hQ ψ.ker with h | h
  · exact h
  · exact absurd h (u3main_ker_ne_top hψ)

private lemma u3main_graph_cube {τ : Tag} {L : Type} [Field L] {ψ : SL(3, L) →* ModGL τ L}
    {y : ModGL τ L} {B : GL (Fin 3) L} (hy : SLFrameAct ψ y B true) (hy3 : y ^ 3 = 1) :
    ∃ B' : GL (Fin 3) L, ∀ X : SL(3, L),
      ψ (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 L B'
        (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 L X)) = ψ X := by
  let c : GL (Fin 3) L →* MulAut SL(3, L) :=
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 L
  let δ : MulAut SL(3, L) := CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 L
  change ∃ B' : GL (Fin 3) L, ∀ X : SL(3, L), ψ (c B' (δ X)) = ψ X
  have hyc : ∀ X : SL(3, L), y * ψ X * y⁻¹ = ψ (c B (δ X)) := by
    intro X
    have h := hy X
    simpa [c, δ] using h
  have hδc : ∀ (C : GL (Fin 3) L) (X : SL(3, L)), δ (c C X) = c
      (CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 L C) (δ X) := by
    intro C X
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [CFSG.ComponentClassification.CatalogueBGraphForm.toGL_slGraphAut,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
      CFSG.ComponentClassification.CatalogueBGraphForm.toGL_slGraphAut]
    simp only [map_mul, map_inv]
  have hδδ : δ * δ = 1 := by
    have := CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_sq 3 L
    simpa [δ, pow_two] using this
  have hconj : ∀ C : GL (Fin 3) L, δ * c C * δ =
      c (CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 L C) := by
    intro C
    have h1 : δ * c C =
        c (CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 L C) * δ := by
      apply DFunLike.ext
      intro X
      rw [MulAut.mul_apply, MulAut.mul_apply]
      exact hδc C X
    rw [h1, mul_assoc, hδδ, mul_one]
  have hcube : (c B * δ) ^ 3 = c (B * CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut
      3 L B * B) * δ := by
    have h2 : (c B * δ) ^ 2 = c (B * CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut
        3 L B) := by
      calc (c B * δ) * (c B * δ) = c B * (δ * c B * δ) := by group
        _ = c B * c (CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 L B) := by
            rw [hconj B]
        _ = c (B * CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 L B) := by
            rw [map_mul]
    rw [pow_succ, h2]
    calc c (B * CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 L B) * (c B * δ)
        = c (B * CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 L B) * c B * δ := by
          group
      _ = c ((B * CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 L B) * B) * δ := by
          rw [← map_mul c (B * CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 L B) B]
  have hiter : ∀ (n : ℕ) (X : SL(3, L)),
      ψ (((c B * δ) ^ n) X) = y ^ n * ψ X * (y ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro X; simp
    | succ n ih =>
        intro X
        calc ψ (((c B * δ) ^ (n + 1)) X)
            = y * ψ (((c B * δ) ^ n) X) * y⁻¹ := by
              rw [pow_succ', MulAut.mul_apply, MulAut.mul_apply]
              exact (hyc (((c B * δ) ^ n) X)).symm
          _ = y ^ (n + 1) * ψ X * (y ^ (n + 1))⁻¹ := by
              rw [ih]
              group
  refine ⟨B * CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 L B * B, fun X => ?_⟩
  have h1 : c (B * CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 L B * B) (δ X)
      = ((c B * δ) ^ 3) X := by
    rw [hcube, MulAut.mul_apply]
  rw [h1, hiter 3 X, hy3]
  group

private lemma u3main_frameRoots_ncard
    {τ : Tag} {L : Type} [Field L] {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ a b, a ≠ b → CFSG.LieType.Steinberg.Adjoint.iform (σ a b) (σ a b) = 2 * κ) :
    (frameRoots σ).ncard = ν * (ν - 1) := by
  have hinj : Set.InjOn (fun q : Fin ν × Fin ν => σ q.1 q.2) {q | q.1 ≠ q.2} := by
    rintro ⟨x, y⟩ hxy ⟨u, v⟩ huv h
    simp only [Set.mem_setOf_eq] at hxy huv
    obtain ⟨rfl, rfl⟩ := hψ.eq_of_eq hκ hnorm hxy huv h
    rfl
  have himg : frameRoots σ = (fun q : Fin ν × Fin ν => σ q.1 q.2) '' {q | q.1 ≠ q.2} := by
    ext r
    constructor
    · rintro ⟨x, y, hxy, rfl⟩
      exact ⟨(x, y), hxy, rfl⟩
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      exact ⟨x, y, hxy, rfl⟩
  rw [himg, hinj.ncard_image]
  have hoff : ({q : Fin ν × Fin ν | q.1 ≠ q.2} : Set (Fin ν × Fin ν)) =
      ↑(Finset.univ.offDiag : Finset (Fin ν × Fin ν)) := by
    ext q
    simp [Finset.mem_offDiag]
  rw [hoff, Set.ncard_coe_finset, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin,
    Nat.mul_sub_left_distrib, mul_one]

private lemma u3main_frame
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (h2 : (2 : L) = 0) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (ha3 : ∀ j, a j ^ 3 = 1) (i : KernelComponent (rootCharHom a))
    (hrk : compRank (componentRoots (rootCharHom a) i) = 2)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 6) :
    ∃ (ψ : SL(3, L) →* ModGL τ L) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ) (κ : ℤ),
      IsSLFrame ψ σ ∧ κ ≠ 0 ∧
      (∀ x y, x ≠ y → CFSG.LieType.Steinberg.Adjoint.iform (σ x y) (σ x y) = 2 * κ) ∧
      componentRoots (rootCharHom a) i = frameRoots σ := by
  have hpL : ((3 : ℕ) : L) ≠ 0 := by
    have h3 : ((3 : ℕ) : L) = 1 := by
      have h31 : ((3 : ℕ) : L) = 2 + 1 := by norm_num
      rw [h31, h2, zero_add]
    rw [h3]
    exact one_ne_zero
  have hTp : rootDiagUnit τ a ^ 3 = 1 := u3main_rootDiagUnit_pow_eq_one_of_forall ha3
  have h2rank : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
  have hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1) := by
    rw [hrk, hcard]
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S Nat.prime_three hpL hTp i h2rank hn
  have hνcard : ν * (ν - 1) = 6 := by
    rw [← u3main_frameRoots_ncard hψ hκ hnorm, ← hΨ, hcard]
  have hν3 : ν = 3 := by
    have hνle : ν ≤ 3 := by
      by_contra h
      push Not at h
      have h1 : 3 ≤ ν - 1 := by omega
      have h2 : 4 * 3 ≤ ν * (ν - 1) := Nat.mul_le_mul (by omega : 4 ≤ ν) h1
      omega
    omega
  obtain rfl : ν = 3 := hν3
  exact ⟨ψ, σ, κ, hψ, hκ, hnorm, hΨ⟩

private lemma u3main_mem_center_of_commutator_mem_center {H : Type*} [Group H]
    (hH : commutator H = ⊤) {x : H}
    (hx : ∀ y : H, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center H) : x ∈ Subgroup.center H := by
  let φ : H →* Subgroup.center H :=
    { toFun := fun y => ⟨x * y * x⁻¹ * y⁻¹, hx y⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun y z => by
        apply Subtype.ext
        have hb := (Subgroup.mem_center_iff.1 (hx z)) y⁻¹
        change x * (y * z) * x⁻¹ * (y * z)⁻¹ = (x * y * x⁻¹ * y⁻¹) * (x * z * x⁻¹ * z⁻¹)
        calc x * (y * z) * x⁻¹ * (y * z)⁻¹
            = x * y * x⁻¹ * ((x * z * x⁻¹ * z⁻¹) * y⁻¹) := by group
          _ = x * y * x⁻¹ * (y⁻¹ * (x * z * x⁻¹ * z⁻¹)) := by rw [← hb]
          _ = (x * y * x⁻¹ * y⁻¹) * (x * z * x⁻¹ * z⁻¹) := by group }
  have hle : commutator H ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [hH] at hle
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 : φ y = 1 := hle (Subgroup.mem_top y)
  have h2 := congrArg Subtype.val h1
  change x * y * x⁻¹ * y⁻¹ = 1 at h2
  calc y * x = (x * y * x⁻¹ * y⁻¹)⁻¹ * (x * y) := by group
    _ = x * y := by rw [h2]; simp

private lemma u3main_comap_center_of_surjective {H H' : Type*} [Group H] [Group H']
    (hH : commutator H = ⊤) (ψ : H →* H') (hψ : Function.Surjective ψ)
    (hk : ψ.ker ≤ Subgroup.center H) :
    (Subgroup.center H').comap ψ = Subgroup.center H := by
  ext x
  rw [Subgroup.mem_comap]
  constructor
  · intro hx
    refine u3main_mem_center_of_commutator_mem_center hH fun y => hk ?_
    have hc : ψ y * ψ x = ψ x * ψ y := (Subgroup.mem_center_iff.1 hx) (ψ y)
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
    group
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := hψ z
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hx) y]

private lemma u3main_exists_equiv {K G : Type*} [Field K] [Group G] (g : SL(3, K) →* G)
    (hg : Function.Surjective g) (hk : g.ker ≤ Subgroup.center SL(3, K)) :
    ∃ e : G ⧸ Subgroup.center G ≃* projectiveSL 3 K,
      ∀ X, e (QuotientGroup.mk (g X)) = proj 3 K X := by
  have hperf : commutator SL(3, K) = ⊤ :=
    Group.isPerfect_def.1
      (CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (n := 3) (K := K)
        (by norm_num))
  have hcomap : (Subgroup.center G).comap g = Subgroup.center SL(3, K) :=
    u3main_comap_center_of_surjective hperf g hg hk
  let χ : SL(3, K) →* G ⧸ Subgroup.center G :=
    (QuotientGroup.mk' (Subgroup.center G)).comp g
  have hχsurj : Function.Surjective χ := (QuotientGroup.mk'_surjective _).comp hg
  have hχker : χ.ker = Subgroup.center SL(3, K) := by
    rw [← hcomap]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact QuotientGroup.eq_one_iff (g x)
  let Q1 : SL(3, K) ⧸ Subgroup.center SL(3, K) ≃* SL(3, K) ⧸ χ.ker :=
    QuotientGroup.quotientMulEquivOfEq hχker.symm
  let Q2 : SL(3, K) ⧸ χ.ker ≃* G ⧸ Subgroup.center G :=
    QuotientGroup.quotientKerEquivOfSurjective χ hχsurj
  have Q2_apply : ∀ x, Q2 (QuotientGroup.mk x) = QuotientGroup.mk (g x) := by
    intro x
    change QuotientGroup.kerLift χ (QuotientGroup.mk x) = QuotientGroup.mk (g x)
    rw [QuotientGroup.kerLift_mk]
    rfl
  let S : SL(3, K) ⧸ Subgroup.center SL(3, K) ≃* projectiveSL 3 K :=
    QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 K).symm
  refine ⟨(Q1.trans Q2).symm.trans S, ?_⟩
  intro X
  have h1 : (Q1.trans Q2) (QuotientGroup.mk X) = QuotientGroup.mk (g X) := by
    rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk, Q2_apply]
  have h2 : (Q1.trans Q2).symm (QuotientGroup.mk (g X)) = QuotientGroup.mk X := by
    rw [← h1, MulEquiv.symm_apply_apply]
  rw [MulEquiv.trans_apply, h2]
  rw [show S (QuotientGroup.mk X) = QuotientGroup.mk X from
    QuotientGroup.quotientMulEquivOfEq_mk _ X]
  rfl

private lemma u3main_map_smul {K L : Type} [Field K] [Field L] (φ : K →+* L)
    (a : K) (A : Matrix (Fin 3) (Fin 3) K) : (a • A).map φ = φ a • A.map φ := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

private lemma u3main_inv_val_smul_map {K L : Type} [Field K] [Field L] (φ : K →+* L)
    (c : L) (hc : c ≠ 0) (M : GL (Fin 3) K) (C : GL (Fin 3) L)
    (hC : (C : Matrix (Fin 3) (Fin 3) L) = c • (M : Matrix (Fin 3) (Fin 3) K).map φ) :
    ((C⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      c⁻¹ • ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map φ := by
  have hM : (M : Matrix (Fin 3) (Fin 3) K).map φ *
      ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map φ = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    ext i j
    simp [Matrix.map_apply, Matrix.one_apply]
  have hright : (c • (M : Matrix (Fin 3) (Fin 3) K).map φ) *
      (c⁻¹ • ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map φ) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul, hM]
  rw [Matrix.GeneralLinearGroup.coe_inv, hC, Matrix.inv_eq_right_inv hright]

private lemma u3main_proj_conj {K L : Type} [Field K] [Field L] (φ : K →+* L)
    (hφ : Function.Injective φ) {c : L} (hc : c ≠ 0) {M : GL (Fin 3) K} {C : GL (Fin 3) L}
    (hC : (C : Matrix (Fin 3) (Fin 3) L) = c • (M : Matrix (Fin 3) (Fin 3) K).map φ)
    {X X' : SL(3, K)} {ζ : L} {ζK : K} (hζK : φ ζK = ζ) (hζ3 : ζK ^ 3 = 1)
    (h : (C : Matrix (Fin 3) (Fin 3) L) * ((X : Matrix (Fin 3) (Fin 3) K).map φ) *
          (((C⁻¹ : GL (Fin 3) L)) : Matrix (Fin 3) (Fin 3) L) =
        ζ • ((X' : Matrix (Fin 3) (Fin 3) K).map φ)) :
    proj 3 K X' = conjAut 3 K M (proj 3 K X) := by
  have hscale : (c • (M : Matrix (Fin 3) (Fin 3) K).map φ) *
      ((X : Matrix (Fin 3) (Fin 3) K).map φ) *
      (c⁻¹ • ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map φ) =
      (M : Matrix (Fin 3) (Fin 3) K).map φ * (X : Matrix (Fin 3) (Fin 3) K).map φ *
      ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map φ := by
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have h1 := h
  rw [hC, u3main_inv_val_smul_map φ c hc M C hC] at h1
  have hcalc : (M : Matrix (Fin 3) (Fin 3) K).map φ * (X : Matrix (Fin 3) (Fin 3) K).map φ *
      ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map φ =
      ζ • ((X' : Matrix (Fin 3) (Fin 3) K).map φ) := by
    rw [← hscale, h1]
  have hmap : ((M : Matrix (Fin 3) (Fin 3) K) * (X : Matrix (Fin 3) (Fin 3) K) *
      ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).map φ =
      (ζK • (X' : Matrix (Fin 3) (Fin 3) K)).map φ := by
    rw [Matrix.map_mul, Matrix.map_mul, u3main_map_smul φ ζK (X' : Matrix (Fin 3) (Fin 3) K),
      hζK, hcalc]
  have hK : (M : Matrix (Fin 3) (Fin 3) K) * (X : Matrix (Fin 3) (Fin 3) K) *
      ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ζK • (X' : Matrix (Fin 3) (Fin 3) K) := Matrix.map_injective hφ hmap
  rw [conjAut_proj, proj_eq_proj_iff]
  refine (mem_scalars (n := 3) (K := K)).mpr ⟨Units.mk0 ζK ?_, ?_, ?_⟩
  · intro h0
    rw [h0, zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at hζ3
    exact one_ne_zero hζ3.symm
  · rw [← Units.val_eq_one, Units.val_pow_eq_pow_val, Units.val_mk0, hζ3]
  · rw [Matrix.SpecialLinearGroup.coe_mul,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix,
      hK, Matrix.mul_smul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply,
      Units.val_mk0]

theorem ggNbrLSideRSExc_u3
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (h2 : (2 : L) = 0) (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)) (Q : ℕ)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (ha3 : ∀ j, a j ^ 3 = 1)
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hQ3 : 3 ∣ Q - 1) (hkind : twistKind S.ρ (rootCharHom a) i = .inner)
    (hrk : compRank (componentRoots (rootCharHom a) i) = 2)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 6)
    (hs3 : ¬ 3 ∣ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
    (hQq : Q = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) :
    ∀ y ∈ S.D.model, y ∈ Subgroup.centralizer {rootDiagUnit τ a} → y ^ 3 = 1 →
      ∀ α : MulAut (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸ Subgroup.center _),
        GGNbrLSideInduces (MulAut.conj y) (rationalComponent S.ρ S.Γ (rootCharHom a) i) α →
          GGInnDiagPSL3 Q
            (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸ Subgroup.center _) α := by
  classical
  intro y hyM hyC hy3 α hα
  let R : Subgroup (ModGL τ L) := rationalComponent S.ρ S.Γ (rootCharHom a) i
  obtain ⟨ψ, σ, κ, hψ, hκ, hnorm, hΨc⟩ := u3main_frame S h2 hT ha3 i hrk hcard
  have hker : ψ.ker ≤ Subgroup.center SL(3, L) := u3main_ker_le_center hψ
  obtain ⟨π, hπ⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.splitShape_of_twistKind_inner
      S hT i hkind (le_refl 3) hψ hκ hnorm hΨc
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  have hQs : Q = r ^ (e * s) := by rw [hQq, hq, hsdef, pow_mul]
  have hQ2 : 2 ≤ Q := by
    rw [hQs]
    have hr1 : 1 ≤ r := le_trans (by norm_num) hr.two_le
    have hes1 : 1 ≤ e * s := Nat.succ_le_of_lt (Nat.mul_pos he hs0)
    calc 2 ≤ r := hr.two_le
      _ = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ (e * s) := pow_le_pow_right' hr1 hes1
  obtain ⟨σQ, hσQ, z, hz, f, hfrange, hfker, hfact⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.split_exists_hom_act
      S hT i (le_refl 3) hψ hΨc π hπ hr hchar he hq
  let K := ↥(fixSubfield σQ)
  have hσ : ∀ c, σQ c = c ^ Q := fun c => by rw [hσQ, ← hQs]
  have hFix := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.finite_card_fixSubfield
    (r := r) (n := e * s) (Nat.mul_pos he hs0) σQ hσQ
  have hKfin : Finite K := hFix.1
  haveI : Finite K := hKfin
  have hKcard : Nat.card K = Q := by rw [hQs, hFix.2]
  have hyR : R.map (MulAut.conj y).toMonoidHom = R := by
    apply le_antisymm
    · rintro g ⟨h, hh, rfl⟩
      exact ggNbrLSideInduces_mem hα ⟨h, hh⟩
    · intro g hg
      refine ⟨y * (y * g * y⁻¹) * y⁻¹, ?_, ?_⟩
      · exact ggNbrLSideInduces_mem hα ⟨y * g * y⁻¹, ggNbrLSideInduces_mem hα ⟨g, hg⟩⟩
      · show (MulAut.conj y) (y * (y * g * y⁻¹) * y⁻¹) = g
        rw [MulAut.conj_apply]
        have hy3' : y * y * y = 1 := by rw [← pow_three', hy3]
        calc y * (y * (y * g * y⁻¹) * y⁻¹) * y⁻¹
            = (y * y * y) * g * (y⁻¹ * y⁻¹ * y⁻¹) := by group
          _ = g := by
            have h3' : y⁻¹ * y⁻¹ * y⁻¹ = 1 := by
              rw [show y⁻¹ * y⁻¹ * y⁻¹ = (y * y * y)⁻¹ by group, hy3', inv_one]
            rw [hy3', h3']
            group
  have hyT : y ∈ toralCentralizer τ L a := ⟨(S.D.mem_model.mp hyM).1, hyC⟩
  obtain ⟨w, hw, m, hm, hyw⟩ := exists_mul_canonicalRep_of_mem_toralCentralizer a hyT
  have hwΨ := weyl_image_component_eq_of_cube S hT i hQS hs3 hyM hy3 hyR hw hm hyw
  obtain ⟨Bm, hBm⟩ := exists_frameAct_of_mem_toralRootGroup i hψ hΨc hm
  obtain ⟨Bw, ε, hBw⟩ := exists_frameAct_canonicalRep i hψ hκ hnorm hΨc hwΨ
  have hyB0 : SLFrameAct ψ y (Bm * Bw) ε := by
    rw [hyw]
    exact u3main_frameAct_mul hBm hBw
  have hεfalse : ε = false := by
    cases ε with
    | false => rfl
    | true =>
        exfalso
        obtain ⟨B', hB'⟩ := u3main_graph_cube hyB0 hy3
        exact false_of_graph_trivial h2 ψ hker B' hB'
  have hyB : SLFrameAct ψ y (Bm * Bw) false := by rw [hεfalse] at hyB0; exact hyB0
  obtain ⟨H, hzH⟩ := exists_frameAct_of_mem_toralRootGroup i hψ hΨc hz
  set B : GL (Fin 3) L := Bm * Bw with hBdef
  let g₀ : SL(3, K) →* ↥R :=
    f.codRestrict R (fun X => hfrange.le (MonoidHom.mem_range.mpr ⟨X, rfl⟩))
  have hg₀val : ∀ X : SL(3, K), (g₀ X : ModGL τ L) = f X := fun X => rfl
  have hg₀surj : Function.Surjective g₀ := by
    rintro ⟨v, hv⟩
    obtain ⟨X, hX⟩ := MonoidHom.mem_range.mp (hfrange ▸ hv : v ∈ f.range)
    exact ⟨X, Subtype.ext hX⟩
  have hg₀ker : g₀.ker ≤ Subgroup.center SL(3, K) := by
    intro X hX
    apply hfker
    rw [MonoidHom.mem_ker]
    have h1 : (g₀ X : ModGL τ L) = 1 := by rw [MonoidHom.mem_ker.mp hX]; rfl
    rwa [hg₀val] at h1
  obtain ⟨e, he⟩ := u3main_exists_equiv g₀ hg₀surj hg₀ker
  have hgS : ∀ {g : ModGL τ L}, g ∈ ψ.range →
      g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    intro g hg
    rw [hψ.range, ← hΨc] at hg
    exact hg
  have hBBinv : ∀ U : SL(3, L),
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 L B
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 L B⁻¹ U)
          = U := by
    intro U
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hyBU : ∀ U : SL(3, L), y * ψ U * y⁻¹ =
      ψ (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 L B U) := by
    intro U
    have h := hyB U
    simpa using h
  have hyinv_mem : ∀ g ∈ ψ.range, y⁻¹ * g * y ∈ ψ.range := by
    rintro g ⟨U, rfl⟩
    refine ⟨CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 L B⁻¹ U, ?_⟩
    have h := hyBU
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 L B⁻¹ U)
    rw [hBBinv U] at h
    rw [← h]
    group
  have hU39 : ∀ (X X' : SL(3, K)), f X' = y * f X * y⁻¹ → ∀ g ∈ ψ.range,
      (y * (z * ψ (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X) * z⁻¹) * y⁻¹) *
        g * (y * (z * ψ (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X) * z⁻¹) *
          y⁻¹)⁻¹ =
      (z * ψ (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X') * z⁻¹) * g *
        (z * ψ (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X') * z⁻¹)⁻¹ := by
    intro X X' hfX' g hg
    have hg1 : y⁻¹ * g * y ∈ ψ.range := hyinv_mem g hg
    have h1 := hfact X (y⁻¹ * g * y) (hgS hg1)
    have h2 := hfact X' g (hgS hg)
    calc (y * (z * ψ (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X) * z⁻¹) * y⁻¹) *
          g * (y * (z * ψ (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X) * z⁻¹) *
            y⁻¹)⁻¹
        = y * ((z * ψ (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X) * z⁻¹) *
            (y⁻¹ * g * y) *
            (z * ψ (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X) * z⁻¹)⁻¹) *
            y⁻¹ := by group
      _ = y * (f X * (y⁻¹ * g * y) * (f X)⁻¹) * y⁻¹ := by rw [← h1]
      _ = (y * f X * y⁻¹) * g * (y * f X * y⁻¹)⁻¹ := by group
      _ = f X' * g * (f X')⁻¹ := by rw [hfX']
      _ = (z * ψ (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X') * z⁻¹) * g *
            (z * ψ (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X') * z⁻¹)⁻¹ := h2
  have hC10 : ∀ X : SL(3, K), ∃ (X' : SL(3, K)) (ζ : L), ζ ^ 3 = 1 ∧
      ((H⁻¹ * B * H : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) *
        (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X : Matrix (Fin 3) (Fin 3) L) *
        (((H⁻¹ * B * H)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
        ζ • (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X' :
          Matrix (Fin 3) (Fin 3) L) := by
    intro X
    obtain ⟨j', hj'val, -⟩ := hα (g₀ X)
    obtain ⟨X', hX'⟩ := hg₀surj j'
    have hfX' : f X' = y * f X * y⁻¹ := by
      have h1 := hj'val
      rw [MulAut.conj_apply, hg₀val X] at h1
      rw [← hX', hg₀val X'] at h1
      exact h1
    obtain ⟨ζ, hζ3, hmat⟩ := ggNbrLSideRSExc_frameAct_conj_eq_smul hψ hyB hzH
      (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X)
      (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X') (hU39 X X' hfX')
    exact ⟨X', ζ, hζ3, hmat⟩
  obtain ⟨M, c, hc0, hCM⟩ :=
    ggNbrLSideRSExc_exists_smul_map_of_conj hQ2 hQ3 σQ hσ (H⁻¹ * B * H) hC10
  have hx : ∀ x : ↥R ⧸ Subgroup.center ↥R, ∃ X : SL(3, K),
      x = QuotientGroup.mk (g₀ X) := by
    intro x
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨X, rfl⟩ := hg₀surj j
    exact ⟨X, rfl⟩
  refine ggInnDiagPSL3_of_conjAut_apply (F := K) (Q := Q) hKcard e M fun x => ?_
  obtain ⟨X, rfl⟩ := hx x
  obtain ⟨j', hj'val, hj'α⟩ := hα (g₀ X)
  obtain ⟨X', hX'⟩ := hg₀surj j'
  have hfX' : f X' = y * f X * y⁻¹ := by
    have h1 := hj'val
    rw [MulAut.conj_apply, hg₀val X] at h1
    rw [← hX', hg₀val X'] at h1
    exact h1
  obtain ⟨ζ, hζ3, hmat⟩ := ggNbrLSideRSExc_frameAct_conj_eq_smul hψ hyB hzH
    (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X)
    (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X') (hU39 X X' hfX')
  have hζQ : ζ ^ Q = ζ := by
    obtain ⟨m, hm⟩ := hQ3
    have hQeq : Q = 3 * m + 1 := by omega
    calc ζ ^ Q = ζ ^ (3 * m + 1) := by rw [hQeq]
      _ = ζ ^ (3 * m) * ζ := by rw [pow_succ]
      _ = (ζ ^ 3) ^ m * ζ := by rw [pow_mul]
      _ = 1 ^ m * ζ := by rw [hζ3]
      _ = ζ := by rw [one_pow, one_mul]
  have hζfix : ζ ∈ fixSubfield σQ :=
    (mem_fixSubfield (σ := σQ)).mpr (by rw [hσ, hζQ])
  let ζK : K := ⟨ζ, hζfix⟩
  have hζK : (fixSubfield σQ).subtype ζK = ζ := rfl
  have hζ3K : ζK ^ 3 = 1 := (fixSubfield σQ).subtype_injective (by
    rw [map_pow, map_one]
    rw [hζK]
    exact hζ3)
  have hproj : proj 3 K X' = conjAut 3 K M (proj 3 K X) :=
    u3main_proj_conj (fixSubfield σQ).subtype (fixSubfield σQ).subtype_injective hc0 hCM
      hζK hζ3K hmat
  have hαx : α (QuotientGroup.mk (g₀ X)) = QuotientGroup.mk (g₀ X') := by
    rw [hj'α, ← hX']
  rw [hαx, he X', he X]
  exact hproj

theorem ggNbrLSideRSExc_u3_of_u2
    (hU2 : GGNbrLSideRSExcU2) : GGNbrLSideRSExcU3 :=
  fun τ L _ _ p₀ S h2 a i Q hP hk hr hc hs =>
    ggNbrLSideRSExc_u3 S h2 a i Q hP.1 hP.2.1 hP.2.2.2.1 hP.2.2.2.2.2.1 hk hr hc hs
      (hU2 τ L p₀ S h2 a i Q hP).2.2.2

end CFSG.StandardType

end

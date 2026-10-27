module

public import CFSG.Assembly.LargeEvenDefs
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSU
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoKGroup
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.ClassicalGroups.Unitary.Simple
import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUDiag
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdUnitaryDiag
import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGRootCentKGMarkingSL
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSU
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary

namespace KGND

@[expose] def suConjSet {k : ℕ} {F : Type} [Field F] {σ : F ≃+* F} {X : Type} [Group X]
    (φ : ↥(SU σ k) →* X) : Set (MulAut X) :=
  {α | ∃ (A : GL (Fin k) F) (hA : InnerDiagSU.IsJUnitary σ A),
    ∀ B, α (φ B) = φ (InnerDiagSU.conjSU A hA B)}

variable {k : ℕ} {F : Type} [Field F] {σ : F ≃+* F} {X : Type} [Group X]

private theorem conjSU_mul {A A' : GL (Fin k) F} (hA : InnerDiagSU.IsJUnitary σ A)
    (hA' : InnerDiagSU.IsJUnitary σ A') (u : ↥(SU σ k)) :
    InnerDiagSU.conjSU A hA (InnerDiagSU.conjSU A' hA' u) =
      InnerDiagSU.conjSU (A * A') (hA.mul hA') u := by
  apply Subtype.ext
  rw [InnerDiagSU.coe_conjSU, InnerDiagSU.coe_conjSU, InnerDiagSU.coe_conjSU]
  group

private theorem map_conjSU_coe (φ : ↥(SU σ k) →* X) (s u : ↥(SU σ k)) :
    φ (InnerDiagSU.conjSU (s : GL (Fin k) F) (InnerDiagSU.isJUnitary_of_mem_SU s) u) =
      φ s * φ u * (φ s)⁻¹ := by
  have h : InnerDiagSU.conjSU (s : GL (Fin k) F) (InnerDiagSU.isJUnitary_of_mem_SU s) u =
      s * u * s⁻¹ := rfl
  rw [h, map_mul, map_mul, map_inv]

theorem conj_mem_suConjSet (φ : ↥(SU σ k) →* X) (B₀ : ↥(SU σ k)) :
    MulAut.conj (φ B₀) ∈ suConjSet φ := by
  refine ⟨(B₀ : GL (Fin k) F), InnerDiagSU.isJUnitary_of_mem_SU B₀, fun B => ?_⟩
  rw [MulAut.conj_apply, map_conjSU_coe]

theorem mul_mem_suConjSet (φ : ↥(SU σ k) →* X) {α β : MulAut X} (hα : α ∈ suConjSet φ)
    (hβ : β ∈ suConjSet φ) : α * β ∈ suConjSet φ := by
  obtain ⟨A, hA, hAα⟩ := hα
  obtain ⟨A', hA', hAβ⟩ := hβ
  refine ⟨A * A', hA.mul hA', fun B => ?_⟩
  calc (α * β) (φ B) = α (β (φ B)) := rfl
    _ = α (φ (InnerDiagSU.conjSU A' hA' B)) := by rw [hAβ B]
    _ = φ (InnerDiagSU.conjSU A hA (InnerDiagSU.conjSU A' hA' B)) := hAα _
    _ = φ (InnerDiagSU.conjSU (A * A') (hA.mul hA') B) := by rw [conjSU_mul]

section Two

variable [Finite F] [CharP F 2] {f : ℕ}

private theorem exists_conjSU_eq_of_isJUnitary_two
    {A : GL (Fin 2) F} (hA : InnerDiagSU.IsJUnitary (unitaryInvolution F 2 f) A) :
    ∃ s : ↥(SU (unitaryInvolution F 2 f) 2),
      ∀ u : ↥(SU (unitaryInvolution F 2 f) 2),
        InnerDiagSU.conjSU A hA u =
          InnerDiagSU.conjSU (s : GL (Fin 2) F) (InnerDiagSU.isJUnitary_of_mem_SU s) u := by
  have hdetA : unitaryInvolution F 2 f (A : Matrix (Fin 2) (Fin 2) F).det *
      (A : Matrix (Fin 2) (Fin 2) F).det = 1 := MpStdSU.normOne_det hA
  obtain ⟨y, hy1, hy2⟩ := MpStdSU.exists_sqrt_normOne hdetA
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hy1
    exact zero_ne_one hy1
  have hyy : y * y ≠ 0 := mul_ne_zero hy0 hy0
  have hdetC : ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy0) : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).det = y * y := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
      Matrix.det_diagonal, Fin.prod_univ_two]
  have hdetCinv : (((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy0))⁻¹ :
      GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = (y * y)⁻¹ := by
    have h1 : (((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy0))⁻¹ :
        GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det *
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy0) : GL (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F).det = 1 := by
      rw [← Matrix.det_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Units.val_one,
        Matrix.det_one]
    rw [hdetC, mul_comm] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hdetS : ((((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy0))⁻¹ * A :
      GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, hdetCinv, ← hy2,
      inv_mul_cancel₀ hyy]
  have hC : InnerDiagSU.IsJUnitary (unitaryInvolution F 2 f)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy0)) := by
    unfold InnerDiagSU.IsJUnitary
    rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply, conjTr,
      Matrix.diagonal_map (map_zero (unitaryInvolution F 2 f)), Matrix.diagonal_transpose]
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [mul_assoc, mul_comm (antidiag 2 i j) y, ← mul_assoc, hy1, one_mul]
  have hcentral : ∀ x : GL (Fin 2) F,
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy0))⁻¹ * x *
        Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy0) = x := by
    intro x
    have hcomm := Matrix.GeneralLinearGroup.scalar_commute (Units.mk0 y hy0) x
    calc (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy0))⁻¹ * x *
          Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy0)
        = (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy0))⁻¹ *
            (x * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy0)) := by
          rw [mul_assoc]
      _ = (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy0))⁻¹ *
            (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy0) * x) := by
          rw [← hcomm]
      _ = x := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  let s : ↥(SU (unitaryInvolution F 2 f) 2) :=
    ⟨(Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy0))⁻¹ * A, hdetS,
      hC.inv.mul hA⟩
  refine ⟨s, fun u => ?_⟩
  apply Subtype.ext
  rw [InnerDiagSU.coe_conjSU, InnerDiagSU.coe_conjSU]
  show A * (u : GL (Fin 2) F) * A⁻¹ =
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy0))⁻¹ * A) *
      (u : GL (Fin 2) F) * (((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy0))⁻¹ *
        A))⁻¹
  rw [_root_.mul_inv_rev, inv_inv, ← hcentral (A * (u : GL (Fin 2) F) * A⁻¹)]
  group

private theorem exists_eq_conj_of_mem_suConjSet_two (φ : ↥(SU (unitaryInvolution F 2 f) 2) →* X)
    (hφ : Function.Surjective φ) {α : MulAut X} (hα : α ∈ suConjSet φ) :
    ∃ s : ↥(SU (unitaryInvolution F 2 f) 2), α = MulAut.conj (φ s) := by
  obtain ⟨A, hA, hAα⟩ := hα
  obtain ⟨s, hs⟩ := exists_conjSU_eq_of_isJUnitary_two hA
  refine ⟨s, ?_⟩
  apply MulEquiv.ext
  intro y
  obtain ⟨u, rfl⟩ := hφ y
  rw [hAα u, hs u, MulAut.conj_apply, map_conjSU_coe]

private theorem suConjSet_subset_slConjSet
    (φ : ↥(SU (unitaryInvolution F 2 f) 2) →* X) (hφ : Function.Surjective φ)
    (e : Matrix.SpecialLinearGroup (Fin 2) (CFSG.LieType.Steinberg.fixedSubfield F 2 f) ≃*
      ↥(SU (unitaryInvolution F 2 f) 2)) :
    suConjSet φ ⊆ slConjSet (φ.comp e.toMonoidHom) := by
  intro α hα
  obtain ⟨s, rfl⟩ := exists_eq_conj_of_mem_suConjSet_two φ hφ hα
  have hval : (φ.comp e.toMonoidHom) (e.symm s) = φ s := by
    show φ (e (e.symm s)) = φ s
    rw [MulEquiv.apply_symm_apply]
  have hconj : MulAut.conj (φ s) =
      MulAut.conj ((φ.comp e.toMonoidHom) (e.symm s)) := by
    rw [hval]
  rw [hconj]
  exact conj_mem_slConjSet (φ.comp e.toMonoidHom) (e.symm s)

private theorem largeEvenMarking_suConjSet_two {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    (hf : 1 ≤ f) (hf2 : 2 ≤ f)
    (φ : ↥(SU (unitaryInvolution F 2 f) 2) →* X)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center ↥(SU (unitaryInvolution F 2 f) 2)) :
    LargeEvenMarking X (fun lab R _ I _ θ => GGChevStTag lab ∧
      ∀ α ∈ suConjSet φ, ∃ ψ ∈ I, ∀ y : X,
        ψ (θ (QuotientGroup.mk y)) = θ (QuotientGroup.mk (α y))) := by
  classical
  obtain ⟨⟨e⟩, hcard⟩ := RCSTSU.exists_equiv_sl2 (F := F) (f := f) hF
  have hφ' : Function.Surjective (φ.comp e.toMonoidHom) := hφ.comp e.surjective
  have hker' : (φ.comp e.toMonoidHom).ker ≤ Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 2) (CFSG.LieType.Steinberg.fixedSubfield F 2 f)) := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
    exact (InnerDiagSU.mem_center_iff_of_mulEquiv e).mp (hker hx)
  have hSL := largeEvenMarking_slConjSet (m := 1)
    (F := CFSG.LieType.Steinberg.fixedSubfield F 2 f) hcard hf le_rfl (fun _ => hf2)
    (φ.comp e.toMonoidHom) hφ' hker'
  refine largeEvenMarking_mono (P := _) (P' := _) (fun lab R _ I F θ hP => ⟨hP.1, ?_⟩) hSL
  intro α hα
  exact hP.2 α (suConjSet_subset_slConjSet φ hφ e hα)

end Two

section Three

variable [Finite F] [CharP F 2] {f : ℕ}

private theorem largeEvenMarking_suConjSet_three_le (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (hk : 3 ≤ k) (hkq : k = 3 → 2 ≤ f)
    (φ : ↥(SU (unitaryInvolution F 2 f) k) →* X)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center ↥(SU (unitaryInvolution F 2 f) k)) :
    LargeEvenMarking X (fun lab R _ I _ θ => GGChevStTag lab ∧
      ∀ α ∈ suConjSet φ, ∃ ψ ∈ I, ∀ y : X,
        ψ (θ (QuotientGroup.mk y)) = θ (QuotientGroup.mk (α y))) := by
  classical
  have hnq : (k, 2 ^ f) ≠ (3, 2) := by
    rintro h
    have h1 : k = 3 := congrArg Prod.fst h
    have h2 : 2 ^ f = 2 := congrArg Prod.snd h
    have h3 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (hkq h1)
    omega
  let H := LargeEvenSUGroup (Fin k) F (2 ^ f)
  have hperfS : Group.IsPerfect (CFSG.Open.StatedSU k (2 ^ f) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF hk hnq
  haveI : Group.IsPerfect ↥H := hperfS
  have hZ : Subgroup.center ↥H = (LargeEvenScalars (Fin k) F).subgroupOf H :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF hk hnq).2
  have hSU : SUid (unitaryInvolution F 2 f) k = H := SUid_eq_statedSU hF k
  set P := (exists_wittMatrix hF k).choose with hPdef
  have hP := (exists_wittMatrix hF k).choose_spec
  let E : ↥(SU (unitaryInvolution F 2 f) k) ≃* ↥H :=
    (conjEquiv P hP).trans (MulEquiv.subgroupCongr hSU)
  have hEu : ∀ u, ((E u : ↥H) : GL (Fin k) F) = P * u * P⁻¹ := fun _ => rfl
  have hperfU : Group.IsPerfect ↥(SU (unitaryInvolution F 2 f) k) :=
    Group.IsPerfect.ofSurjective (f := E.symm.toMonoidHom) E.symm.surjective
  have hperf : commutator ↥(SU (unitaryInvolution F 2 f) k) = ⊤ :=
    Group.isPerfect_def.mp hperfU
  let q₁ : ↥(SU (unitaryInvolution F 2 f) k) →* X ⧸ Subgroup.center X :=
    (QuotientGroup.mk' _).comp φ
  let q₂ : ↥(SU (unitaryInvolution F 2 f) k) →* LargeEvenProj H :=
    (LargeEvenProjMk H).comp E.toMonoidHom
  have hq₁ : Function.Surjective q₁ := (QuotientGroup.mk'_surjective _).comp hφ
  have hq₂ : Function.Surjective q₂ :=
    (QuotientGroup.mk'_surjective _).comp E.surjective
  have hk₁ : q₁.ker = Subgroup.center ↥(SU (unitaryInvolution F 2 f) k) := by
    ext u
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (φ u) : X ⧸ Subgroup.center X) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hu
      refine InnerDiagA.mem_center_of_rangeRestrict_mem_center hperf φ hker ?_
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp hu l
    · intro hu
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨s, rfl⟩ := hφ y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hu s]
  have hk₂ : q₂.ker = Subgroup.center ↥(SU (unitaryInvolution F 2 f) k) := by
    ext u
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (s := (LargeEvenScalars (Fin k) F).subgroupOf H) (E u) :
      LargeEvenProj H) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, ← InnerDiagSU.mem_center_iff_of_mulEquiv E, hZ]
  let θ : X ⧸ Subgroup.center X ≃* LargeEvenProj H :=
    (QuotientGroup.quotientKerEquivOfSurjective q₁ hq₁).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (hk₁.trans hk₂.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective q₂ hq₂))
  have hθ : ∀ u, θ (q₁ u) = q₂ u := fun u => by
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective q₁ hq₁).symm (q₁ u) =
        (u : ↥(SU (unitaryInvolution F 2 f) k) ⧸ q₁.ker) :=
      (MulEquiv.symm_apply_eq _).mpr rfl
    simp only [θ, MulEquiv.trans_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hsimple : IsSimpleGroup (LargeEvenProj H) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 f hF k hk hnq
  have hnonab : ∃ a b : LargeEvenProj H, a * b ≠ b * a := by
    haveI : Group.IsPerfect (LargeEvenProj H) :=
      Group.IsPerfect.ofSurjective (f := LargeEvenProjMk H) (QuotientGroup.mk'_surjective _)
    have := hsimple.toNontrivial
    by_contra h
    push Not at h
    exact Group.IsPerfect.not_isMulCommutative (LargeEvenProj H) ⟨⟨h⟩⟩
  have hcomm : commutator X = ⊤ := by
    have h1 := congrArg (Subgroup.map φ) hperf
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hφ] at h1
    rw [commutator_def]
    exact h1
  have key : ∀ α ∈ suConjSet φ, ∃ ψ ∈ LargeEvenMatConjImage (LargeEvenProjMk H)
      (LargeEvenGUSet (Fin k) F (2 ^ f)), ∀ y : X,
        ψ (θ (QuotientGroup.mk y)) = θ (QuotientGroup.mk (α y)) := by
    intro α hα
    obtain ⟨A, hA, hAα⟩ := hα
    have hB : InnerDiagSU.IsIdUnitary (unitaryInvolution F 2 f) (P * A * P⁻¹) :=
      InnerDiagSU.isIdUnitary_conj hP hA
    have hBN : P * A * P⁻¹ ∈ Subgroup.normalizer (H : Set (GL (Fin k) F)) := by
      have h1 := InnerDiagSU.mem_normalizer_SUid hB
      rw [hSU] at h1
      exact h1
    refine ⟨TableB.projConj H ⟨P * A * P⁻¹, hBN⟩,
      ⟨P * A * P⁻¹, ?_, fun h h' hh' => ?_⟩, ?_⟩
    · refine ⟨1, one_ne_zero, one_pow _, ?_⟩
      rw [one_smul]
      have hmap : ((P * A * P⁻¹ : GL (Fin k) F) :
          Matrix (Fin k) (Fin k) F).map (· ^ 2 ^ f) =
          ((P * A * P⁻¹ : GL (Fin k) F) :
            Matrix (Fin k) (Fin k) F).map (unitaryInvolution F 2 f) := by
        ext i j
        simp only [Matrix.map_apply, unitaryInvolution_apply]
      rw [hmap]
      exact hB
    · show TableB.projConj H ⟨P * A * P⁻¹, hBN⟩ (h : LargeEvenProj H) = (h' : LargeEvenProj H)
      rw [TableB.projConj_mk]
      congr 1
      exact Subtype.ext hh'.symm
    · intro y
      obtain ⟨u, rfl⟩ := hφ y
      rw [hAα u]
      change TableB.projConj H ⟨P * A * P⁻¹, hBN⟩ (θ (q₁ u)) =
        θ (q₁ (InnerDiagSU.conjSU A hA u))
      rw [hθ u, hθ (InnerDiagSU.conjSU A hA u)]
      change TableB.projConj H ⟨P * A * P⁻¹, hBN⟩ ((E u : ↥H) : LargeEvenProj H) =
        ((E (InnerDiagSU.conjSU A hA u) : ↥H) : LargeEvenProj H)
      rw [TableB.projConj_mk]
      congr 1
      apply Subtype.ext
      show P * A * P⁻¹ * (E u : GL (Fin k) F) * (P * A * P⁻¹)⁻¹ =
        (E (InnerDiagSU.conjSU A hA u) : GL (Fin k) F)
      rw [hEu, hEu, InnerDiagSU.coe_conjSU]
      group
  have hm1 : k - 1 = 2 → 2 ≤ f := fun h => hkq (by omega)
  refine ⟨hcomm, ⟨.twA, k - 1, f⟩, ?_, ?_⟩
  · dsimp only [LargeEvenInLambda2]
    exact ⟨hf, by omega, hm1⟩
  · dsimp only [LargeEvenRawDatumLegacy]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
    exact ⟨F, inferInstance, inferInstance, hF, hsimple, hnonab, θ,
      ⟨by simp [GGChevStTag], key⟩⟩

end Three

theorem largeEvenMarking_suConjSet {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) {k : ℕ} (hk : 2 ≤ k) (hkq : k ≤ 3 → 2 ≤ f)
    {X : Type} [Group X] (φ : ↥(SU (unitaryInvolution F 2 f) k) →* X)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center ↥(SU (unitaryInvolution F 2 f) k)) :
    LargeEvenMarking X (fun lab R _ I _ θ => GGChevStTag lab ∧
      ∀ α ∈ suConjSet φ, ∃ ψ ∈ I, ∀ y : X,
        ψ (θ (QuotientGroup.mk y)) = θ (QuotientGroup.mk (α y))) := by
  classical
  rcases Nat.lt_or_ge k 3 with hlt | hge
  · have hk2 : k = 2 := by omega
    subst hk2
    exact largeEvenMarking_suConjSet_two hF hf (hkq (by omega)) φ hφ hker
  · exact largeEvenMarking_suConjSet_three_le hF hf hge (fun h => hkq (by omega)) φ hφ hker

end KGND

end CFSG.StandardType

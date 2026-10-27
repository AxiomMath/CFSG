module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenTriDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityOrthRestrict
import CFSG.LocalAnalysis.WeakClosure81.TrialityMarkedFrame
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlParamMain
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.StandardType QuadraticMap Matrix
open CFSG.ClassicalGroups.Alternating (symplecticTransvection symplecticTransvection_apply
  symplecticTransvection_zero alternating_transvection_generation)

section Linear

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {v : Fin d → K}

theorem symmetryCentralizer_le_closure (hQ : Q.polarBilin.Nondegenerate) (hv : Q v = 1) :
    symmetryCentralizer Q v ≤
      Subgroup.closure {g | ∃ z, Q z = 1 ∧ polar Q z v = 0 ∧ g = symmetryGL Q z} := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hvv : polar Q v v = 0 := by rw [polar_self, hv, two_nsmul, CharTwo.add_self_eq_zero]
  set S : Set (GL (Fin d) K) := {g | ∃ z, Q z = 1 ∧ polar Q z v = 0 ∧ g = symmetryGL Q z}
    with hS
  set H : Subgroup (symmetryCentralizer Q v) :=
    (Subgroup.closure S).subgroupOf (symmetryCentralizer Q v) with hH
  have hsz : ∀ z, Q z = 1 → polar Q z v = 0 → symmetryGL Q z ∈ symmetryCentralizer Q v := by
    intro z hz hzv
    refine ⟨symmetryGL_mem Q z,
      (mem_centralizer_symmetryGL_iff hQ hv (symmetryGL_mem Q z)).mpr ?_⟩
    rw [symmetryGL_mulVec_of_charTwo hz, hzv, zero_smul, add_zero]
  have hlift : ∀ (a : vQuot Q v) (c : K),
      symplecticTransvection (vQuotForm Q v) (vQuotForm_isAlt Q v) a c ∈
        H.map (symmetryRestrict hQ hv) := by
    intro a c
    by_cases hc : c = 0
    · rw [hc, symplecticTransvection_zero]
      exact one_mem _
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
    obtain ⟨b, hb⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2)
      (1 + Q (l • (u : Fin d → K)))
    have huv : polar Q (u : Fin d → K) v = 0 := by
      rw [polar_comm]
      exact u.2
    set z : Fin d → K := l • (u : Fin d → K) + b • v with hzdef
    have hz : Q z = 1 := by
      rw [hzdef, QuadraticMap.map_add Q, QuadraticMap.map_smul Q b v, hv, polar_smul_left,
        polar_smul_right, huv, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_zero, mul_zero,
        add_zero, mul_one, ← hb]
      linear_combination Q (l • (u : Fin d → K)) * h22
    have hzv : polar Q z v = 0 := by
      rw [hzdef, polar_add_left, polar_smul_left, polar_smul_left, huv, hvv, smul_zero, smul_zero,
        add_zero]
    refine ⟨⟨symmetryGL Q z, hsz z hz hzv⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure ⟨z, hz, hzv, rfl⟩)
    · apply Units.ext
      apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | H x =>
        rw [symmetryRestrict_mk, symplecticTransvection_apply, vQuotForm_mk,
          ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq,
          Submodule.mem_comap]
        have hx : polar Q v (x : Fin d → K) = 0 := x.2
        have hzx : polar Q z (x : Fin d → K) = l * polar Q (x : Fin d → K) u := by
          rw [hzdef, polar_add_left, polar_smul_left, polar_smul_left, hx, smul_zero, add_zero,
            polar_comm, smul_eq_mul]
        have hact : ((symmetryGL Q z : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
            (x : Fin d → K) = (x : Fin d → K) + (c * polar Q (x : Fin d → K) u) •
              (u : Fin d → K) + (l * polar Q (x : Fin d → K) u * b) • v := by
          rw [symmetryGL_mulVec_of_charTwo hz, hzx, hzdef, hl]
          module
        refine Submodule.mem_span_singleton.mpr ⟨l * polar Q (x : Fin d → K) u * b, ?_⟩
        simp only [Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_add,
          Submodule.coe_smul]
        change _ = ((symmetryGL Q z : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
          (x : Fin d → K) - _
        rw [hact]
        abel
  intro g hg
  have hrange : (symmetryRestrict hQ hv).range ≤ H.map (symmetryRestrict hQ hv) := by
    rintro _ ⟨g', rfl⟩
    have h1 := symmetryRestrict_mem hQ hv g'
    rw [alternating_transvection_generation (vQuotForm_isAlt Q v)
      (vQuotForm_nondegenerate hQ hv0)] at h1
    exact (Subgroup.closure_le _).2 (by rintro _ ⟨a, c, rfl⟩; exact hlift a c) h1
  obtain ⟨k, hk, hkg⟩ := hrange ⟨⟨g, hg⟩, rfl⟩
  have hker : k⁻¹ * ⟨g, hg⟩ ∈ (symmetryRestrict hQ hv).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkg, inv_mul_cancel]
  rw [ker_symmetryRestrict] at hker
  have hsvH : (⟨symmetryGL Q v, symmetryGL_mem_symmetryCentralizer⟩ : symmetryCentralizer Q v) ∈
      H := by
    rw [hH, Subgroup.mem_subgroupOf]
    exact Subgroup.subset_closure ⟨v, hv, hvv, rfl⟩
  have h2 : k⁻¹ * ⟨g, hg⟩ ∈ H := Subgroup.zpowers_le.2 hsvH hker
  have h3 : (⟨g, hg⟩ : symmetryCentralizer Q v) ∈ H := by
    have := mul_mem hk h2
    rwa [mul_inv_cancel_left] at this
  exact Subgroup.mem_subgroupOf.1 h3

end Linear

theorem TrialityData.centralizer_eq_closure {X : Type} [Group X] {s : X}
    {ε : X →* Equiv.Perm (Fin 3)} (h : TrialityData X s ε) (r : X) (hr : IsConj s r) :
    Subgroup.centralizer ({r} : Set X) =
      Subgroup.closure ({x : X | IsConj s x} ∩ (Subgroup.centralizer ({r} : Set X) : Set X)) := by
  refine le_antisymm ?_ ((Subgroup.closure_le _).2 Set.inter_subset_right)
  obtain ⟨F, _, _, _, Λ, s₁, hs₁, hΛs₁, -⟩ := h.exists_orthFrame
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus (K := F) (n := 4) (by norm_num)
  have hv₀ : coordinateQuadPlus 4 F (CFSG.SeitzReduction.OmegaPilot.plusUnitVector
      Triality.one_le_four) = 1 := AutOm.plusUnitVector_form Triality.one_le_four
  have hΛs₁' : ((Λ s₁ : matrixIsometries (coordinateQuadPlus 4 F)) : GL (Fin (2 * 4)) F) =
      symmetryGL (coordinateQuadPlus 4 F)
        (CFSG.SeitzReduction.OmegaPilot.plusUnitVector Triality.one_le_four) :=
    hΛs₁.trans (AutOm.reflMat_eq_symmetryGL Triality.one_le_four)
  have hτ := h.map_ne_one_and_mul_self hs₁
  have hS3 : ∀ p : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3), p.2 ≠ 1 → p.2 * p.2 = 1 →
      p.1 * p.2 = p.2 * p.1 → p.1 = 1 ∨ p.1 = p.2 := by
    decide
  have key : Subgroup.centralizer ({(s₁ : X)} : Set X) ≤
      Subgroup.closure ({x : X | IsConj s x} ∩
        (Subgroup.centralizer ({(s₁ : X)} : Set X) : Set X)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    have hxL : x ∈ ε.ker ⊔ Subgroup.zpowers s := by
      have hc : ε x * ε s₁ = ε s₁ * ε x := by rw [← map_mul, ← map_mul, hx]
      obtain h1 | h1 : ε x = 1 ∨ ε x = ε s₁ := hS3 (ε x, ε s₁) hτ.1 hτ.2 hc
      · exact Subgroup.mem_sup_left ((MonoidHom.mem_ker).2 h1)
      · have h2 : x * (s₁ : X)⁻¹ ∈ ε.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
        have h3 := mul_mem (Subgroup.mem_sup_left h2 : x * (s₁ : X)⁻¹ ∈ ε.ker ⊔ Subgroup.zpowers s)
          s₁.2
        rwa [inv_mul_cancel_right] at h3
    have hcomm : (⟨x, hxL⟩ : ↥(ε.ker ⊔ Subgroup.zpowers s)) * s₁ = s₁ * ⟨x, hxL⟩ :=
      Subtype.ext hx
    have hC : ((Λ ⟨x, hxL⟩ : matrixIsometries (coordinateQuadPlus 4 F)) : GL (Fin (2 * 4)) F) ∈
        symmetryCentralizer (coordinateQuadPlus 4 F)
          (CFSG.SeitzReduction.OmegaPilot.plusUnitVector Triality.one_le_four) := by
      refine Subgroup.mem_inf.2 ⟨(Λ ⟨x, hxL⟩).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hΛs₁', ← Subgroup.coe_mul,
        ← Subgroup.coe_mul, ← map_mul, ← map_mul, hcomm]
    have hcl := symmetryCentralizer_le_closure hnd hv₀ hC
    have hSO : Subgroup.closure {g : GL (Fin (2 * 4)) F | ∃ z,
        coordinateQuadPlus 4 F z = 1 ∧ polar (coordinateQuadPlus 4 F) z
          (CFSG.SeitzReduction.OmegaPilot.plusUnitVector Triality.one_le_four) = 0 ∧
            g = symmetryGL (coordinateQuadPlus 4 F) z} ≤
        matrixIsometries (coordinateQuadPlus 4 F) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨z, -, -, rfl⟩
      exact symmetryGL_mem _ z
    have hall : ∀ (g : GL (Fin (2 * 4)) F) (hg : g ∈ Subgroup.closure {g : GL (Fin (2 * 4)) F |
        ∃ z, coordinateQuadPlus 4 F z = 1 ∧ polar (coordinateQuadPlus 4 F) z
          (CFSG.SeitzReduction.OmegaPilot.plusUnitVector Triality.one_le_four) = 0 ∧
            g = symmetryGL (coordinateQuadPlus 4 F) z}),
        ((Λ.symm ⟨g, hSO hg⟩ : ↥(ε.ker ⊔ Subgroup.zpowers s)) : X) ∈
          Subgroup.closure ({x : X | IsConj s x} ∩
            (Subgroup.centralizer ({(s₁ : X)} : Set X) : Set X)) := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem g hgS =>
        obtain ⟨z, hz, hzv, rfl⟩ := hgS
        have hz0 : coordinateQuadPlus 4 F z ≠ 0 := by rw [hz]; exact one_ne_zero
        apply Subgroup.subset_closure
        constructor
        · obtain ⟨γ, hγ, hγz⟩ := CFSG.SeitzReduction.SymplecticPilot.exists_conj_reflMat hnd hT
            (AutOm.plusUnitVector_form_ne_zero (K := F) Triality.one_le_four) hz0
          have he : ∀ hp : symmetryGL (coordinateQuadPlus 4 F) z ∈
              matrixIsometries (coordinateQuadPlus 4 F),
              (⟨symmetryGL (coordinateQuadPlus 4 F) z, hp⟩ :
                matrixIsometries (coordinateQuadPlus 4 F)) = ⟨γ, hγ⟩ * Λ s₁ * ⟨γ, hγ⟩⁻¹ := by
            intro hp
            apply Subtype.ext
            change symmetryGL (coordinateQuadPlus 4 F) z =
              γ * ((Λ s₁ : matrixIsometries (coordinateQuadPlus 4 F)) : GL (Fin (2 * 4)) F) * γ⁻¹
            rw [hΛs₁, hγz, CFSG.SeitzReduction.SymplecticPilot.bParam_symmetryGL_eq_reflMat hz hz0]
          rw [he, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_mul,
            Subgroup.coe_mul, Subgroup.coe_inv]
          exact hs₁.trans (isConj_iff.2 ⟨_, rfl⟩)
        · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
          have hcz : symmetryGL (coordinateQuadPlus 4 F) z *
              symmetryGL (coordinateQuadPlus 4 F)
                (CFSG.SeitzReduction.OmegaPilot.plusUnitVector Triality.one_le_four) =
              symmetryGL (coordinateQuadPlus 4 F)
                (CFSG.SeitzReduction.OmegaPilot.plusUnitVector Triality.one_le_four) *
                symmetryGL (coordinateQuadPlus 4 F) z := by
            refine Subgroup.mem_centralizer_singleton_iff.1
              ((mem_centralizer_symmetryGL_iff hnd hv₀ (symmetryGL_mem _ z)).mpr ?_)
            rw [symmetryGL_mulVec_of_charTwo hz, hzv, zero_smul, add_zero]
          have hm : (⟨symmetryGL (coordinateQuadPlus 4 F) z, hSO (Subgroup.subset_closure
              ⟨z, hz, hzv, rfl⟩)⟩ : matrixIsometries (coordinateQuadPlus 4 F)) * Λ s₁ =
              Λ s₁ * ⟨symmetryGL (coordinateQuadPlus 4 F) z, hSO (Subgroup.subset_closure
                ⟨z, hz, hzv, rfl⟩)⟩ :=
            Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hΛs₁']; exact hcz)
          have h1 := congrArg (fun y => ((Λ.symm y : ↥(ε.ker ⊔ Subgroup.zpowers s)) : X)) hm
          simpa only [map_mul, Subgroup.coe_mul, MulEquiv.symm_apply_apply] using h1
      | one =>
        have h1 : (⟨1, hSO (one_mem _)⟩ : matrixIsometries (coordinateQuadPlus 4 F)) = 1 := rfl
        rw [h1, map_one, Subgroup.coe_one]
        exact one_mem _
      | mul g₁ g₂ hg₁ hg₂ ih₁ ih₂ =>
        have h1 : (⟨g₁ * g₂, hSO (mul_mem hg₁ hg₂)⟩ : matrixIsometries (coordinateQuadPlus 4 F)) =
            ⟨g₁, hSO hg₁⟩ * ⟨g₂, hSO hg₂⟩ := rfl
        rw [h1, map_mul, Subgroup.coe_mul]
        exact mul_mem ih₁ ih₂
      | inv g hg ih =>
        have h1 : (⟨g⁻¹, hSO (inv_mem hg)⟩ : matrixIsometries (coordinateQuadPlus 4 F)) =
            (⟨g, hSO hg⟩)⁻¹ := rfl
        rw [h1, map_inv, Subgroup.coe_inv]
        exact inv_mem ih
    have h1 := hall _ hcl
    have h2 : (⟨_, hSO hcl⟩ : matrixIsometries (coordinateQuadPlus 4 F)) = Λ ⟨x, hxL⟩ :=
      Subtype.ext rfl
    rw [h2, MulEquiv.symm_apply_apply] at h1
    exact h1
  obtain ⟨g, rfl⟩ := isConj_iff.1 (hs₁.symm.trans hr)
  intro x hx
  have h1 : g⁻¹ * x * g ∈ Subgroup.centralizer ({(s₁ : X)} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc g⁻¹ * x * g * s₁ = g⁻¹ * (x * (g * s₁ * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * s₁ * g⁻¹) * x) * g := by rw [hx]
      _ = s₁ * (g⁻¹ * x * g) := by group
  have h3 : (Subgroup.closure ({x : X | IsConj s x} ∩
      (Subgroup.centralizer ({(s₁ : X)} : Set X) : Set X))).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.closure ({x : X | IsConj s x} ∩
        (Subgroup.centralizer ({g * s₁ * g⁻¹} : Set X) : Set X)) := by
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
    refine ⟨hy1.trans (isConj_iff.2 ⟨g, rfl⟩), ?_⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy2 ⊢
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * y * g⁻¹ * (g * s₁ * g⁻¹) = g * (y * s₁) * g⁻¹ := by group
      _ = g * (s₁ * y) * g⁻¹ := by rw [hy2]
      _ = g * s₁ * g⁻¹ * (g * y * g⁻¹) := by group
  have h4 := h3 (Subgroup.mem_map_of_mem _ (key h1))
  rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h4

end CFSG.LocalAnalysis.WeakClosure81

end

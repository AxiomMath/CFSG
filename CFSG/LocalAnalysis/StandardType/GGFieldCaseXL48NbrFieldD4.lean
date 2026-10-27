module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48NbrField
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds
public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallBIso
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Semilinear

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

namespace NbrFieldD4

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section Triality

variable {θ : MulAut (matrixDerived (coordinateQuadPlus 4 K))}

theorem exists_eq_of_mem_closure_triality (hθ3 : θ ^ 3 = 1)
    (hρθ : AutOm.plusRefl (K := K) (by norm_num : 1 ≤ 4) * θ * AutOm.plusRefl (by norm_num) = θ⁻¹)
    {g : MulAut (matrixDerived (coordinateQuadPlus 4 K))}
    (hg : g ∈ Subgroup.closure {θ, AutOm.plusRefl (K := K) (by norm_num : 1 ≤ 4)}) :
    ∃ k : ℕ, g = θ ^ k ∨ g = θ ^ k * AutOm.plusRefl (K := K) (by norm_num : 1 ≤ 4) := by
  have h14 : 1 ≤ 4 := by norm_num
  have hρ := AutOm.plusRefl_mul_self (K := K) h14
  have hr : ∀ l : ℕ, AutOm.plusRefl (K := K) h14 * θ ^ l = θ ^ (2 * l) * AutOm.plusRefl h14 :=
    AutOm.plusRefl_mul_pow le_rfl hθ3 hρθ
  have hinv : ∀ k : ℕ, (θ ^ k)⁻¹ = θ ^ (2 * k) := fun k => by
    rw [inv_eq_iff_mul_eq_one, ← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, hθ3, one_pow]
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact ⟨1, Or.inl (pow_one _).symm⟩
    · exact ⟨0, Or.inr (by rw [pow_zero, one_mul])⟩
  | one => exact ⟨0, Or.inl (pow_zero _).symm⟩
  | mul g g' _ _ ih ih' =>
    obtain ⟨k, rfl | rfl⟩ := ih <;> obtain ⟨l, rfl | rfl⟩ := ih'
    · exact ⟨k + l, Or.inl (pow_add _ _ _).symm⟩
    · exact ⟨k + l, Or.inr (by rw [pow_add, mul_assoc])⟩
    · exact ⟨k + 2 * l, Or.inr (by rw [mul_assoc, hr, ← mul_assoc, ← pow_add])⟩
    · refine ⟨k + 2 * l, Or.inl ?_⟩
      rw [mul_assoc, ← mul_assoc (AutOm.plusRefl h14), hr, mul_assoc, hρ, mul_one, ← pow_add]
  | inv g _ ih =>
    obtain ⟨k, rfl | rfl⟩ := ih
    · exact ⟨2 * k, Or.inl (hinv k)⟩
    · refine ⟨2 * (2 * k), Or.inr ?_⟩
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_left hρ, hinv, hr]

theorem ggInndiagComm_le_sup_closure
    (hφθ : ∀ σ : K ≃+* K, θ * AutOm.fieldAutP 4 σ = AutOm.fieldAutP 4 σ * θ)
    (hgen : ∀ α : MulAut (matrixDerived (coordinateQuadPlus 4 K)),
      ∃ ι ∈ inner (matrixDerived (coordinateQuadPlus 4 K)), ∃ k : ℕ,
        ∃ c ∈ AutOm.plusCompl (K := K) (by norm_num : 1 ≤ 4), α = ι * (θ ^ k * c)) :
    ggInndiagComm (matrixDerived (coordinateQuadPlus 4 K)) ≤
      inner (matrixDerived (coordinateQuadPlus 4 K)) ⊔
        Subgroup.closure {θ, AutOm.plusRefl (K := K) (by norm_num : 1 ≤ 4)} := by
  have h14 : 1 ≤ 4 := by norm_num
  set T := inner (matrixDerived (coordinateQuadPlus 4 K)) ⊔
    Subgroup.closure {θ, AutOm.plusRefl (K := K) h14}
  have hθT : θ ∈ T := Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_insert _ _))
  have hρT : AutOm.plusRefl (K := K) h14 ∈ T :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  refine sup_le le_sup_left ?_
  rw [Subgroup.commutator_le]
  intro a _ b _
  rw [commutatorElement_def]
  refine commutator_mem_of_eq_mul T (Set.range (AutOm.fieldAutP (K := K) 4)) ?_ ?_ ?_ a b
  · rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
    rw [← map_mul, ← map_mul, ringEquiv_mul_comm_of_finite]
  · rintro _ ⟨σ, rfl⟩ d hd
    have hle : T ≤ T.comap (MulAut.conj (AutOm.fieldAutP 4 σ)).toMonoidHom := by
      refine sup_le (fun ι hι => ?_) ?_
      · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact Subgroup.mem_sup_left ((inner_normal _).conj_mem ι hι _)
      · rw [Subgroup.closure_le]
        rintro g (rfl | rfl)
        · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            ← hφθ σ, mul_inv_cancel_right]
          exact hθT
        · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            ← AutOm.plusRefl_mul_fieldAutP h14 σ, mul_inv_cancel_right]
          exact hρT
    have := hle hd
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  · intro α
    obtain ⟨ι, hι, k, c, hc, rfl⟩ := hgen α
    obtain ⟨σ, rfl | rfl⟩ := hc
    · exact ⟨ι * θ ^ k, mul_mem (Subgroup.mem_sup_left hι) (pow_mem hθT k), _, ⟨σ, rfl⟩,
        by rw [mul_assoc]⟩
    · exact ⟨ι * (θ ^ k * AutOm.plusRefl h14),
        mul_mem (Subgroup.mem_sup_left hι) (mul_mem (pow_mem hθT k) hρT), _, ⟨σ, rfl⟩,
        by simp only [mul_assoc]⟩

theorem eq_one_of_fieldAutP_mem_sup_closure (hθ3 : θ ^ 3 = 1)
    (hρθ : AutOm.plusRefl (K := K) (by norm_num : 1 ≤ 4) * θ * AutOm.plusRefl (by norm_num) = θ⁻¹)
    (huniq : ∀ k : ℕ, ∀ c ∈ AutOm.plusCompl (K := K) (by norm_num : 1 ≤ 4),
      θ ^ k * c ∈ inner (matrixDerived (coordinateQuadPlus 4 K)) → θ ^ k = 1 ∧ c = 1)
    {σ : K ≃+* K}
    (hσ : AutOm.fieldAutP 4 σ ∈ inner (matrixDerived (coordinateQuadPlus 4 K)) ⊔
        Subgroup.closure {θ, AutOm.plusRefl (K := K) (by norm_num : 1 ≤ 4)}) :
    σ = 1 := by
  have h14 : 1 ≤ 4 := by norm_num
  have := inner_normal (matrixDerived (coordinateQuadPlus 4 K))
  obtain ⟨ι, hι, g, hg, hιg⟩ := Subgroup.mem_sup_of_normal_left.mp hσ
  have hι' : ι⁻¹ = g * AutOm.fieldAutP 4 σ⁻¹ := by
    rw [map_inv, ← hιg]
    group
  obtain ⟨k, rfl | rfl⟩ := exists_eq_of_mem_closure_triality hθ3 hρθ hg
  · obtain ⟨-, hc⟩ := huniq k _ ⟨σ⁻¹, Or.inl rfl⟩ (hι' ▸ inv_mem hι)
    exact inv_eq_one.mp (AutOm.eq_one_of_mem_inner_plusCompl (n := 4) (by norm_num) (Or.inl rfl)
      (hc ▸ one_mem _))
  · rw [mul_assoc] at hι'
    obtain ⟨-, hc⟩ := huniq k _ ⟨σ⁻¹, Or.inr rfl⟩ (hι' ▸ inv_mem hι)
    exact inv_eq_one.mp (AutOm.eq_one_of_mem_inner_plusCompl (n := 4) (by norm_num) (Or.inr rfl)
      (hc ▸ one_mem _))

end Triality

theorem eq_one_of_fieldAutP_mem_ggInndiagComm {σ : K ≃+* K}
    (hσ : AutOm.fieldAutP 4 σ ∈ ggInndiagComm (matrixDerived (coordinateQuadPlus 4 K))) :
    σ = 1 := by
  obtain ⟨θ, hθ3, hρθ, hφθ, hgen, huniq, -⟩ := plusFourTrialityInput_holds K
  exact eq_one_of_fieldAutP_mem_sup_closure hθ3 hρθ huniq
    (ggInndiagComm_le_sup_closure hφθ hgen hσ)

theorem ggRawFieldNotComm_omegaPlusFour {p : ℕ} (hp : p ≠ 1) :
    GGRawFieldNotComm p (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4)))) := by
  intro f hf hord hfT
  have h14 : 1 ≤ 4 := by norm_num
  obtain ⟨σ, hσ⟩ := RecipeFieldOmega.congr_plusEquiv_of_mem_field h14 hf
  rw [ggInndiag_eq_range_of_subset subset_rfl] at hfT
  have h1 := (mem_ggInndiagComm_congr_iff (RecipeFieldOmega.plusEquiv (K := K) h14) f).mp hfT
  rw [hσ] at h1
  have hσ1 := eq_one_of_fieldAutP_mem_ggInndiagComm h1
  rw [hσ1, map_one] at hσ
  have hf1 : f = 1 := (MulAut.congr (RecipeFieldOmega.plusEquiv (K := K) h14)).injective
    (hσ.trans (map_one _).symm)
  rw [hf1, orderOf_one] at hord
  exact hp hord.symm

end NbrFieldD4

open NbrFieldD4

theorem largeEvenLabelAll_fieldNotComm_dFour {p : ℕ} (hp : p ≠ 1) {lab : LargeEvenLabel}
    (ht : lab.tag = .D) (h4 : lab.rank = 4) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard (GGRawFieldNotComm p)) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht h4
  subst h4
  exact largeEvenLabelAll_omegaPlus ht le_rfl fun _ _ _ _ _ _ _ =>
    ggRawFieldNotComm_omegaPlusFour hp

end CFSG.StandardType

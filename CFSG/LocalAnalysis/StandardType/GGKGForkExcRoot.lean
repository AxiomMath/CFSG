module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRootRefl
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRootJ
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRootC
public import CFSG.LocalAnalysis.StandardType.GGKGForkTransfer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem ggKGEd_Y_injective
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E) :
    Function.Injective (ggKGExcY F) := by
  intro x y h
  apply Subtype.ext
  apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
  have h3 : F.D.g0 * ggKGExcY F x * F.D.g0⁻¹ = F.D.g0 * ggKGExcY F y * F.D.g0⁻¹ := by
    rw [h]
  rw [ggKGExcY_apply, ggKGExcY_apply] at h3
  calc baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K)
      = F.D.g0 * (F.D.g0⁻¹ *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
          F.D.g0) * F.D.g0⁻¹ := by group
    _ = F.D.g0 * (F.D.g0⁻¹ *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL τ K) *
          F.D.g0) * F.D.g0⁻¹ := h3
    _ = baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL τ K) := by group

private theorem ggKGEd_mem_centralizer_iff
    {τ : Tag} {K : Type} [Field K]
    [Finite K] {p : ℕ} {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E)
    {γ : Fin τ.rank → ℤ} {w : adjointGroup τ K}
    (hwγ : ggKGExcY F w =
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ))
    (e : adjointGroup τ K) :
    e ∈ Subgroup.centralizer ({w} : Set (adjointGroup τ K)) ↔
      ggKGExcY F e ∈ Subgroup.centralizer
        ({canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ)} :
          Set (ModGL τ (AlgebraicClosure K))) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [← hwγ, ← map_mul, ← map_mul, h]
  · intro h
    apply ggKGEd_Y_injective F
    rw [map_mul, map_mul, hwγ]
    exact h

private theorem ggKGEd_isQuasisimple_assembly {Q : Type*} [Group Q]
    (h : CFSG.IsQuasisimple Q) : CFSG.Assembly.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

private theorem ggKGEd_inf_centralizer_eq_hyp
    {τ : Tag} {K : Type} [Field K]
    [Finite K] {p : ℕ} {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E)
    {γ : Fin τ.rank → ℤ} {w : adjointGroup τ K}
    (hwγ : ggKGExcY F w =
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ)) :
    E ⊓ Subgroup.centralizer ({w} : Set (adjointGroup τ K)) = ggKGExcHyp F γ := by
  ext e
  unfold ggKGExcHyp
  simp only [Subgroup.mem_inf, Subgroup.mem_comap]
  constructor
  · rintro ⟨he, hc⟩
    exact ⟨he, (ggKGEd_mem_centralizer_iff F hwγ e).mp hc⟩
  · rintro ⟨he, hc⟩
    exact ⟨he, (ggKGEd_mem_centralizer_iff F hwγ e).mpr hc⟩

theorem ggKGExc_rootDatumAt
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (hp : p.Prime)
    (hp3 : 3 ≤ p) (hτ6 : τ = .E6 → 5 ≤ p) (hpq : p ∣ Nat.card K - 1) (F : ExcFrame τ K p E)
    (hw : F.w = 1) :
    GGKGRootDatumAt p E := by
  intro w₀ hrefl
  obtain ⟨γ, hγ, hγeq⟩ := ggKGExc_reflection_isRoot hτ hp hp3 hτ6 hpq F hw hrefl
  obtain ⟨w, hwJ, hwγ⟩ := ggKGExcJ_weyl hτ F hw hγ
  have h4 : 4 ≤ Nat.card K := by
    have hK1 : 1 < Nat.card K := Finite.one_lt_card
    have hle : p ≤ Nat.card K - 1 := Nat.le_of_dvd (by omega) hpq
    omega
  have hinf : E ⊓ Subgroup.centralizer ({w} : Set (adjointGroup τ K)) = ggKGExcHyp F γ :=
    ggKGEd_inf_centralizer_eq_hyp F hwγ
  refine ⟨w, ?_, ggKGExcJ F γ, hwJ, ?_, ?_, ?_⟩
  · intro e he
    have hleft : ggKGExcY F (w * e * w⁻¹) =
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ) *
          ggKGExcY F e *
          (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ))⁻¹ := by
      rw [map_mul, map_mul, map_inv, hwγ]
    have hright : ggKGExcY F (w₀ * e * w₀⁻¹) =
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ) *
          ggKGExcY F e *
          (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ))⁻¹ := by
      rw [ggKGExcY_apply, ggKGExcY_apply]
      exact hγeq e he
    exact ggKGEd_Y_injective F (hleft.trans hright.symm)
  · rw [hinf]
    exact ⟨ggKGExcJ_le_centralizer hp hp3 F hγ,
      ggKGExcJ_subnormal hτ hp hp3 hτ6 hpq F hw hγ,
      ggKGEd_isQuasisimple_assembly (ggKGExcJ_quasisimple hτ F hw hγ h4)⟩
  · exact ggKGExcJ_dvd_card hτ F hw hγ hpq
  · intro a ha haw
    apply ggKGExcJ_layer hτ hp hp3 F hw hγ h4
    rw [← hinf]
    exact ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr haw.symm⟩

end CFSG.StandardType
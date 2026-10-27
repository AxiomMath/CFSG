module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.StandardType.GGL45HFourD4Three

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggL45NtHFourD4_exists_mul_ne {R : Type*} [Group R] [IsSimpleGroup R]
    (hperf : commutator R = ⊤) : ∃ a b : R, a * b ≠ b * a := by
  haveI : Group.IsPerfect R := Group.isPerfect_def.mpr hperf
  haveI : Nontrivial R := IsSimpleGroup.toNontrivial
  have hnc : ¬ IsMulCommutative R := Group.IsPerfect.not_isMulCommutative R
  rw [isMulCommutative_iff] at hnc
  push Not at hnc
  exact hnc

private theorem ggL45NtHFourD4_commutator_eq_top_of_centerQuot {K R : Type*} [Group K] [Group R]
    (hK : commutator K = ⊤) (θ : K ⧸ Subgroup.center K ≃* R) : commutator R = ⊤ := by
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hK
  haveI hQ : Group.IsPerfect (K ⧸ Subgroup.center K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center K))
      (QuotientGroup.mk'_surjective (Subgroup.center K))
  exact (Group.IsPerfect.ofSurjective (f := θ.toMonoidHom) θ.surjective).commutator_eq_top

private theorem ggL45NtHFourD4_isSimpleGroup_recipe (K : Type) [Field K] [Finite K] [CharP K 2] :
    IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) :=
  CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus
    (K := K) (n := 4) (by norm_num)

private theorem ggL45NtHFourD4_eq_inducedAut {X : Type*} [Group X] {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) (α : MulAut X) (φ : MulAut R)
    (h : LargeEvenInduces θ (fun x x' => x' = α x) φ) : ggInducedAut θ α = φ := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H l =>
      rw [ggInducedAut_apply]
      exact (h l (α l) rfl).symm

theorem ggL45H4Raw_d4_three {lab : LargeEvenLabel} (ht : lab.tag = .D) (h4 : lab.rank = 4) :
    LargeEvenLabelAll lab (GGL45H4Raw 3 lab) := by
  have hmod := ggL45HFourMod_d4_three ht h4
  have hfield : LargeEvenLabelAll lab (GGRawInnField 3) :=
    largeEvenLabelAll_omegaPlus ht (by omega)
      (fun K _ _ _ _ => RecipeFieldOmega.ggRawInnField_omegaPlus (by omega) (by norm_num))
  have hsimple : LargeEvenLabelAll lab (fun R _ _ _ => IsSimpleGroup R) :=
    largeEvenLabelAll_omegaPlus ht (by omega) (fun K _ _ _ _ => by
      rw [h4]
      exact ggL45NtHFourD4_isSimpleGroup_recipe K)
  refine LargeEvenLabelAll.mono ?_
    (largeEvenLabelAll_and (largeEvenLabelAll_and hmod hfield) hsimple)
  rintro R _ I F ⟨⟨hA, hB⟩, hC⟩
  intro K _ _ θ hK ψ E hyp
  obtain ⟨hψ, ⟨f, hf, u, hu, hord, hind⟩, hE, _hcard, hD4, hEI, hEψ, _hsat, _hrk, _hpi⟩ := hyp
  have hnc : ∃ a b : R, a * b ≠ b * a :=
    ggL45NtHFourD4_exists_mul_ne (ggL45NtHFourD4_commutator_eq_top_of_centerQuot hK θ)
  obtain ⟨hBmul, hBinv, _hBconj, hBf⟩ := hB hC hnc
  have hfI : f ∉ I := hBf f hf hord
  have hψbar_eq : ggInducedAut θ ψ = u * f * u⁻¹ :=
    ggL45NtHFourD4_eq_inducedAut θ ψ (u * f * u⁻¹) hind
  have hψbarI : ggInducedAut θ ψ ∉ I := by
    intro hmem
    have h1 : u⁻¹ * ggInducedAut θ ψ * u ∈ I :=
      hBmul (u⁻¹ * ggInducedAut θ ψ)
        (hBmul u⁻¹ (hBinv u hu) (ggInducedAut θ ψ) hmem) u hu
    have hfeq : u⁻¹ * ggInducedAut θ ψ * u = f := by rw [hψbar_eq]; group
    exact hfI (hfeq ▸ h1)
  have hψbar3 : ggInducedAut θ ψ ^ 3 = 1 := by rw [← map_pow, hψ, map_one]
  have hψbarE : ∀ e ∈ E, ggInducedAut θ ψ * ggInducedAut θ e =
      ggInducedAut θ e * ggInducedAut θ ψ := by
    intro e he
    rw [← map_mul, ← map_mul, hEψ e he]
  have h27 : 27 ≤ Nat.card E := by
    have h := hD4 ht h4 rfl
    norm_num at h
    exact h
  exact hA (K := K) θ hK E hE h27 hEI (ggInducedAut θ ψ) hψbar3 hψbarI hψbarE

end CFSG.StandardType

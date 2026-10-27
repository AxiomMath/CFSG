module

public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankClass
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaPlus

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGD4TrialityCentBound {R : Type} [Group R] (I F : Set (MulAut R)) : Prop :=
  ∀ φ : MulAut R, φ ^ 3 = 1 → (¬ ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, φ = u * f) →
    ∀ E : Subgroup R, IsElemAbelian 3 E → (∀ e ∈ E, φ e = e) → Nat.card E ≤ 9

namespace NbrGraphD4

open CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem mem_inner_sup_of_conjAct {α : MulAut (Om8 K)} (hα3 : α ^ 3 = 1)
    {g : similarityPairs (coordinateQuadPlus 4 K)} (hg : conjAct _ g = α) :
    α ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range := by
  obtain ⟨ι, hι, c, hc, hgc⟩ := exists_inner_mul_plusCompl_of_pair g
  rw [hg] at hgc
  obtain ⟨σ, rfl | rfl⟩ := hc
  · rw [hgc]
    exact Subgroup.mul_mem_sup hι ⟨σ, rfl⟩
  · obtain ⟨γ, rfl⟩ := hι
    set r : MulAut (Om8 K) := AutOm.plusRefl one_le_four with hr_def
    set f : MulAut (Om8 K) := AutOm.fieldAutP 4 σ with hf_def
    have hr : r * r = 1 := AutOm.plusRefl_mul_self one_le_four
    have h2 : r * f = f * r := AutOm.plusRefl_mul_fieldAutP one_le_four σ
    obtain ⟨γ', hγ'⟩ := D4Rank.conj_mul_cube (r * f) γ
    have hcube : (1 * (r * f)) ^ 3 = 1 * (r * f ^ 3) :=
      D4Rank.beta_cube (t := (1 : MulAut (Om8 K))) (by rw [one_mul, mul_one]) h2
        (by rw [mul_one, hr, inv_one])
    simp only [one_mul] at hcube
    rw [← hgc, hα3, hcube] at hγ'
    have hinn : r * f ^ 3 = MulAut.conj γ'⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_right hγ'.symm
    have hmem : (theta : MulAut (Om8 K)) ^ 0 * (r * AutOm.fieldAutP 4 (σ ^ 3)) ∈
        Inn (Om8 K) := by
      rw [pow_zero, one_mul, map_pow, ← hf_def, hinn]
      exact ⟨_, rfl⟩
    have h1 := (theta_pow_mul_mem_inner 0 ⟨σ ^ 3, Or.inr rfl⟩ hmem).2
    have hrf : r * f = AutOm.fieldAutP 4 ((σ ^ 3)⁻¹ * σ) := by
      rw [map_mul, map_inv, ← hf_def, ← eq_inv_of_mul_eq_one_left h1]
    rw [hgc, hrf]
    exact Subgroup.mul_mem_sup ⟨γ, rfl⟩ ⟨_, rfl⟩

theorem card_le_nine_of_not_mem {α : MulAut (Om8 K)} (hα3 : α ^ 3 = 1)
    (hα : α ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range) {E : Subgroup (Om8 K)}
    (hE : IsElemAbelian 3 E) (hfix : ∀ e ∈ E, α e = e) : Nat.card E ≤ 9 :=
  D4Rank.card_le_nine_of_classInput D4Rank.ggD4TrialityClassInput_holds α hα3
    (fun _ hg => hα (mem_inner_sup_of_conjAct hα3 hg)) E hE hfix

omit [Finite K] in
theorem exists_inner_mul_field_of_mem
    {φ : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))}
    (h : MulAut.congr (RecipeFieldOmega.plusEquiv (K := K) one_le_four) φ ∈
      Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range) :
    ∃ u ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))),
      ∃ f ∈ Subgroup.closure
        (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4)))),
        φ = u * f := by
  set Θ := RecipeFieldOmega.plusEquiv (K := K) one_le_four
  obtain ⟨ι, hι, _, ⟨σ, rfl⟩, hs⟩ := Subgroup.mem_sup_of_normal_left.1 h
  obtain ⟨ψ, hψ, hψσ⟩ := RecipeFieldOmega.exists_mem_field_congr_plusEquiv one_le_four σ
  refine ⟨(MulAut.congr Θ).symm ι, (RecipeFieldOmega.mem_innSet_iff_congr Θ _).2 (by
    rwa [MulEquiv.apply_symm_apply]), ψ, Subgroup.subset_closure hψ, ?_⟩
  apply (MulAut.congr Θ).injective
  rw [map_mul, MulEquiv.apply_symm_apply, hψσ, hs]

theorem card_le_of_congr {R Γ : Type} [Group R] [Group Γ] (Θ : R ≃* Γ) {φ : MulAut R} {n : ℕ}
    (hΓ : ∀ E : Subgroup Γ, IsElemAbelian 3 E → (∀ e ∈ E, MulAut.congr Θ φ e = e) →
      Nat.card E ≤ n)
    {E : Subgroup R} (hE : IsElemAbelian 3 E) (hfix : ∀ e ∈ E, φ e = e) : Nat.card E ≤ n := by
  have hE' : IsElemAbelian 3 (E.map Θ.toMonoidHom) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a, ha, rfl⟩⟩ := a
      obtain ⟨_, ⟨b, hb, rfl⟩⟩ := b
      apply Subtype.ext
      change Θ a * Θ b = Θ b * Θ a
      rw [← map_mul, ← map_mul,
        show a * b = b * a from congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)]
    · rintro _ ⟨a, ha, rfl⟩
      change Θ a ^ 3 = 1
      rw [← map_pow, hE.2 a ha, map_one]
  have hfix' : ∀ e ∈ E.map Θ.toMonoidHom, MulAut.congr Θ φ e = e := by
    rintro _ ⟨e, he, rfl⟩
    change Θ (φ (Θ.symm (Θ e))) = Θ e
    rw [MulEquiv.symm_apply_apply, hfix e he]
  have h := hΓ _ hE' hfix'
  rwa [Subgroup.card_map_of_injective Θ.injective] at h

theorem ggD4TrialityCentBound_omegaPlus :
    GGD4TrialityCentBound (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4)))) := by
  intro φ hφ3 hnot E hE hfix
  refine card_le_of_congr (RecipeFieldOmega.plusEquiv (K := K) one_le_four)
    (fun E' hE' hfix' => card_le_nine_of_not_mem ?_ ?_ hE' hfix') hE hfix
  · rw [← map_pow, hφ3, map_one]
  · exact fun h => hnot (exists_inner_mul_field_of_mem h)

end NbrGraphD4

theorem largeEvenLabelAll_d4TrialityCentBound {lab : LargeEvenLabel} (ht : lab.tag = .D)
    (h4 : lab.rank = 4) : LargeEvenLabelAll lab fun _ _ I F => GGD4TrialityCentBound I F := by
  refine largeEvenLabelAll_omegaPlus ht (by omega) fun K _ _ _ _ => ?_
  rw [h4]
  exact NbrGraphD4.ggD4TrialityCentBound_omegaPlus

end CFSG.StandardType

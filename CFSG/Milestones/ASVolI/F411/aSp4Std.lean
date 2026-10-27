module

public import CFSG.RankThree.PartOne.AUTSL.SpTwoAut

public section

namespace CFSG.ASVolI

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.AUTSL.SpTwo

section Sp4Std

variable {K : Type} [Field K]

variable (K) in
@[expose] def burnsideF411a_longRoot : Set (StatedProj (StatedSp 2 K)) :=
  Set.range fun a : K => proj 2 K (tv a)

theorem burnsideF411a_longRoot_subset :
    burnsideF411a_longRoot K ⊆ (projUnipotent 2 K : Set (StatedProj (StatedSp 2 K))) := by
  rintro _ ⟨a, rfl⟩
  exact Subgroup.mem_map_of_mem _ (tv_mem_unipotent a)

theorem burnsideF411a_mulVec_eOne_of_normalizer (g : StatedSp 2 K)
    (hg : proj 2 K g ∈ Subgroup.normalizer (burnsideF411a_longRoot K)) :
    ∃ l : K, mat g *ᵥ eOne = l • eOne := by
  obtain ⟨a', ha'⟩ := (Subgroup.mem_set_normalizer_iff.1 hg (proj 2 K (tv 1))).1 ⟨1, rfl⟩
  have h3 : proj 2 K (g * tv 1 * g⁻¹) = proj 2 K (tv a') := by
    rw [map_mul, map_mul, map_inv]
    exact ha'.symm
  have hs : (tv a')⁻¹ * (g * tv 1 * g⁻¹) ∈ spScalars 2 K := QuotientGroup.eq.1 h3.symm
  obtain ⟨c, hc⟩ : ∃ c : Kˣ,
      Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c =
        (((tv a')⁻¹ * (g * tv 1 * g⁻¹) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) := by
    have := Subgroup.mem_subgroupOf.1 hs
    obtain ⟨c, hc⟩ := (show _ ∈ (Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2)).range from this)
    exact ⟨c, hc⟩
  have hM : mat (g * tv 1 * g⁻¹) = mat (tv a') * Matrix.scalar (Fin 2 ⊕ Fin 2) (c : K) := by
    have h4 : mat ((tv a')⁻¹ * (g * tv 1 * g⁻¹)) = Matrix.scalar (Fin 2 ⊕ Fin 2) (c : K) := by
      have := congrArg
        (fun x : GL (Fin 2 ⊕ Fin 2) K => (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hc
      simp only [Matrix.GeneralLinearGroup.coe_scalar] at this
      exact this.symm
    have h5 : mat (tv a') * mat ((tv a')⁻¹ * (g * tv 1 * g⁻¹)) = mat (g * tv 1 * g⁻¹) := by
      rw [← mat_mul, mul_inv_cancel_left]
    rw [← h5, h4]
  refine exists_mulVec_eOne_of_conj g a' (c : K) fun v => ?_
  have hsv : (Matrix.scalar (Fin 2 ⊕ Fin 2) (c : K)) *ᵥ v = (c : K) • v := by
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  rw [hM, ← mulVec_mulVec, hsv, mulVec_smul]

theorem burnsideF411a_normalizer_longRoot :
    Subgroup.normalizer (burnsideF411a_longRoot K) = projStabilizer 2 K (flag 2 K 1) := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, rfl⟩ := proj_surjective x
    refine ⟨g, ?_, rfl⟩
    exact mem_stabilizer_flag_one (burnsideF411a_mulVec_eOne_of_normalizer g hx)
      (burnsideF411a_mulVec_eOne_of_normalizer g⁻¹ (by
        rw [map_inv]
        exact inv_mem hx))
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨l, hl⟩ := exists_mulVec_eOne hg
    obtain ⟨l', hl'⟩ := exists_mulVec_eOne (inv_mem hg : g⁻¹ ∈ stabilizer 2 K (flag 2 K 1))
    rw [Subgroup.mem_set_normalizer_iff]
    intro z
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨l * l * a, ?_⟩
      show proj 2 K (tv (l * l * a)) = proj 2 K g * proj 2 K (tv a) * (proj 2 K g)⁻¹
      rw [← map_inv, ← map_mul, ← map_mul, conj_tv_of_mulVec_eq g a l hl]
    · rintro ⟨a, ha⟩
      dsimp only at ha
      refine ⟨l' * l' * a, ?_⟩
      have hz : z = proj 2 K g⁻¹ * proj 2 K (tv a) * (proj 2 K g⁻¹)⁻¹ := by
        rw [ha, map_inv]
        group
      show proj 2 K (tv (l' * l' * a)) = z
      rw [hz, ← conj_tv_of_mulVec_eq g⁻¹ a l' hl']
      simp only [map_mul, map_inv]

theorem burnsideF411a_map_normalizer_of_fix {G : Type*} [Group G] (X : Set G) (α : MulAut G)
    (hα : ∀ x ∈ X, α x = x) :
    (Subgroup.normalizer X).map α.toMonoidHom = Subgroup.normalizer X := by
  have key : ∀ β : MulAut G, (∀ x ∈ X, β x = x) →
      (Subgroup.normalizer X).map β.toMonoidHom ≤ Subgroup.normalizer X := by
    intro β hβ
    have hβs : ∀ x ∈ X, β.symm x = x := fun x hx => by
      rw [MulEquiv.symm_apply_eq, hβ x hx]
    rintro _ ⟨g, hg', rfl⟩
    have hg := Subgroup.mem_set_normalizer_iff.mp hg'
    rw [Subgroup.mem_set_normalizer_iff]
    intro n
    constructor
    · intro hn
      have h1 := (hg n).1 hn
      have h2 : β.toMonoidHom g * n * (β.toMonoidHom g)⁻¹ = β (g * n * g⁻¹) := by
        rw [map_mul, map_mul, map_inv, hβ n hn]
        rfl
      rw [h2, hβ _ h1]
      exact h1
    · intro hn
      have hnm : n = β (β.symm n) := (MulEquiv.apply_symm_apply β n).symm
      have h2 : β.toMonoidHom g * n * (β.toMonoidHom g)⁻¹ = β (g * β.symm n * g⁻¹) := by
        rw [map_mul, map_mul, map_inv, ← hnm]
        rfl
      rw [h2] at hn
      have h3 : g * β.symm n * g⁻¹ ∈ X := by
        have := hβs _ hn
        rw [MulEquiv.symm_apply_apply] at this
        rw [this]
        exact hn
      have h4 : β.symm n ∈ X := (hg _).2 h3
      rw [hnm, hβ _ h4]
      exact h4
  refine le_antisymm (key α hα) fun g hg => ?_
  have hαs : ∀ x ∈ X, α.symm x = x := fun x hx => by
    rw [MulEquiv.symm_apply_eq, hα x hx]
  exact ⟨α.symm g, key α.symm hαs ⟨g, hg, rfl⟩, by simp⟩

theorem burnsideF411a_map_pointStab (α : MulAut (StatedProj (StatedSp 2 K)))
    (hα : ∀ x ∈ projUnipotent 2 K, α x = x) :
    (projStabilizer 2 K (flag 2 K 1)).map α.toMonoidHom = projStabilizer 2 K (flag 2 K 1) := by
  rw [← burnsideF411a_normalizer_longRoot]
  exact burnsideF411a_map_normalizer_of_fix _ α fun x hx =>
    hα x (burnsideF411a_longRoot_subset hx)

theorem burnsideF411a_map_projStabilizer_point (α : MulAut (StatedProj (StatedSp 2 K)))
    (h0 : (projStabilizer 2 K (flag 2 K 1)).map α.toMonoidHom = projStabilizer 2 K (flag 2 K 1))
    (L : SpPoint 2 K) :
    ∃ L' : SpPoint 2 K, (projStabilizer 2 K L.line).map α.toMonoidHom =
      projStabilizer 2 K L'.line := by
  let L₀ : SpPoint 2 K := SpPoint.ofVec eOne (single_ne_zero _)
  have hL₀ : L₀.line = flag 2 K 1 := by rw [line_ofVec, flag_one_eq_span]
  obtain ⟨g, hg⟩ := exists_smul_eq_point L₀ L
  obtain ⟨g', hg'⟩ := proj_surjective (α (proj 2 K g))
  refine ⟨g' • L₀, ?_⟩
  rw [← hg, line_smul, line_smul, projStabilizer_map_spAct, projStabilizer_map_spAct, hL₀,
    Subgroup.map_map]
  have e2 : α.toMonoidHom.comp (MulAut.conj (proj 2 K g)).toMonoidHom =
      (MulAut.conj (proj 2 K g')).toMonoidHom.comp α.toMonoidHom := by
    ext y
    simp [MulAut.conj_apply, hg']
  rw [e2, ← Subgroup.map_map, h0]

theorem burnsideF411a_sp4_exists_pointEquiv [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (α : MulAut (StatedProj (StatedSp 2 K)))
    (h0 : (projStabilizer 2 K (flag 2 K 1)).map α.toMonoidHom = projStabilizer 2 K (flag 2 K 1)) :
    ∃ f : SpPoint 2 K ≃ SpPoint 2 K, ∀ L : SpPoint 2 K,
      (projStabilizer 2 K L.line).map α.toMonoidHom = projStabilizer 2 K (f L).line := by
  classical
  obtain ⟨-, -, hinj⟩ := maximal_parabolics (K := K) p (by omega : 1 ≤ 2)
  have hη : Function.Injective fun L : SpPoint 2 K => projStabilizer 2 K L.line :=
    fun L M h => SpPoint.ext (hinj _ _ L.line_ne_bot (isTotallyIsotropic_line L)
      M.line_ne_bot (isTotallyIsotropic_line M) h)
  choose f₀ hf₀ using burnsideF411a_map_projStabilizer_point α h0
  have hinj' : Function.Injective f₀ := fun L₁ L₂ h => by
    have h1 : (projStabilizer 2 K L₁.line).map α.toMonoidHom =
        (projStabilizer 2 K L₂.line).map α.toMonoidHom := by
      rw [hf₀, hf₀, h]
    exact hη (Subgroup.map_injective (f := α.toMonoidHom) α.injective h1)
  exact ⟨Equiv.ofBijective f₀ ⟨hinj', Finite.injective_iff_surjective.mp hinj'⟩, hf₀⟩

theorem burnsideF411a_sp4_standard_of_fix [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (α : MulAut (StatedProj (StatedSp 2 K))) (hα : ∀ x ∈ projUnipotent 2 K, α x = x) :
    ∃ (A : gsp 2 K) (σ : K ≃+* K), α = conjAut 2 K A * fieldAut 2 K σ := by
  classical
  obtain ⟨-, -, hinj⟩ := maximal_parabolics (K := K) p (by omega : 1 ≤ 2)
  have hη : Function.Injective fun L : SpPoint 2 K => projStabilizer 2 K L.line :=
    fun L M h => SpPoint.ext (hinj _ _ L.line_ne_bot (isTotallyIsotropic_line L)
      M.line_ne_bot (isTotallyIsotropic_line M) h)
  obtain ⟨f, hf⟩ := burnsideF411a_sp4_exists_pointEquiv p α (burnsideF411a_map_pointStab α hα)
  obtain ⟨A, σ, μ, hA, hfL⟩ :=
    geometric_semilinear_realization (by omega : 2 ≤ 2) f
      (automorphism_orthogonality_two α f hf)
  refine ⟨⟨A, μ, hA⟩, σ, LinearFlag.equivariant_subgroup_rigidity
    (fun L : SpPoint 2 K => projStabilizer 2 K L.line) hη projStabilizer_smul α _ f
    f.bijective hf fun L => ?_⟩
  rw [map_projStabilizer_conjAut_mul_fieldAut, ← hfL L]

end Sp4Std

end CFSG.ASVolI

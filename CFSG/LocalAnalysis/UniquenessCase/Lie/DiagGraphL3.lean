module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.DiagGraphCore
public import CFSG.LocalAnalysis.UniquenessCase.Lie.Shared
public import CFSG.Milestones.ASVolI.A2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup Module Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Std

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem uc22pdiag_projSL_cover (hn : 1 ≤ n) (Q : Sylow 2 (projectiveSL n K))
    (P : Subgroup (projectiveSL n K)) (hP : IsCoatom P) (hN : normalizer (Q : Set (projectiveSL n K)) ≤ P) :
    ∃ F ∈ {F : Subgroup (projectiveSL n K) | ∃ d, 1 ≤ d ∧ d < n ∧ F = projStabilizer (flagSpace n K d)},
      ∃ h : projectiveSL n K, P = F.map (MulAut.conj h).toMonoidHom := by
  have hmem : P ∈ maximalParabolics (projectiveSL n K) 2 := ⟨hP, _, ⟨Q, rfl⟩, hN⟩
  rw [(maximal_parabolics (K := K) 2 hn).1] at hmem
  obtain ⟨W, ⟨h0, htop⟩, rfl⟩ := hmem
  obtain ⟨g, hg⟩ := exists_map_flagSpace_eq W
  obtain ⟨hd, hdn⟩ := one_le_finrank_and_lt h0 htop
  refine ⟨projStabilizer (flagSpace n K (finrank K W)), ⟨_, hd, hdn, rfl⟩, proj n K g, ?_⟩
  have := projStabilizer_map_conj g (flagSpace n K (finrank K W))
  rw [hg] at this
  exact this.symm

theorem uc22pdiag_classPres_conjAut (hn : 1 ≤ n) (A : GL (Fin n) K) :
    uc22pdiag_ClassPres (projectiveSL n K) (conjAut n K A) := by
  refine uc22pdiag_ClassPres_of_std _ (fun Q P hP hN => uc22pdiag_projSL_cover hn Q P hP hN) ?_
  rintro F ⟨d, hd, hdn, rfl⟩
  have hinj : Function.Injective (mulVecLin (A : Matrix (Fin n) (Fin n) K)) :=
    Matrix.mulVec_injective_iff_isUnit.2 A.isUnit
  have hfin : finrank K (flagSpace n K d) =
      finrank K ((flagSpace n K d).map (mulVecLin (A : Matrix (Fin n) (Fin n) K))) :=
    LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _)
  obtain ⟨g, hg⟩ := exists_map_eq_of_finrank_eq hfin
  refine ⟨proj n K g, ?_⟩
  have h1 := (standard_automorphism_transport (K := K) (n := n)).2.2.2.2.2.2.1 A (flagSpace n K d)
  have h2 := projStabilizer_map_conj g (flagSpace n K d)
  rw [hg] at h2
  exact h1.trans h2.symm

theorem uc22pdiag_classPres_fieldAut (hn : 1 ≤ n) (σ : K ≃+* K) :
    uc22pdiag_ClassPres (projectiveSL n K) (fieldAut n K σ) := by
  refine uc22pdiag_ClassPres_of_std _ (fun Q P hP hN => uc22pdiag_projSL_cover hn Q P hP hN) ?_
  rintro F ⟨d, hd, hdn, rfl⟩
  have hF : coordImage σ (flagSpace n K d) = flagSpace n K d := by
    ext v
    rw [mem_coordImage, mem_flagSpace, mem_flagSpace]
    exact forall_congr' fun j => forall_congr' fun _ => by simp
  refine ⟨1, ?_⟩
  have h1 := (standard_automorphism_transport (K := K) (n := n)).2.2.2.2.2.2.2.1 σ (flagSpace n K d)
  rw [hF] at h1
  exact h1.trans (uc22pdiag_map_conj_one _).symm

end Std

section Stated

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

open CFSG.Assembly.LowTwoRank CFSG.ASVolI.ChA CFSG.Open

@[expose] noncomputable def uc22pdiag_statedEquiv (n : ℕ) (K : Type) [Field K] :
    StatedProj (StatedSL n K) ≃* projectiveSL n K :=
  (projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)

theorem uc22pdiag_stated_mk (A : SpecialLinearGroup (Fin n) K) :
    uc22pdiag_statedEquiv n K (QuotientGroup.mk (specialLinearGroupEquivStatedSL n K A)) =
      proj n K A := by
  have h : (projectiveSpecialLinearGroupEquivStatedProj n K) (QuotientGroup.mk A) =
      QuotientGroup.mk (specialLinearGroupEquivStatedSL n K A) := rfl
  change LinearCover.projectiveSpecialLinearEquivProjectiveSL n K
    ((projectiveSpecialLinearGroupEquivStatedProj n K).symm
      (QuotientGroup.mk (specialLinearGroupEquivStatedSL n K A))) = _
  rw [← h, MulEquiv.symm_apply_apply]
  rfl

theorem uc22pdiag_congr_proj (φ : MulAut (StatedProj (StatedSL n K))) (A : SpecialLinearGroup (Fin n) K) :
    MulAut.congr (uc22pdiag_statedEquiv n K) φ (proj n K A) =
      uc22pdiag_statedEquiv n K (φ (QuotientGroup.mk (specialLinearGroupEquivStatedSL n K A))) := by
  have hA : (uc22pdiag_statedEquiv n K).symm (proj n K A) =
      QuotientGroup.mk (specialLinearGroupEquivStatedSL n K A) :=
    ((uc22pdiag_statedEquiv n K).symm_apply_eq).2 (uc22pdiag_stated_mk A).symm
  change uc22pdiag_statedEquiv n K (φ ((uc22pdiag_statedEquiv n K).symm (proj n K A))) = _
  rw [hA]

theorem uc22pdiag_classPres_L_conj (hn : 1 ≤ n) (c : GL (Fin n) K)
    (φ : MulAut (StatedProj (StatedSL n K))) (h : IsProjConjAut (StatedSL n K) c φ) :
    uc22pdiag_ClassPres (StatedProj (StatedSL n K)) φ := by
  refine uc22pdiag_ClassPres_of_congr (uc22pdiag_statedEquiv n K) φ ?_
  have hφ : MulAut.congr (uc22pdiag_statedEquiv n K) φ = conjAut n K c := by
    ext x
    obtain ⟨A, rfl⟩ := proj_surjective n K x
    rw [uc22pdiag_congr_proj, conjAut_proj]
    obtain ⟨g', hg', hφg⟩ := h (specialLinearGroupEquivStatedSL n K A)
    rw [hφg]
    have : g' = specialLinearGroupEquivStatedSL n K
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K c A) :=
      Subtype.ext (Units.ext (by
        have h1 : ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (c : Matrix (Fin n) (Fin n) K) *
            (A : Matrix (Fin n) (Fin n) K) * ((c⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [hg']; rfl
        rw [h1, specialLinearGroupEquivStatedSL_coe, coe_slConjugation]))
    rw [this]
    exact uc22pdiag_stated_mk _
  rw [hφ]
  exact uc22pdiag_classPres_conjAut hn c

theorem uc22pdiag_classPres_L_field (hn : 1 ≤ n) (σ : K ≃+* K) (φ : MulAut (StatedProj (StatedSL n K)))
    (h : IsProjFieldAut (StatedSL n K) σ φ) : uc22pdiag_ClassPres (StatedProj (StatedSL n K)) φ := by
  refine uc22pdiag_ClassPres_of_congr (uc22pdiag_statedEquiv n K) φ ?_
  have hφ : MulAut.congr (uc22pdiag_statedEquiv n K) φ = fieldAut n K σ := by
    ext x
    obtain ⟨A, rfl⟩ := proj_surjective n K x
    rw [uc22pdiag_congr_proj, fieldAut_proj]
    obtain ⟨g', hg', hφg⟩ := h (specialLinearGroupEquivStatedSL n K A)
    rw [hφg]
    have : g' = specialLinearGroupEquivStatedSL n K (SpecialLinearGroup.map σ.toRingHom A) :=
      Subtype.ext (Units.ext (by rw [hg', specialLinearGroupEquivStatedSL_coe]; rfl))
    rw [this]
    exact uc22pdiag_stated_mk _
  rw [hφ]
  exact uc22pdiag_classPres_fieldAut hn σ

end Stated

section TwoClasses

open CFSG.Blueprint (LieModel)

theorem uc22pdiag_twoClasses_projSL3 {K : Type} [Field K] [Finite K] [CharP K 2]
    (V₀ : Sylow 2 (projectiveSL 3 K)) (hV₀ : (V₀ : Subgroup _) = projUnitriangular 3 K) :
    uc22pdiag_TwoClasses (projectiveSL 3 K) (V₀ : Subgroup (projectiveSL 3 K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : normalizer ((V₀ : Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K)) =
      projUpperTriangular 3 K := by
    rw [hV₀]; exact normalizer_projUnitriangular 2
  let Q : ℕ → Subgroup (projectiveSL 3 K) := fun d => projStabilizer (flagSpace 3 K d)
  have hrefl : ∀ (i j : ℕ) (hj : 1 ≤ j) (hjn : j < 3),
      proj 3 K (reflection 3 K j hj hjn) ∈ Q i ↔ i ≠ j := by
    intro i j hj hjn
    constructor
    · intro h hij
      subst hij
      have : reflection 3 K i hj hjn ∈ stabilizer (flagSpace 3 K i) := by
        rw [← comap_projStabilizer]; exact h
      exact reflection_notMem_stabilizer hj hjn this
    · intro hij
      exact ⟨_, reflection_mem_stabilizer_of_ne hj hjn hij, rfl⟩
  refine ⟨Q 1, Q 2, ?_, isCoatom_projStabilizer_flagSpace (by norm_num) (by norm_num),
    isCoatom_projStabilizer_flagSpace (by norm_num) (by norm_num), ?_, ?_, ?_, ?_⟩
  · intro h
    have := (hrefl 1 2 (by norm_num) (by norm_num)).2 (by norm_num)
    rw [show Q 1 = Q 2 from h] at this
    exact (hrefl 2 2 (by norm_num) (by norm_num)).1 this rfl
  · rw [hN]; exact projUpperTriangular_le_projStabilizer 1
  · rw [hN]; exact projUpperTriangular_le_projStabilizer 2
  · intro P hP hNP
    rw [hN] at hNP
    obtain ⟨d, h1, h2, rfl⟩ := eq_projStabilizer_of_isCoatom hP hNP
    interval_cases d
    · left; rfl
    · right; rfl
  · intro g hg
    obtain ⟨g', rfl⟩ := proj_surjective 3 K g
    have hg' : projStabilizer ((flagSpace 3 K 1).map (mulVecLin (g' : Matrix (Fin 3) (Fin 3) K))) =
        projStabilizer (flagSpace 3 K 2) := by
      rw [← projStabilizer_map_conj]; exact hg
    obtain ⟨hM, hinj, -⟩ := maximal_parabolics (K := K) 2 (n := 3) (by norm_num)
    have hfin : finrank K ((flagSpace 3 K 1).map (mulVecLin (g' : Matrix (Fin 3) (Fin 3) K))) = 1 :=
      (LinearEquiv.finrank_map_eq (SpecialLinearGroup.toLin' g') _).trans
        (finrank_flagSpace (by norm_num))
    have hW1 : (⊥ < (flagSpace 3 K 1).map (mulVecLin (g' : Matrix (Fin 3) (Fin 3) K)) ∧
        (flagSpace 3 K 1).map (mulVecLin (g' : Matrix (Fin 3) (Fin 3) K)) < ⊤) :=
      bot_lt_and_lt_top_of_finrank (by omega) (by omega)
    have hW2 : (⊥ < flagSpace 3 K 2 ∧ flagSpace 3 K 2 < ⊤) :=
      bot_lt_and_lt_top_of_finrank (by rw [finrank_flagSpace (by norm_num)]; norm_num)
        (by rw [finrank_flagSpace (by norm_num)]; norm_num)
    have heq := hinj hW1 hW2 hg'
    rw [heq, finrank_flagSpace (by norm_num : 2 ≤ 3)] at hfin
    omega

theorem uc22pdiag_twoClasses_L3 {M : Type} [Group M] [Finite M] {n : ℕ} (h : LieModel M .PSL 3 2 n)
    (V : Sylow 2 M) : uc22pdiag_TwoClasses M (V : Subgroup M) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  haveI : CharP K 2 := uc22pwlie_charP_two hK
  obtain ⟨V₀, hV₀⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  let VN : Sylow 2 (projectiveSL 3 K) := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective V
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (projectiveSL 3 K) V₀ VN
  have h1 := uc22pdiag_TwoClasses_map (MulAut.conj k) (uc22pdiag_twoClasses_projSL3 V₀ hV₀)
  have hVN : (V₀ : Subgroup _).map (MulAut.conj k).toMonoidHom = (VN : Subgroup _) := by
    rw [← hk]; rfl
  rw [hVN] at h1
  have h2 := uc22pdiag_TwoClasses_map e.symm h1
  have hback : (VN : Subgroup _).map e.symm.toMonoidHom = (V : Subgroup M) := by
    change ((V : Subgroup M).map e.toMonoidHom).map e.symm.toMonoidHom = _
    rw [Subgroup.map_map]
    have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id M := by ext x; simp
    rw [this, Subgroup.map_id]
  rwa [hback] at h2

end TwoClasses

end CFSG.LocalAnalysis.UniquenessCase.UC22

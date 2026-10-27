module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.DiagGraphCore
public import CFSG.LocalAnalysis.UniquenessCase.Lie.Shared
public import CFSG.Milestones.ASVolI.A2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup Module Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

section Std

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}

theorem uc22pdiag_projSp_cover (hr : 1 ≤ r) (Q : Sylow 2 (StatedProj (StatedSp r K)))
    (P : Subgroup (StatedProj (StatedSp r K))) (hP : IsCoatom P)
    (hN : normalizer (Q : Set (StatedProj (StatedSp r K))) ≤ P) :
    ∃ F ∈ {F : Subgroup (StatedProj (StatedSp r K)) |
        ∃ d, 1 ≤ d ∧ d ≤ r ∧ F = projStabilizer r K (flag r K d)},
      ∃ h : StatedProj (StatedSp r K), P = F.map (MulAut.conj h).toMonoidHom := by
  have hmem : P ∈ spMaximalParabolics r K 2 := ⟨hP, _, ⟨Q, rfl⟩, hN⟩
  rw [(maximal_parabolics (K := K) 2 hr).1] at hmem
  obtain ⟨W, hW0, hW, rfl⟩ := hmem
  obtain ⟨d, g, hd, hdr, hg⟩ := exists_map_flag_eq_of_isTotallyIsotropic hW0 hW
  refine ⟨projStabilizer r K (flag r K d), ⟨d, hd, hdr, rfl⟩, proj r K g, ?_⟩
  rw [← hg, projStabilizer_map_spAct]

theorem uc22pdiag_classPres_Sp_field (hr : 1 ≤ r) (σ : K ≃+* K) :
    uc22pdiag_ClassPres (StatedProj (StatedSp r K)) (fieldAut r K σ) := by
  refine uc22pdiag_ClassPres_of_std _ (fun Q P hP hN => uc22pdiag_projSp_cover hr Q P hP hN) ?_
  rintro F ⟨d, hd, hdr, rfl⟩
  have hF : spCoordImage σ (flag r K d) = flag r K d := by
    ext v
    rw [mem_spCoordImage, mem_flag_iff, mem_flag_iff]
    exact forall_congr' fun x => forall_congr' fun _ => by simp
  have h1 := map_projStabilizer_fieldAut σ (flag r K d)
  rw [hF] at h1
  exact ⟨1, h1.trans (uc22pdiag_map_conj_one _).symm⟩

theorem uc22pdiag_classPres_Sp4_field (σ : K ≃+* K) (φ : MulAut (StatedProj (StatedSp 2 K)))
    (h : CFSG.ASVolI.ChA.IsProjFieldAut (StatedSp 2 K) σ φ) :
    uc22pdiag_ClassPres (StatedProj (StatedSp 2 K)) φ := by
  have hφ : φ = fieldAut 2 K σ := by
    ext x
    obtain ⟨g, rfl⟩ := proj_surjective x
    obtain ⟨g', hg', hφg⟩ := h g
    rw [fieldAut_proj]
    exact hφg.trans (congrArg _ (Subtype.ext hg'))
  rw [hφ]
  exact uc22pdiag_classPres_Sp_field (by norm_num) σ

end Std

section TwoClasses

open CFSG.Blueprint (LieModel)

theorem uc22pdiag_twoClasses_projSp4 {K : Type} [Field K] [Finite K] [CharP K 2]
    (V₀ : Sylow 2 (StatedProj (StatedSp 2 K))) (hV₀ : (V₀ : Subgroup _) = projUnipotent 2 K) :
    uc22pdiag_TwoClasses (StatedProj (StatedSp 2 K)) (V₀ : Subgroup (StatedProj (StatedSp 2 K))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : normalizer ((V₀ : Subgroup (StatedProj (StatedSp 2 K))) :
      Set (StatedProj (StatedSp 2 K))) = projBorel 2 K := by
    rw [hV₀]; exact normalizer_projUnipotent 2 (by norm_num)
  let Q : ℕ → Subgroup (StatedProj (StatedSp 2 K)) := fun d => projStabilizer 2 K (flag 2 K d)
  obtain ⟨-, -, hinj⟩ := maximal_parabolics (K := K) (r := 2) 2 (by norm_num)
  have hfl : ∀ d, 1 ≤ d → d ≤ 2 → flag 2 K d ≠ ⊥ := by
    intro d h1 h2 h0
    have := finrank_flag (r := 2) (K := K) (i := d) (by omega)
    rw [h0, finrank_bot] at this
    omega
  have hit : ∀ d, d ≤ 2 → IsTotallyIsotropic (pairedSympForm K 2) (flag 2 K d) := fun d hd =>
    fun x hx y hy => isCompleteIsotropicFlag_flag.2.2 d hd x hx y hy
  refine ⟨Q 1, Q 2, ?_, isCoatom_projStabilizer_flag (by norm_num) (by norm_num),
    isCoatom_projStabilizer_flag (by norm_num) (by norm_num), ?_, ?_, ?_, ?_⟩
  · intro h
    have := hinj _ _ (hfl 1 le_rfl (by norm_num)) (hit 1 (by norm_num))
      (hfl 2 (by norm_num) le_rfl) (hit 2 le_rfl) h
    have hf := congrArg (fun W : Submodule K (Fin 2 ⊕ Fin 2 → K) => finrank K W) this
    simp only [finrank_flag (r := 2) (K := K) (by norm_num : 1 ≤ 2 * 2),
      finrank_flag (r := 2) (K := K) (by norm_num : 2 ≤ 2 * 2)] at hf
    omega
  · rw [hN]; exact Subgroup.map_mono (borelSubgroup_le_stabilizer_flag (by norm_num))
  · rw [hN]; exact Subgroup.map_mono (borelSubgroup_le_stabilizer_flag (by norm_num))
  · intro P hP hNP
    rw [hN] at hNP
    obtain ⟨d, h1, h2, rfl⟩ := eq_projStabilizer_of_isCoatom hP hNP
    interval_cases d
    · left; rfl
    · right; rfl
  · intro g hg
    obtain ⟨g', rfl⟩ := proj_surjective g
    have hg' : projStabilizer 2 K ((flag 2 K 1).map (spAct g')) = projStabilizer 2 K (flag 2 K 2) := by
      rw [projStabilizer_map_spAct]; exact hg
    have hW0 : (flag 2 K 1).map (spAct g') ≠ ⊥ := by
      intro h0
      have := finrank_map_spAct g' (flag 2 K 1)
      rw [h0, finrank_bot, finrank_flag (by norm_num : 1 ≤ 2 * 2)] at this
      omega
    have hWi : IsTotallyIsotropic (pairedSympForm K 2) ((flag 2 K 1).map (spAct g')) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [spAct, mulVecLin_apply, mulVecLin_apply, pairedSympForm_mulVec]
      exact isCompleteIsotropicFlag_flag.2.2 1 (by norm_num) x hx y hy
    have heq := hinj _ _ hW0 hWi (hfl 2 (by norm_num) le_rfl) (hit 2 le_rfl) hg'
    have hfin := finrank_map_spAct g' (flag 2 K 1)
    rw [heq, finrank_flag (by norm_num : 2 ≤ 2 * 2), finrank_flag (by norm_num : 1 ≤ 2 * 2)] at hfin
    omega

theorem uc22pdiag_twoClasses_Sp4 {M : Type} [Group M] [Finite M] {n : ℕ} (h : LieModel M .PSp 2 2 n)
    (V : Sylow 2 M) : uc22pdiag_TwoClasses M (V : Subgroup M) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two hK
  obtain ⟨V₀, hV₀⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  let VN : Sylow 2 (StatedProj (StatedSp 2 K)) := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective V
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (StatedProj (StatedSp 2 K)) V₀ VN
  have h1 := uc22pdiag_TwoClasses_map (MulAut.conj k) (uc22pdiag_twoClasses_projSp4 V₀ hV₀)
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

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.Dich
public import CFSG.Milestones.ASVolI.A2
import CFSG.Milestones.ASVolI.A2OddAut
import CFSG.Milestones.ASVolI.F411.aSwSp4
import CFSG.Milestones.ASVolI.F411.SpOdd
import CFSG.Quasithin.EmptyFaithful.T1521SSp4Std
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.RankOneBorel

open Subgroup Module CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint (LieModel)

private theorem projStabilizer_flag_one_ne_two {K : Type} [Field K] [Finite K] [CharP K 2] :
    SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 1) ≠
      SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 2) := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hinj⟩ := SymplecticHigher.maximal_parabolics (K := K) (r := 2) 2
    (by norm_num)
  have hfl : ∀ d, 1 ≤ d → d ≤ 2 → SymplecticFlag.flag 2 K d ≠ ⊥ := by
    intro d h1 h2 h0
    have := SymplecticHigher.finrank_flag (r := 2) (K := K) (i := d) (by omega)
    rw [h0, finrank_bot] at this
    omega
  have hit : ∀ d, d ≤ 2 →
      SymplecticFlag.IsTotallyIsotropic (pairedSympForm K 2) (SymplecticFlag.flag 2 K d) :=
    fun d hd x hx y hy => SymplecticHigher.isCompleteIsotropicFlag_flag.2.2 d hd x hx y hy
  have hf := hinj _ _ (hfl 1 le_rfl (by norm_num)) (hit 1 (by norm_num))
    (hfl 2 (by norm_num) le_rfl) (hit 2 le_rfl) h
  have hfin := congrArg (fun W : Submodule K (Fin 2 ⊕ Fin 2 → K) => finrank K W) hf
  simp only [SymplecticHigher.finrank_flag (r := 2) (K := K) (by norm_num : 1 ≤ 2 * 2),
    SymplecticHigher.finrank_flag (r := 2) (K := K) (by norm_num : 2 ≤ 2 * 2)] at hfin
  omega

theorem projStabilizer_inf_le_normalizer_sp {K : Type} [Field K] [Finite K] [CharP K 2] :
    SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 1) ⊓
        SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 2) ≤
      normalizer ((SymplecticFlag.projUnipotent 2 K : Subgroup (StatedProj (StatedSp 2 K))) :
        Set (StatedProj (StatedSp 2 K))) := by
  rw [CFSG.ASVolI.burnsideF411_projStab_inf]
  exact CFSG.ASVolI.burnsideF411_projBorel_le_normalizer

theorem isInnDiagFieldAut_of_map_eq_sp {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n) (φ : X ≃* StatedProj (StatedSp 2 K))
    (θ : MulAut X)
    (hU : (SymplecticFlag.projUnipotent 2 K).map (MulAut.congr φ θ).toMonoidHom =
      SymplecticFlag.projUnipotent 2 K)
    (hP : (SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 1)).map
        (MulAut.congr φ θ).toMonoidHom =
      SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 1)) :
    CFSG.ASVolI.ChA.IsInnDiagFieldAut X θ := by
  set α : MulAut (StatedProj (StatedSp 2 K)) := MulAut.congr φ θ with hα
  have hU' : (SymplecticFlag.projUnipotent 2 K).map α.toMonoidHom =
      SymplecticFlag.projUnipotent 2 K := by
    rw [hα]; exact hU
  have hP' : (SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 1)).map
      α.toMonoidHom = SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 1) := by
    rw [hα]; exact hP
  obtain ⟨A, σ, ε, hε, hαeq⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow α
  have hε01 : ε = 0 ∨ ε = 1 := by omega
  rcases hε01 with rfl | rfl
  · have hAσ : α = SymplecticHigher.conjAut 2 K A * SymplecticHigher.fieldAut 2 K σ := by
      simpa using hαeq
    refine ⟨MulAut.congr φ.symm (SymplecticHigher.conjAut 2 K A),
      MulAut.congr φ.symm (SymplecticHigher.fieldAut 2 K σ), Or.inl ?_, ?_, ?_⟩
    · exact (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr φ.symm _).2
        (CFSG.RankThree.PartTwo.KFacts.conjAut_mem_inner_of_charTwo A)
    · refine Or.inr (Or.inr (Or.inr (Or.inl
        ⟨n, K, inferInstance, inferInstance, φ, σ, hK, ?_⟩)))
      intro g
      refine ⟨SymplecticHigher.fieldSp 2 K σ g, rfl, ?_⟩
      rw [CFSG.ASVolI.burnsideA26_congr_congr_symm]
      rfl
    · rw [← map_mul, ← hAσ, hα, CFSG.ASVolI.burnsideA26_congr_symm_congr]
  · exfalso
    have hAτ : α = SymplecticHigher.conjAut 2 K A * SymplecticHigher.fieldAut 2 K σ *
        (CFSG.QuasithinUnique.Lin2.Five.tauAut (F := K)) := by
      simpa using hαeq
    have hσU : (SymplecticFlag.projUnipotent 2 K).map
        (SymplecticHigher.fieldAut 2 K σ).toMonoidHom =
        SymplecticFlag.projUnipotent 2 K :=
      CFSG.RankThree.PartTwo.Sec17.HeadProof.map_eq_of_forall_mem
        (SymplecticHigher.fieldAut 2 K σ) fun x hx =>
          (CFSG.Quasithin.Sp4.fieldAut_mem_projUnipotent_iff σ x).2 hx
    have hτU : (SymplecticFlag.projUnipotent 2 K).map
        (CFSG.QuasithinUnique.Lin2.Five.tauAut (F := K)).toMonoidHom =
        SymplecticFlag.projUnipotent 2 K :=
      CFSG.RankThree.PartTwo.Sec17.HeadProof.map_eq_of_forall_mem
        (CFSG.QuasithinUnique.Lin2.Five.tauAut (F := K)) fun x hx =>
          (CFSG.Quasithin.Sp4.tauAut_mem_projUnipotent_iff x).2 hx
    have hAU : (SymplecticFlag.projUnipotent 2 K).map
        (SymplecticHigher.conjAut 2 K A).toMonoidHom =
        SymplecticFlag.projUnipotent 2 K := by
      have h1 : (SymplecticFlag.projUnipotent 2 K).map α.toMonoidHom =
          (SymplecticFlag.projUnipotent 2 K).map
            (SymplecticHigher.conjAut 2 K A).toMonoidHom := by
        conv_lhs => rw [hAτ]
        rw [CFSG.LieType.Chevalley.map_mulAut_mul,
          CFSG.LieType.Chevalley.map_mulAut_mul, hτU, hσU]
      rw [hU'] at h1
      exact h1.symm
    obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.KFacts.conjAut_mem_inner_of_charTwo A
    have hgN : g ∈ Subgroup.normalizer
        (SymplecticFlag.projUnipotent 2 K : Set (StatedProj (StatedSp 2 K))) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      rw [← hg] at hAU
      exact hAU
    have hgB : g ∈ SymplecticFlag.projBorel 2 K := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [← SymplecticHigher.normalizer_projUnipotent (r := 2) (K := K) 2 (by norm_num)]
      exact hgN
    have hgQ2 : g ∈ SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 2) := by
      have hB : g ∈ SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 1) ⊓
          SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 2) := by
        rw [CFSG.ASVolI.burnsideF411_projStab_inf]
        exact hgB
      exact hB.2
    have hA2 : (SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 2)).map
        (SymplecticHigher.conjAut 2 K A).toMonoidHom =
        SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 2) := by
      rw [← hg]
      exact CFSG.LieType.Chevalley.map_conj_self hgQ2
    have hσQ2 : (SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 2)).map
        (SymplecticHigher.fieldAut 2 K σ).toMonoidHom =
        SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 2) := by
      rw [SymplecticHigher.map_projStabilizer_fieldAut,
        CFSG.ASVolI.burnsideF411_spCoordImage_flag σ (i := 2) (by norm_num)]
    have hτ12 : (SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 1)).map
        (CFSG.QuasithinUnique.Lin2.Five.tauAut (F := K)).toMonoidHom =
        SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 2) :=
      CFSG.ASVolI.burnsideF411a_map_tauAut_projStabilizer
        (CFSG.ASVolI.burnsideF411a_map_tauEquiv_stabilizer (K := K)).1
    have hαQ1 : (SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 1)).map
        α.toMonoidHom =
        SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 2) := by
      conv_lhs => rw [hAτ]
      rw [CFSG.LieType.Chevalley.map_mulAut_mul,
        CFSG.LieType.Chevalley.map_mulAut_mul, hτ12, hσQ2, hA2]
    have hEq : SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 1) =
        SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 2) := by
      rw [← hP', hαQ1]
    exact projStabilizer_flag_one_ne_two hEq

theorem graphSp4_dich {X : Type} [Group X] [Finite X] {n : ℕ} (hX : LieModel X .PSp 2 2 n)
    (θ : MulAut X) (hθ : ¬ CFSG.ASVolI.ChA.IsInnDiagFieldAut X θ) (S : Sylow 2 X)
    (hθS : (S : Subgroup X).map θ.toMonoidHom = S) (H : Subgroup X)
    (hSH : (S : Subgroup X) ≤ H) (hθH : H.map θ.toMonoidHom = H) :
    H ≤ normalizer ((S : Subgroup X) : Set X) ∨ H = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX' : StatedClassicalModel X .PSp 2 2 n :=
    LieModel.statedClassicalModel_of_ne_zero (by norm_num) hX
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf (S : Subgroup X) ⊤ :=
    CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S
  obtain ⟨K, _, _, _, φ, hK, hφU, hR, -⟩ :=
    CFSG.QuasithinUnique.Setup.X7a.even_rank_two_residual_symplectic hX' hU
  let Q : ℕ → Subgroup (StatedProj (StatedSp 2 K)) := fun d =>
    SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K d)
  let P : Fin 2 → Subgroup X := fun j => (Q ((j : ℕ) + 1)).map φ.symm.toMonoidHom
  have hinf : P 0 ⊓ P 1 ≤ normalizer ((S : Subgroup X) : Set X) := by
    have hN : Q 1 ⊓ Q 2 ≤ normalizer (SymplecticFlag.projUnipotent 2 K :
        Set (StatedProj (StatedSp 2 K))) :=
      projStabilizer_inf_le_normalizer_sp (K := K)
    have hS : (SymplecticFlag.projUnipotent 2 K).map φ.symm.toMonoidHom =
        (S : Subgroup X) := by
      rw [← hφU, Subgroup.map_equiv_eq_comap_symm' φ (S : Subgroup X)]
      exact Subgroup.map_comap_eq_self_of_surjective φ.symm.surjective (S : Subgroup X)
    have hmain : (Q 1 ⊓ Q 2).map φ.symm.toMonoidHom ≤
        normalizer ((S : Subgroup X) : Set X) := by
      calc
        (Q 1 ⊓ Q 2).map φ.symm.toMonoidHom
            ≤ (normalizer (SymplecticFlag.projUnipotent 2 K :
                Set (StatedProj (StatedSp 2 K)))).map φ.symm.toMonoidHom :=
              Subgroup.map_mono hN
        _ = normalizer ((SymplecticFlag.projUnipotent 2 K).map φ.symm.toMonoidHom :
              Set X) := Subgroup.map_equiv_normalizer_eq _ φ.symm
        _ = normalizer ((S : Subgroup X) : Set X) := by rw [hS]
    have hP : P 0 ⊓ P 1 = (Q 1 ⊓ Q 2).map φ.symm.toMonoidHom := by
      rw [Subgroup.map_inf_eq _ _ _ φ.symm.injective]
      simp [P]
    rw [hP]
    exact hmain
  have hθP : (P 0).map θ.toMonoidHom ≠ P 0 := by
    intro hP0
    apply hθ
    have hcomp : (MulAut.congr φ θ).toMonoidHom.comp φ.toMonoidHom =
        φ.toMonoidHom.comp θ.toMonoidHom := by
      ext x
      simp [MulAut.congr_apply]
    have hφθU : (SymplecticFlag.projUnipotent 2 K).map
        (MulAut.congr φ θ).toMonoidHom = SymplecticFlag.projUnipotent 2 K := by
      rw [← hφU, Subgroup.map_map, hcomp, ← Subgroup.map_map, hθS]
    have hP0φ : (P 0).map φ.toMonoidHom =
        SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 1) := by
      change ((Q 1).map φ.symm.toMonoidHom).map φ.toMonoidHom = Q 1
      rw [Subgroup.map_equiv_eq_comap_symm' φ.symm (Q 1)]
      exact Subgroup.map_comap_eq_self_of_surjective φ.surjective (Q 1)
    have hφθP : (SymplecticHigher.projStabilizer 2 K
        (SymplecticFlag.flag 2 K 1)).map (MulAut.congr φ θ).toMonoidHom =
        SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 1) := by
      calc
        (Q 1).map (MulAut.congr φ θ).toMonoidHom
            = ((P 0).map φ.toMonoidHom).map (MulAut.congr φ θ).toMonoidHom := by
                rw [hP0φ]
        _ = (P 0).map ((MulAut.congr φ θ).toMonoidHom.comp φ.toMonoidHom) := by
                rw [Subgroup.map_map]
        _ = (P 0).map (φ.toMonoidHom.comp θ.toMonoidHom) := by rw [hcomp]
        _ = ((P 0).map θ.toMonoidHom).map φ.toMonoidHom :=
              (Subgroup.map_map (K := P 0) φ.toMonoidHom θ.toMonoidHom).symm
        _ = (P 0).map φ.toMonoidHom := by rw [hP0]
        _ = Q 1 := hP0φ
    exact isInnDiagFieldAut_of_map_eq_sp hK φ θ hφθU hφθP
  exact dich_of_residual hR hinf θ hθS hθP H hSH hθH

end CFSG.LocalAnalysis.UniquenessCase.UC22.RankOneBorel

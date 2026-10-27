module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagL2
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherFieldParabolic
public import CFSG.RankThree.PartOne.KC.SymplecticSemi

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

@[expose] def projMulEquiv (K : Type) [Field K] [CharP K 2] :
    StatedSp 2 K ≃* StatedProj (StatedSp 2 K) :=
  MulEquiv.ofBijective (proj 2 K)
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
      (r := 2) (K := K))

theorem projMulEquiv_apply {K : Type} [Field K] [CharP K 2] (g : StatedSp 2 K) :
    projMulEquiv K g = proj 2 K g :=
  MulEquiv.ofBijective_apply (proj 2 K) _ g

theorem mulAut_congr_symm_apply {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (f : MulAut H) (x : G) : MulAut.congr e.symm f x = e.symm (f (e x)) :=
  rfl

theorem conjSp_eq_conj {K : Type} [Field K] (s : StatedSp 2 K) :
    conjSp 2 K ⟨s, statedSp_le_gsp s.2⟩ = MulAut.conj s := by
  ext g : 1
  apply Subtype.ext
  rw [coe_conjSp, MulAut.conj_apply]
  rfl

theorem congr_symm_fieldAut {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) :
    MulAut.congr (projMulEquiv K).symm (fieldAut 2 K σ) = fieldSp 2 K σ := by
  ext g : 1
  rw [mulAut_congr_symm_apply, projMulEquiv_apply, fieldAut_proj]
  exact MulEquiv.symm_apply_apply (projMulEquiv K) (fieldSp 2 K σ g)

theorem congr_symm_conjAut {K : Type} [Field K] [CharP K 2] (s : StatedSp 2 K) :
    MulAut.congr (projMulEquiv K).symm (conjAut 2 K ⟨s, statedSp_le_gsp s.2⟩) =
      MulAut.conj s := by
  ext g : 1
  rw [mulAut_congr_symm_apply, projMulEquiv_apply, conjAut_proj]
  rw [← projMulEquiv_apply (K := K) (conjSp 2 K ⟨s, statedSp_le_gsp s.2⟩ g),
    MulEquiv.symm_apply_apply]
  exact congrArg (fun f : MulAut (StatedSp 2 K) => f g)
    (conjSp_eq_conj (K := K) s)

theorem mulAut_decomp {K : Type} [Field K] [Finite K] [CharP K 2]
    (θ : MulAut (StatedSp 2 K)) (hodd : Odd (orderOf θ)) :
    ∃ (g : StatedSp 2 K) (σ : K ≃+* K), θ = MulAut.conj g * fieldSp 2 K σ := by
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  set α : MulAut (StatedProj (StatedSp 2 K)) := MulAut.congr (projMulEquiv K) θ with hα
  have hαp : α ^ orderOf θ = 1 := by
    rw [hα, ← map_pow, pow_orderOf_eq_one, map_one]
  obtain ⟨A, σ, hAσ⟩ :=
    CFSG.RankThree.PartOne.KCSpComm.mem_spSemilinearAutGroup_iff.mp
      (CFSG.RankThree.PartOne.CTP.mem_spSemilinearAutGroup_of_odd_pow hodd hαp)
  obtain ⟨g, hg⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_conjAut_eq_statedSp (r := 2)
      (K := K) A
  refine ⟨g, σ, ?_⟩
  have hαeq : α = conjAut 2 K ⟨g, statedSp_le_gsp g.2⟩ * fieldAut 2 K σ := by
    rw [hAσ, hg]
  calc θ = MulAut.congr (projMulEquiv K).symm (MulAut.congr (projMulEquiv K) θ) := by
        ext g
        simp [MulAut.congr_apply]
    _ = MulAut.congr (projMulEquiv K).symm α := rfl
    _ = MulAut.congr (projMulEquiv K).symm
          (conjAut 2 K ⟨g, statedSp_le_gsp g.2⟩ * fieldAut 2 K σ) := by rw [hαeq]
    _ = MulAut.congr (projMulEquiv K).symm (conjAut 2 K ⟨g, statedSp_le_gsp g.2⟩) *
          MulAut.congr (projMulEquiv K).symm (fieldAut 2 K σ) := map_mul _ _ _
    _ = MulAut.conj g * fieldSp 2 K σ := by
        rw [congr_symm_conjAut, congr_symm_fieldAut]

theorem kDiag_statedSp (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∀ (θ : MulAut (StatedSp 2 K)), Odd (orderOf θ) →
    ∀ S : Sylow 2 (StatedSp 2 K),
      (∀ x ∈ (S : Subgroup (StatedSp 2 K)), θ x ∈ (S : Subgroup (StatedSp 2 K))) →
    ∀ P : Subgroup (StatedSp 2 K), IsParabolicTwo (StatedSp 2 K) P →
      (S : Subgroup (StatedSp 2 K)) ≤
        Subgroup.normalizer (P : Set (StatedSp 2 K)) →
      ∀ x ∈ P, θ x ∈ P := by
  intro θ hodd S hSθ P hPpar hSP x hx
  obtain ⟨g, σ, hθeq⟩ := mulAut_decomp (K := K) θ hodd
  have hSP' : (S : Subgroup (StatedSp 2 K)) ≤ P :=
    hPpar.le_of_le_normalizer S.isPGroup' hSP
  have hNP : Subgroup.normalizer ((S : Subgroup (StatedSp 2 K)) : Set (StatedSp 2 K)) ≤ P :=
    hPpar.normalizer_le S hSP'
  have hSmap : (S : Subgroup (StatedSp 2 K)).map
      (MulAut.conj g * fieldSp 2 K σ).toMonoidHom = S := by
    rw [← hθeq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hSθ y hy
    · rw [Subgroup.card_map_of_injective θ.injective]
  have hPmap := map_eq_of_normalizer_le (K := K) g σ S hSmap hNP
  rw [← hθeq] at hPmap
  exact hPmap ▸ Subgroup.mem_map_of_mem θ.toMonoidHom hx

theorem kDiag_statedProj (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∀ (θ : MulAut (StatedProj (StatedSp 2 K))), Odd (orderOf θ) →
    ∀ S : Sylow 2 (StatedProj (StatedSp 2 K)),
      (∀ x ∈ (S : Subgroup (StatedProj (StatedSp 2 K))),
        θ x ∈ (S : Subgroup (StatedProj (StatedSp 2 K)))) →
    ∀ P : Subgroup (StatedProj (StatedSp 2 K)), IsParabolicTwo (StatedProj (StatedSp 2 K)) P →
      (S : Subgroup (StatedProj (StatedSp 2 K))) ≤
        Subgroup.normalizer (P : Set (StatedProj (StatedSp 2 K))) →
      ∀ x ∈ P, θ x ∈ P :=
  kDiag_transport (projMulEquiv K).symm (kDiag_statedSp K)

theorem kDiag_of_isSp4 {n : ℕ} {X : Type} [Group X] [Finite X] (hX : IsSp4 X n) :
    ∀ (θ : MulAut X), Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ (P : Subgroup X), IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P := by
  have hX' : CFSG.Blueprint.LieModel X .PSp 2 2 n := hX
  have ht : (CFSG.Open.StatedLieTag.PSp) ∈ CFSG.Blueprint.classicalTags := by decide
  have hmodel : CFSG.Open.StatedClassicalModel X .PSp 2 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX' ht
  rw [CFSG.Open.StatedClassicalModel] at hmodel
  obtain ⟨hadm, K, hfield, hfinite, hcard, ⟨e⟩⟩ := hmodel
  letI : Field K := hfield
  letI : Finite K := hfinite
  letI : Fintype K := Fintype.ofFinite K
  rw [CFSG.Open.StatedLieAdmissible] at hadm
  have hn1 : 1 ≤ n := hadm.2.1
  have hEven : Fintype.card K % 2 = 0 := by
    rw [Fintype.card_eq_nat_card, hcard]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
  have hchar : ringChar K = 2 := FiniteField.even_card_iff_char_two.mpr hEven
  haveI : CharP K 2 := ringChar.of_eq hchar
  exact kDiag_transport e (kDiag_statedProj K)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end


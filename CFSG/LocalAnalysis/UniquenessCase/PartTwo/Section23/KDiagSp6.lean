module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagSp4

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.AGLEmbedding.ParabAutIrr

theorem map_eq_of_normalizer_le_higher {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (B : StatedSp r K) (σ : K ≃+* K)
    (S : Sylow 2 (StatedSp r K))
    (hS : (S : Subgroup (StatedSp r K)).map
      (MulAut.conj B * fieldSp r K σ).toMonoidHom = S)
    {P : Subgroup (StatedSp r K)}
    (hP : Subgroup.normalizer ((S : Subgroup (StatedSp r K)) : Set (StatedSp r K)) ≤ P) :
    P.map (MulAut.conj B * fieldSp r K σ).toMonoidHom = P := by
  classical
  obtain ⟨Q, hQ⟩ := exists_sylow_unipotent (K := K) 2 r
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedSp r K) Q S
  have hSU : (S : Subgroup (StatedSp r K)) =
      (unipotent r K).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, hQ]
    rfl
  have hφU : (unipotent r K).map (fieldSp r K σ).toMonoidHom = unipotent r K := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro x ⟨u, hu, rfl⟩
      exact fieldSp_mem_unipotent σ hu
    · exact le_of_eq (Subgroup.card_map_of_injective (fieldSp r K σ).injective).symm
  have hNB : Subgroup.normalizer (S : Set (StatedSp r K)) =
      (borelSubgroup r K).map (MulAut.conj g).toMonoidHom := by
    have h := Subgroup.map_equiv_normalizer_eq (H := unipotent r K) (MulAut.conj g)
    rw [normalizer_unipotent] at h
    rw [← hSU] at h
    exact h.symm
  have hcancel : ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) =
      MonoidHom.id (StatedSp r K) := by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  have hB_le : borelSubgroup r K ≤ P.map (MulAut.conj g⁻¹).toMonoidHom := by
    have h1 : (borelSubgroup r K).map (MulAut.conj g).toMonoidHom ≤ P := by
      rw [← hNB]
      exact hP
    have h2 : ((borelSubgroup r K).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj g⁻¹).toMonoidHom ≤ P.map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.map_mono h1
    rw [Subgroup.map_map, hcancel, Subgroup.map_id] at h2
    exact h2
  have hN : g⁻¹ * B * fieldSp r K σ g ∈
      Subgroup.normalizer (unipotent r K : Set (StatedSp r K)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      have hx' : x ∈ (unipotent r K).map (fieldSp r K σ).toMonoidHom := by
        rw [hφU]
        exact hx
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx'
      change (MulAut.conj (g⁻¹ * B * fieldSp r K σ g)) (fieldSp r K σ u) ∈
        unipotent r K
      have hgu : g * u * g⁻¹ ∈ (S : Subgroup (StatedSp r K)) := by
        rw [hSU]
        exact Subgroup.mem_map.mpr ⟨u, hu, by simp [MulAut.conj_apply]⟩
      have hαS : (MulAut.conj B * fieldSp r K σ) (g * u * g⁻¹) ∈
          (S : Subgroup (StatedSp r K)) := by
        have hmem : (MulAut.conj B * fieldSp r K σ) (g * u * g⁻¹) ∈
            (S : Subgroup (StatedSp r K)).map
              (MulAut.conj B * fieldSp r K σ).toMonoidHom :=
          Subgroup.mem_map.mpr ⟨_, hgu, rfl⟩
        rwa [hS] at hmem
      rw [hSU] at hαS
      obtain ⟨v, hv, hveq⟩ := Subgroup.mem_map.mp hαS
      have hconj : (MulAut.conj (g⁻¹ * B * fieldSp r K σ g)) (fieldSp r K σ u) =
          (MulAut.conj g⁻¹) ((MulAut.conj B * fieldSp r K σ) (g * u * g⁻¹)) := by
        simp only [MulAut.mul_apply, MulAut.conj_apply]
        simp only [map_mul, map_inv]
        group
      rw [hconj, ← hveq]
      change (MulAut.conj g⁻¹) ((MulAut.conj g) v) ∈ unipotent r K
      have hcancel' : (MulAut.conj g⁻¹) ((MulAut.conj g) v) = v := by
        simp only [MulAut.mul_apply, MulAut.conj_apply]
        group
      rw [hcancel']
      exact hv
    · exact le_of_eq (Subgroup.card_map_of_injective
        (MulAut.conj (g⁻¹ * B * fieldSp r K σ g)).injective).symm
  have hhB : g⁻¹ * B * fieldSp r K σ g ∈ borelSubgroup r K := by
    rw [← normalizer_unipotent]
    exact hN
  have hα_le : P.map (MulAut.conj B * fieldSp r K σ).toMonoidHom ≤ P := by
    rintro y ⟨x, hxP, rfl⟩
    change (MulAut.conj B * fieldSp r K σ) x ∈ P
    have hxQ : g⁻¹ * x * g ∈ P.map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, hxP, by simp [MulAut.conj_apply]⟩
    have hφfix : (P.map (MulAut.conj g⁻¹).toMonoidHom).map
        (fieldSp r K σ).toMonoidHom = P.map (MulAut.conj g⁻¹).toMonoidHom :=
      map_fieldSp_eq_of_borel_le σ hB_le
    have hφmem : fieldSp r K σ (g⁻¹ * x * g) ∈
        P.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [← hφfix]
      exact Subgroup.mem_map.mpr ⟨_, hxQ, rfl⟩
    obtain ⟨x', hx'P, hx'eq⟩ := Subgroup.mem_map.mp hφmem
    have hαx : (MulAut.conj B * fieldSp r K σ) x =
        g * (g⁻¹ * B * fieldSp r K σ g) * fieldSp r K σ (g⁻¹ * x * g) *
          (g⁻¹ * B * fieldSp r K σ g)⁻¹ * g⁻¹ := by
      simp only [MulAut.mul_apply, MulAut.conj_apply]
      simp only [map_mul, map_inv]
      group
    rw [hαx, ← hx'eq]
    have hghN : g * (g⁻¹ * B * fieldSp r K σ g) * g⁻¹ ∈
        Subgroup.normalizer (S : Set (StatedSp r K)) := by
      rw [hNB]
      exact Subgroup.mem_map.mpr ⟨_, hhB, by simp [MulAut.conj_apply]⟩
    have hghP : g * (g⁻¹ * B * fieldSp r K σ g) * g⁻¹ ∈ P := hP hghN
    have heq : g * (g⁻¹ * B * fieldSp r K σ g) *
          (MulAut.conj g⁻¹) x' * (g⁻¹ * B * fieldSp r K σ g)⁻¹ * g⁻¹ =
        (g * (g⁻¹ * B * fieldSp r K σ g) * g⁻¹) * x' *
          (g * (g⁻¹ * B * fieldSp r K σ g) * g⁻¹)⁻¹ := by
      simp only [MulAut.mul_apply, MulAut.conj_apply]
      group
    change g * (g⁻¹ * B * fieldSp r K σ g) * (MulAut.conj g⁻¹) x' *
        (g⁻¹ * B * fieldSp r K σ g)⁻¹ * g⁻¹ ∈ P
    rw [heq]
    exact P.mul_mem (P.mul_mem hghP hx'P) (P.inv_mem hghP)
  refine Subgroup.eq_of_le_of_card_ge hα_le ?_
  exact le_of_eq (Subgroup.card_map_of_injective
    (MulAut.conj B * fieldSp r K σ).injective).symm

@[expose] def projMulEquiv3 (K : Type) [Field K] [CharP K 2] :
    StatedSp 3 K ≃* StatedProj (StatedSp 3 K) := by
  haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  exact MulEquiv.ofBijective (proj 3 K)
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
      (r := 3) (K := K))

theorem projMulEquiv3_apply {K : Type} [Field K] [CharP K 2] (g : StatedSp 3 K) :
    projMulEquiv3 K g = proj 3 K g :=
  MulEquiv.ofBijective_apply (proj 3 K) _ g

theorem conjSp_eq_conj3 {K : Type} [Field K] (s : StatedSp 3 K) :
    conjSp 3 K ⟨s, statedSp_le_gsp s.2⟩ = MulAut.conj s := by
  ext g : 1
  apply Subtype.ext
  rw [coe_conjSp, MulAut.conj_apply]
  rfl

theorem congr_symm_fieldAut3 {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) :
    MulAut.congr (projMulEquiv3 K).symm (fieldAut 3 K σ) = fieldSp 3 K σ := by
  ext g : 1
  rw [mulAut_congr_symm_apply, projMulEquiv3_apply, fieldAut_proj]
  exact MulEquiv.symm_apply_apply (projMulEquiv3 K) (fieldSp 3 K σ g)

theorem congr_symm_conjAut3 {K : Type} [Field K] [CharP K 2] (s : StatedSp 3 K) :
    MulAut.congr (projMulEquiv3 K).symm (conjAut 3 K ⟨s, statedSp_le_gsp s.2⟩) =
      MulAut.conj s := by
  ext g : 1
  rw [mulAut_congr_symm_apply, projMulEquiv3_apply, conjAut_proj]
  rw [← projMulEquiv3_apply (K := K) (conjSp 3 K ⟨s, statedSp_le_gsp s.2⟩ g),
    MulEquiv.symm_apply_apply]
  exact congrArg (fun f : MulAut (StatedSp 3 K) => f g)
    (conjSp_eq_conj3 (K := K) s)

theorem mulAut_decomp3 {K : Type} [Field K] [Finite K] [CharP K 2]
    (θ : MulAut (StatedSp 3 K)) :
    ∃ (g : StatedSp 3 K) (σ : K ≃+* K), θ = MulAut.conj g * fieldSp 3 K σ := by
  haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  set α : MulAut (StatedProj (StatedSp 3 K)) := MulAut.congr (projMulEquiv3 K) θ with hα
  obtain ⟨A, σ, hAσ⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.automorphism_generation
      (K := K) (r := 3) (by norm_num)).2 α
  obtain ⟨g, hg⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_conjAut_eq_statedSp
      (r := 3) (K := K) A
  refine ⟨g, σ, ?_⟩
  have hαeq : α = conjAut 3 K ⟨g, statedSp_le_gsp g.2⟩ * fieldAut 3 K σ := by
    rw [hAσ, hg]
  calc θ = MulAut.congr (projMulEquiv3 K).symm (MulAut.congr (projMulEquiv3 K) θ) := by
        ext g
        simp [MulAut.congr_apply]
    _ = MulAut.congr (projMulEquiv3 K).symm α := rfl
    _ = MulAut.congr (projMulEquiv3 K).symm
          (conjAut 3 K ⟨g, statedSp_le_gsp g.2⟩ * fieldAut 3 K σ) := by rw [hαeq]
    _ = MulAut.congr (projMulEquiv3 K).symm (conjAut 3 K ⟨g, statedSp_le_gsp g.2⟩) *
          MulAut.congr (projMulEquiv3 K).symm (fieldAut 3 K σ) := map_mul _ _ _
    _ = MulAut.conj g * fieldSp 3 K σ := by
        rw [congr_symm_conjAut3, congr_symm_fieldAut3]

theorem kDiag_statedSp3 (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∀ (θ : MulAut (StatedSp 3 K)), Odd (orderOf θ) →
    ∀ S : Sylow 2 (StatedSp 3 K),
      (∀ x ∈ (S : Subgroup (StatedSp 3 K)), θ x ∈ (S : Subgroup (StatedSp 3 K))) →
    ∀ P : Subgroup (StatedSp 3 K), IsParabolicTwo (StatedSp 3 K) P →
      (S : Subgroup (StatedSp 3 K)) ≤
        Subgroup.normalizer (P : Set (StatedSp 3 K)) →
      ∀ x ∈ P, θ x ∈ P := by
  intro θ hodd S hSθ P hPpar hSP x hx
  obtain ⟨g, σ, hθeq⟩ := mulAut_decomp3 (K := K) θ
  have hSP' : (S : Subgroup (StatedSp 3 K)) ≤ P :=
    hPpar.le_of_le_normalizer S.isPGroup' hSP
  have hNP : Subgroup.normalizer ((S : Subgroup (StatedSp 3 K)) :
      Set (StatedSp 3 K)) ≤ P :=
    hPpar.normalizer_le S hSP'
  have hSmap : (S : Subgroup (StatedSp 3 K)).map
      (MulAut.conj g * fieldSp 3 K σ).toMonoidHom = S := by
    rw [← hθeq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hSθ y hy
    · rw [Subgroup.card_map_of_injective θ.injective]
  have hPmap := map_eq_of_normalizer_le_higher (K := K) (r := 3) g σ S hSmap hNP
  rw [← hθeq] at hPmap
  exact hPmap ▸ Subgroup.mem_map_of_mem θ.toMonoidHom hx

theorem kDiag_statedProj3 (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∀ (θ : MulAut (StatedProj (StatedSp 3 K))), Odd (orderOf θ) →
    ∀ S : Sylow 2 (StatedProj (StatedSp 3 K)),
      (∀ x ∈ (S : Subgroup (StatedProj (StatedSp 3 K))),
        θ x ∈ (S : Subgroup (StatedProj (StatedSp 3 K)))) →
    ∀ P : Subgroup (StatedProj (StatedSp 3 K)),
      IsParabolicTwo (StatedProj (StatedSp 3 K)) P →
      (S : Subgroup (StatedProj (StatedSp 3 K))) ≤
        Subgroup.normalizer (P : Set (StatedProj (StatedSp 3 K))) →
      ∀ x ∈ P, θ x ∈ P :=
  kDiag_transport (projMulEquiv3 K).symm (kDiag_statedSp3 K)

theorem kDiag_of_lieModel_psp6 {n : ℕ} {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .PSp 3 2 n) :
    ∀ (θ : MulAut X), Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ (P : Subgroup X), IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P := by
  have ht : (CFSG.Open.StatedLieTag.PSp) ∈ CFSG.Blueprint.classicalTags := by decide
  have hmodel : CFSG.Open.StatedClassicalModel X .PSp 3 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX ht
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
  exact kDiag_transport e (kDiag_statedProj3 K)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

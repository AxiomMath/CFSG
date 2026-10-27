module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22PointStabilizer
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherIncidenceGraph
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.Quasithin.Recognition.M22WittData

public section

namespace CFSG.Quasithin.H13.NQCat.L34Aut

open MulAction Module CFSG.Fischer CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

section Stabilizer

variable {n : ℕ} {K : Type*} [Field K]

theorem proj_mem_projStabilizer_iff {W : Submodule K (Fin n → K)}
    {A : SpecialLinearGroup (Fin n) K} : proj n K A ∈ projStabilizer W ↔ A ∈ stabilizer W := by
  constructor
  · rintro ⟨B, hB, hBA⟩
    have h1 : B⁻¹ * A ∈ scalars n K := (QuotientGroup.eq).1 hBA
    have h2 : A = B * (B⁻¹ * A) := by group
    rw [h2]
    exact mul_mem hB (scalars_le_stabilizer W h1)
  · intro h
    exact Subgroup.mem_map_of_mem _ h

theorem map_conj_projStabilizer (g : SpecialLinearGroup (Fin n) K) (W : Submodule K (Fin n → K)) :
    (projStabilizer W).map (MulAut.conj (proj n K g)).toMonoidHom =
      projStabilizer (W.map (mulVecLin (g : Matrix (Fin n) (Fin n) K))) := by
  rw [← conjAut_toGL]
  exact (standard_automorphism_transport (n := n) (K := K)).2.2.2.2.2.2.1 _ W

end Stabilizer

theorem imgSub_slHom (A : SpecialLinearGroup (Fin 3) F4) (W : Submodule F4 Vec3) :
    imgSub (slHom A) W = W.map (mulVecLin (A : Matrix (Fin 3) (Fin 3) F4)) := by
  ext v
  rw [mem_imgSub, Submodule.mem_map]
  simp only [slHom_apply, mulVecLin_apply]

theorem imgSub_eq_of_forall (g : GammaL3) (W : PG24Plane)
    (h : ∀ P : PG24Point, imgSub g P ≤ W ↔ (P : Submodule F4 Vec3) ≤ W) :
    imgSub g W = W := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ (finrank_imgSub g W)
  rintro _ ⟨w, hw, rfl⟩
  by_cases hw0 : w = 0
  · obtain ⟨A, σ, hA⟩ := g.2
    rw [hw0, hA, slin_zero]
    exact W.1.zero_mem
  · let P : PG24Point := ⟨F4 ∙ w, finrank_span_singleton hw0⟩
    have hPW : (P : Submodule F4 Vec3) ≤ W := by
      change (F4 ∙ w) ≤ (W : Submodule F4 Vec3)
      exact (Submodule.span_singleton_le_iff_mem w (W : Submodule F4 Vec3)).2 hw
    exact (h P).2 hPW ⟨w, Submodule.mem_span_singleton_self w, rfl⟩

theorem exists_m22Zero_equiv :
    ∃ Ψ : ↥(stabilizer M22 (0 : Fin 22)) ≃* projectiveSL 3 F4,
      (∀ x : ↥(stabilizer M22 (0 : Fin 22)),
        (x : M22) ∈ m22TwoStab ↔ Ψ x ∈ projStabilizer (flagSpace 3 F4 1)) ∧
        ∀ x : ↥(stabilizer M22 (0 : Fin 22)),
          (x : M22) ∈ m22PtHexStab ↔ Ψ x ∈ projStabilizer (flagSpace 3 F4 2) := by
  classical
  obtain ⟨e, he⟩ := iso_PG24 (isSteinerTriple_hexads.derived (0 : Fin 22))
  have hI : (stabilizerToPG 0 e).range = (rhoGL.comp slHom).range := by
    refine eq_of_relIndex_le_six (range_stabilizerToPG_le 0 e he)
      relIndex_range_rhoGL_comp_slHom.le ?_ isSimpleGroup_range_SL ?_
    · rw [card_range_rhoGL_comp_slHom, ← card_stabilizer_point (0 : Fin 22)]
      exact Nat.card_congr (MonoidHom.ofInjective (stabilizerToPG_injective 0 e)).toEquiv.symm
    · rw [card_range_rhoGL_comp_slHom]
      decide
  let ι : ↥(stabilizer M22 (0 : Fin 22)) ≃* (rhoGL.comp slHom).range :=
    (MonoidHom.ofInjective (stabilizerToPG_injective 0 e)).trans (MulEquiv.subgroupCongr hI)
  let κ := QuotientGroup.quotientKerEquivRange (rhoGL.comp slHom)
  let Q : SpecialLinearGroup (Fin 3) F4 ⧸ (rhoGL.comp slHom).ker ≃* projectiveSL 3 F4 :=
    QuotientGroup.quotientMulEquivOfEq (ker_rhoGL_comp_slHom.trans (scalars_eq_center 3 F4).symm)
  let Ψ₀ : ↥(stabilizer M22 (0 : Fin 22)) ≃* projectiveSL 3 F4 := ι.trans (κ.symm.trans Q)
  have hΨ₀ : ∀ (x : ↥(stabilizer M22 (0 : Fin 22))) (A : SpecialLinearGroup (Fin 3) F4),
      rhoGL (slHom A) = stabilizerToPG 0 e x → Ψ₀ x = proj 3 F4 A := by
    intro x A hA
    have h1 : ι x = κ (A : SpecialLinearGroup (Fin 3) F4 ⧸ (rhoGL.comp slHom).ker) := by
      apply Subtype.ext
      exact hA.symm
    change Q (κ.symm (ι x)) = _
    rw [h1, MulEquiv.symm_apply_apply]
    rfl
  have hlift : ∀ x : ↥(stabilizer M22 (0 : Fin 22)), ∃ A : SpecialLinearGroup (Fin 3) F4,
      rhoGL (slHom A) = stabilizerToPG 0 e x := by
    intro x
    obtain ⟨A, hA⟩ : stabilizerToPG 0 e x ∈ (rhoGL.comp slHom).range := hI ▸ ⟨x, rfl⟩
    exact ⟨A, hA⟩
  have hact : ∀ (x : ↥(stabilizer M22 (0 : Fin 22))) (q : {y : Fin 22 // y ≠ 0}),
      stabilizerToPG 0 e x (e q) = e (resPoint 0 x q) := fun x q => by
    simp [stabilizerToPG, Equiv.permCongr_apply]
  set q₁ : {y : Fin 22 // y ≠ 0} := ⟨1, by decide⟩ with hq₁
  set p₁ : PG24Point := e q₁ with hp₁
  set L₀ : Finset {y : Fin 22 // y ≠ 0} := m22HexadF.subtype (· ≠ 0) with hL₀
  have hL₀mem : L₀ ∈ derivedLines hexads (0 : Fin 22) :=
    Finset.mem_image.2 ⟨m22HexadF, Finset.mem_filter.2 ⟨M22Witt.m22HexadF_mem_hexads, by decide⟩,
      rfl⟩
  obtain ⟨W₀, -, hW₀⟩ := Finset.mem_image.1 ((he L₀).1 hL₀mem)
  have hmemW₀ : ∀ q : {y : Fin 22 // y ≠ 0},
      ((e q : PG24Point) : Submodule F4 Vec3) ≤ W₀ ↔ (q : Fin 22) ∈ m22HexadF := by
    intro q
    have h1 : e q ∈ L₀.map e.toEmbedding ↔ q ∈ L₀ := Finset.mem_map_equiv.trans (by simp)
    rw [← hW₀, Finset.mem_filter] at h1
    simpa [hL₀, mem_subtype_ne] using h1
  have hp₁W₀ : (p₁ : Submodule F4 Vec3) ≤ W₀ := (hmemW₀ q₁).2 (by decide)
  obtain ⟨g, hg1, hg2⟩ := exists_map_flagSpace_eq_of_le (n := 3) (K := F4) (by norm_num)
    hp₁W₀ p₁.2 W₀.2
  set φ : MulAut (projectiveSL 3 F4) := MulAut.conj (proj 3 F4 g) with hφ
  refine ⟨Ψ₀.trans φ.symm, fun x => ?_, fun x => ?_⟩
  · obtain ⟨A, hA⟩ := hlift x
    have hmap : ∀ y, φ.symm y ∈ projStabilizer (flagSpace 3 F4 1) ↔
        y ∈ projStabilizer (p₁ : Submodule F4 Vec3) := fun y => by
      rw [← hg1, ← map_conj_projStabilizer, Subgroup.mem_map_equiv]
    change _ ↔ φ.symm (Ψ₀ x) ∈ _
    rw [hmap, hΨ₀ x A hA, proj_mem_projStabilizer_iff, mem_stabilizer, ← imgSub_slHom]
    have h1 : imgSub (slHom A) p₁ = ((rhoGL (slHom A) p₁ : PG24Point) : Submodule F4 Vec3) := rfl
    rw [h1, hA, hp₁, hact, ← Subtype.ext_iff, e.apply_eq_iff_eq, Subtype.ext_iff,
      coe_resPoint_apply, hq₁]
    simp only [m22TwoStab, Subgroup.mem_inf, x.2, true_and, mem_stabilizer_iff, smul_m22_def]
  · obtain ⟨A, hA⟩ := hlift x
    have hmap : ∀ y, φ.symm y ∈ projStabilizer (flagSpace 3 F4 2) ↔
        y ∈ projStabilizer (W₀ : Submodule F4 Vec3) := fun y => by
      rw [← hg2, ← map_conj_projStabilizer, Subgroup.mem_map_equiv]
    change _ ↔ φ.symm (Ψ₀ x) ∈ _
    rw [hmap, hΨ₀ x A hA, proj_mem_projStabilizer_iff, mem_stabilizer, ← imgSub_slHom]
    have hx0 : ((x : M22) : Equiv.Perm (Fin 22)) 0 = 0 := x.2
    have hpt : ∀ q : {y : Fin 22 // y ≠ 0},
        (imgSub (slHom A) (e q) ≤ W₀ ↔ ((x : M22) : Equiv.Perm (Fin 22)) q ∈ m22HexadF) := by
      intro q
      have h1 : imgSub (slHom A) (e q) =
          ((rhoGL (slHom A) (e q) : PG24Point) : Submodule F4 Vec3) := rfl
      rw [h1, hA, hact, hmemW₀, coe_resPoint_apply]
    simp only [m22PtHexStab, Subgroup.mem_inf, x.2, true_and, mem_m22HexStab_iff, PresHex]
    constructor
    · intro hpres
      refine imgSub_eq_of_forall _ W₀ fun P => ?_
      obtain ⟨q, rfl⟩ := e.surjective P
      rw [hpt, hmemW₀]
      exact hpres q
    · intro hW p
      by_cases hp : p = 0
      · rw [hp, hx0]
      · have h1 := hpt ⟨p, hp⟩
        rw [← hmemW₀ ⟨p, hp⟩]
        change _ ↔ ((e ⟨p, hp⟩ : PG24Point) : Submodule F4 Vec3) ≤ W₀
        rw [← h1]
        conv_lhs => rw [← hW]
        exact imgSub_le_imgSub_iff _ _ _

end CFSG.Quasithin.H13.NQCat.L34Aut

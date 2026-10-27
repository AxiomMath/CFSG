module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c3
public import CFSG.Quasithin.Background.P3OrthoOm4
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.Quasithin.Background.G64RealizeSec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KO4Swap

open Matrix CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit Subgroup

theorem map_orthogonalPlus_two (K : Type) [Field K] :
    (CFSG.PGLModel.orthogonalPlus 2 K).map (CFSG.Quasithin.G11.P3Ortho.Om4.Ψ K).toMonoidHom =
      DeterminantIsometries K := by
  have hplus : CFSG.PGLModel.plusQuadForm 2 (K := K) = CFSG.Open.StatedQuadPlus 2 K := rfl
  have hset : {A : GL (Fin 2 ⊕ Fin 2) K |
      ∀ v : Fin 2 ⊕ Fin 2 → K,
        CFSG.PGLModel.plusQuadForm 2 (K := K) ((A : Matrix _ _ K) *ᵥ v) =
          CFSG.PGLModel.plusQuadForm 2 (K := K) v} =
      (((DeterminantIsometries K).comap
        (CFSG.Quasithin.G11.P3Ortho.Om4.Ψ K).toMonoidHom : Subgroup _) : Set _) := by
    ext A
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, Subgroup.mem_comap,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · intro h X
      have hX : X.det = CFSG.PGLModel.plusQuadForm 2
          ((CFSG.Quasithin.G11.P3Ortho.Om4.toMat K).symm X) := by
        rw [hplus, ← CFSG.Quasithin.G11.P3Ortho.Om4.det_toMat,
          LinearEquiv.apply_symm_apply]
      rw [determinantForm_apply, determinantForm_apply,
        CFSG.Quasithin.G11.P3Ortho.Om4.Ψ_apply,
        CFSG.Quasithin.G11.P3Ortho.Om4.det_toMat, ← hplus, h, hX]
    · intro h v
      have h1 := h (CFSG.Quasithin.G11.P3Ortho.Om4.toMat K v)
      rw [determinantForm_apply, determinantForm_apply,
        CFSG.Quasithin.G11.P3Ortho.Om4.Ψ_apply, LinearEquiv.symm_apply_apply,
        CFSG.Quasithin.G11.P3Ortho.Om4.det_toMat,
        CFSG.Quasithin.G11.P3Ortho.Om4.det_toMat] at h1
      simpa [hplus] using h1
  unfold CFSG.PGLModel.orthogonalPlus CFSG.PGLModel.orthogonalGroup
  rw [hset, Subgroup.closure_eq,
    Subgroup.map_comap_eq_self_of_surjective (CFSG.Quasithin.G11.P3Ortho.Om4.Ψ K).surjective]

theorem exists_mulEquiv_determinantIsometries {W : Type} [CommGroup W] [Finite W]
    {R : Subgroup (MulAut W)} {e : ℕ} (h : PartTwo.IsNaturalO4Plus R e) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ e ∧
      Nonempty (↥R ≃* ↥(DeterminantIsometries K)) := by
  obtain ⟨K, hKfield, hKfinite, hKcard, hreal⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  letI : Fintype K := Fintype.ofFinite K
  let Γ := CFSG.PGLModel.orthogonalPlus 2 K
  obtain ⟨π, hπ⟩ := hreal
  have hinj : Function.Injective π :=
    CFSG.Quasithin.G64.RealizesVia.injective_of_faithful'
      (CFSG.Quasithin.FFModel.nat_faithful _) hπ
  let eΓ : Γ ≃* ↥R := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  have hchar : CharP K 2 := by
    have h1 : Fintype.card K = 2 ^ e := by
      rw [← Nat.card_eq_fintype_card]
      exact hKcard
    exact charP_of_card_eq_prime_pow (f := e) h1
  haveI : CharP K 2 := hchar
  refine ⟨K, hKfield, hKfinite, hchar, hKcard, ⟨?_⟩⟩
  exact eΓ.symm.trans
    ((MulEquiv.subgroupMap (CFSG.Quasithin.G11.P3Ortho.Om4.Ψ K) Γ).trans
      (MulEquiv.subgroupCongr (map_orthogonalPlus_two K)))

variable {M G : Type*} [Group M] [Group G]

theorem isQuasisimple_map {R L : Subgroup M} (φ : ↥R ≃* G) (hL : CFSG.Open.IsQuasisimple L)
    (hLR : L ≤ R) : CFSG.IsQuasisimple ((L.subgroupOf R).map φ.toMonoidHom) := by
  let e1 : ↥L ≃* ↥(L.subgroupOf R) := (Subgroup.subgroupOfEquivOfLe hLR).symm
  let e2 : ↥(L.subgroupOf R) ≃* ↥((L.subgroupOf R).map φ.toMonoidHom) :=
    MulEquiv.subgroupMap φ (L.subgroupOf R)
  have hq : CFSG.IsQuasisimple ↥L := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hL
  exact CFSG.IsQuasisimple.of_mulEquiv (e1.trans e2).symm hq

theorem isSubnormal_map {R L : Subgroup M} (φ : ↥R ≃* G) (hL : CFSG.Open.IsSubnormal L R) :
    CFSG.Assembly.IsSubnormal ((L.subgroupOf R).map φ.toMonoidHom) ⊤ := by
  rw [CFSG.Assembly.isSubnormal_iff_open]
  exact CFSG.Open.IsSubnormal.of_mathlib
    ((CFSG.Open.IsSubnormal.subgroupOf hL).map φ.surjective)

theorem not_two_dvd_index_map {R S : Subgroup M} (φ : ↥R ≃* G)
    (hS : CFSG.Quasithin.IsSylowIn 2 S R) :
    ¬ 2 ∣ ((S.subgroupOf R).map φ.toMonoidHom).index := by
  have hidx : ((S.subgroupOf R).map φ.toMonoidHom).index = (S.subgroupOf R).index :=
    Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective (S.subgroupOf R)
  rw [hidx]
  exact hS.2.2

theorem map_le_normalizer_map {R S L : Subgroup M} (φ : ↥R ≃* G) (hSR : S ≤ R) (hLR : L ≤ R)
    (h : S ≤ normalizer (L : Set M)) :
    (S.subgroupOf R).map φ.toMonoidHom ≤
      normalizer (((L.subgroupOf R).map φ.toMonoidHom : Subgroup G) : Set G) := by
  rintro _ ⟨s, hs, rfl⟩
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨s * l * s⁻¹, ?_, ?_⟩
    · change (s : M) * (l : M) * (s : M)⁻¹ ∈ L
      have hsS : (s : M) ∈ S := Subgroup.mem_subgroupOf.mp hs
      have hlL : (l : M) ∈ L := Subgroup.mem_subgroupOf.mp hl
      exact (Subgroup.mem_set_normalizer_iff.mp (h hsS) (l : M)).mp hlL
    · simp
  · rintro ⟨l, hl, hyl⟩
    refine ⟨s⁻¹ * l * s, ?_, ?_⟩
    · change (s : M)⁻¹ * (l : M) * (s : M) ∈ L
      have hs' : (s⁻¹ : ↥R) ∈ S.subgroupOf R := (S.subgroupOf R).inv_mem hs
      have hsS : (s⁻¹ : M) ∈ S := Subgroup.mem_subgroupOf.mp hs'
      have hlL : (l : M) ∈ L := Subgroup.mem_subgroupOf.mp hl
      have hmem := (Subgroup.mem_set_normalizer_iff.mp (h hsS) (l : M)).mp hlL
      simpa using hmem
    · rw [map_mul, map_mul, map_inv, hyl]
      group

end CFSG.LocalAnalysis.UniquenessCase.UC22.KO4Swap

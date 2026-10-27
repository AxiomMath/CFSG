module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionBNormalForm
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapGraphBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvdModel
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimAction

public section

namespace CFSG.StandardType.TypeANbrDvd

open CFSG Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.SeitzReduction.LinearPilot CFSG.SeitzReduction.F4Pilot

variable {F : Type} [Field F] {d : ℕ} {G : Type} [Group G]

@[expose] noncomputable def blockImage (S : Finset (Fin d)) (P : Subgroup G)
    (φ : SpecialLinearGroup (Fin d) F →* P) : Subgroup G :=
  (blockSpecialLinear (K := F) S).map (P.subtype.comp φ)

@[expose] noncomputable def blockToJ {J : Subgroup G} (S : Finset (Fin d)) (P : Subgroup G)
    (φ : SpecialLinearGroup (Fin d) F →* P) (hJ : J = blockImage S P φ) :
    blockSpecialLinear (K := F) S →* J where
  toFun x := ⟨(P.subtype.comp φ) x, hJ.symm ▸ Subgroup.mem_map_of_mem _ x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

@[expose] noncomputable def blockSLCoverS {J : Subgroup G} (S : Finset (Fin d)) (P : Subgroup G)
    (φ : SpecialLinearGroup (Fin d) F →* P) (hJ : J = blockImage S P φ) :
    SpecialLinearGroup S F →* J :=
  (blockToJ S P φ hJ).comp (blockSpecialLinearMulEquivSL F S).symm.toMonoidHom

@[expose] noncomputable def blockSLCover {J : Subgroup G} (S : Finset (Fin d)) (P : Subgroup G)
    (φ : SpecialLinearGroup (Fin d) F →* P) (hJ : J = blockImage S P φ)
    (e : S ≃ Fin S.card) : SpecialLinearGroup (Fin S.card) F →* J :=
  (blockSLCoverS S P φ hJ).comp (reindexSpecialLinear e.symm).toMonoidHom

theorem blockSLCover_apply {J : Subgroup G} (S : Finset (Fin d)) (P : Subgroup G)
    (φ : SpecialLinearGroup (Fin d) F →* P) (hJ : J = blockImage S P φ)
    (e : S ≃ Fin S.card) (g : SpecialLinearGroup (Fin S.card) F) :
    ((blockSLCover S P φ hJ e g : J) : G) =
      (P.subtype.comp φ) (blockEmbed S (reindexSpecialLinear e.symm g)) := by
  simp only [blockSLCover, blockSLCoverS, blockToJ, MonoidHom.comp_apply,
    MulEquiv.toMonoidHom_eq_coe, Subgroup.coe_subtype]
  rfl

theorem blockToJ_surjective {J : Subgroup G} (S : Finset (Fin d)) (P : Subgroup G)
    (φ : SpecialLinearGroup (Fin d) F →* P) (hJ : J = blockImage S P φ) :
    Function.Surjective (blockToJ S P φ hJ) := by
  intro j
  have hj : (j : G) ∈ blockImage S P φ := hJ ▸ j.2
  obtain ⟨x, hx, hxj⟩ := Subgroup.mem_map.mp hj
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  simpa [blockToJ] using hxj

theorem blockSLCoverS_surjective {J : Subgroup G} (S : Finset (Fin d)) (P : Subgroup G)
    (φ : SpecialLinearGroup (Fin d) F →* P) (hJ : J = blockImage S P φ) :
    Function.Surjective (blockSLCoverS S P φ hJ) :=
  (blockToJ_surjective S P φ hJ).comp
    (blockSpecialLinearMulEquivSL F S).symm.surjective

theorem blockSLCover_surjective {J : Subgroup G} (S : Finset (Fin d)) (P : Subgroup G)
    (φ : SpecialLinearGroup (Fin d) F →* P) (hJ : J = blockImage S P φ)
    (e : S ≃ Fin S.card) : Function.Surjective (blockSLCover S P φ hJ e) := by
  rw [blockSLCover]
  exact (blockSLCoverS_surjective S P φ hJ).comp (reindexSpecialLinear e.symm).surjective

theorem blockToJ_injective {J : Subgroup G} (S : Finset (Fin d)) (P : Subgroup G)
    (φ : SpecialLinearGroup (Fin d) F →* P) (hJ : J = blockImage S P φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars d F) (hS : S.card < d) :
    Function.Injective (blockToJ S P φ hJ) := by
  intro x y hxy
  have hval : (P.subtype (φ (x : SpecialLinearGroup (Fin d) F))) =
      (P.subtype (φ (y : SpecialLinearGroup (Fin d) F))) :=
    congrArg (fun z : J => (z : G)) hxy
  have hφ : φ (x : SpecialLinearGroup (Fin d) F) = φ (y : SpecialLinearGroup (Fin d) F) :=
    Subtype.ext hval
  have hmem : (x : SpecialLinearGroup (Fin d) F) * (y : SpecialLinearGroup (Fin d) F)⁻¹ ∈
      scalars d F := by
    apply hker
    rw [map_mul, map_inv, hφ]
    exact mul_inv_cancel _
  have hblock : (x : SpecialLinearGroup (Fin d) F) * (y : SpecialLinearGroup (Fin d) F)⁻¹ ∈
      blockSpecialLinear (K := F) S :=
    (blockSpecialLinear (K := F) S).mul_mem x.2 ((blockSpecialLinear (K := F) S).inv_mem y.2)
  have hone : (x : SpecialLinearGroup (Fin d) F) * (y : SpecialLinearGroup (Fin d) F)⁻¹ = 1 :=
    CFSG.SeitzReduction.LinearPilot.eq_one_of_mem_scalars_of_mem_blockSpecialLinear hS hblock hmem
  apply Subtype.ext
  have h := congrArg (fun z : SpecialLinearGroup (Fin d) F =>
    z * (y : SpecialLinearGroup (Fin d) F)) hone
  simpa [mul_assoc] using h

theorem blockSLCover_injective {J : Subgroup G} (S : Finset (Fin d)) (P : Subgroup G)
    (φ : SpecialLinearGroup (Fin d) F →* P) (hJ : J = blockImage S P φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars d F) (hS : S.card < d) (e : S ≃ Fin S.card) :
    Function.Injective (blockSLCover S P φ hJ e) := by
  rw [blockSLCover, blockSLCoverS]
  exact (blockToJ_injective S P φ hJ hker hS).comp
    ((blockSpecialLinearMulEquivSL F S).symm.injective.comp
      (reindexSpecialLinear e.symm).injective)

theorem blockEmbed_reindex_slConjugation {S : Finset (Fin d)} (e : S ≃ Fin S.card)
    {v : Fin d → Fˣ} {u : Fin S.card → Fˣ} (hu : ∀ k, u k = v (e.symm k))
    (g : SpecialLinearGroup (Fin S.card) F) :
    blockEmbed S (reindexSpecialLinear e.symm
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation (S.card) F (ggDiagUnit u) g)) =
      ggDiagConj v (blockEmbed S (reindexSpecialLinear e.symm g)) := by
  apply Subtype.ext
  ext i j
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · have hleft : ((reindexSpecialLinear e.symm
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation (S.card) F (ggDiagUnit u) g) :
          SpecialLinearGroup S F) : Matrix S S F) ⟨i, hi⟩ ⟨j, hj⟩ =
        (ggDiagConj u g : Matrix (Fin S.card) (Fin S.card) F)
          (e ⟨i, hi⟩) (e ⟨j, hj⟩) := rfl
    rw [coe_blockEmbed, blockMatrix_apply, dif_pos ⟨hi, hj⟩, hleft, ggDiagConj_apply]
    rw [ggDiagConj_apply, coe_blockEmbed, blockMatrix_apply, dif_pos ⟨hi, hj⟩]
    have hright : ((reindexSpecialLinear e.symm g : SpecialLinearGroup S F) :
        Matrix S S F) ⟨i, hi⟩ ⟨j, hj⟩ =
        (g : Matrix (Fin S.card) (Fin S.card) F) (e ⟨i, hi⟩) (e ⟨j, hj⟩) := rfl
    rw [hright, hu, hu]
    simp only [Equiv.symm_apply_apply]
  all_goals
    have hnot : ¬ (i ∈ S ∧ j ∈ S) := by tauto
    rw [coe_blockEmbed, blockMatrix_apply, dif_neg hnot]
    rw [ggDiagConj_apply, coe_blockEmbed, blockMatrix_apply, dif_neg hnot]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]


theorem mem_scalars_of_blockEmbed_reindex_mem_scalars {S : Finset (Fin d)}
    (e : S ≃ Fin S.card) (hcard : S.card = d) {g : SpecialLinearGroup (Fin S.card) F}
    (hz : blockEmbed S (reindexSpecialLinear e.symm g) ∈ scalars d F) :
    g ∈ scalars (S.card) F := by
  obtain ⟨c, hc, hmat⟩ := mem_scalars.mp hz
  rw [mem_scalars]
  refine ⟨c, by simpa [hcard] using hc, ?_⟩
  ext a b
  have h2 : ((blockEmbed S (reindexSpecialLinear e.symm g) :
      SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F)
        (e.symm a) (e.symm b) =
      (g : Matrix (Fin S.card) (Fin S.card) F) a b := by
    rw [coe_blockEmbed, blockMatrix_apply, dif_pos ⟨(e.symm a).2, (e.symm b).2⟩]
    change (g : Matrix (Fin S.card) (Fin S.card) F)
      (e (e.symm a)) (e (e.symm b)) = _
    rw [e.apply_symm_apply, e.apply_symm_apply]
  rw [← h2, hmat, Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases hab : a = b
  · subst hab
    simp
  · have hne : e.symm a ≠ e.symm b := fun h => hab (e.symm.injective h)
    simp [hab, hne]

theorem blockSLCover_ker_scalar {J : Subgroup G} (S : Finset (Fin d)) (P : Subgroup G)
    (φ : SpecialLinearGroup (Fin d) F →* P) (hJ : J = blockImage S P φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars d F) (e : S ≃ Fin S.card) :
    ∀ g, blockSLCover S P φ hJ e g = 1 → g ∈ scalars (S.card) F := by
  intro g hg
  have hφ : φ (blockEmbed S (reindexSpecialLinear e.symm g)) = 1 := by
    have h := congrArg (fun z : J => (z : G)) hg
    rw [blockSLCover_apply] at h
    exact Subtype.ext h
  have hz : blockEmbed S (reindexSpecialLinear e.symm g) ∈ scalars d F := hker _ hφ
  by_cases hS : S.card < d
  · have hg1 : g = 1 :=
      blockSLCover_injective S P φ hJ hker hS e (by simpa using hg)
    rw [hg1]
    exact (scalars (S.card) F).one_mem
  · have hle : S.card ≤ d := by simpa using Finset.card_le_univ S
    have hcard : S.card = d := by omega
    exact mem_scalars_of_blockEmbed_reindex_mem_scalars e hcard hz

theorem blockSLCover_actsDiag {J B Bs : Subgroup G} {S : Finset (Fin d)} {P : Subgroup G}
    (φ : SpecialLinearGroup (Fin d) F →* P) (hJ : J = blockImage S P φ)
    (hN : Bs ≤ Subgroup.normalizer (P : Set G))
    (hBJ : B ≤ Subgroup.normalizer (J : Set G))
    (hB : B ≤ Bs) (e : S ≃ Fin S.card) {b : B} {t : Fin d → F}
    (hb : TypeANbrDvd.ActsDiag φ (ggGamma P hN ⟨b, hB b.2⟩) t) :
    TypeANbrDvd.ActsDiag (blockSLCover S P φ hJ e) (ggGamma J hBJ b)
      (fun k => t (e.symm k)) := by
  classical
  let v : Fin d → Fˣ := fun i => Units.mk0 (t i) (hb.ne_zero i)
  let u : Fin S.card → Fˣ := fun k => v (e.symm k)
  refine ⟨ggDiagUnit u, rfl, ?_⟩
  intro g
  apply Subtype.ext
  let bX : Bs := ⟨b, hB b.2⟩
  let y : SpecialLinearGroup (Fin d) F :=
    blockEmbed S (reindexSpecialLinear e.symm g)
  obtain ⟨D, hD, hDact⟩ := hb
  have hDv : D = ggDiagUnit v := Units.ext (by rw [hD]; rfl)
  have hDact' : ((ggGamma P hN bX) (φ y) : G) = (φ (ggDiagConj v y) : G) := by
    have h := congrArg (fun z : P => (z : G)) (hDact y)
    rw [h] at *
    rw [hDv]
    rfl
  calc
    ((ggGamma J hBJ b) (blockSLCover S P φ hJ e g) : G)
        = (b : G) * ((blockSLCover S P φ hJ e g : J) : G) * (b : G)⁻¹ := by
          rw [ggGamma_coe]
    _ = (b : G) * (P.subtype (φ y)) * (b : G)⁻¹ := by
          rw [blockSLCover_apply]
          rfl
    _ = ((ggGamma P hN bX) (φ y) : G) := by
          rw [ggGamma_coe]
          rfl
    _ = (φ (ggDiagConj v y) : G) := hDact'
    _ = (P.subtype (φ (blockEmbed S (reindexSpecialLinear e.symm
          (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
            (S.card) F (ggDiagUnit u) g))))) := by
          rw [blockEmbed_reindex_slConjugation (S := S) (e := e) (v := v) (u := u) (fun k => rfl) g]
          rfl
    _ = ((blockSLCover S P φ hJ e (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
          (S.card) F (ggDiagUnit u) g) : J) : G) := by
          rw [blockSLCover_apply]
          rfl

theorem card_range_ggGamma_le [Finite F] {p : ℕ} (hp : p.Prime)
    {J B Bs : Subgroup G} {S : Finset (Fin d)} {P : Subgroup G}
    (φ : SpecialLinearGroup (Fin d) F →* P) (hJ : J = blockImage S P φ)
    (hN : Bs ≤ Subgroup.normalizer (P : Set G))
    (hBJ : B ≤ Subgroup.normalizer (J : Set G)) (hB : B ≤ Bs)
    (hker : ∀ g, φ g = 1 → g ∈ scalars d F) (hS2 : 2 ≤ S.card)
    (hdiag : ∀ a ∈ (ggGamma P hN).range, ∃ t : Fin d → F,
      TypeANbrDvd.ActsDiag φ a t)
    (hBexp : ∀ b : B, b ^ p = 1) :
    Nat.card (ggGamma J hBJ).range ≤ p ^ (S.card - 1) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  let e : S ≃ Fin S.card := S.equivFin
  let χ : SpecialLinearGroup (Fin S.card) F →* J := blockSLCover S P φ hJ e
  have hχs : Function.Surjective χ := blockSLCover_surjective S P φ hJ e
  have hχker : ∀ g, χ g = 1 → g ∈ scalars (S.card) F :=
    blockSLCover_ker_scalar (F := F) S P φ hJ hker e
  have hAp : ∀ a ∈ (ggGamma J hBJ).range, a ^ p = 1 := by
    rintro a ⟨b, rfl⟩
    rw [← map_pow, hBexp b, map_one]
  have hAdiag : ∀ a ∈ (ggGamma J hBJ).range, ∃ u : Fin S.card → F,
      TypeANbrDvd.ActsDiag χ a u := by
    rintro a ⟨b, rfl⟩
    obtain ⟨t, ht⟩ := hdiag (ggGamma P hN ⟨b, hB b.2⟩) ⟨_, rfl⟩
    exact ⟨fun k => t (e.symm k), blockSLCover_actsDiag (S := S) (P := P) (φ := φ)
      (hJ := hJ) (hN := hN) (hBJ := hBJ) (hB := hB) e ht⟩
  exact TypeANbrDvd.card_le_of_actsDiag (F := F) (H := J) (p := p) (d := S.card)
    (φ := χ) (A := (ggGamma J hBJ).range) (by omega) hχs hχker hAp hAdiag

end CFSG.StandardType.TypeANbrDvd

end

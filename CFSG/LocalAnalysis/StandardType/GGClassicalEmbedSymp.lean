module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeInner
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicSymplectic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldSympMark
public import CFSG.RankThree.PartOne.KC.SymplecticSemi
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

private noncomputable def ems_finEquiv (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
  finSumFinEquiv.trans (finCongr (by omega))

private noncomputable def ems_reindexGL (m : ℕ) (K : Type) [Field K] :
    GL (Fin m ⊕ Fin m) K ≃* GL (Fin (2 * m)) K :=
  (ems_finEquiv m).reindexGL K

private theorem ems_reindexGL_scalar (m : ℕ) (K : Type) [Field K] (c : Kˣ) :
    (ems_reindexGL m K (Matrix.GeneralLinearGroup.scalar (Fin m ⊕ Fin m) c) :
        Matrix (Fin (2 * m)) (Fin (2 * m)) K) =
      Matrix.scalar (Fin (2 * m)) (c : K) := by
  rw [ems_reindexGL]
  ext i j
  rw [Equiv.coe_reindexGL, Matrix.submatrix_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : (ems_finEquiv m).symm i ≠ (ems_finEquiv m).symm j :=
      fun hh => h ((ems_finEquiv m).symm.injective hh)
    simp [h, h']

private theorem ems_reindexGL_center (m : ℕ) (K : Type) [Field K] :
    (Subgroup.center (GL (Fin m ⊕ Fin m) K)).map (ems_reindexGL m K).toMonoidHom =
      Subgroup.center (GL (Fin (2 * m)) K) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar,
    Matrix.GeneralLinearGroup.center_eq_range_scalar]
  ext g
  constructor
  · rintro ⟨x, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, Units.ext (ems_reindexGL_scalar m K c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Matrix.GeneralLinearGroup.scalar (Fin m ⊕ Fin m) c, ⟨c, rfl⟩,
      Units.ext (ems_reindexGL_scalar m K c)⟩

private noncomputable def ems_reindexPGL (m : ℕ) (K : Type) [Field K] :
    ProjGenLinGroup (Fin m ⊕ Fin m) K ≃* ProjGenLinGroup (Fin (2 * m)) K :=
  QuotientGroup.congr (Subgroup.center (GL (Fin m ⊕ Fin m) K))
    (Subgroup.center (GL (Fin (2 * m)) K)) (ems_reindexGL m K) (ems_reindexGL_center m K)

private noncomputable def ems_mapPGL (m : ℕ) (K K' : Type) [Field K] [Field K'] [Algebra K K'] :
    gsp m K →* ProjGenLinGroup (Fin m ⊕ Fin m) K' :=
  (ProjGenLinGroup.mk).comp
    ((Matrix.GeneralLinearGroup.map (algebraMap K K')).comp (gsp m K).subtype)

private theorem ems_scalar_of_map_scalar (m : ℕ) (K K' : Type) [Field K] [Field K'] [Algebra K K']
    [Nonempty (Fin m ⊕ Fin m)] {A : GL (Fin m ⊕ Fin m) K} {c : K'ˣ}
    (hA : Matrix.GeneralLinearGroup.map (algebraMap K K') A =
      Matrix.GeneralLinearGroup.scalar (Fin m ⊕ Fin m) c) :
    ∃ c₀ : Kˣ, A = Matrix.GeneralLinearGroup.scalar (Fin m ⊕ Fin m) c₀ := by
  have hmap : ∀ i j : Fin m ⊕ Fin m,
      algebraMap K K' ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) i j) =
        if i = j then (c : K') else 0 := by
    intro i j
    have h := congrArg (fun g : GL (Fin m ⊕ Fin m) K' =>
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K') i j) hA
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply] at h
    exact h
  obtain ⟨i₀⟩ := ‹Nonempty (Fin m ⊕ Fin m)›
  have hc : (c : K') =
      algebraMap K K' ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) i₀ i₀) := by
    have := hmap i₀ i₀
    simpa using this.symm
  have hc0 : (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) i₀ i₀ ≠ 0 := by
    intro hzero
    have : (c : K') = 0 := by rw [hc, hzero, map_zero]
    exact c.ne_zero this
  refine ⟨Units.mk0 _ hc0, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply (algebraMap K K').injective
  rw [hmap i j]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, if_pos rfl, hc]
    simp
  · rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, if_neg hij]
    simp [hij]

private theorem ems_mapPGL_ker (m : ℕ) (K K' : Type) [Field K] [Field K'] [Algebra K K']
    [Nonempty (Fin m ⊕ Fin m)] :
    (ems_mapPGL m K K').ker = (StatedScalars (Fin m ⊕ Fin m) K).subgroupOf (gsp m K) := by
  ext A
  rw [MonoidHom.mem_ker, ems_mapPGL, MonoidHom.comp_apply, ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range,
    Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨c₀, hc₀⟩ := ems_scalar_of_map_scalar m K K' hc.symm
    exact ⟨c₀, hc₀.symm⟩
  · rintro ⟨c₀, hc₀⟩
    refine ⟨Units.map (algebraMap K K') c₀, ?_⟩
    exact (Matrix.GeneralLinearGroup.map_scalar (algebraMap K K') c₀).symm.trans
      (congrArg (Matrix.GeneralLinearGroup.map (algebraMap K K')) hc₀)

private noncomputable def ems_extPGL (m : ℕ) (K K' : Type) [Field K] [Field K'] [Algebra K K'] :
    gsp m K →* ProjGenLinGroup (Fin (2 * m)) K' :=
  (ems_reindexPGL m K').toMonoidHom.comp (ems_mapPGL m K K')

private theorem ems_extPGL_ker (m : ℕ) (K K' : Type) [Field K] [Field K'] [Algebra K K']
    [Nonempty (Fin m ⊕ Fin m)] :
    (ems_extPGL m K K').ker = (StatedScalars (Fin m ⊕ Fin m) K).subgroupOf (gsp m K) := by
  have hker : (ems_mapPGL m K K').ker =
      (StatedScalars (Fin m ⊕ Fin m) K).subgroupOf (gsp m K) := ems_mapPGL_ker m K K'
  ext A
  rw [MonoidHom.mem_ker, ems_extPGL, MonoidHom.comp_apply]
  constructor
  · intro h
    change (ems_reindexPGL m K') ((ems_mapPGL m K K') A) = 1 at h
    have h1 : (ems_mapPGL m K K') A = 1 :=
      (ems_reindexPGL m K').injective (by rw [h, map_one])
    exact hker ▸ MonoidHom.mem_ker.mpr h1
  · intro h
    have h1 : (ems_mapPGL m K K') A = 1 := MonoidHom.mem_ker.mp (hker.symm ▸ h)
    rw [h1, map_one]

private theorem ems_conjAut_ker (m : ℕ) (hm : 1 ≤ m) (K : Type) [Field K] [Finite K] :
    (conjAut m K).ker = (StatedScalars (Fin m ⊕ Fin m) K).subgroupOf (gsp m K) := by
  ext A
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  change conjAut m K A = 1 ↔ (A : GL (Fin m ⊕ Fin m) K) ∈
    (Matrix.GeneralLinearGroup.scalar (Fin m ⊕ Fin m)).range
  rw [MonoidHom.mem_range]
  constructor
  · intro h
    obtain ⟨c, hc⟩ :=
      (CFSG.RankThree.PartOne.KCSpComm.conjAut_eq_one_iff (r := m) (K := K) hm A).mp h
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    exact (CFSG.RankThree.PartOne.KCSpComm.conjAut_eq_one_iff (r := m) (K := K) hm A).mpr
      ⟨c, hc.symm⟩

private theorem ems_embedAt_sp (m : ℕ) (hm : 2 ≤ m) (K : Type) [Field K] [Finite K]
    {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    GGClassicalProjEmbedAt (2 * m) (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m))
        (LargeEvenGSpSet K m)) := by
  have hchar : CharP K 2 := CFSG.StandardType.LayerCC.charP_two_of_natCard hK
  have hne : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  refine ⟨fun r => CFSG.StandardType.innSet_subset_symplectic m ⟨r, rfl⟩, ?_⟩
  let K' := AlgebraicClosure K
  have hIrange : LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m))
      (LargeEvenGSpSet K m) = Set.range (conjAut m K) := by
    ext φ
    exact ⟨fun hφ =>
        CFSG.LocalAnalysis.GLTheoremA.Y10GFldSympMark.exists_conjAut_eq_of_mem_matConjImage hφ,
      by
        rintro ⟨A, rfl⟩
        exact CFSG.LocalAnalysis.GLTheoremA.Y10GFldSympMark.conjAut_mem_matConjImage A⟩
  have hclosure : Subgroup.closure (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m))
      (LargeEvenGSpSet K m)) = (conjAut m K).range := by
    rw [hIrange, ← MonoidHom.coe_range, Subgroup.closure_eq]
  have hker : (conjAut m K).ker = (ems_extPGL m K K').ker := by
    rw [ems_extPGL_ker m K K', ems_conjAut_ker m (by omega) K]
  let ψ : (gsp m K) ⧸ (conjAut m K).ker →* ProjGenLinGroup (Fin (2 * m)) K' :=
    ((ems_extPGL m K K').range).subtype.comp
      ((QuotientGroup.quotientKerEquivRange (ems_extPGL m K K')).toMonoidHom.comp
        (QuotientGroup.quotientMulEquivOfEq hker).toMonoidHom)
  have hψ : Function.Injective ψ := by
    intro x y hxy
    exact (QuotientGroup.quotientMulEquivOfEq hker).injective
      ((QuotientGroup.quotientKerEquivRange (ems_extPGL m K K')).injective
        (Subtype.coe_injective hxy))
  let e₁ : (conjAut m K).range ≃* (gsp m K) ⧸ (conjAut m K).ker :=
    (QuotientGroup.quotientKerEquivRange (conjAut m K)).symm
  let e₀ : ↥(Subgroup.closure (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m))
      (LargeEvenGSpSet K m))) ≃* (conjAut m K).range :=
    MulEquiv.subgroupCongr hclosure
  exact ⟨K', inferInstance, inferInstance, inferInstance,
    (ψ.comp e₁.toMonoidHom).comp e₀.toMonoidHom,
    fun x y hxy => e₀.injective (e₁.injective (hψ hxy))⟩

theorem ggClassicalProjEmbed_symp (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .B ∨ lab.tag = .C) :
    LargeEvenLabelAll lab fun R _ I _ => GGClassicalProjEmbedAt (ggClassDeg lab) R I := by
  obtain ⟨t, l, n⟩ := lab
  rcases h with ht | ht
  · subst ht
    have hl : 2 ≤ l := by
      have hh := hlab
      simp only [LargeEvenInLambda2] at hh
      exact hh.2.1
    intro Q hQ
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    exact ⟨K, i1, i2, hK, hq, ems_embedAt_sp l hl K hK⟩
  · subst ht
    have hl : 2 ≤ l := by
      have hh := hlab
      simp only [LargeEvenInLambda2] at hh
      exact hh.2.1
    intro Q hQ
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    exact ⟨K, i1, i2, hK, hq, ems_embedAt_sp l hl K hK⟩

end CFSG.StandardType

end

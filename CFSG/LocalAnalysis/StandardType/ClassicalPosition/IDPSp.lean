module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.SymplecticExtras
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSp
public import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
public import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Steinberg.CentralExt.SpCentrallyClosed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType

private noncomputable abbrev idSp_x (F : Type) [Field F] (γ : Fin 1 → ℤ) (c : F) :
    ↥(CFSG.Open.StatedSp 1 F) :=
  CFSG.LieType.Steinberg.Sp.x 1 F γ c

private abbrev idSp_hαstd :
    Symplectic.stdVec (TauCeti.GLSymplecticFin.RootSubgroupIndex.positiveLong 0) =
      Symplectic.toStd 1 (Pi.single (0 : Fin 1) 1) :=
  Symplectic.SpExtras.stdVec_positiveLong_eq (n := 1) (k := 0) (by omega)

private abbrev idSp_hβstd :
    Symplectic.stdVec (TauCeti.GLSymplecticFin.RootSubgroupIndex.negativeLong 0) =
      Symplectic.toStd 1 (-Pi.single (0 : Fin 1) 1) :=
  Symplectic.SpExtras.stdVec_negativeLong_eq (n := 1) (k := 0) (by omega)

private theorem idSp_mat_x_pos (F : Type) [Field F] (c : F) :
    Symplectic.SpExtras.mat 1 F (idSp_x F (Pi.single 0 1) c) =
      Matrix.transvection (Sum.inl 0) (Sum.inr 0) c := by
  simp only [idSp_x]
  rw [CFSG.LieType.Steinberg.Sp.x_eq idSp_hαstd]
  exact Symplectic.SpExtras.mat_elt_positiveLong 0 c

private theorem idSp_mat_x_neg (F : Type) [Field F] (c : F) :
    Symplectic.SpExtras.mat 1 F (idSp_x F (-Pi.single 0 1) c) =
      Matrix.transvection (Sum.inr 0) (Sum.inl 0) c := by
  simp only [idSp_x]
  rw [CFSG.LieType.Steinberg.Sp.x_eq idSp_hβstd]
  exact Symplectic.SpExtras.mat_elt_negativeLong 0 c

private theorem idSp_weyl_eq_pos (F : Type) [Field F] [CharP F 2] :
    Symplectic.weylRep 1 F 0 =
      idSp_x F (Pi.single 0 1) 1 * idSp_x F (-Pi.single 0 1) 1 *
        idSp_x F (Pi.single 0 1) 1 := by
  rw [Symplectic.SpExtras.weylRep_eq_long (n := 1) (F := F) (k := 0) (by omega)]
  simp only [idSp_x]
  rw [CFSG.LieType.Steinberg.Sp.x_eq idSp_hαstd,
      CFSG.LieType.Steinberg.Sp.x_eq idSp_hβstd]
  rw [CharTwo.neg_eq]

private theorem idSp_toBlock_M (F : Type) [Field F] [CharP F 2] (r s : F) :
    Symplectic.SpExtras.toBlock (Sum.inl 0) (Sum.inr 0)
      (Symplectic.SpExtras.mat 1 F (idSp_x F (Pi.single 0 1) r *
        idSp_x F (-Pi.single 0 1) s * idSp_x F (Pi.single 0 1) r)) =
      !![1 + r * s, r ^ 2 * s; s, 1 + r * s] := by
  rw [map_mul, map_mul, idSp_mat_x_pos, idSp_mat_x_neg]
  rw [Symplectic.SpExtras.toBlock_mul (p := Sum.inl 0) (q := Sum.inr 0) Sum.inl_ne_inr
        (Symplectic.SpExtras.isBlk_mul
          (Symplectic.SpExtras.isBlk_transvection (Or.inl ⟨rfl, rfl⟩) r)
          (Symplectic.SpExtras.isBlk_transvection (Or.inr ⟨rfl, rfl⟩) s)),
      Symplectic.SpExtras.toBlock_mul (p := Sum.inl 0) (q := Sum.inr 0) Sum.inl_ne_inr
        (Symplectic.SpExtras.isBlk_transvection (Or.inl ⟨rfl, rfl⟩) r),
      Symplectic.SpExtras.toBlock_transvection_pq (p := Sum.inl 0) (q := Sum.inr 0) Sum.inl_ne_inr,
      Symplectic.SpExtras.toBlock_transvection_qp (p := Sum.inl 0) (q := Sum.inr 0) Sum.inl_ne_inr]
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    try ring_nf
    try simp [h2]

private theorem idSp_toBlock_N (F : Type) [Field F] [CharP F 2] (r s : F) :
    Symplectic.SpExtras.toBlock (Sum.inl 0) (Sum.inr 0)
      (Symplectic.SpExtras.mat 1 F (idSp_x F (-Pi.single 0 1) s *
        idSp_x F (Pi.single 0 1) r * idSp_x F (-Pi.single 0 1) s)) =
      !![1 + r * s, r; s ^ 2 * r, 1 + r * s] := by
  rw [map_mul, map_mul, idSp_mat_x_neg, idSp_mat_x_pos]
  rw [Symplectic.SpExtras.toBlock_mul (p := Sum.inl 0) (q := Sum.inr 0) Sum.inl_ne_inr
        (Symplectic.SpExtras.isBlk_mul
          (Symplectic.SpExtras.isBlk_transvection (Or.inr ⟨rfl, rfl⟩) s)
          (Symplectic.SpExtras.isBlk_transvection (Or.inl ⟨rfl, rfl⟩) r)),
      Symplectic.SpExtras.toBlock_mul (p := Sum.inl 0) (q := Sum.inr 0) Sum.inl_ne_inr
        (Symplectic.SpExtras.isBlk_transvection (Or.inr ⟨rfl, rfl⟩) s),
      Symplectic.SpExtras.toBlock_transvection_pq (p := Sum.inl 0) (q := Sum.inr 0) Sum.inl_ne_inr,
      Symplectic.SpExtras.toBlock_transvection_qp (p := Sum.inl 0) (q := Sum.inr 0) Sum.inl_ne_inr]
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    try ring_nf
    try simp [h2]

private theorem idSp_rankOne_scalar_product (F : Type) [Field F] [CharP F 2]
    {G : Type} [Group G] (ψ' : ↥(CFSG.Open.StatedSp 1 F) →* G)
    (hinj : Function.Injective ψ') (x : G) (r s : F)
    (hr : ∀ c, x⁻¹ * ψ' (idSp_x F (Pi.single 0 1) c) * x =
      ψ' (idSp_x F (Pi.single 0 1) (r * c)))
    (hs : ∀ c, x⁻¹ * ψ' (idSp_x F (-Pi.single 0 1) c) * x =
      ψ' (idSp_x F (-Pi.single 0 1) (s * c))) :
    r * s = 1 := by
  let β' : ↥(CFSG.Open.StatedSp 1 F) →* G :=
    { toFun := fun y => x⁻¹ * ψ' y * x
      map_one' := by simp
      map_mul' := fun a b => by simp only [map_mul]; group }
  have hβ' : ∀ y, β' y = x⁻¹ * ψ' y * x := fun y => rfl
  have hβ'α : ∀ c, β' (idSp_x F (Pi.single 0 1) c) =
      ψ' (idSp_x F (Pi.single 0 1) (r * c)) := fun c => by
    rw [hβ' (idSp_x F (Pi.single 0 1) c), hr c]
  have hβ'β : ∀ c, β' (idSp_x F (-Pi.single 0 1) c) =
      ψ' (idSp_x F (-Pi.single 0 1) (s * c)) := fun c => by
    rw [hβ' (idSp_x F (-Pi.single 0 1) c), hs c]
  have hβ'w : β' (Symplectic.weylRep 1 F 0) =
      ψ' (idSp_x F (Pi.single 0 1) r * idSp_x F (-Pi.single 0 1) s *
        idSp_x F (Pi.single 0 1) r) := by
    rw [idSp_weyl_eq_pos]
    simp only [map_mul, hβ'α, hβ'β, mul_one]
  have hα : (Pi.single 0 1 : Fin 1 → ℤ) ∈ (Symplectic.rootDatum 1 F).roots :=
    Symplectic.SpExtras.mem_roots_of_stdVec
      idSp_hαstd
  obtain ⟨ε, hε, hconj⟩ := CFSG.LieType.Steinberg.Sp.weylRep_conj_x (n := 1) (F := F) 0 hα
  have hreflect : (CFSG.LieType.RootSystem.reflection (Symplectic.cartanC 1) 0)
      (Pi.single 0 1) = -Pi.single 0 1 :=
    CFSG.LieType.RootSystem.reflection_single_self (by simp [Symplectic.cartanC])
  have hεF : (ε : F) = 1 := by
    rcases hε with h | h <;> rw [h] <;> simp [CharTwo.neg_eq]
  have hconj1 : Symplectic.weylRep 1 F 0 * idSp_x F (Pi.single 0 1) 1 *
      (Symplectic.weylRep 1 F 0)⁻¹ = idSp_x F (-Pi.single 0 1) 1 := by
    have h := hconj 1
    rw [hreflect, hεF, one_mul] at h
    exact h
  have hA : (idSp_x F (Pi.single 0 1) r * idSp_x F (-Pi.single 0 1) s *
      idSp_x F (Pi.single 0 1) r) * idSp_x F (Pi.single 0 1) r *
      (idSp_x F (Pi.single 0 1) r * idSp_x F (-Pi.single 0 1) s *
        idSp_x F (Pi.single 0 1) r)⁻¹ = idSp_x F (-Pi.single 0 1) s := by
    apply hinj
    have h := congrArg β' hconj1
    rw [map_mul, map_mul, map_inv] at h
    rw [hβ'w, hβ'α 1, hβ'β 1] at h
    simp only [mul_one, ← map_mul, ← map_inv] at h
    exact h
  have hMN : idSp_x F (Pi.single 0 1) r * idSp_x F (-Pi.single 0 1) s *
      idSp_x F (Pi.single 0 1) r =
      idSp_x F (-Pi.single 0 1) s * idSp_x F (Pi.single 0 1) r *
        idSp_x F (-Pi.single 0 1) s := by
    have h2 : idSp_x F (Pi.single 0 1) r * idSp_x F (-Pi.single 0 1) s *
        idSp_x F (Pi.single 0 1) r * idSp_x F (Pi.single 0 1) r =
        idSp_x F (-Pi.single 0 1) s *
          (idSp_x F (Pi.single 0 1) r * idSp_x F (-Pi.single 0 1) s *
            idSp_x F (Pi.single 0 1) r) := by
      calc idSp_x F (Pi.single 0 1) r * idSp_x F (-Pi.single 0 1) s *
            idSp_x F (Pi.single 0 1) r * idSp_x F (Pi.single 0 1) r
          = (idSp_x F (Pi.single 0 1) r * idSp_x F (-Pi.single 0 1) s *
              idSp_x F (Pi.single 0 1) r * idSp_x F (Pi.single 0 1) r *
              (idSp_x F (Pi.single 0 1) r * idSp_x F (-Pi.single 0 1) s *
                idSp_x F (Pi.single 0 1) r)⁻¹) *
              (idSp_x F (Pi.single 0 1) r * idSp_x F (-Pi.single 0 1) s *
                idSp_x F (Pi.single 0 1) r) := by group
        _ = idSp_x F (-Pi.single 0 1) s *
              (idSp_x F (Pi.single 0 1) r * idSp_x F (-Pi.single 0 1) s *
                idSp_x F (Pi.single 0 1) r) := by rw [hA]
    calc idSp_x F (Pi.single 0 1) r * idSp_x F (-Pi.single 0 1) s *
          idSp_x F (Pi.single 0 1) r
        = (idSp_x F (Pi.single 0 1) r * idSp_x F (-Pi.single 0 1) s *
            idSp_x F (Pi.single 0 1) r * idSp_x F (Pi.single 0 1) r) *
            (idSp_x F (Pi.single 0 1) r)⁻¹ := by group
      _ = (idSp_x F (-Pi.single 0 1) s *
            (idSp_x F (Pi.single 0 1) r * idSp_x F (-Pi.single 0 1) s *
              idSp_x F (Pi.single 0 1) r)) * (idSp_x F (Pi.single 0 1) r)⁻¹ := by rw [h2]
      _ = idSp_x F (-Pi.single 0 1) s * idSp_x F (Pi.single 0 1) r *
            idSp_x F (-Pi.single 0 1) s := by group
  have hentry : r ^ 2 * s = r := by
    have h := congrArg (fun z => Symplectic.SpExtras.toBlock (Sum.inl 0) (Sum.inr 0)
      (Symplectic.SpExtras.mat 1 F z)) hMN
    rw [idSp_toBlock_M F r s, idSp_toBlock_N F r s] at h
    have h01 := congrFun (congrFun h 0) 1
    simpa using h01
  have hr0 : r ≠ 0 := by
    intro hr0
    have hxα0 : idSp_x F (Pi.single 0 1) (0 : F) = 1 := by
      simp only [idSp_x]
      rw [CFSG.LieType.Steinberg.Sp.x_eq idSp_hαstd]
      exact Symplectic.SpExtras.elt_zero _
    have hx : idSp_x F (Pi.single 0 1) 1 = 1 := by
      apply hinj
      rw [map_one]
      have h := hr 1
      rw [hr0, zero_mul, hxα0, map_one] at h
      calc ψ' (idSp_x F (Pi.single 0 1) 1)
          = x * (x⁻¹ * ψ' (idSp_x F (Pi.single 0 1) 1) * x) * x⁻¹ := by group
        _ = x * 1 * x⁻¹ := by rw [h]
        _ = 1 := by group
    have hne : idSp_x F (Pi.single 0 1) 1 ≠ 1 := by
      intro h1
      have h1' : (1 : F) = 0 := by
        have hh := congrArg (fun z => Symplectic.SpExtras.toBlock (Sum.inl 0) (Sum.inr 0)
          (Symplectic.SpExtras.mat 1 F z)) h1
        rw [idSp_mat_x_pos,
          Symplectic.SpExtras.toBlock_transvection_pq (p := Sum.inl 0) (q := Sum.inr 0)
            Sum.inl_ne_inr,
          map_one, Symplectic.SpExtras.toBlock_one (p := Sum.inl 0) (q := Sum.inr 0) Sum.inl_ne_inr]
          at hh
        have h01 := congrFun (congrFun hh 0) 1
        simpa using h01
      exact one_ne_zero h1'
    exact hne hx
  have hmul : r * (r * s - 1) = 0 := by
    rw [show r * (r * s - 1) = r ^ 2 * s - r by ring]
    rw [hentry, sub_self]
  rcases mul_eq_zero.mp hmul with h | h
  · exact absurd h hr0
  · exact sub_eq_zero.mp h

private theorem idSp_center_eq_bot (n : ℕ) (F : Type) [Field F] [CharP F 2] :
    Subgroup.center ↥(CFSG.Open.StatedSp n F) = ⊥ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine (Subgroup.eq_bot_iff_forall _).mpr fun x _ => ?_
    exact Subsingleton.elim x 1
  · exact CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two hn

private theorem idSp_mem_rootGroup_x_pos (F : Type) [Field F] {z : ↥(CFSG.Open.StatedSp 1 F)} :
    z ∈ Symplectic.rootGroup 1 F (Pi.single (0 : Fin 1) 1) ↔
      ∃ c, z = idSp_x F (Pi.single (0 : Fin 1) 1) c := by
  rw [Symplectic.SpExtras.mem_rootGroup_iff
    idSp_hαstd]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, (CFSG.LieType.Steinberg.Sp.x_eq idSp_hαstd c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, CFSG.LieType.Steinberg.Sp.x_eq idSp_hαstd c⟩

private theorem idSp_mem_rootGroup_x_neg (F : Type) [Field F] {z : ↥(CFSG.Open.StatedSp 1 F)} :
    z ∈ Symplectic.rootGroup 1 F (-Pi.single (0 : Fin 1) 1) ↔
      ∃ c, z = idSp_x F (-Pi.single (0 : Fin 1) 1) c := by
  rw [Symplectic.SpExtras.mem_rootGroup_iff
    idSp_hβstd]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, (CFSG.LieType.Steinberg.Sp.x_eq idSp_hβstd c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, CFSG.LieType.Steinberg.Sp.x_eq idSp_hβstd c⟩

private theorem idSp_exists_zero (F : Type) [Field F] {X : Type} [Group X]
    (ψ : ↥(CFSG.Open.StatedSp 0 F) →* X) (b : X) :
    ∃ s : ↥(CFSG.Open.StatedSp 0 F), ∀ u, b⁻¹ * ψ u * b = ψ (s * u * s⁻¹) := by
  refine ⟨1, fun u => ?_⟩
  rw [Subsingleton.elim u 1]
  simp

private theorem idSp_exists_ge_two (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
    {X : Type} [Group X] (ψ : ↥(CFSG.Open.StatedSp n F) →* X)
    (hψ : ψ.ker ≤ Subgroup.center ↥(CFSG.Open.StatedSp n F)) {b : X}
    (_hbN : b ∈ Subgroup.normalizer (ψ.range : Set X))
    (hb : GGPsiInnerDiag (Symplectic.rootDatum n F) ψ b) (hn : 2 ≤ n) :
    ∃ s : ↥(CFSG.Open.StatedSp n F), ∀ u, b⁻¹ * ψ u * b = ψ (s * u * s⁻¹) := by
  obtain ⟨g, hg, hgc⟩ := CFSG.StandardType.PsiDiag.Symp.exists_mem_centralizer hn ψ hψ hb
  obtain ⟨s, rfl⟩ := hg
  refine ⟨s, fun u => ?_⟩
  have key : ψ u * (b * ψ s) = (b * ψ s) * ψ u :=
    (Subgroup.mem_centralizer_iff.mp hgc) (ψ u) (ψ.mem_range.mpr ⟨u, rfl⟩)
  calc b⁻¹ * ψ u * b
      = b⁻¹ * (ψ u * (b * ψ s)) * (ψ s)⁻¹ := by group
    _ = b⁻¹ * ((b * ψ s) * ψ u) * (ψ s)⁻¹ := by rw [key]
    _ = ψ s * ψ u * (ψ s)⁻¹ := by group
    _ = ψ (s * u * s⁻¹) := by simp only [map_mul, map_inv]

private theorem idSp_exists_one (F : Type) [Field F] [CharP F 2] {X : Type} [Group X]
    (ψ : ↥(CFSG.Open.StatedSp 1 F) →* X)
    (hψ : ψ.ker ≤ Subgroup.center ↥(CFSG.Open.StatedSp 1 F)) {b : X}
    (_hbN : b ∈ Subgroup.normalizer (ψ.range : Set X))
    (hb : GGPsiInnerDiag (Symplectic.rootDatum 1 F) ψ b) :
    ∃ s : ↥(CFSG.Open.StatedSp 1 F), ∀ u, b⁻¹ * ψ u * b = ψ (s * u * s⁻¹) := by
  obtain ⟨g, hg, hγ⟩ := hb
  obtain ⟨u₀, rfl⟩ := hg
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact le_bot_iff.mp (hψ.trans (le_of_eq (idSp_center_eq_bot 1 F)))
  have hα : (Pi.single (0 : Fin 1) 1 : Fin 1 → ℤ) ∈ (Symplectic.rootDatum 1 F).roots :=
    Symplectic.SpExtras.mem_roots_of_stdVec
      idSp_hαstd
  have hβ : (-Pi.single (0 : Fin 1) 1 : Fin 1 → ℤ) ∈ (Symplectic.rootDatum 1 F).roots :=
    Symplectic.SpExtras.mem_roots_of_stdVec
      idSp_hβstd
  obtain ⟨hpos, hhpos, hzpos⟩ := hγ (Pi.single (0 : Fin 1) 1) hα
  obtain ⟨hneg, hhneg, hzneg⟩ := hγ (-Pi.single (0 : Fin 1) 1) hβ
  obtain ⟨r, hr⟩ := CFSG.StandardType.PsiDiag.Symp.ggTorus_conj_x
    (n := 1) (F := F) (Pi.single (0 : Fin 1) 1) hα hpos hhpos
  obtain ⟨ρ, hρ⟩ := CFSG.StandardType.PsiDiag.Symp.ggTorus_conj_x
    (n := 1) (F := F) (-Pi.single (0 : Fin 1) 1) hβ hpos hhpos
  obtain ⟨s, hs⟩ := CFSG.StandardType.PsiDiag.Symp.ggTorus_conj_x
    (n := 1) (F := F) (-Pi.single (0 : Fin 1) 1) hβ hneg hhneg
  have hr' : ∀ c, hpos * idSp_x F (Pi.single (0 : Fin 1) 1) c * hpos⁻¹ =
      idSp_x F (Pi.single (0 : Fin 1) 1) (r * c) := hr
  have hρ' : ∀ c, hpos * idSp_x F (-Pi.single (0 : Fin 1) 1) c * hpos⁻¹ =
      idSp_x F (-Pi.single (0 : Fin 1) 1) (ρ * c) := hρ
  have hs' : ∀ c, hneg * idSp_x F (-Pi.single (0 : Fin 1) 1) c * hneg⁻¹ =
      idSp_x F (-Pi.single (0 : Fin 1) 1) (s * c) := hs
  have hxα : ∀ c, (b * ψ u₀)⁻¹ * ψ (idSp_x F (Pi.single (0 : Fin 1) 1) c) * (b * ψ u₀) =
      ψ (idSp_x F (Pi.single (0 : Fin 1) 1) (r * c)) := by
    intro c
    have hz := hzpos (idSp_x F (Pi.single (0 : Fin 1) 1) c)
      ((idSp_mem_rootGroup_x_pos F).mpr ⟨c, rfl⟩)
    rw [hr' c] at hz
    exact hz
  have hxβn : ∀ c, (b * ψ u₀)⁻¹ * ψ (idSp_x F (-Pi.single (0 : Fin 1) 1) c) * (b * ψ u₀) =
      ψ (idSp_x F (-Pi.single (0 : Fin 1) 1) (s * c)) := by
    intro c
    have hz := hzneg (idSp_x F (-Pi.single (0 : Fin 1) 1) c)
      ((idSp_mem_rootGroup_x_neg F).mpr ⟨c, rfl⟩)
    rw [hs' c] at hz
    exact hz
  have hrs : r * s = 1 :=
    idSp_rankOne_scalar_product F ψ hinj (b * ψ u₀) r s hxα hxβn
  have hrρ : r * ρ = 1 :=
    idSp_rankOne_scalar_product F (MonoidHom.id ↥(CFSG.Open.StatedSp 1 F))
      Function.injective_id hpos⁻¹ r ρ hr' hρ'
  have hsρ : s = ρ := by
    have hr0 : r ≠ 0 := fun h0 => by rw [h0, zero_mul] at hrs; exact zero_ne_one hrs
    have h : r * s = r * ρ := by rw [hrs, hrρ]
    exact mul_left_cancel₀ hr0 h
  have hxβ : ∀ c, (b * ψ u₀)⁻¹ * ψ (idSp_x F (-Pi.single (0 : Fin 1) 1) c) * (b * ψ u₀) =
      ψ (idSp_x F (-Pi.single (0 : Fin 1) 1) (ρ * c)) := by
    intro c
    rw [← hsρ]
    exact hxβn c
  have hgen : (Symplectic.rootDatum 1 F).rootGroup (Pi.single (0 : Fin 1) 1) ⊔
      (Symplectic.rootDatum 1 F).rootGroup (-Pi.single (0 : Fin 1) 1) = ⊤ := by
    rw [← (Symplectic.isCTGroupDatum 1 F).iSup_eq_top]
    refine le_antisymm ?_ ?_
    · refine sup_le ?_ ?_
      · exact le_iSup₂_of_le _ hα le_rfl
      · exact le_iSup₂_of_le _ hβ le_rfl
    · refine iSup₂_le fun γ hγ => ?_
      obtain ⟨rr, hrr⟩ := Symplectic.SpExtras.exists_stdVec_of_mem_roots hγ
      have hcase : γ = Pi.single (0 : Fin 1) 1 ∨ γ = -Pi.single (0 : Fin 1) 1 := by
        cases rr with
        | positiveLong i =>
          have hi : i = 0 := Subsingleton.elim i 0
          rw [hi] at hrr
          left
          apply Symplectic.SpExtras.toStd_inj
          rw [← hrr]
          exact Symplectic.SpExtras.stdVec_positiveLong_eq (n := 1) (k := 0) (by omega)
        | negativeLong i =>
          have hi : i = 0 := Subsingleton.elim i 0
          rw [hi] at hrr
          right
          apply Symplectic.SpExtras.toStd_inj
          rw [← hrr]
          exact Symplectic.SpExtras.stdVec_negativeLong_eq (n := 1) (k := 0) (by omega)
        | difference i j hij => exact absurd (Subsingleton.elim i j) hij
        | positiveSum i j hij => exact absurd (Subsingleton.elim i j) (ne_of_lt hij)
        | negativeSum i j hij => exact absurd (Subsingleton.elim i j) (ne_of_lt hij)
      rcases hcase with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
  let φ₁ : ↥(CFSG.Open.StatedSp 1 F) →* X :=
    { toFun := fun u => b⁻¹ * ψ u * b
      map_one' := by simp
      map_mul' := fun u v => by simp only [map_mul]; group }
  let φ₂ : ↥(CFSG.Open.StatedSp 1 F) →* X :=
    { toFun := fun u => ψ ((u₀ * hpos) * u * (u₀ * hpos)⁻¹)
      map_one' := by simp
      map_mul' := fun u v => by
        rw [← map_mul]
        congr 1
        group }
  have hα_agree : ∀ z ∈ Symplectic.rootGroup 1 F (Pi.single (0 : Fin 1) 1), φ₁ z = φ₂ z := by
    intro z hz
    obtain ⟨c, rfl⟩ := (idSp_mem_rootGroup_x_pos F).mp hz
    change b⁻¹ * ψ (idSp_x F (Pi.single (0 : Fin 1) 1) c) * b =
      ψ ((u₀ * hpos) * idSp_x F (Pi.single (0 : Fin 1) 1) c * (u₀ * hpos)⁻¹)
    calc b⁻¹ * ψ (idSp_x F (Pi.single (0 : Fin 1) 1) c) * b
        = ψ u₀ * ((b * ψ u₀)⁻¹ * ψ (idSp_x F (Pi.single (0 : Fin 1) 1) c) * (b * ψ u₀)) *
            ψ u₀⁻¹ := by simp only [map_inv]; group
      _ = ψ u₀ * ψ (idSp_x F (Pi.single (0 : Fin 1) 1) (r * c)) * ψ u₀⁻¹ := by rw [hxα c]
      _ = ψ (u₀ * idSp_x F (Pi.single (0 : Fin 1) 1) (r * c) * u₀⁻¹) := by
        simp only [← map_mul, ← map_inv]
      _ = ψ ((u₀ * hpos) * idSp_x F (Pi.single (0 : Fin 1) 1) c * (u₀ * hpos)⁻¹) := by
        rw [← hr' c]
        congr 1
        group
  have hβ_agree : ∀ z ∈ Symplectic.rootGroup 1 F (-Pi.single (0 : Fin 1) 1), φ₁ z = φ₂ z := by
    intro z hz
    obtain ⟨c, rfl⟩ := (idSp_mem_rootGroup_x_neg F).mp hz
    change b⁻¹ * ψ (idSp_x F (-Pi.single (0 : Fin 1) 1) c) * b =
      ψ ((u₀ * hpos) * idSp_x F (-Pi.single (0 : Fin 1) 1) c * (u₀ * hpos)⁻¹)
    calc b⁻¹ * ψ (idSp_x F (-Pi.single (0 : Fin 1) 1) c) * b
        = ψ u₀ * ((b * ψ u₀)⁻¹ * ψ (idSp_x F (-Pi.single (0 : Fin 1) 1) c) * (b * ψ u₀)) *
            ψ u₀⁻¹ := by simp only [map_inv]; group
      _ = ψ u₀ * ψ (idSp_x F (-Pi.single (0 : Fin 1) 1) (ρ * c)) * ψ u₀⁻¹ := by rw [hxβ c]
      _ = ψ (u₀ * idSp_x F (-Pi.single (0 : Fin 1) 1) (ρ * c) * u₀⁻¹) := by
        simp only [← map_mul, ← map_inv]
      _ = ψ ((u₀ * hpos) * idSp_x F (-Pi.single (0 : Fin 1) 1) c * (u₀ * hpos)⁻¹) := by
        rw [← hρ' c]
        congr 1
        group
  let E : Subgroup ↥(CFSG.Open.StatedSp 1 F) :=
    { carrier := {u | φ₁ u = φ₂ u}
      one_mem' := by simp
      mul_mem' := fun {u v} hu hv => by
        simp only [Set.mem_setOf_eq] at hu hv ⊢
        rw [map_mul, map_mul, hu, hv]
      inv_mem' := fun {u} hu => by
        simp only [Set.mem_setOf_eq] at hu ⊢
        rw [map_inv, map_inv, hu] }
  have hE : (Symplectic.rootDatum 1 F).rootGroup (Pi.single (0 : Fin 1) 1) ⊔
      (Symplectic.rootDatum 1 F).rootGroup (-Pi.single (0 : Fin 1) 1) ≤ E := by
    refine sup_le ?_ ?_
    · intro z hz; exact hα_agree z hz
    · intro z hz; exact hβ_agree z hz
  have hEt : E = ⊤ := by
    rw [hgen] at hE
    exact top_le_iff.mp hE
  refine ⟨u₀ * hpos, fun u => ?_⟩
  exact (show u ∈ E from by rw [hEt]; exact Subgroup.mem_top u)

theorem exists_conj_eq_PSp (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] {X : Type} [Group X]
    (ψ : ↥(CFSG.Open.StatedSp n F) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {b : X} (hbN : b ∈ Subgroup.normalizer (ψ.range : Set X))
    (hb : GGPsiInnerDiag (Symplectic.rootDatum n F) ψ b) :
    ∃ s : ↥(CFSG.Open.StatedSp n F), ∀ u, b⁻¹ * ψ u * b = ψ (s * u * s⁻¹) := by
  rcases n with _ | _ | n
  · exact idSp_exists_zero F ψ b
  · exact idSp_exists_one F ψ hψ hbN hb
  · exact idSp_exists_ge_two (n + 2) F ψ hψ hbN hb (by omega)

theorem conj_eq_unique_PSp (n : ℕ) (F : Type) [Field F] [CharP F 2] {X : Type} [Group X]
    (ψ : ↥(CFSG.Open.StatedSp n F) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {s s' : ↥(CFSG.Open.StatedSp n F)}
    (hss' : ∀ u, ψ (s * u * s⁻¹) = ψ (s' * u * s'⁻¹)) : s = s' := by
  have hcenter : Subgroup.center ↥(CFSG.Open.StatedSp n F) = ⊥ := idSp_center_eq_bot n F
  have hker : ψ.ker = ⊥ := le_bot_iff.mp (hψ.trans (le_of_eq hcenter))
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hker
  let w : ↥(CFSG.Open.StatedSp n F) := s'⁻¹ * s
  have hwu : ∀ u, w * u * w⁻¹ = u := by
    intro u
    apply hinj
    have key : ψ (w * u * w⁻¹) = ψ (s'⁻¹ * (s * u * s⁻¹) * s') := by
      congr 1
      change (s'⁻¹ * s) * u * (s'⁻¹ * s)⁻¹ = s'⁻¹ * (s * u * s⁻¹) * s'
      group
    rw [key]
    have h := congrArg (fun t => ψ s'⁻¹ * t * ψ s') (hss' u)
    simp only [map_mul, map_inv] at h ⊢
    rw [h]
    group
  have hwcenter : w ∈ Subgroup.center ↥(CFSG.Open.StatedSp n F) := by
    rw [Subgroup.mem_center_iff]
    intro u
    calc u * w = (w * u * w⁻¹) * w := by rw [hwu u]
      _ = w * u := by group
  have hw1 : w = 1 := by
    have : w ∈ (⊥ : Subgroup ↥(CFSG.Open.StatedSp n F)) := by simpa [hcenter] using hwcenter
    simpa using this
  have hs : s'⁻¹ * s = 1 := hw1
  exact (inv_mul_eq_one.mp hs).symm

theorem conj_eq_commute_PSp (n : ℕ) (F : Type) [Field F] [CharP F 2] {X : Type} [Group X]
    (ψ : ↥(CFSG.Open.StatedSp n F) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {b b' : X} (hbb' : Commute b b')
    {s s' : ↥(CFSG.Open.StatedSp n F)}
    (hs : ∀ u, b⁻¹ * ψ u * b = ψ (s * u * s⁻¹)) (hs' : ∀ u, b'⁻¹ * ψ u * b' = ψ (s' * u * s'⁻¹)) :
    Commute s s' := by
  rw [Commute]
  apply conj_eq_unique_PSp n F ψ hψ
  intro u
  have h1 : (b * b')⁻¹ * ψ u * (b * b') = ψ ((s' * s) * u * (s' * s)⁻¹) := by
    have e1 : (b * b')⁻¹ * ψ u * (b * b') = b'⁻¹ * (b⁻¹ * ψ u * b) * b' := by group
    rw [e1, hs u, hs' (s * u * s⁻¹)]
    congr 1
    group
  have h2 : (b * b')⁻¹ * ψ u * (b * b') = ψ ((s * s') * u * (s * s')⁻¹) := by
    rw [hbb'.eq]
    have e1 : (b' * b)⁻¹ * ψ u * (b' * b) = b⁻¹ * (b'⁻¹ * ψ u * b') * b := by group
    rw [e1, hs' u, hs (s' * u * s'⁻¹)]
    congr 1
    group
  rw [← h2, h1]


end CFSG.StandardType.ClassicalPosition

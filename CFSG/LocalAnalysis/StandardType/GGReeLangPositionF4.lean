module

public import CFSG.RankThree.PartOne.TCX.Ree.Closure
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly
import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyClosedLang
import CFSG.LieType.AlgebraicGroups.ToralCentralizerComponent
import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerLangCurves
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
import CFSG.RankThree.PartOne.KLR.FrameTorus
import CFSG.LieType.AlgebraicGroups.SeminaireExp3Basic
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.CTMain
public import CFSG.RankThree.PartOne.KLR.CoreGroup
public import CFSG.RankThree.PartOne.KLR.FrobTrick
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities

public noncomputable section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Ree CFSG.RankThree.PartOne.TCX.Ree CFSG.RankThree.PartOne.RF4 WithConv

open scoped CFSG.ConvolutionPoints

theorem ggReeLangAux_exists_S0_co
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (C : ReeClosure L) (b : ℕ) :
    ∃ σ₀ : (realizedCoord ReeTag.F4.tag L) →ₐc[L] (realizedCoord ReeTag.F4.tag L), (∀ φ, realizedPointEquiv ReeTag.F4.tag L (pointMap σ₀ φ) = (C.Φ * C.Fr ^ b) (realizedPointEquiv ReeTag.F4.tag L φ)) ∧
      ∀ D ∈ tangentSpace L (realizedCoord ReeTag.F4.tag L) (Bialgebra.counitAlgHom L (realizedCoord ReeTag.F4.tag L)),
        D ∘ₗ ((σ₀ : (realizedCoord ReeTag.F4.tag L) →ₐ[L] (realizedCoord ReeTag.F4.tag L)) ^ 2).toLinearMap = 0 := by
  have : CharP L ReeTag.F4.prime := ‹CharP L 2›
  have hli := linearIndependent_pinnedE_tangentH_F4 (F := L)
  obtain ⟨σ, hσ, -, ⟨Frc, hFrc⟩, hall⟩ := exceptional_Lang_ree_map_regularity C.isExc hli
  obtain ⟨-, -, hpow⟩ := hall Frc hFrc
  obtain ⟨-, hD⟩ := hpow b
  have hFrc' : ∀ φ, realizedPointEquiv ReeTag.F4.tag L (pointMap Frc φ) = C.Fr (realizedPointEquiv ReeTag.F4.tag L φ) := fun φ =>
    Subtype.ext (by rw [hFrc, C.fr_apply]; rfl)
  refine ⟨Frc ^ b * σ, fun φ => ?_, fun D hDT => by rw [sq]; exact hD D hDT⟩
  rw [pointMap_mul, hσ, realizedPointEquiv_pointMap_pow' ReeTag.F4.tag Frc C.Fr hFrc', MulAut.mul_apply]

abbrev ggReeLangAux_famSub {L : Type} [Field L]
    {ι : Type} (b : ι → Fin ReeTag.F4.tag.rank → Lˣ) : Subgroup (adjointGroup ReeTag.F4.tag L) :=
  (familyGroup (τ := ReeTag.F4.tag) (K := L) b).subgroupOf (adjointGroup ReeTag.F4.tag L)

abbrev ggReeLangAux_famSubImage {L : Type} [Field L]
    [IsAlgClosed L] {ι : Type} (b : ι → Fin ReeTag.F4.tag.rank → Lˣ) :
    Subgroup (WithConv ((realizedCoord ReeTag.F4.tag L) →ₐ[L] L)) :=
  (ggReeLangAux_famSub b).map (realizedPointEquiv ReeTag.F4.tag L).symm.toMonoidHom

private theorem ggReeLangAux_modGLPoint_E {L : Type} [Field L] [IsAlgClosed L]
    (φ : WithConv ((realizedCoord ReeTag.F4.tag L) →ₐ[L] L)) :
    modGLPoint ReeTag.F4.tag L (realizedPointEquiv ReeTag.F4.tag L φ : ModGL ReeTag.F4.tag L) = toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ L _)) := by
  rw [coe_realizedPointEquiv, MulEquiv.apply_symm_apply]

private theorem ggReeLangAux_mem_transport_iff {L : Type} [Field L] [IsAlgClosed L]
    {ι : Type} (b : ι → Fin ReeTag.F4.tag.rank → Lˣ) (y : (realizedCoord ReeTag.F4.tag L) →ₐ[L] L) :
    y ∈ transportPoints (realizedPointEquiv ReeTag.F4.tag L).symm (ggReeLangAux_famSub b) ↔
      y.comp (Ideal.Quotient.mkₐ L _) ∈
        transportPoints (modGLPoint ReeTag.F4.tag L) (familyGroup (τ := ReeTag.F4.tag) (K := L) b : Set (ModGL ReeTag.F4.tag L)) := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g, Subgroup.mem_subgroupOf.1 hg, ?_⟩
    have := ggReeLangAux_modGLPoint_E ((realizedPointEquiv ReeTag.F4.tag L).symm g)
    rw [MulEquiv.apply_symm_apply] at this
    beta_reduce
    rw [this, ofConv_toConv]
  · rintro ⟨h, hh, hy⟩
    refine ⟨realizedPointEquiv ReeTag.F4.tag L (toConv y), Subgroup.mem_subgroupOf.2 ?_, by simp only [MulEquiv.symm_apply_apply, ofConv_toConv]⟩
    have h1 := ggReeLangAux_modGLPoint_E (toConv y)
    rw [ofConv_toConv, ← hy, toConv_ofConv] at h1
    rw [(modGLPoint ReeTag.F4.tag L).injective h1]
    exact hh

private theorem ggReeLangAux_famSub_points {L : Type} [Field L] [IsAlgClosed L]
    {ι : Type} (b : ι → Fin ReeTag.F4.tag.rank → Lˣ) :
    IsPointClosed L (transportPoints (realizedPointEquiv ReeTag.F4.tag L).symm (ggReeLangAux_famSub b)) ∧
      IsPointIrreducible L (transportPoints (realizedPointEquiv ReeTag.F4.tag L).symm (ggReeLangAux_famSub b)) := by
  set π := Ideal.Quotient.mkₐ L (subgroupIdeal (adjointPointSubgroup ReeTag.F4.tag L))
  have hset : transportPoints (realizedPointEquiv ReeTag.F4.tag L).symm (ggReeLangAux_famSub b) =
      {y | y.comp π ∈ transportPoints (modGLPoint ReeTag.F4.tag L) (familyGroup (τ := ReeTag.F4.tag) (K := L) b : Set _)} := by
    ext y; exact ggReeLangAux_mem_transport_iff b y
  have hcl : IsPointClosed L (transportPoints (realizedPointEquiv ReeTag.F4.tag L).symm (ggReeLangAux_famSub b)) := by
    rw [hset]; exact (isPointClosed_familyGroup b).preimage_comp π
  have hirr : IsPointIrreducible L (transportPoints (realizedPointEquiv ReeTag.F4.tag L).symm (ggReeLangAux_famSub b)) := by
    have h := isPointIrreducible_familyGroup (k := L) b
    have himg : PrimeSpectrum.comap (π : _ →+* (realizedCoord ReeTag.F4.tag L)) '' (pointSpec '' transportPoints (realizedPointEquiv ReeTag.F4.tag L).symm
        (ggReeLangAux_famSub b)) = pointSpec '' transportPoints (modGLPoint ReeTag.F4.tag L)
          (familyGroup (τ := ReeTag.F4.tag) (K := L) b : Set _) := by
      rw [Set.image_image]
      ext q
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.comp π, (ggReeLangAux_mem_transport_iff b y).1 hy, (comap_pointSpec π y).symm⟩
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨h, hh, rfl⟩ := hz
        refine ⟨((realizedPointEquiv ReeTag.F4.tag L).symm ⟨h, ?_⟩).ofConv, ⟨_, Subgroup.mem_subgroupOf.2 hh, rfl⟩, ?_⟩
        · exact ((mem_familyCentralizer).1 (familyGroup_le_familyCentralizer b hh)).1
        · beta_reduce
          rw [comap_pointSpec]
          congr 1
    rw [IsPointIrreducible, ← himg] at h
    exact (SeminaireExp3.isIrreducible_image_iff_of_isInducing
      (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
        (Ideal.Quotient.mkₐ_surjective L _)).isInducing).1 h
  exact ⟨hcl, hirr⟩

theorem ggReeLangAux_isConnected_famSub {L : Type} [Field L] [IsAlgClosed L]
    {ι : Type} (b : ι → Fin ReeTag.F4.tag.rank → Lˣ) :
    IsConnectedAlgebraicSubgroup L
      ((ggReeLangAux_famSub b).map (realizedPointEquiv ReeTag.F4.tag L).symm.toMonoidHom) :=
  (isConnectedAlgebraicSubgroup_map (realizedPointEquiv ReeTag.F4.tag L).symm (ggReeLangAux_famSub b)
    (ggReeLangAux_famSub_points b).1.isPointConstructible (ggReeLangAux_famSub_points b).2).2.1

private theorem ggReeLangAux_famSub_coset
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (C : ReeClosure L) (b' : ℕ) {ι : Type} (b : ι → Fin ReeTag.F4.tag.rank → Lˣ)
    (d : ι → adjointGroup ReeTag.F4.tag L)
    (hd : ∀ i, (d i : ModGL ReeTag.F4.tag L) = rootDiagUnit ReeTag.F4.tag (b i))
    (u : adjointGroup ReeTag.F4.tag L)
    (hu : ∀ i, u * (C.Φ * C.Fr ^ b') (d i) * u⁻¹ = d i) :
    ∃ (σ₀ : (realizedCoord ReeTag.F4.tag L) →ₐc[L] (realizedCoord ReeTag.F4.tag L))
      (v : WeylGroup ReeTag.F4.tag),
      (∀ φ, realizedPointEquiv ReeTag.F4.tag L (pointMap σ₀ φ) =
        (C.Φ * C.Fr ^ b') (realizedPointEquiv ReeTag.F4.tag L φ)) ∧
      (∀ D ∈ tangentSpace L (realizedCoord ReeTag.F4.tag L)
        (Bialgebra.counitAlgHom L (realizedCoord ReeTag.F4.tag L)),
        D ∘ₗ (((σ₀ : (realizedCoord ReeTag.F4.tag L) →ₐ[L] (realizedCoord ReeTag.F4.tag L)) ^ 2).toLinearMap) = 0) ∧
      (∀ y ∈ subgroupPoints ((ggReeLangAux_famSub b).map
        (realizedPointEquiv ReeTag.F4.tag L).symm.toMonoidHom),
        y.comp (((σ₀ : (realizedCoord ReeTag.F4.tag L) →ₐ[L] (realizedCoord ReeTag.F4.tag L)).comp
          (innerCo ((realizedPointEquiv ReeTag.F4.tag L).symm u)))) ∈
          subgroupPoints ((ggReeLangAux_famSub b).map
            (realizedPointEquiv ReeTag.F4.tag L).symm.toMonoidHom)) := by
  classical
  obtain ⟨σ₀, hσ₀, hD⟩ := ggReeLangAux_exists_S0_co C b'
  set S := C.Φ * C.Fr ^ b' with hS
  set Eq := realizedPointEquiv ReeTag.F4.tag L with hEq
  set x := Eq.symm u with hx
  set t : (realizedCoord ReeTag.F4.tag L) →ₐ[L] (realizedCoord ReeTag.F4.tag L) :=
    (σ₀ : (realizedCoord ReeTag.F4.tag L) →ₐ[L] (realizedCoord ReeTag.F4.tag L)).comp (innerCo x)
    with htdef
  have ht : ∀ y : WithConv ((realizedCoord ReeTag.F4.tag L) →ₐ[L] L),
      Eq (toConv (y.ofConv.comp t)) = u * S (Eq y) * u⁻¹ := by
    intro y
    rw [htdef, point_comp_twist, map_mul, map_mul, map_inv, hσ₀, hx, MulEquiv.apply_symm_apply]
  set Fb := ggReeLangAux_famSub b with hFb
  set G' := Fb.map Eq.symm.toMonoidHom with hG'def
  have hG' : IsConnectedAlgebraicSubgroup L G' := ggReeLangAux_isConnected_famSub b
  have hmemG' : ∀ y : (realizedCoord ReeTag.F4.tag L) →ₐ[L] L,
      y ∈ subgroupPoints G' ↔ Eq (toConv y) ∈ Fb := by
    intro y
    change toConv y ∈ G' ↔ _
    rw [hG'def, Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  have hP : subgroupPoints G' = transportPoints Eq.symm Fb := subgroupPoints_map _ _
  obtain ⟨hclP, hirrP⟩ := ggReeLangAux_famSub_points b
  rw [← hP] at hclP hirrP
  have hcomm : ∀ g ∈ Fb, ∀ i, d i * g * (d i)⁻¹ = g := by
    intro g hg i
    have h := ((mem_familyCentralizer).1
      (familyGroup_le_familyCentralizer b (Subgroup.mem_subgroupOf.1 hg))).2 i
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hd]
    exact h
  have hcent : ∀ g ∈ Fb, ((u * S g * u⁻¹ : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) ∈
      familyCentralizer ReeTag.F4.tag L b := by
    intro g hg
    refine (mem_familyCentralizer).2 ⟨(u * S g * u⁻¹).2, fun i => ?_⟩
    have h1 : d i * (u * S g * u⁻¹) * (d i)⁻¹ = u * S g * u⁻¹ := by
      calc d i * (u * S g * u⁻¹) * (d i)⁻¹
          = (u * S (d i) * u⁻¹) * (u * S g * u⁻¹) * (u * S (d i) * u⁻¹)⁻¹ := by rw [hu i]
        _ = u * S (d i * g * (d i)⁻¹) * u⁻¹ := by simp only [map_mul, map_inv]; group
        _ = u * S g * u⁻¹ := by rw [hcomm g hg i]
    rw [← hd i]
    exact congrArg Subtype.val h1
  have : Fintype (WeylGroup ReeTag.F4.tag) := Fintype.ofFinite _
  let nG : WeylGroup ReeTag.F4.tag → adjointGroup ReeTag.F4.tag L := fun v =>
    ⟨canonicalRep (coxeterSystem ReeTag.F4.tag) L v, canonicalRep_mem_adjointGroup _ L v⟩
  have hT : ∀ v, IsPointClosed L
      {y | y.comp (rightTransCo (Eq.symm (nG v))⁻¹) ∈ subgroupPoints G'} :=
    fun v => hclP.preimage_comp _
  choose Z hZ hZeq using hT
  have hTmem : ∀ v (y : (realizedCoord ReeTag.F4.tag L) →ₐ[L] L),
      y.comp (rightTransCo (Eq.symm (nG v))⁻¹) ∈ subgroupPoints G' ↔
        Eq (toConv y) * (nG v)⁻¹ ∈ Fb := by
    intro v y
    rw [hmemG', point_comp_rightTransCo, map_mul, map_inv, MulEquiv.apply_symm_apply]
  set Y := pointSpec '' ((fun y => y.comp t) '' subgroupPoints G') with hY
  have hYirr : IsIrreducible Y := by
    have : Y = PrimeSpectrum.comap (t : _ →+* _) '' (pointSpec '' subgroupPoints G') := by
      rw [hY, Set.image_image, Set.image_image]
      simp only [comap_pointSpec]
    rw [this]
    exact hirrP.image _ (PrimeSpectrum.continuous_comap _).continuousOn
  have hYcov : Y ⊆ ⋃₀ ↑(Finset.univ.image Z) := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    set g := Eq (toConv y)
    have hg : g ∈ Fb := (hmemG' y).1 hy
    obtain ⟨w, -, m, hm, hmw⟩ := familyCentralizer_le_mul ReeTag.F4.tag L b (hcent g hg)
    refine Set.mem_sUnion.2 ⟨Z w, Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ _)),
      ?_⟩
    have hyw : y.comp t ∈ {y | y.comp (rightTransCo (Eq.symm (nG w))⁻¹) ∈ subgroupPoints G'} := by
      change _ ∈ subgroupPoints G'
      rw [hTmem]
      have e1 : Eq (toConv (y.comp t)) = u * S g * u⁻¹ := by
        have := ht (toConv y); rwa [ofConv_toConv] at this
      rw [e1]
      refine Subgroup.mem_subgroupOf.2 ?_
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hmw]
      simpa [nG] using hm
    rw [hZeq w] at hyw
    exact hyw
  obtain ⟨_, hz, hYz⟩ := (isIrreducible_iff_sUnion_isClosed.1 hYirr) _ (by
    intro z hz
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hz
    exact hZ v) hYcov
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hz
  have hmemT : ∀ y ∈ subgroupPoints G', Eq (toConv (y.comp t)) * (nG v)⁻¹ ∈ Fb := by
    intro y hy
    have h1 : pointSpec (y.comp t) ∈ Z v := hYz ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [← Set.mem_preimage, ← hZeq v] at h1
    exact (hTmem v _).1 h1
  have h1P : (1 : WithConv ((realizedCoord ReeTag.F4.tag L) →ₐ[L] L)).ofConv ∈ subgroupPoints G' := by
    change toConv _ ∈ G'
    rw [toConv_ofConv]
    exact G'.one_mem
  have hnv : (nG v)⁻¹ ∈ Fb := by
    have h := hmemT _ h1P
    rwa [toConv_ofConv, ht, map_one, map_one, mul_one, mul_inv_cancel, one_mul] at h
  have hφ : ∀ y ∈ subgroupPoints G', y.comp t ∈ subgroupPoints G' := by
    intro y hy
    rw [hmemG']
    have h := Fb.mul_mem (hmemT y hy) (Fb.inv_mem hnv)
    rwa [inv_inv, inv_mul_cancel_right] at h
  refine ⟨σ₀, v, hσ₀, hD, ?_⟩
  simpa [htdef, hx, hEq, hFb, hG'def] using hφ

theorem ggReeLangAux_famSub_sigmaB
    {L : Type} [Field L] [IsAlgClosed L] {ι : Type} (b : ι → Fin ReeTag.F4.tag.rank → Lˣ)
    (σ₀ : (realizedCoord ReeTag.F4.tag L) →ₐc[L] (realizedCoord ReeTag.F4.tag L))
    (u : adjointGroup ReeTag.F4.tag L)
    (hD : ∀ D ∈ tangentSpace L (realizedCoord ReeTag.F4.tag L)
      (Bialgebra.counitAlgHom L (realizedCoord ReeTag.F4.tag L)),
      D ∘ₗ (((σ₀ : (realizedCoord ReeTag.F4.tag L) →ₐ[L] (realizedCoord ReeTag.F4.tag L)) ^ 2).toLinearMap) = 0)
    (hφ : ∀ y ∈ subgroupPoints (ggReeLangAux_famSubImage b),
      y.comp (((σ₀ : (realizedCoord ReeTag.F4.tag L) →ₐ[L] (realizedCoord ReeTag.F4.tag L)).comp
        (innerCo ((realizedPointEquiv ReeTag.F4.tag L).symm u)))) ∈
        subgroupPoints (ggReeLangAux_famSubImage b)) :
    ∃ σB : (realizedCoord ReeTag.F4.tag L ⧸
        subgroupIdeal (ggReeLangAux_famSubImage b)) →ₐc[L]
        (realizedCoord ReeTag.F4.tag L ⧸ subgroupIdeal (ggReeLangAux_famSubImage b)),
      (∀ a, (σB : (realizedCoord ReeTag.F4.tag L ⧸ subgroupIdeal (ggReeLangAux_famSubImage b)) →ₐ[L]
          (realizedCoord ReeTag.F4.tag L ⧸ subgroupIdeal (ggReeLangAux_famSubImage b)))
        (Ideal.Quotient.mkₐ L (subgroupIdeal (ggReeLangAux_famSubImage b)) a) =
        Ideal.Quotient.mkₐ L (subgroupIdeal (ggReeLangAux_famSubImage b))
          (((σ₀ : (realizedCoord ReeTag.F4.tag L) →ₐ[L] (realizedCoord ReeTag.F4.tag L)).comp
            (innerCo ((realizedPointEquiv ReeTag.F4.tag L).symm u))) a)) ∧
      ∀ D ∈ tangentSpace L (realizedCoord ReeTag.F4.tag L ⧸ subgroupIdeal (ggReeLangAux_famSubImage b))
        (Bialgebra.counitAlgHom L _),
        D ∘ₗ (((σB : (realizedCoord ReeTag.F4.tag L ⧸ subgroupIdeal (ggReeLangAux_famSubImage b)) →ₐ[L]
          (realizedCoord ReeTag.F4.tag L ⧸ subgroupIdeal (ggReeLangAux_famSubImage b))) ^ 2).toLinearMap) = 0 := by
  classical
  set Eq := realizedPointEquiv ReeTag.F4.tag L with hEq
  set x := Eq.symm u with hx
  set t : (realizedCoord ReeTag.F4.tag L) →ₐ[L] (realizedCoord ReeTag.F4.tag L) :=
    (σ₀ : (realizedCoord ReeTag.F4.tag L) →ₐ[L] (realizedCoord ReeTag.F4.tag L)).comp (innerCo x)
    with htdef
  set Fb := ggReeLangAux_famSub b with hFb
  set G' := Fb.map Eq.symm.toMonoidHom with hG'def
  have hG' : IsConnectedAlgebraicSubgroup L G' := ggReeLangAux_isConnected_famSub b
  have hmul : ∀ y z : WithConv ((realizedCoord ReeTag.F4.tag L) →ₐ[L] L),
      toConv ((y * z).ofConv.comp t) = toConv (y.ofConv.comp t) * toConv (z.ofConv.comp t) := by
    intro y z
    rw [htdef, point_comp_twist, point_comp_twist, point_comp_twist, map_mul]
    group
  have := hG'.finiteType
  have := hG'.isReduced
  have := hG'.smooth.1
  have := hG'.connectedSpace
  set π := Ideal.Quotient.mkₐ L (subgroupIdeal G') with hπ
  set σB := bialgHomOfPointMul (quotientCo G' t hφ) (quotientCo_pointMul G' t hφ hmul) with hσB
  have hσBπ : ∀ a, (σB : (realizedCoord ReeTag.F4.tag L ⧸ subgroupIdeal G') →ₐ[L] (realizedCoord ReeTag.F4.tag L ⧸ subgroupIdeal G')) (π a) = π (t a) := fun a => rfl
  have hzero : ∀ D ∈ tangentSpace L (realizedCoord ReeTag.F4.tag L ⧸ subgroupIdeal G')
      (Bialgebra.counitAlgHom L _),
      D ∘ₗ (((σB : (realizedCoord ReeTag.F4.tag L ⧸ subgroupIdeal G') →ₐ[L] (realizedCoord ReeTag.F4.tag L ⧸ subgroupIdeal G'))) ^ 2).toLinearMap = 0 := by
    intro D hDt
    have hc : (Bialgebra.counitAlgHom L (realizedCoord ReeTag.F4.tag L ⧸ subgroupIdeal G')).comp π =
        Bialgebra.counitAlgHom L (realizedCoord ReeTag.F4.tag L) :=
      AlgHom.ext fun _ => rfl
    have hDπ : D ∘ₗ π.toLinearMap ∈ tangentSpace L (realizedCoord ReeTag.F4.tag L)
        (Bialgebra.counitAlgHom L _) := (tangentMap π hc ⟨D, hDt⟩).2
    have h2 := twist_pow σ₀ x 2
    refine LinearMap.ext fun e => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective L (subgroupIdeal G') e
    have e1 : ((σB : (realizedCoord ReeTag.F4.tag L ⧸ subgroupIdeal G') →ₐ[L] (realizedCoord ReeTag.F4.tag L ⧸ subgroupIdeal G')) ^ 2) (π a) = π ((t ^ 2) a) := by
      rw [sq, sq, AlgHom.mul_apply, hσBπ, hσBπ, AlgHom.mul_apply]
    have h3 := congrArg (fun f => f ((innerCo ((List.range 2).map
      fun i => (pointMap σ₀)^[i] x).prod) a)) (hD _ hDπ)
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.zero_apply] at h3
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.zero_apply]
    rw [e1, htdef, h2, AlgHom.comp_apply]
    exact h3
  refine ⟨σB, hσBπ, ?_⟩
  exact hzero

private theorem ggReeLangAux_lang_famSub
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (C : ReeClosure L) (b' : ℕ) {ι : Type} (b : ι → Fin ReeTag.F4.tag.rank → Lˣ)
    (d : ι → adjointGroup ReeTag.F4.tag L)
    (hd : ∀ i, (d i : ModGL ReeTag.F4.tag L) = rootDiagUnit ReeTag.F4.tag (b i))
    (u : adjointGroup ReeTag.F4.tag L)
    (hu : ∀ i, u * (C.Φ * C.Fr ^ b') (d i) * u⁻¹ = d i) :
    ∀ c : adjointGroup ReeTag.F4.tag L, (c : ModGL ReeTag.F4.tag L) ∈ familyGroup (K := L) b →
      ∃ z : adjointGroup ReeTag.F4.tag L, (z : ModGL ReeTag.F4.tag L) ∈ familyGroup (K := L) b ∧
        z⁻¹ * (u * (C.Φ * C.Fr ^ b') z * u⁻¹) = c := by
  classical
  obtain ⟨σ₀, v, hσ₀, hD, hφ⟩ := ggReeLangAux_famSub_coset C b' b d hd u hu
  obtain ⟨σB, hσBπ, hzero⟩ := ggReeLangAux_famSub_sigmaB b σ₀ u hD hφ
  set S := C.Φ * C.Fr ^ b' with hS
  set Eq := realizedPointEquiv ReeTag.F4.tag L with hEq
  set x := Eq.symm u with hx
  set t : (realizedCoord ReeTag.F4.tag L) →ₐ[L] (realizedCoord ReeTag.F4.tag L) :=
    (σ₀ : (realizedCoord ReeTag.F4.tag L) →ₐ[L] (realizedCoord ReeTag.F4.tag L)).comp (innerCo x)
    with htdef
  have ht : ∀ y : WithConv ((realizedCoord ReeTag.F4.tag L) →ₐ[L] L),
      Eq (toConv (y.ofConv.comp t)) = u * S (Eq y) * u⁻¹ := by
    intro y
    rw [htdef, point_comp_twist, map_mul, map_mul, map_inv, hσ₀, hx, MulEquiv.apply_symm_apply]
  set Fb := ggReeLangAux_famSub b with hFb
  set G' := Fb.map Eq.symm.toMonoidHom with hG'def
  have hG' : IsConnectedAlgebraicSubgroup L G' := ggReeLangAux_isConnected_famSub b
  have hmemG' : ∀ y : (realizedCoord ReeTag.F4.tag L) →ₐ[L] L,
      y ∈ subgroupPoints G' ↔ Eq (toConv y) ∈ Fb := by
    intro y
    change toConv y ∈ G' ↔ _
    rw [hG'def, Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  have := hG'.finiteType
  have := hG'.isReduced
  have := hG'.smooth.1
  have := hG'.connectedSpace
  set π := Ideal.Quotient.mkₐ L (subgroupIdeal G') with hπ
  intro c hc
  set eB := subgroupQuotientPointsEquiv G' hG'.pointsZero_eq with heB
  have hcG : Eq.symm c ∈ G' := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hc)
  obtain ⟨h, hh⟩ := exceptional_Lang_connected_twisted_orbit_surjectivity σB (m := 2)
    (by norm_num) hzero (eB.symm ⟨_, hcG⟩)
  set w0 : WithConv ((realizedCoord ReeTag.F4.tag L) →ₐ[L] L) := ((eB h : G') : WithConv ((realizedCoord ReeTag.F4.tag L) →ₐ[L] L)) with hw0
  have hz' : w0.ofConv ∈ subgroupPoints G' := by
    change toConv _ ∈ G'
    rw [toConv_ofConv]
    exact (eB h).2
  have hzF := (hmemG' _).1 hz'
  rw [toConv_ofConv] at hzF
  refine ⟨Eq w0, Subgroup.mem_subgroupOf.1 hzF, ?_⟩
  have hpm : ((eB (pointMap σB h) : G') : WithConv ((realizedCoord ReeTag.F4.tag L) →ₐ[L] L)) = toConv (w0.ofConv.comp t) := by
    apply WithConv.ext
    have e1 : ((eB (pointMap σB h) : G') : WithConv ((realizedCoord ReeTag.F4.tag L) →ₐ[L] L)).ofConv =
        (pointMap σB h).ofConv.comp π := subgroupQuotientPointsEquiv_apply G' _ _
    have e2 : w0.ofConv = h.ofConv.comp π := subgroupQuotientPointsEquiv_apply G' _ _
    rw [e1, e2, ofConv_toConv, pointMap_apply, ofConv_toConv, ofConv_toConv]
    rw [AlgHom.comp_assoc]
    rw [show ((σB : (realizedCoord ReeTag.F4.tag L ⧸ subgroupIdeal G') →ₐ[L]
        (realizedCoord ReeTag.F4.tag L ⧸ subgroupIdeal G')).comp π) = π.comp t from
      AlgHom.ext fun a => hσBπ a]
    rw [AlgHom.comp_assoc]
  have h4 := congrArg (fun w => Eq ((eB w : G') : WithConv ((realizedCoord ReeTag.F4.tag L) →ₐ[L] L))) hh
  simp only [MulEquiv.apply_symm_apply, map_mul, map_inv, Subgroup.coe_mul,
    Subgroup.coe_inv] at h4
  rw [h4, hpm, ht]

section Glue

private theorem ggReeLangAux_rlp_of_glue
    {L : Type} [Field L] [IsAlgClosed L] {τ : Tag}
    (S : adjointGroup τ L →* adjointGroup τ L)
    (hH : ∀ h : adjointGroup τ L, (h : ModGL τ L) ∈ torusGroup τ L →
      (S h : ModGL τ L) ∈ torusGroup τ L)
    (hglue : ∀ {ι : Type} (b : ι → Fin τ.rank → Lˣ) (d : ι → adjointGroup τ L)
      (_ : ∀ i, (d i : ModGL τ L) = rootDiagUnit τ (b i)) (u : adjointGroup τ L),
      (∀ i, u * S (d i) * u⁻¹ = d i) →
      ∀ c : adjointGroup τ L, (c : ModGL τ L) ∈ familyGroup (K := L) b →
        ∃ z : adjointGroup τ L, (z : ModGL τ L) ∈ familyGroup (K := L) b ∧
          z⁻¹ * (u * S z * u⁻¹) = c)
    (A : Subgroup (adjointGroup τ L)) (hA : ∀ x ∈ A, S x = x) (g₁ : adjointGroup τ L)
    (hg₁ : ∀ x ∈ A, ((g₁⁻¹ * x * g₁ : adjointGroup τ L) : ModGL τ L) ∈ torusGroup τ L) :
    ∃ (g : adjointGroup τ L) (w : WeylGroup τ),
      ((g⁻¹ * S g : adjointGroup τ L) : ModGL τ L) = canonicalRep (coxeterSystem τ) L w ∧
      ∀ x ∈ A, ((g⁻¹ * x * g : adjointGroup τ L) : ModGL τ L) ∈ torusGroup τ L := by
  classical
  set d : A → adjointGroup τ L := fun x => g₁⁻¹ * x * g₁ with hd
  choose b hb using fun x : A => exists_rootDiagUnit_eq_of_mem_torusGroup (hg₁ x x.2)
  choose b' hb' using fun x : A => exists_rootDiagUnit_eq_of_mem_torusGroup (hH (d x) (hg₁ x x.2))
  set n : adjointGroup τ L := g₁⁻¹ * S g₁ with hn
  have hnd : ∀ x : A, n * S (d x) * n⁻¹ = d x := by
    intro x
    simp only [hn, hd, map_mul, map_inv, hA x x.2]
    group
  obtain ⟨w, hw⟩ := exists_weyl_of_conj_family τ L b b' (g := (n : ModGL τ L)) n.2 (fun x => by
    rw [← hb, ← hb']
    exact congrArg Subtype.val (hnd x))
  set nw := canonicalRep (coxeterSystem τ) L w with hnw
  have hc : (n : ModGL τ L) * nw⁻¹ ∈ familyCentralizer τ L b := by
    refine mem_familyCentralizer.2 ⟨mul_mem n.2 (inv_mem
      (canonicalRep_mem_adjointGroup _ L w)), fun x => ?_⟩
    have h1 : (n : ModGL τ L) * rootDiagUnit τ (b' x) * (n : ModGL τ L)⁻¹ = rootDiagUnit τ (b x) := by
      rw [← hb, ← hb']; exact congrArg Subtype.val (hnd x)
    have h2 : nw⁻¹ * rootDiagUnit τ (b x) * nw = rootDiagUnit τ (b' x) := by
      rw [hw x]; group
    calc rootDiagUnit τ (b x) * ((n : ModGL τ L) * nw⁻¹) * (rootDiagUnit τ (b x))⁻¹
        = (n * rootDiagUnit τ (b' x) * (n : ModGL τ L)⁻¹) * (n * nw⁻¹) *
            (rootDiagUnit τ (b x))⁻¹ := by rw [h1]
      _ = n * rootDiagUnit τ (b' x) * nw⁻¹ * (rootDiagUnit τ (b x))⁻¹ := by group
      _ = n * (nw⁻¹ * rootDiagUnit τ (b x) * nw) * nw⁻¹ * (rootDiagUnit τ (b x))⁻¹ := by rw [h2]
      _ = (n : ModGL τ L) * nw⁻¹ := by group
  obtain ⟨w₁, -, m, hm, hcm⟩ := familyCentralizer_le_mul τ L b hc
  obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (R := L) w₁ w
  have hkM : k ∈ familyGroup (K := L) b := Subgroup.mem_sup_left hk
  have hm'M : m * k ∈ familyGroup (K := L) b := mul_mem hm hkM
  have hFbG : ∀ y ∈ familyGroup (K := L) b, y ∈ adjointGroup τ L := fun y hy =>
    (mem_familyCentralizer.1 (familyGroup_le_familyCentralizer b hy)).1
  set U : adjointGroup τ L := ⟨_, canonicalRep_mem_adjointGroup _ L (w₁ * w)⟩ with hU
  set m' : adjointGroup τ L := ⟨m * k, hFbG _ hm'M⟩ with hm'
  have hnm : n = m' * U := by
    apply Subtype.ext
    have : (n : ModGL τ L) = ((n : ModGL τ L) * nw⁻¹) * nw := by group
    simp only [Subgroup.coe_mul, hm', hU]
    rw [this, hcm, mul_assoc m, hnw, hkk, mul_assoc]
  have hcomm : ∀ y : adjointGroup τ L, (y : ModGL τ L) ∈ familyGroup (K := L) b →
      ∀ x : A, y * d x * y⁻¹ = d x := by
    intro y hy x
    have h := (mem_familyCentralizer.1 (familyGroup_le_familyCentralizer b hy)).2 x
    rw [← hb] at h
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (y : ModGL τ L) * d x * (y : ModGL τ L)⁻¹
        = (y : ModGL τ L) * (d x * y * (d x : ModGL τ L)⁻¹)⁻¹ * d x := by group
      _ = d x := by rw [h]; group
  have hUd : ∀ x : A, U * S (d x) * U⁻¹ = d x := by
    intro x
    have h := hnd x
    rw [hnm] at h
    have h' := hcomm m'⁻¹ (by simpa [hm'] using inv_mem hm'M) x
    calc U * S (d x) * U⁻¹ = m'⁻¹ * ((m' * U) * S (d x) * (m' * U)⁻¹) * m'⁻¹⁻¹ := by group
      _ = d x := by rw [h]; exact h'
  have hLang := hglue b d hb U hUd
  set M : Subgroup (adjointGroup τ L) := (familyGroup (K := L) b).comap (adjointGroup τ L).subtype
    with hM
  obtain ⟨z, hz, hzS⟩ := exists_mem_lang_conj S (M := M) (Q := U) (g := g₁) (m := m')
    (show (m' : ModGL τ L) ∈ familyGroup (K := L) b from hm'M) (by rw [← hn, hnm])
    (fun c hc => by
      obtain ⟨z, hz, hzc⟩ := hLang c hc
      exact ⟨z, hz, hzc⟩)
  refine ⟨g₁ * z, w₁ * w, by rw [hzS], fun x hx => ?_⟩
  have h := hcomm z⁻¹ (inv_mem (show (z : ModGL τ L) ∈ familyGroup (K := L) b from hz)) ⟨x, hx⟩
  have : (g₁ * z)⁻¹ * x * (g₁ * z) = d ⟨x, hx⟩ := by
    rw [← h]; simp only [hd]; group
  rw [this]
  exact hg₁ x hx

end Glue

@[expose] def GGReeLangPositionF4 : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (C : ReeClosure L) (b : ℕ)
    (A : Subgroup (adjointGroup ReeTag.F4.tag L)),
    (∀ x ∈ A, (C.Φ * C.Fr ^ b) x = x) →
    (∃ g₁ : adjointGroup ReeTag.F4.tag L, ∀ x ∈ A,
      ((g₁⁻¹ * x * g₁ : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) ∈ torusGroup ReeTag.F4.tag L) →
    ∃ (g : adjointGroup ReeTag.F4.tag L) (w : WeylGroup ReeTag.F4.tag),
      ((g⁻¹ * (C.Φ * C.Fr ^ b) g : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
        canonicalRep (coxeterSystem ReeTag.F4.tag) L w ∧
      ∀ x ∈ A, ((g⁻¹ * x * g : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) ∈ torusGroup ReeTag.F4.tag L


theorem ggReeLangPositionF4_holds : GGReeLangPositionF4 := by
  intro L _ _ _ C b A hA hg₁
  obtain ⟨g₁, hg₁⟩ := hg₁
  have hFrtw : ∀ y, C.Fr y = frobeniusTwist Tag.F4 L (iterateFrobenius L 2 1) y := fun y =>
    Subtype.ext (C.fr_apply y)
  have hF := CFSG.RankThree.PartOne.KLR.isReeFrob_of_exceptional C.isExc hFrtw b
  refine ggReeLangAux_rlp_of_glue (C.Φ * C.Fr ^ b).toMonoidHom (fun h hh => ?_)
    (fun b' d hd u hu => ggReeLangAux_lang_famSub C b b' d hd u hu) A hA g₁ hg₁
  obtain ⟨hadj, hmap⟩ := hF.map_torusGroup hh
  simpa using hmap

end CFSG.StandardType

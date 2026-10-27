module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviSplitComp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem monomial_conj_frameDiag_gen_e7
    {L : Type} [Field L] {p : ℕ} [NeZero p]
    {ζ : Lˣ} (hζ : ζ ^ p = 1) {m : ModGL .E7 L} (hm : m ∈ monomialSubgroup .E7 L)
    {w : WeylGroup .E7} (hmw : MapsRootLines m w) (s : Fin Tag.E7.rank → ZMod p) :
    m * ExcFrames.frameDiag ζ hζ s * m⁻¹ =
      ExcFrames.frameDiag ζ hζ (TableBExc.torusAct .E7 p w s) := by
  rw [ExcFrames.frameDiag, TableBExc.E6Three.monomial_conj_rootDiagUnit_weylTuple hm hmw,
    TableBExc.E6Three.weylTuple_zetaVec, ExcFrames.adAct_frameCoord, ExcFrames.frameDiag]

theorem e7Split_class
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {p : ℕ} [Fact p.Prime] [NeZero p] {ζ : Kˣ} {hζ : ζ ^ p = 1}
    {ι₀ : Multiplicative (Fin Tag.E7.rank → ZMod p) →* adjointGroup .E7 K}
    (hιι₀ : ∀ s, (ι₀ (Multiplicative.ofAdd s) : ModGL .E7 K) = ExcFrames.frameDiag ζ hζ s)
    {t : Fin Tag.E7.rank → ZMod p} {Y : Subgroup (adjointGroup .E7 K)}
    (hY : IsComponentOf Y
      (Subgroup.centralizer ({ι₀ (Multiplicative.ofAdd t)} : Set (adjointGroup .E7 K)))) :
    ∃ i : KernelComponent
        (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E7 p t))),
      Y.map (adjointGroup .E7 K).subtype = componentRootSpan K
        (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E7 p t))) i ∧
      ∀ s : Fin Tag.E7.rank → ZMod p,
        (∀ γ ∈ componentRoots
            (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E7 p t))) i,
          ∑ j, (γ j : ZMod p) * ExcFrames.frameCoord .E7 p s j = 0) →
        ι₀ (Multiplicative.ofAdd s) ∈ Subgroup.centralizer (Y : Set (adjointGroup .E7 K)) := by
  classical
  let a : Fin Tag.E7.rank → Kˣ :=
    TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E7 p t)
  let g : ↥(adjointGroup .E7 K) := ι₀ (Multiplicative.ofAdd t)
  have ha : ∀ k, a k ^ p = 1 := fun k => by
    change TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E7 p t) k ^ p = 1
    rw [TableBExc.E6Three.zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hg : (adjointGroup .E7 K).subtype g = ExcFrames.frameDiag ζ hζ t := hιι₀ t
  have hy : ∀ l, (adjointGroup .E7 K).subtype (MulAut.conj g l) =
      rootDiagUnit .E7 a * (adjointGroup .E7 K).subtype l * (rootDiagUnit .E7 a)⁻¹ := by
    intro l
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hg]
    rfl
  have hker : ((adjointGroup .E7 K).subtype).ker ≤ Subgroup.center ↥(adjointGroup .E7 K) := by
    rw [Subgroup.ker_subtype]
    exact bot_le
  have hψ : ((adjointGroup .E7 K).subtype).range = adjointGroup .E7 K := by
    rw [Subgroup.range_subtype]
  have : Finite (ModGL .E7 K) := finite_modGL
  have : Finite ↥(adjointGroup .E7 K) := Subtype.finite
  have hJ : CFSG.Open.IsComponentOf Y
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj g)) := by
    rw [ggTBJ_fixSubgroup_conj]
    change CFSG.Open.IsComponentOf Y
      (Subgroup.centralizer ({ι₀ (Multiplicative.ofAdd t)} : Set ↥(adjointGroup .E7 K)))
    exact CFSG.Assembly.isComponentOf_iff_open.1 hY
  obtain ⟨i, hmap⟩ := ggTBJ_class_fix (p := p) Fact.out hK
    (ψ := (adjointGroup .E7 K).subtype) hker hψ a ha (MulAut.conj g) hy hJ
  refine ⟨i, ?_, ?_⟩
  · change Y.map (adjointGroup .E7 K).subtype = componentRootSpan K (rootCharHom a) i
    exact hmap
  · intro s hs
    have hS : ∀ γ ∈ componentRoots (rootCharHom a) i,
        IsRoot .E7 γ ∧
          rootChar (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E7 p s)) γ = 1 := by
      intro γ hγ
      refine ⟨(isRootComponent_componentRoots i).isRoot γ hγ, ?_⟩
      rw [NoOffE8Five.rootChar_zetaVec hζ, hs γ hγ, ofAdd_zero, map_one]
    refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
    have hzY : (z : ModGL .E7 K) ∈ componentRootSpan K (rootCharHom a) i := by
      rw [← hmap]
      exact ⟨z, hz, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_iff.1
      (CFSG.LieType.SeitzGeneration.ExcHighThree.rootSpan_le_centralizer_rootDiagUnit (K := K)
        (a := TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E7 p s))
        (S := componentRoots (rootCharHom a) i) hS hzY))
      (rootDiagUnit .E7 (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E7 p s)))
      (by simp)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hιι₀ s]
    exact hcomm.symm

theorem e7Split_lower
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} [Fact p.Prime] [NeZero p] {ζ : Kˣ} {hζ : ζ ^ p = 1}
    {ι₀ : Multiplicative (Fin Tag.E7.rank → ZMod p) →* adjointGroup .E7 K}
    (hιι₀ : ∀ s, (ι₀ (Multiplicative.ofAdd s) : ModGL .E7 K) = ExcFrames.frameDiag ζ hζ s)
    {a : Fin Tag.E7.rank → Kˣ} (i : KernelComponent (rootCharHom a))
    {Y : Subgroup (adjointGroup .E7 K)}
    (hY : Y.map (adjointGroup .E7 K).subtype = componentRootSpan K (rootCharHom a) i) :
    ∀ c ∈ componentRoots (rootCharHom a) i, ∃ g ∈ Y, ∀ s,
      g * ι₀ (Multiplicative.ofAdd s) * g⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p (rootReflection c) s)) := by
  intro c hc
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hcr : IsRoot .E7 c := hΨ.isRoot c hc
  have hneg : -c ∈ componentRoots (rootCharHom a) i := hΨ.neg_mem c hc
  have hmem : rootSL2 .E7 K c WSL ∈ componentRootSpan K (rootCharHom a) i := by
    have hsub : ({c, -c} : Set (Fin Tag.E7.rank → ℤ)) ⊆
        componentRoots (rootCharHom a) i := by
      intro α hα
      rcases hα with rfl | hα
      · exact hc
      · rw [Set.mem_singleton_iff] at hα
        rw [hα]
        exact hneg
    exact rootSpan_mono hsub (rootSL2_mem_rootSpan_pair (L := K) hcr WSL)
  have hmap : rootSL2 .E7 K c WSL ∈ Y.map (adjointGroup .E7 K).subtype := by
    rw [hY]
    exact hmem
  obtain ⟨g, hgY, hg⟩ := Subgroup.mem_map.mp hmap
  refine ⟨g, hgY, fun s => ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hgc : (g : ModGL .E7 K) = rootSL2 .E7 K c WSL := hg
  rw [hgc, hιι₀, hιι₀ (TableBExc.torusAct .E7 p (rootReflection c) s)]
  exact monomial_conj_frameDiag_gen_e7 hζ
    (CFSG.ClassicalInvolution.ModelFacts.Levi.rootSL2_WSL_mem_monomialSubgroup
      (τ := .E7) (K := K) hcr)
    (CFSG.ClassicalInvolution.ModelFacts.Levi.mapsRootLines_rootSL2_WSL
      (τ := .E7) (K := K) hcr) s

end CFSG.StandardType

end

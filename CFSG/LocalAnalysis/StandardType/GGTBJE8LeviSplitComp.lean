module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnComp
public import CFSG.LocalAnalysis.StandardType.GGTBJXClass
public import CFSG.LocalAnalysis.GLTheoremA.CatC.RationalTypeAModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

theorem e8Split_class
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {p : ℕ} [Fact p.Prime] [NeZero p] {ζ : Kˣ} {hζ : ζ ^ p = 1}
    {ι₀ : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hιι₀ : ∀ s, (ι₀ (Multiplicative.ofAdd s) : ModGL τ K) = ExcFrames.frameDiag ζ hζ s)
    {t : Fin τ.rank → ZMod p} {Y : Subgroup (adjointGroup τ K)}
    (hY : IsComponentOf Y
      (Subgroup.centralizer ({ι₀ (Multiplicative.ofAdd t)} : Set (adjointGroup τ K)))) :
    ∃ i : KernelComponent
        (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord τ p t))),
      Y.map (adjointGroup τ K).subtype = componentRootSpan K
        (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord τ p t))) i ∧
      ∀ s : Fin τ.rank → ZMod p,
        (∀ γ ∈ componentRoots
            (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord τ p t))) i,
          ∑ j, (γ j : ZMod p) * ExcFrames.frameCoord τ p s j = 0) →
        ι₀ (Multiplicative.ofAdd s) ∈ Subgroup.centralizer (Y : Set (adjointGroup τ K)) := by
  classical
  let a : Fin τ.rank → Kˣ :=
    TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord τ p t)
  let g : ↥(adjointGroup τ K) := ι₀ (Multiplicative.ofAdd t)
  have ha : ∀ k, a k ^ p = 1 := fun k => by
    change TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord τ p t) k ^ p = 1
    rw [TableBExc.E6Three.zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hg : (adjointGroup τ K).subtype g = ExcFrames.frameDiag ζ hζ t := hιι₀ t
  have hy : ∀ l, (adjointGroup τ K).subtype (MulAut.conj g l) =
      rootDiagUnit τ a * (adjointGroup τ K).subtype l * (rootDiagUnit τ a)⁻¹ := by
    intro l
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hg]
    rfl
  have hker : ((adjointGroup τ K).subtype).ker ≤ Subgroup.center ↥(adjointGroup τ K) := by
    rw [Subgroup.ker_subtype]
    exact bot_le
  have hψ : ((adjointGroup τ K).subtype).range = adjointGroup τ K := by
    rw [Subgroup.range_subtype]
  haveI : Finite (ModGL τ K) := finite_modGL
  haveI : Finite ↥(adjointGroup τ K) := Subtype.finite
  have hJ : CFSG.Open.IsComponentOf Y
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj g)) := by
    rw [ggTBJ_fixSubgroup_conj]
    change CFSG.Open.IsComponentOf Y
      (Subgroup.centralizer ({ι₀ (Multiplicative.ofAdd t)} : Set ↥(adjointGroup τ K)))
    exact CFSG.Assembly.isComponentOf_iff_open.1 hY
  obtain ⟨i, hmap⟩ := ggTBJ_class_fix (p := p) Fact.out hK
    (ψ := (adjointGroup τ K).subtype) hker hψ a ha (MulAut.conj g) hy hJ
  refine ⟨i, ?_, ?_⟩
  · change Y.map (adjointGroup τ K).subtype = componentRootSpan K (rootCharHom a) i
    exact hmap
  · intro s hs
    have hS : ∀ γ ∈ componentRoots (rootCharHom a) i,
        IsRoot τ γ ∧
          rootChar (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord τ p s)) γ = 1 := by
      intro γ hγ
      refine ⟨(isRootComponent_componentRoots i).isRoot γ hγ, ?_⟩
      rw [NoOffE8Five.rootChar_zetaVec hζ, hs γ hγ, ofAdd_zero, map_one]
    refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
    have hzY : (z : ModGL τ K) ∈ componentRootSpan K (rootCharHom a) i := by
      rw [← hmap]
      exact ⟨z, hz, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_iff.1
      (CFSG.LieType.SeitzGeneration.ExcHighThree.rootSpan_le_centralizer_rootDiagUnit (K := K)
        (a := TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord τ p s))
        (S := componentRoots (rootCharHom a) i) hS hzY))
      (rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord τ p s)))
      (by simp)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hιι₀ s]
    exact hcomm.symm

theorem e8Split_lower
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} [Fact p.Prime] [NeZero p] {ζ : Kˣ} {hζ : ζ ^ p = 1}
    {ι₀ : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hιι₀ : ∀ s, (ι₀ (Multiplicative.ofAdd s) : ModGL τ K) = ExcFrames.frameDiag ζ hζ s)
    {a : Fin τ.rank → Kˣ} (i : KernelComponent (rootCharHom a))
    {Y : Subgroup (adjointGroup τ K)}
    (hY : Y.map (adjointGroup τ K).subtype = componentRootSpan K (rootCharHom a) i) :
    ∀ c ∈ componentRoots (rootCharHom a) i, ∃ g ∈ Y, ∀ s,
      g * ι₀ (Multiplicative.ofAdd s) * g⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct τ p (rootReflection c) s)) := by
  intro c hc
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hcr : IsRoot τ c := hΨ.isRoot c hc
  have hneg : -c ∈ componentRoots (rootCharHom a) i := hΨ.neg_mem c hc
  have hmem : rootSL2 τ K c WSL ∈ componentRootSpan K (rootCharHom a) i := by
    have hsub : ({c, -c} : Set (Fin τ.rank → ℤ)) ⊆
        componentRoots (rootCharHom a) i := by
      intro α hα
      rcases hα with rfl | hα
      · exact hc
      · rw [Set.mem_singleton_iff] at hα
        rw [hα]
        exact hneg
    exact rootSpan_mono hsub (rootSL2_mem_rootSpan_pair (L := K) hcr WSL)
  have hmap : rootSL2 τ K c WSL ∈ Y.map (adjointGroup τ K).subtype := by
    rw [hY]
    exact hmem
  obtain ⟨g, hgY, hg⟩ := Subgroup.mem_map.mp hmap
  refine ⟨g, hgY, fun s => ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hgc : (g : ModGL τ K) = rootSL2 τ K c WSL := hg
  rw [hgc, hιι₀, hιι₀ (TableBExc.torusAct τ p (rootReflection c) s)]
  exact monomial_conj_frameDiag_gen hζ
    (CFSG.ClassicalInvolution.ModelFacts.Levi.rootSL2_WSL_mem_monomialSubgroup
      (τ := τ) (K := K) hcr)
    (CFSG.ClassicalInvolution.ModelFacts.Levi.mapsRootLines_rootSL2_WSL
      (τ := τ) (K := K) hcr) s

theorem e8Split_a8
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hq : Nat.card K = 2 ^ n)
    {a : Fin Tag.E8.rank → Kˣ} (i : KernelComponent (rootCharHom a))
    {Y : Subgroup (adjointGroup .E8 K)}
    (hY : Y.map (adjointGroup .E8 K).subtype = componentRootSpan K (rootCharHom a) i)
    {v : WeylGroup .E8}
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' kacE8.rootsOf (e8A8Nodes : Set (Option (Fin Tag.E8.rank)))) :
    GGHasLabel (⟨.A, 8, n⟩ : LargeEvenLabel) (↥Y ⧸ Subgroup.center ↥Y) := by
  classical
  obtain ⟨ψ, σ, hψ, hframe⟩ := e8A8_frame_exists (L := K) v
  have hΨframe : componentRoots (rootCharHom a) i = frameRoots σ := hΨ.trans hframe.symm
  have hrange : ψ.range = Y.map (adjointGroup .E8 K).subtype := by
    rw [hψ.range, hY, show componentRootSpan K (rootCharHom a) i =
      rootSpan .E8 K (componentRoots (rootCharHom a) i) from rfl, hΨframe]
  let eY : ↥Y ≃* ↥(Y.map (adjointGroup .E8 K).subtype) :=
    Y.equivMapOfInjective (adjointGroup .E8 K).subtype (adjointGroup .E8 K).subtype_injective
  let ψY : Matrix.SpecialLinearGroup (Fin 9) K →* ↥(Y.map (adjointGroup .E8 K).subtype) :=
    ψ.codRestrict _ fun x => hrange ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩
  let g : Matrix.SpecialLinearGroup (Fin 9) K →* ↥Y := eY.symm.toMonoidHom.comp ψY
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    have hm : (eY ⟨y, hy⟩ : ModGL .E8 K) ∈ ψ.range := by
      rw [hrange]
      exact (eY ⟨y, hy⟩).2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hm
    refine ⟨z, ?_⟩
    change eY.symm (ψY z) = ⟨y, hy⟩
    rw [show ψY z = eY ⟨y, hy⟩ from Subtype.ext hz, MulEquiv.symm_apply_apply]
  have hgk : g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 9) K) := by
    intro x hx
    have h1 : ψ x = 1 := by
      have h2 : ψY x = 1 := by
        apply eY.symm.injective
        change eY.symm (ψY x) = 1 at hx
        rw [eY.symm.map_one]
        exact hx
      exact congrArg Subtype.val h2
    exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.frame_ker_le_center
      (by norm_num) hψ (MonoidHom.mem_ker.2 h1)
  have hf : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · have h := Finite.one_lt_card (α := K)
      rw [hq, pow_zero] at h
      exact absurd h (lt_irrefl 1)
    · exact h0
  refine ggHasLabel_typeA (n := 8) (f := n) ?_
  exact CFSG.LocalAnalysis.GLTheoremA.RationalModel.statedClassicalModel_PSL_of_slCover_of_three_le
    Nat.prime_two hf hq (by norm_num) g hg hgk

end CFSG.StandardType

end

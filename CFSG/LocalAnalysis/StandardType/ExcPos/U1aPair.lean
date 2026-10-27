module

public import CFSG.LocalAnalysis.StandardType.ExcPos.U1aRootSub
public import CFSG.LocalAnalysis.StandardType.ExcPos.U1aPairInner
public import CFSG.LocalAnalysis.StandardType.ExcPos.U1aPairOuter
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.GroupTheory.OddKernelImage
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongE6
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2E7Bridge
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongE8

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

namespace ExcLangFrame

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.GGFinModel CFSG.StandardType.ClassicalPosition
  CFSG.StandardType.S2MathFi1035Pos


theorem exists_pair {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) {X : Type} [Group X]
    [Finite X] {n f p : ℕ} {ψ : (ggU t n f).K →* X} {G₀ B₁ D J L : Subgroup X} {x : X}
    (h : GGSixPosHyp t n f ψ p G₀ B₁ D J L x) (F : ExcLangFrame t n f p ψ G₀ B₁ D x)
    (iJ : KernelComponent F.chiD)
    (hJ : (J.subgroupOf G₀).map F.η = LieCore.ratComp F.ρ F.Δ.Γ (componentRoots F.chiD iJ))
    (hb : componentOrbitLength F.ρ (componentRoots F.chiD iJ) = 1) :
    ∃ (R Rm : Subgroup X) (α : Fin (langTag t).rank → ℤ) (w : ModGL (langTag t) GGL),
      R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 t n f p ψ R Rm ∧ α ∈ componentRoots F.chiD iJ ∧
      w ∈ torusGroup (langTag t) GGL ⊔ rootSpan (langTag t) GGL (kernelRoots F.chiD) ∧
      Nat.card ((R.subgroupOf G₀).map F.η) = Nat.card (GaloisField 2 f) ∧
      (R.subgroupOf G₀).map F.η = excCurve α w ⊓ F.Δ.model ∧
      Nat.card ((Rm.subgroupOf G₀).map F.η) = Nat.card (GaloisField 2 f) ∧
      (Rm.subgroupOf G₀).map F.η = excCurve (-α) w ⊓ F.Δ.model ∧
      (excCurve α w).map F.Δ.step = excCurve α w ∧
      (excCurve (-α) w).map F.Δ.step = excCurve (-α) w := by
  classical
  have hne := F.coord_ne_one h
  obtain ⟨h1, -, -, h4, hp, hp2, -, -, -, -, -, -, -, -, h15, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -⟩ := h
  obtain ⟨hJG, -, hJqs⟩ := h15
  have hJG' : J ≤ G₀ := hJG.trans inf_le_left
  have hcen : F.η.ker ≤ Subgroup.center ↥G₀ := F.ker_η.le
  have hoddZ : Odd (Nat.card (Subgroup.center ↥G₀)) := by
    have hZle : (Subgroup.center ↥G₀).map (Subgroup.subtype G₀) ≤
        Subgroup.centralizer (G₀ : Set X) := by
      rintro z ⟨zc, hzc, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨y, hy⟩)
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective G₀)]
    exact Odd.of_dvd_nat h4 (Subgroup.card_dvd_of_le hZle)
  have hoddEta : Odd (Nat.card F.η.ker) := by
    rw [F.ker_η]
    exact hoddZ
  have hKq : CFSG.Assembly.IsQuasisimple ↥(J.subgroupOf G₀) :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJG') hJqs
  have hKq' : CFSG.IsQuasisimple ↥(J.subgroupOf G₀) :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff ↥(J.subgroupOf G₀)).2.1).mpr hKq
  have himg' : CFSG.IsQuasisimple ↥((J.subgroupOf G₀).map F.η) := by
    refine CFSG.LocalCores.isQuasisimple_of_surjective hKq'
      (F.η.subgroupMap (J.subgroupOf G₀)) (F.η.subgroupMap_surjective _) ?_
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hzη : F.η (z : ↥G₀) = 1 := by
      have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hz)
      simpa [MonoidHom.subgroupMap_apply_coe] using h
    have hzZ : (z : ↥G₀) ∈ Subgroup.center ↥G₀ := by
      rw [← F.ker_η]
      exact MonoidHom.mem_ker.mpr hzη
    simpa using Subgroup.mem_center_iff.mp hzZ (y : ↥G₀)
  have hqs : CFSG.Assembly.IsQuasisimple
      ↥(LieCore.ratComp F.ρ F.Δ.Γ (componentRoots F.chiD iJ)) := by
    have : CFSG.Assembly.IsQuasisimple ↥((J.subgroupOf G₀).map F.η) :=
      ⟨himg'.1.commutator_eq_top, himg'.2.1⟩
    rwa [hJ] at this
  have hx : x ∈ D := by
    rw [← F.closure_eq]
    exact Subgroup.subset_closure (by simp)
  have hτ : langTag t = .E6 ∨ langTag t = .E7 ∨ langTag t = .E8 := by
    rcases ht with rfl | rfl | rfl <;> simp [langTag]
  obtain ⟨α, w, hα, hw, hV, hVm, hle, hlem⟩ :=
    if hinner : twistInner (componentRoots F.chiD iJ) F.ρ then
      exists_stable_pair_inner hτ F.one_le_f F.Δ F.q_eq F.frob F.finite
        (F.coord_torus x hx) (F.coord_torus F.d F.d_mem) iJ hb hinner hqs
    else
      exists_stable_pair_outer hτ F.one_le_f F.Δ F.q_eq F.frob F.finite hp hp2
        (F.coord_torus x hx) (F.coord_torus F.d F.d_mem) (F.coord_pow x hx)
        (F.coord_pow F.d F.d_mem) hne iJ hb hinner hqs
  have hαroot : IsRoot (langTag t) α :=
    CFSG.LieType.Chevalley.isRoot_of_mem_componentRoots hα
  have hwAdj : w ∈ adjointGroup (langTag t) GGL :=
    sup_le (CFSG.RankThree.Classical2.torusGroup_le_adjointGroup_of_field)
      (CFSG.LieType.Chevalley.rootSpan_le_adjointGroup GGL (kernelRoots F.chiD)) hw
  obtain ⟨β, k, hβ, hlong, hRη, hRmη, hRcard, hRmcard⟩ :=
    exists_rootSub ht h1 F hαroot hwAdj hV hVm
  set R : Subgroup X := ggRootSub (ggU t n f).D ψ β k with hRdef
  set Rm : Subgroup X := ggRootSub (ggU t n f).D ψ (-β) k with hRmdef
  have hRη' : (R.subgroupOf G₀).map F.η = excCurve α w ⊓ F.Δ.model := by
    rw [hRdef]
    exact hRη
  have hRmη' : (Rm.subgroupOf G₀).map F.η = excCurve (-α) w ⊓ F.Δ.model := by
    rw [hRmdef]
    exact hRmη
  have hRG : R ≤ G₀ := by
    rw [hRdef, ggRootSub, ← h1]
    exact Subgroup.map_le_range ψ _
  have hRmG : Rm ≤ G₀ := by
    rw [hRmdef, ggRootSub, ← h1]
    exact Subgroup.map_le_range ψ _
  have hR2 : IsPGroup 2 R := by
    have hpid : IsPGroup 2
        (ggRootSub (ggU t n f).D (MonoidHom.id (ggU t n f).K) β k) := by
      rcases ht with rfl | rfl | rfl
      · exact CFSG.StandardType.LieKnownR2.E6.rootGroup_isPGroup_E6 k rfl
      · exact CFSG.StandardType.LieKnownR2.E7.rootGroup_isPGroup_E7 k rfl
      · exact CFSG.StandardType.LieKnownR2.E8.rootGroup_isPGroup_E8 hβ k rfl
    have hmap : R = (ggRootSub (ggU t n f).D (MonoidHom.id (ggU t n f).K) β k).map ψ := by
      rw [hRdef]
      simp only [ggRootSub, Subgroup.map_id]
    rw [hmap]
    exact hpid.map ψ
  have hRm2 : IsPGroup 2 Rm := by
    have hpid : IsPGroup 2
        (ggRootSub (ggU t n f).D (MonoidHom.id (ggU t n f).K) (-β) k) := by
      rcases ht with rfl | rfl | rfl
      · exact CFSG.StandardType.LieKnownR2.E6.rootGroup_isPGroup_E6 k rfl
      · exact CFSG.StandardType.LieKnownR2.E7.rootGroup_isPGroup_E7 k rfl
      · refine CFSG.StandardType.LieKnownR2.E8.rootGroup_isPGroup_E8 ?_ k rfl
        exact CFSG.LieType.Steinberg.OfCartan.neg_mem_roots
          (ggU .E8 n f).D.isFiniteType hβ
    have hmap : Rm = (ggRootSub (ggU t n f).D (MonoidHom.id (ggU t n f).K) (-β) k).map ψ := by
      rw [hRmdef]
      simp only [ggRootSub, Subgroup.map_id]
    rw [hmap]
    exact hpid.map ψ
  have hRJ' : R.subgroupOf G₀ ≤ J.subgroupOf G₀ := by
    refine CFSG.GroupTheory.le_of_map_le_map_of_odd hcen hoddEta hR2.comap_subtype ?_
    rw [hRη', hJ]
    exact hle
  have hRmJ' : Rm.subgroupOf G₀ ≤ J.subgroupOf G₀ := by
    refine CFSG.GroupTheory.le_of_map_le_map_of_odd hcen hoddEta hRm2.comap_subtype ?_
    rw [hRmη', hJ]
    exact hlem
  have hRJ : R ≤ J := CFSG.LocalCores.le_of_subgroupOf_le hRG hRJ'
  have hRmJ : Rm ≤ J := CFSG.LocalCores.le_of_subgroupOf_le hRmG hRmJ'
  refine ⟨R, Rm, α, w, hRJ, hRmJ, ⟨β, hβ, Or.inl hlong, k, hRdef, hRmdef⟩, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ExcLangFrame.chiD] using hα
  · simpa [ExcLangFrame.chiD] using hw
  · rw [hRη']
    exact hRcard
  · exact hRη'
  · rw [hRmη']
    exact hRmcard
  · exact hRmη'
  · exact hV
  · exact hVm

end ExcLangFrame

end CFSG.StandardType.LieKnownR2.ExcPos

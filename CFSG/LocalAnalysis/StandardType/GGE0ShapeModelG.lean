module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeModel
public import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteenFourteenP

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem shapeModel_normalizerMonoidHom_eq_conj {G : Type*} [Group G] {G0 : Subgroup G}
    (y : Subgroup.normalizer (G0 : Set G)) (hyG0 : (y : G) ∈ G0) :
    G0.normalizerMonoidHom y = MulAut.conj (⟨(y : G), hyG0⟩ : G0) := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [normalizerMonoidHom_apply_coe y.2 x, MulAut.conj_apply]
  rfl

theorem ggE0Concl_of_modelShape
    {G : Type} [Group G] [Finite G] {G0 : Subgroup G}
    (hC : Subgroup.centralizer (G0 : Set G) = ⊥)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (halg : letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω)
    {I : Subgroup (MulAut G0)} (R : ShapeRealization G0 I Ω)
    {b : G} (hbN : b ∈ Subgroup.normalizer (G0 : Set G))
    (hbI : contextImage G0 (Subgroup.zpowers b) ≤ I) (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1)
    {E0 : Subgroup G} (hE0 : E0 ≤ Subgroup.normalizer (G0 : Set G))
    (hEI : contextImage G0 E0 ≤ I) (hEb : E0 ≤ Subgroup.centralizer {b})
    (hrig : RigidToralPlane (realizedSubgroup R (contextImage G0 E0)))
    {C₀ : Subgroup G} (hC₀ : IsComponentOf C₀ (G0 ⊓ Subgroup.centralizer {b})) :
    GGE0Concl E0 C₀ := by
  have _hfin : Finite G := inferInstance
  let N : Subgroup G := Subgroup.normalizer (G0 : Set G)
  let Φ : N →* MulAut G0 := Subgroup.normalizerMonoidHom G0
  let bN : N := ⟨b, hbN⟩
  let β : MulAut G0 := Φ bN
  let E : Subgroup (MulAut G0) := contextImage G0 E0
  let X : Subgroup (MulAut G0) := (C₀.subgroupOf G0).map (MulAut.conj : G0 →* MulAut G0)
  have hΦ_inj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have hyCent : (y : G) ∈ Subgroup.centralizer (G0 : Set G) :=
      (normalizerMonoidHom_eq_one_iff y.2).mp hy
    rw [hC] at hyCent
    exact Subtype.ext (by simpa using hyCent)
  have hβI : β ∈ I := by
    change Φ bN ∈ I
    apply hbI
    exact Subgroup.mem_map_of_mem Φ
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers b))
  have hβ1 : β ≠ 1 := by
    intro h
    apply hb1
    have hβ_eq : Φ bN = 1 := h
    have h2 : bN = 1 := hΦ_inj (by rw [hβ_eq, map_one])
    show (bN : G) = 1
    rw [h2]
    rfl
  have hβ3 : β ^ 3 = 1 := by
    change Φ bN ^ 3 = 1
    rw [← map_pow]
    have hbN3 : bN ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hb3
    rw [hbN3, map_one]
  have hEβ : E ≤ Subgroup.centralizer {β} := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    change Φ y * Φ bN = Φ bN * Φ y
    have hyb : (y : G) * b = b * (y : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hEb hy)
    have hybN : y * bN = bN * y := Subtype.ext hyb
    rw [← map_mul, ← map_mul, hybN]
  have hconj_inj : Function.Injective (MulAut.conj : G0 →* MulAut G0) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    apply Subtype.ext
    have hxCent : (x : G) ∈ Subgroup.centralizer (G0 : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hG : (x : G) * g * (x : G)⁻¹ = g := by
        have h := congrArg (fun f : MulAut G0 => ((f ⟨g, hg⟩ : G0) : G)) hx
        rwa [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * (x : G) = ((x : G) * g * (x : G)⁻¹) * (x : G) := by rw [hG]
        _ = (x : G) * g := by group
    rw [hC] at hxCent
    simpa using hxCent
  have hKconj : (((G0 ⊓ Subgroup.centralizer {b}).subgroupOf G0)).map
        (MulAut.conj : G0 →* MulAut G0) =
      (MulAut.conj : G0 →* MulAut G0).range ⊓ Subgroup.centralizer {β} := by
    ext φ
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hg' : (g : G) ∈ G0 ⊓ Subgroup.centralizer {b} := hg
      refine Subgroup.mem_inf.mpr ⟨⟨g, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hgb : (g : G) * b = b * (g : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hg'.2
      have hconj_eq : MulAut.conj g = Φ ⟨(g : G), G0.le_normalizer g.2⟩ :=
        (shapeModel_normalizerMonoidHom_eq_conj (G0 := G0)
          ⟨(g : G), G0.le_normalizer g.2⟩ g.2).symm
      have hN : (⟨(g : G), G0.le_normalizer g.2⟩ : N) * bN =
          bN * ⟨(g : G), G0.le_normalizer g.2⟩ := Subtype.ext hgb
      change MulAut.conj g * β = β * MulAut.conj g
      rw [hconj_eq]
      change Φ ⟨(g : G), G0.le_normalizer g.2⟩ * Φ bN =
        Φ bN * Φ ⟨(g : G), G0.le_normalizer g.2⟩
      rw [← map_mul, ← map_mul, hN]
    · rintro ⟨hφr, hφc⟩
      obtain ⟨g, hgφ⟩ := hφr
      refine Subgroup.mem_map.mpr ⟨g, ?_, hgφ⟩
      refine Subgroup.mem_inf.mpr ⟨g.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm : φ * β = β * φ :=
        Subgroup.mem_centralizer_singleton_iff.mp hφc
      have hconj_eq : MulAut.conj g = Φ ⟨(g : G), G0.le_normalizer g.2⟩ :=
        (shapeModel_normalizerMonoidHom_eq_conj (G0 := G0)
          ⟨(g : G), G0.le_normalizer g.2⟩ g.2).symm
      have hN : (⟨(g : G), G0.le_normalizer g.2⟩ : N) * bN =
          bN * ⟨(g : G), G0.le_normalizer g.2⟩ := by
        apply hΦ_inj
        rw [map_mul, map_mul, ← hconj_eq, hgφ]
        change φ * β = β * φ
        exact hcomm
      simpa using congrArg (fun z : N => (z : G)) hN
  have hXcomp : IsComponentOf X
      ((MulAut.conj : G0 →* MulAut G0).range ⊓ Subgroup.centralizer {β}) := by
    have hC₀G0 : IsComponentOf (C₀.subgroupOf G0)
        ((G0 ⊓ Subgroup.centralizer {b}).subgroupOf G0) :=
      ggIsComponentOf_subgroupOf hC₀ inf_le_left
    have h := isComponentOf_map_of_injective (MulAut.conj : G0 →* MulAut G0) hconj_inj hC₀G0
    rwa [hKconj] at h
  have hconcl_model : GGE0Concl E X :=
    ggE0ModelShape_holds halg R β hβI E hEI hβ1 hβ3 hEβ hrig X hXcomp
  have hX_eq : (C₀.subgroupOf N).map Φ = X := by
    ext φ
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyC : (y : G) ∈ C₀ := Subgroup.mem_subgroupOf.mp hy
      have hyG0 : (y : G) ∈ G0 := (hC₀.1 hyC).1
      have hconj_eq : Φ y = MulAut.conj (⟨(y : G), hyG0⟩ : G0) :=
        shapeModel_normalizerMonoidHom_eq_conj y hyG0
      rw [hconj_eq]
      exact Subgroup.mem_map_of_mem (MulAut.conj : G0 →* MulAut G0)
        (Subgroup.mem_subgroupOf.mpr hyC)
    · rintro ⟨g, hg, rfl⟩
      have hgC : (g : G) ∈ C₀ := Subgroup.mem_subgroupOf.mp hg
      have hgG0 : (g : G) ∈ G0 := (hC₀.1 hgC).1
      have hgN : (g : G) ∈ N := G0.le_normalizer hgG0
      refine Subgroup.mem_map.mpr ⟨⟨(g : G), hgN⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr hgC
      · exact shapeModel_normalizerMonoidHom_eq_conj ⟨(g : G), hgN⟩ g.2
  have h_in_N : GGE0Concl (E0.subgroupOf N) (C₀.subgroupOf N) := by
    have h1 : GGE0Concl ((E0.subgroupOf N).map Φ) ((C₀.subgroupOf N).map Φ) := by
      rw [hX_eq]
      exact hconcl_model
    exact (ggE0Concl_map_iff Φ hΦ_inj (E0.subgroupOf N) (C₀.subgroupOf N)).mp h1
  have hC₀N : C₀ ≤ N := hC₀.1.trans (inf_le_left.trans (Subgroup.le_normalizer))
  have h_back : GGE0Concl ((E0.subgroupOf N).map N.subtype)
      ((C₀.subgroupOf N).map N.subtype) :=
    (ggE0Concl_map_iff N.subtype N.subtype_injective (E0.subgroupOf N)
      (C₀.subgroupOf N)).mpr h_in_N
  rw [Subgroup.map_subgroupOf_eq_of_le hE0, Subgroup.map_subgroupOf_eq_of_le hC₀N] at h_back
  exact h_back

end CFSG.StandardType

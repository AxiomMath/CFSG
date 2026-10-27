module

public import Mathlib
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSpecial
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartOne.KCSpIsotypic

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary
open scoped commutatorElement

universe u

section Generic

theorem primaryMultiplicity_X_sub_C_eq {K : Type} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (x : Module.End K V) (μ : K) :
    primaryMultiplicity x (X - C μ) = Module.finrank K (primaryComponent x (X - C μ)) := by
  have : Fact (Irreducible (X - C μ : K[X])) := ⟨irreducible_X_sub_C μ⟩
  have h := finrank_primaryComponent x (X - C μ)
  rw [natDegree_X_sub_C, one_mul] at h
  exact h.symm

theorem eq_one_of_det_eq_one_of_finrank_le_one {E W : Type*} [Field E] [AddCommGroup W]
    [Module E W] [FiniteDimensional E W] (h : Module.finrank E W ≤ 1)
    (γ : LinearMap.GeneralLinearGroup E W) (hdet : LinearMap.det (γ : Module.End E W) = 1) :
    γ = 1 := by
  rcases Nat.lt_or_ge (Module.finrank E W) 1 with h0 | h1
  · have : Subsingleton W := (Module.finrank_zero_iff (R := E)).mp (by omega)
    exact Units.ext (LinearMap.ext fun w => Subsingleton.elim _ _)
  · have hfr : Module.finrank E W = 1 := by omega
    obtain ⟨c, hc⟩ := exists_smul_of_forall_commute (γ : Module.End E W)
      (End_commute_of_finrank_le_one h _)
    have hγ : (γ : Module.End E W) = c • (1 : Module.End E W) := LinearMap.ext fun w => by
      rw [hc w]
      rfl
    have hdc : LinearMap.det (γ : Module.End E W) = c := by
      rw [hγ, LinearMap.det_smul, hfr, pow_one, (LinearMap.det : Module.End E W →* E).map_one,
        mul_one]
    refine Units.ext (LinearMap.ext fun w => ?_)
    rw [hc w, ← hdc, hdet, one_smul]
    rfl

variable {K : Type} [Field K] {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {σ : K →+* K}

structure SpBlockFacts (B : V →ₛₗ[σ] V →ₗ[K] K) (x : LinearMap.GeneralLinearGroup K V)
    (a : primaryFactors (x : Module.End K V)) : Prop where
  commutator_eq : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) →
    ⁅orbitFactor B x (a : K[X]), orbitFactor B x (a : K[X])⁆ = specialBlock B x (a : K[X])
  quasisimple : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) →
    CFSG.IsQuasisimple (specialBlock B x (a : K[X]))
  special_bot : primaryMultiplicity (x : Module.End K V) (a : K[X]) ≤ 1 →
    specialBlock B x (a : K[X]) = ⊥
  abelian : primaryMultiplicity (x : Module.End K V) (a : K[X]) ≤ 1 →
    ∀ g ∈ orbitFactor B x (a : K[X]), ∀ g' ∈ orbitFactor B x (a : K[X]), Commute g g'
  scalar : ∀ Y ∈ gl_centralizer x,
    (2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) →
      ∀ g ∈ specialBlock B x (a : K[X]), Commute Y g) →
    ∃ c : AdjoinRoot (a : K[X]), ∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
      ((Y : LinearMap.GeneralLinearGroup K V) : Module.End K V) (v : V) =
        ((c • v : primaryComponent (x : Module.End K V) (a : K[X])) : V)

variable {B : V →ₛₗ[σ] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}
  {a : primaryFactors (x : Module.End K V)}

omit [FiniteDimensional K V] in
theorem specialBlock_eq_kerImage {Ω : Type*} [Group Ω] (φ : orbitFactor B x (a : K[X]) ≃* Ω)
    (ι : Ω →* blockGL (x : Module.End K V) (a : K[X]))
    (hφ : ∀ (g : orbitFactor B x (a : K[X])) (v : V)
      (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
      blockApply (ι (φ g)) v hv = ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) :
    specialBlock B x (a : K[X]) = kerImage (orbitFactor B x (a : K[X])) φ
      ((blockGLDet (x : Module.End K V) (a : K[X])).comp ι) := by
  have hcompat : ∀ s : orbitFactor B x (a : K[X]), ι (φ s) =
      blockRestrict x (a : K[X]) ⟨s.1, orbitFactor_le_gl_centralizer s.2⟩ :=
    fun s => blockGL_ext fun v hv => hφ s v hv
  ext g
  rw [mem_specialBlock, mem_kerImage]
  constructor
  · rintro ⟨hs, hg, h⟩
    refine ⟨hs, ?_⟩
    change blockGLDet (x : Module.End K V) (a : K[X]) (ι (φ ⟨g, hs⟩)) = 1
    rw [hcompat ⟨g, hs⟩]
    exact h
  · rintro ⟨hs, h⟩
    refine ⟨hs, orbitFactor_le_gl_centralizer hs, ?_⟩
    change blockGLDet (x : Module.End K V) (a : K[X]) (ι (φ ⟨g, hs⟩)) = 1 at h
    rw [hcompat ⟨g, hs⟩] at h
    exact h

theorem scalar_of_commute_restrictions
    (P : blockGL (x : Module.End K V) (a : K[X]) → Prop)
    (hP : ∀ γ : Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V)
        (a : K[X])), (∀ δ, P δ → Commute γ (δ : Module.End (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X])))) → ∃ c : AdjoinRoot (a : K[X]),
          ∀ w, γ w = c • w)
    (hPg : ∀ δ, P δ → ∃ g ∈ specialBlock B x (a : K[X]),
      ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
        blockApply δ v hv = ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v)
    {Y : LinearMap.GeneralLinearGroup K V} (hY : Y ∈ gl_centralizer x)
    (hcomm : ∀ g ∈ specialBlock B x (a : K[X]), Commute Y g) :
    ∃ c : AdjoinRoot (a : K[X]), ∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
      ((Y : LinearMap.GeneralLinearGroup K V) : Module.End K V) (v : V) =
        ((c • v : primaryComponent (x : Module.End K V) (a : K[X])) : V) := by
  obtain ⟨c, hc⟩ := hP ((blockRestrict x (a : K[X]) ⟨Y, hY⟩ : blockGL (x : Module.End K V)
    (a : K[X])) : Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V)
      (a : K[X]))) (fun δ hδ => by
    obtain ⟨g, hg, hδg⟩ := hPg δ hδ
    exact commute_blockRestrict_of_commute hY (hcomm g hg) δ hδg)
  exact ⟨c, fun v => congrArg Subtype.val (hc v)⟩

end Generic

section Paired

variable {K : Type} [Field K] {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}
  {a : primaryFactors (x : Module.End K V)}

theorem spBlockFacts_of_paired (φ : orbitFactor B x (a : K[X]) ≃*
      blockGL (x : Module.End K V) (a : K[X]))
    (hφ : ∀ (g : orbitFactor B x (a : K[X])) (v : V)
      (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
      blockApply (φ g) v hv = ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v)
    (hE : ∃ s : Finset (AdjoinRoot (a : K[X])), s.card = 4) : SpBlockFacts B x a := by
  have hspec := specialBlock_eq_kerImage (B := B) φ (MonoidHom.id _) hφ
  rw [MonoidHom.comp_id] at hspec
  have hquasi : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) →
      CFSG.IsQuasisimple (blockGLDet (x : Module.End K V) (a : K[X])).ker := fun hm =>
    isQuasisimple_ker_det hm (Or.inr hE)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hm
    rw [hspec]
    exact (kerImage_eq_commutator _ φ _ (hquasi hm).1).symm
  · intro hm
    obtain ⟨e⟩ := nonempty_kerImage_mulEquiv (orbitFactor B x (a : K[X])) φ
      (blockGLDet (x : Module.End K V) (a : K[X]))
    rw [hspec]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (hquasi hm)
  · intro hm
    rw [hspec]
    refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
    obtain ⟨hs, h⟩ := (mem_kerImage _ φ _).mp hg
    have h1 : φ ⟨g, hs⟩ = 1 := by
      refine eq_one_of_det_eq_one_of_finrank_le_one (E := AdjoinRoot (a : K[X])) hm _ ?_
      have := congrArg Units.val h
      simpa [blockGLDet] using this
    have : (⟨g, hs⟩ : orbitFactor B x (a : K[X])) = 1 := φ.injective (by rw [h1, map_one])
    exact congrArg Subtype.val this
  · intro hm g hg g' hg'
    have h1 : φ ⟨g, hg⟩ * φ ⟨g', hg'⟩ = φ ⟨g', hg'⟩ * φ ⟨g, hg⟩ := by
      apply Units.ext
      exact (End_commute_of_finrank_le_one hm _ _).eq
    have h2 : (⟨g, hg⟩ : orbitFactor B x (a : K[X])) * ⟨g', hg'⟩ = ⟨g', hg'⟩ * ⟨g, hg⟩ := by
      apply φ.injective
      rw [map_mul, map_mul, h1]
    exact congrArg Subtype.val h2
  · intro Y hY hcomm
    rcases Nat.lt_or_ge (primaryMultiplicity (x : Module.End K V) (a : K[X])) 2 with hm | hm
    · obtain ⟨c, hc⟩ := exists_scalar_of_multiplicity_le_one a (by omega)
        ((blockRestrict x (a : K[X]) ⟨Y, hY⟩ : blockGL (x : Module.End K V) (a : K[X])) :
          Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X])))
      exact ⟨c, fun v => congrArg Subtype.val (hc v)⟩
    · refine scalar_of_commute_restrictions
        (fun δ => LinearMap.det (δ : Module.End (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X]))) = 1)
        (fun γ hγ => exists_smul_of_commute_special_linear hm γ hγ)
        (fun δ hδ => ?_) hY (hcomm hm)
      obtain ⟨g, hgF, hg, hφg⟩ := exists_mem_kerImage (orbitFactor B x (a : K[X])) φ
        (blockGLDet (x : Module.End K V) (a : K[X])) (δ := δ) (by
          apply Units.ext
          simpa [blockGLDet] using hδ)
      refine ⟨g, hspec ▸ hgF, fun v hv => ?_⟩
      rw [← hφg]
      exact hφ ⟨g, hg⟩ v hv

end Paired

section SelfDual

variable {K : Type} [Field K] {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}
  {a : primaryFactors (x : Module.End K V)}

theorem spBlockFacts_of_selfDual {ℓ f' : ℕ} (hE : UnitaryFieldData ℓ f' (AdjoinRoot (a : K[X])))
    {Hf : primaryComponent (x : Module.End K V) (a : K[X]) →ₛₗ[hE.bar]
      primaryComponent (x : Module.End K V) (a : K[X]) →ₗ[AdjoinRoot (a : K[X])]
        AdjoinRoot (a : K[X])}
    (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)
    (φ : orbitFactor B x (a : K[X]) ≃* sesqUnitaryGroup Hf)
    (hφ : ∀ (g : orbitFactor B x (a : K[X])) (v : V)
      (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
      blockApply (φ g : blockGL (x : Module.End K V) (a : K[X])) v hv =
        ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v)
    (hQ : 4 ≤ ℓ ^ f') : SpBlockFacts B x a := by
  have hq2 : 2 ≤ ℓ ^ f' := by omega
  let ι : sesqUnitaryGroup Hf →* blockGL (x : Module.End K V) (a : K[X]) :=
    (sesqUnitaryGroup Hf).subtype
  have hspec := specialBlock_eq_kerImage (B := B) φ ι hφ
  let D : sesqUnitaryGroup Hf →* (AdjoinRoot (a : K[X]))ˣ :=
    (blockGLDet (x : Module.End K V) (a : K[X])).comp ι
  have hker : D.ker = (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf) := by
    ext δ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup]
    constructor
    · intro h
      refine ⟨δ.2, ?_⟩
      have := congrArg Units.val h
      simpa [D, ι, blockGLDet] using this
    · rintro ⟨-, h⟩
      apply Units.ext
      simpa [D, ι, blockGLDet] using h
  have hquasi : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) →
      CFSG.IsQuasisimple D.ker := fun hm => by
    rw [hker]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).symm
      (isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf hHfl hm
        ⟨fun _ => hQ, fun _ => by omega⟩)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hm
    rw [hspec]
    exact (kerImage_eq_commutator _ φ _ (hquasi hm).1).symm
  · intro hm
    obtain ⟨e⟩ := nonempty_kerImage_mulEquiv (orbitFactor B x (a : K[X])) φ D
    rw [hspec]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (hquasi hm)
  · intro hm
    rw [hspec]
    refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
    obtain ⟨hs, h⟩ := (mem_kerImage _ φ _).mp hg
    have h1 : (φ ⟨g, hs⟩ : blockGL (x : Module.End K V) (a : K[X])) = 1 := by
      refine eq_one_of_det_eq_one_of_finrank_le_one (E := AdjoinRoot (a : K[X])) hm _ ?_
      have := congrArg Units.val h
      simpa [D, ι, blockGLDet] using this
    have h2 : φ ⟨g, hs⟩ = 1 := Subtype.ext h1
    have : (⟨g, hs⟩ : orbitFactor B x (a : K[X])) = 1 := φ.injective (by rw [h2, map_one])
    exact congrArg Subtype.val this
  · intro hm g hg g' hg'
    have h1 : φ ⟨g, hg⟩ * φ ⟨g', hg'⟩ = φ ⟨g', hg'⟩ * φ ⟨g, hg⟩ := by
      apply Subtype.ext
      apply Units.ext
      exact (End_commute_of_finrank_le_one hm _ _).eq
    have h2 : (⟨g, hg⟩ : orbitFactor B x (a : K[X])) * ⟨g', hg'⟩ = ⟨g', hg'⟩ * ⟨g, hg⟩ := by
      apply φ.injective
      rw [map_mul, map_mul, h1]
    exact congrArg Subtype.val h2
  · intro Y hY hcomm
    rcases Nat.lt_or_ge (primaryMultiplicity (x : Module.End K V) (a : K[X])) 2 with hm | hm
    · obtain ⟨c, hc⟩ := exists_scalar_of_multiplicity_le_one a (by omega)
        ((blockRestrict x (a : K[X]) ⟨Y, hY⟩ : blockGL (x : Module.End K V) (a : K[X])) :
          Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X])))
      exact ⟨c, fun v => congrArg Subtype.val (hc v)⟩
    · refine scalar_of_commute_restrictions
        (fun δ => δ ∈ sesqSpecialUnitaryGroup Hf)
        (fun γ hγ => exists_smul_of_commute_special_unitary hE hHf hHfl hm hq2 γ hγ)
        (fun δ hδ => ?_) hY (hcomm hm)
      have hδU : δ ∈ sesqUnitaryGroup Hf := (mem_sesqSpecialUnitaryGroup.mp hδ).1
      obtain ⟨g, hgF, hg, hφg⟩ := exists_mem_kerImage (orbitFactor B x (a : K[X])) φ D
        (δ := ⟨δ, hδU⟩) (by
          apply Units.ext
          simpa [D, ι, blockGLDet] using (mem_sesqSpecialUnitaryGroup.mp hδ).2)
      refine ⟨g, hspec ▸ hgF, fun v hv => ?_⟩
      have := hφ ⟨g, hg⟩ v hv
      rw [hφg] at this
      exact this

end SelfDual

section Fixed

variable {K : Type} [Field K] {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : LinearMap.BilinForm K V} {x : LinearMap.GeneralLinearGroup K V}
  {a : primaryFactors (x : Module.End K V)}

local notation "𝒲" => primaryComponent (x : Module.End K V) (a : K[X])

theorem spBlockFacts_of_fixed (hsq : Squarefree (minpoly K (x : Module.End K V)))
    (ha : (a : K[X]) = X - 1) (hB : B.IsAlt) (hnd : (B.restrict 𝒲).Nondegenerate)
    (φ : orbitFactor B x (a : K[X]) ≃* sesqUnitaryGroup (B.restrict 𝒲))
    (hφ : ∀ (g : orbitFactor B x (a : K[X])) (v : 𝒲),
      ((((φ g : sesqUnitaryGroup (B.restrict 𝒲)) : LinearMap.GeneralLinearGroup K 𝒲) :
        Module.End K 𝒲) v : V) = ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) (v : V))
    (hK : 4 ≤ Nat.card K ∨ (Nat.card K = 3 ∧ 4 ≤ Module.finrank K 𝒲) ∨
      (Nat.card K = 2 ∧ 6 ≤ Module.finrank K 𝒲)) :
    SpBlockFacts B x a := by
  have hBalt : (B.restrict 𝒲).IsAlt := fun z => hB.self_eq_zero z
  have hnt : Nontrivial 𝒲 := Submodule.nontrivial_iff_ne_bot.mpr
    (primaryComponent_ne_bot hsq a.2)
  have hpos : 0 < Module.finrank K 𝒲 := Module.finrank_pos
  obtain ⟨s, hs, -⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp hBalt hnd
  have h2 : 2 ≤ Module.finrank K 𝒲 := by omega
  have hm : primaryMultiplicity (x : Module.End K V) (a : K[X]) = Module.finrank K 𝒲 := by
    rw [ha, show (X - 1 : K[X]) = X - C 1 by rw [C_1]]
    exact primaryMultiplicity_X_sub_C_eq _ _
  have hm2 : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) := by omega
  have hQS : CFSG.IsQuasisimple (sesqUnitaryGroup (B.restrict 𝒲)) :=
    isQuasisimple_sesqUnitaryGroup_of_alt hBalt hnd h2 hK
  have hperf : Group.IsPerfect (orbitFactor B x (a : K[X])) :=
    @isPerfect_of_surjective _ _ _ _ φ.symm.toMonoidHom φ.symm.surjective hQS.1
  have hdet : ∀ (g : LinearMap.GeneralLinearGroup K V) (hg : g ∈ orbitFactor B x (a : K[X])),
      blockDetHom x (a : K[X]) ⟨g, orbitFactor_le_gl_centralizer hg⟩ = 1 := by
    intro g hg
    exact eq_one_of_perfect_of_comm hperf (fun u v => mul_comm u v)
      ((blockDetHom x (a : K[X])).comp (Subgroup.inclusion orbitFactor_le_gl_centralizer)) ⟨g, hg⟩
  have hspec : specialBlock B x (a : K[X]) = orbitFactor B x (a : K[X]) := by
    ext g
    rw [mem_specialBlock]
    exact ⟨fun h => h.1, fun hg => ⟨hg, orbitFactor_le_gl_centralizer hg, hdet g hg⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _
    rw [hspec]
    exact commutator_eq_of_isPerfect hperf
  · intro _
    rw [hspec]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm hQS
  · intro hle
    omega
  · intro hle
    omega
  · intro Y hY hcomm
    have hYc : Commute (Y : Module.End K V) (x : Module.End K V) := mem_gl_centralizer.mp hY
    have hfull : ∀ g ∈ orbitFactor B x (a : K[X]), Commute Y g := fun g hg =>
      hcomm hm2 g (hspec ▸ hg)
    let γ : Module.End K 𝒲 := (Y : Module.End K V).restrict
      (fun v hv => apply_mem_primaryComponent hYc hv)
    have hγv : ∀ v : 𝒲, ((γ v : 𝒲) : V) = (Y : Module.End K V) (v : V) := fun v => rfl
    obtain ⟨c₀, hc₀⟩ := exists_smul_of_commute_sesqUnitaryGroup_alt hBalt hnd γ (fun δ hδ => by
      set g : orbitFactor B x (a : K[X]) := φ.symm ⟨δ, hδ⟩ with hg
      have hδg : ∀ v : 𝒲, ((δ : Module.End K 𝒲) v : V) = ((g : LinearMap.GeneralLinearGroup K V) :
          Module.End K V) (v : V) := fun v => by
        have := hφ g v
        rw [hg, MulEquiv.apply_symm_apply] at this
        exact this
      have hcg : ∀ v : V, (Y : Module.End K V) (((g : LinearMap.GeneralLinearGroup K V) :
          Module.End K V) v) = ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V)
            ((Y : Module.End K V) v) := fun v => by
        have := congrArg (fun T : LinearMap.GeneralLinearGroup K V =>
          (T : Module.End K V) v) (hfull g g.2).eq
        simpa using this
      refine LinearMap.ext fun v => Subtype.ext ?_
      change ((γ ((δ : Module.End K 𝒲) v) : 𝒲) : V) = (((δ : Module.End K 𝒲) (γ v) : 𝒲) : V)
      rw [hγv, hδg, hδg, hγv]
      exact hcg (v : V))
    refine ⟨algebraMap K (AdjoinRoot (a : K[X])) c₀, fun v => ?_⟩
    rw [coe_algebraMap_smul_primaryComponent, ← hγv v, hc₀ v]
    rfl

end Fixed

end CFSG.RankThree.PartOne.KCSpIsotypic

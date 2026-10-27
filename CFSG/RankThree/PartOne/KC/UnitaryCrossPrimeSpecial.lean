module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeBlocks
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra

public section

namespace CFSG.RankThree.PartOne.KCUnitary

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne
open scoped commutatorElement

section Linear

theorem End_commute_of_finrank_le_one {E W : Type*} [Field E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (h : Module.finrank E W ≤ 1) (γ δ : Module.End E W) :
    Commute γ δ := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp h
  obtain ⟨c₁, hc₁⟩ := hv (γ v)
  obtain ⟨c₂, hc₂⟩ := hv (δ v)
  refine LinearMap.ext fun w => ?_
  obtain ⟨t, rfl⟩ := hv w
  change γ (δ (t • v)) = δ (γ (t • v))
  simp only [map_smul, ← hc₁, ← hc₂, smul_smul]
  congr 1
  ring

theorem nonempty_specialLinearGroup_mulEquiv_ker_det {E W : Type*} [Field E] [AddCommGroup W]
    [Module E W] [FiniteDimensional E W] :
    Nonempty (Matrix.SpecialLinearGroup (Fin (Module.finrank E W)) E ≃*
      (Units.map (LinearMap.det : Module.End E W →* E)).ker) := by
  classical
  set n := Module.finrank E W with hn
  let b := Module.finBasis E W
  let θ : (Module.End E W)ˣ ≃* (Matrix (Fin n) (Fin n) E)ˣ :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
  have hdet : ∀ γ : (Module.End E W)ˣ,
      Matrix.GeneralLinearGroup.det (θ γ) =
        Units.map (LinearMap.det : Module.End E W →* E) γ := by
    intro γ
    apply Units.ext
    change Matrix.det (LinearMap.toMatrix b b (γ : Module.End E W)) =
      LinearMap.det (γ : Module.End E W)
    exact LinearMap.det_toMatrix b _
  have hmap : (Units.map (LinearMap.det : Module.End E W →* E)).ker.map θ.toMonoidHom =
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin n) E →* Eˣ).ker := by
    ext A
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      show Matrix.GeneralLinearGroup.det (θ γ) = 1
      rw [hdet]
      exact hγ
    · intro hA
      refine ⟨θ.symm A, ?_, by simp⟩
      show Units.map (LinearMap.det : Module.End E W →* E) (θ.symm A) = 1
      rw [← hdet, θ.apply_symm_apply]
      exact hA
  let e : (Units.map (LinearMap.det : Module.End E W →* E)).ker ≃*
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin n) E →* Eˣ).ker :=
    (θ.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
  exact ⟨Matrix.SpecialLinearGroup.toGLKerEquiv.trans e.symm⟩

theorem isQuasisimple_ker_det {E W : Type*} [Field E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (hm : 2 ≤ Module.finrank E W)
    (h : 3 ≤ Module.finrank E W ∨ ∃ s : Finset E, s.card = 4) :
    CFSG.IsQuasisimple (Units.map (LinearMap.det : Module.End E W →* E)).ker := by
  obtain ⟨e⟩ := nonempty_specialLinearGroup_mulEquiv_ker_det (E := E) (W := W)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e (isQuasisimple_SL hm h)

end Linear

section Cases

universe u

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K}
  {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

structure SpecialBlockFacts (B : V →ₛₗ[hK.bar] V →ₗ[K] K) (x : LinearMap.GeneralLinearGroup K V)
    (a : primaryFactors (x : Module.End K V)) : Prop where
  detK : ∀ g ∈ specialBlock B x (a : K[X]), LinearMap.det (g : Module.End K V) = 1
  commutator_eq : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) →
    ⁅orbitFactor B x (a : K[X]), orbitFactor B x (a : K[X])⁆ = specialBlock B x (a : K[X])
  quasisimple : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) →
    CFSG.IsQuasisimple (specialBlock B x (a : K[X]))
  abelian : primaryMultiplicity (x : Module.End K V) (a : K[X]) ≤ 1 →
    ∀ g ∈ orbitFactor B x (a : K[X]), ∀ g' ∈ orbitFactor B x (a : K[X]), Commute g g'
  scalar : ∀ Y ∈ unitaryCentralizer B x,
    (2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) →
      ∀ g ∈ specialBlock B x (a : K[X]), Commute Y g) →
    ∃ c : AdjoinRoot (a : K[X]), ∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
      ((Y : LinearMap.GeneralLinearGroup K V) : Module.End K V) (v : V) =
        ((c • v : primaryComponent (x : Module.End K V) (a : K[X])) : V)

theorem exists_finset_card_four (hK : UnitaryFieldData ℓ f K) {E : Type*} [Field E] [Algebra K E]
    (hq : 2 ≤ ℓ ^ f) :
    ∃ s : Finset E, s.card = 4 := by
  have := hK.finite
  have hcard : 4 ≤ Nat.card K := by
    rw [hK.card_eq_sq]
    nlinarith
  have := Fintype.ofFinite K
  have h4 : 4 ≤ (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact hcard
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
  exact ⟨s.map ⟨algebraMap K E, (algebraMap K E).injective⟩, by rw [Finset.card_map, hs]⟩

omit [FiniteDimensional K V] in
theorem commute_blockRestrict_of_commute {a : K[X]} {Y g : LinearMap.GeneralLinearGroup K V}
    (hY : Y ∈ gl_centralizer x) (hcomm : Commute Y g)
    (δ : blockGL (x : Module.End K V) a)
    (hδ : ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) a),
      blockApply δ v hv = ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) :
    Commute ((blockRestrict x a ⟨Y, hY⟩ : blockGL (x : Module.End K V) a) :
        Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a))
      (δ : Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  have h1 : (Y : Module.End K V) ((g : Module.End K V) (w : V)) =
      (g : Module.End K V) ((Y : Module.End K V) (w : V)) := by
    have := congrArg (fun T : LinearMap.GeneralLinearGroup K V => (T : Module.End K V) (w : V))
      hcomm.eq
    exact this
  have hγ : ∀ u : primaryComponent (x : Module.End K V) a,
      ((((blockRestrict x a ⟨Y, hY⟩ : blockGL (x : Module.End K V) a) :
        Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) u :
          primaryComponent (x : Module.End K V) a) : V) = (Y : Module.End K V) (u : V) :=
    fun u => blockApply_blockRestrict x a ⟨Y, hY⟩ u.1 u.2
  have hδ' : ∀ u : primaryComponent (x : Module.End K V) a,
      (((δ : Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) u :
        primaryComponent (x : Module.End K V) a) : V) = (g : Module.End K V) (u : V) :=
    fun u => hδ u.1 u.2
  change ((((blockRestrict x a ⟨Y, hY⟩ : blockGL (x : Module.End K V) a) :
        Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a))
      ((δ : Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) w) :
        primaryComponent (x : Module.End K V) a) : V) =
    (((δ : Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a))
      (((blockRestrict x a ⟨Y, hY⟩ : blockGL (x : Module.End K V) a) :
        Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) w) :
          primaryComponent (x : Module.End K V) a) : V)
  rw [hγ, hδ', hδ', hγ, h1]

theorem exists_scalar_of_multiplicity_le_one (a : primaryFactors (x : Module.End K V))
    (h : primaryMultiplicity (x : Module.End K V) (a : K[X]) ≤ 1)
    (γ : Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) :
    ∃ c : AdjoinRoot (a : K[X]), ∀ w, γ w = c • w :=
  exists_smul_of_forall_commute γ (End_commute_of_finrank_le_one h γ)

theorem exists_pairedFactor {a : primaryFactors (x : Module.End K V)}
    (hP : PairedPrimaryBlock hK B x a) :
    ∃ φ : orbitFactor B x (a : K[X]) ≃* blockGL (x : Module.End K V) (a : K[X]),
      (∀ (g : orbitFactor B x (a : K[X])) (v : V)
        (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
          blockApply (φ g) v hv = ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) ∧
      (∀ g : orbitFactor B x (a : K[X]),
        LinearMap.det ((φ g : blockGL (x : Module.End K V) (a : K[X])) :
          Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) =
            1 → LinearMap.det ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) = 1) := by
  obtain ⟨φ, -, hφ, -, -, hdetK⟩ := hP.factor
  exact ⟨φ, hφ, hdetK⟩

theorem specialBlockFacts_of_paired (hq : 2 ≤ ℓ ^ f) (a : primaryFactors (x : Module.End K V))
    (hP : PairedPrimaryBlock hK B x a) : SpecialBlockFacts B x a := by
  obtain ⟨φ, hφ, hdetK⟩ := exists_pairedFactor hP
  have hcompat : ∀ s : orbitFactor B x (a : K[X]), φ s = blockRestrict x (a : K[X])
      ⟨s.1, orbitFactor_le_gl_centralizer s.2⟩ :=
    fun s => blockGL_ext fun v hv => hφ s v hv
  have hspec : specialBlock B x (a : K[X]) = kerImage (orbitFactor B x (a : K[X])) φ
      (blockGLDet (x : Module.End K V) (a : K[X])) := by
    ext g
    rw [mem_specialBlock, mem_kerImage]
    constructor
    · rintro ⟨hs, hg, h⟩
      refine ⟨hs, ?_⟩
      rw [hcompat ⟨g, hs⟩]
      exact h
    · rintro ⟨hs, h⟩
      refine ⟨hs, orbitFactor_le_gl_centralizer hs, ?_⟩
      rw [hcompat ⟨g, hs⟩] at h
      exact h
  have hquasi : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) →
      CFSG.IsQuasisimple (blockGLDet (x : Module.End K V) (a : K[X])).ker := fun hm =>
    isQuasisimple_ker_det hm (Or.inr (exists_finset_card_four hK hq))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rw [hspec, mem_kerImage] at hg
    obtain ⟨hs, h⟩ := hg
    refine hdetK ⟨g, hs⟩ ?_
    have := congrArg Units.val h
    simpa [blockGLDet] using this
  · intro hm
    rw [hspec]
    exact (kerImage_eq_commutator _ φ _ (hquasi hm).1).symm
  · intro hm
    obtain ⟨e⟩ := nonempty_kerImage_mulEquiv (orbitFactor B x (a : K[X])) φ
      (blockGLDet (x : Module.End K V) (a : K[X]))
    rw [hspec]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (hquasi hm)
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
        ((blockRestrict x (a : K[X]) ⟨Y, hY.2⟩ : blockGL (x : Module.End K V) (a : K[X])) :
          Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X])))
      exact ⟨c, fun v => congrArg Subtype.val (hc v)⟩
    · obtain ⟨c, hc⟩ := exists_smul_of_commute_special_linear hm
        ((blockRestrict x (a : K[X]) ⟨Y, hY.2⟩ : blockGL (x : Module.End K V) (a : K[X])) :
          Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X])))
        (fun δ hδ => by
          obtain ⟨g, hgF, hg, hφg⟩ := exists_mem_kerImage (orbitFactor B x (a : K[X])) φ
            (blockGLDet (x : Module.End K V) (a : K[X])) (δ := δ) (by
              apply Units.ext
              simpa [blockGLDet] using hδ)
          refine commute_blockRestrict_of_commute hY.2 (hcomm hm g (hspec ▸ hgF)) δ ?_
          intro v hv
          rw [← hφg]
          exact hφ ⟨g, hg⟩ v hv)
      exact ⟨c, fun v => congrArg Subtype.val (hc v)⟩

theorem exists_selfDualFactor {a : primaryFactors (x : Module.End K V)}
    (hself : dualPoly hK.bar (a : K[X]) = a) (hS : SelfDualPrimaryBlock hK B x a) :
    ∃ (hE : UnitaryFieldData ℓ (f * (a : K[X]).natDegree) (AdjoinRoot (a : K[X])))
      (Hf : primaryComponent (x : Module.End K V) (a : K[X]) →ₛₗ[hE.bar]
        primaryComponent (x : Module.End K V) (a : K[X]) →ₗ[AdjoinRoot (a : K[X])]
          AdjoinRoot (a : K[X])),
      Hf.IsSymm ∧ Hf.SeparatingLeft ∧
      ∃ φ : orbitFactor B x (a : K[X]) ≃* sesqUnitaryGroup Hf,
        (∀ (g : orbitFactor B x (a : K[X])) (v : V)
          (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
            blockApply (φ g : blockGL (x : Module.End K V) (a : K[X])) v hv =
              ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) ∧
        (∀ g : orbitFactor B x (a : K[X]),
          (φ g : blockGL (x : Module.End K V) (a : K[X])) ∈ sesqSpecialUnitaryGroup Hf →
            LinearMap.det ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) = 1) := by
  obtain ⟨hE, -, -, Hf, hHf, hHfl, -, -, φ, hφ, hdetK⟩ := hS.unitaryForm
  have hsupp : orbitFactor B x (a : K[X]) = supportedUnitary B x {(a : K[X])} := by
    unfold orbitFactor
    rw [hself, Set.pair_eq_singleton]
  refine ⟨hE, Hf, hHf, hHfl, (MulEquiv.subgroupCongr hsupp).trans φ, ?_, ?_⟩
  · intro g v hv
    exact hφ ((MulEquiv.subgroupCongr hsupp) g) v hv
  · intro g hg
    exact hdetK ((MulEquiv.subgroupCongr hsupp) g) hg

theorem le_pow_natDegree (hK : UnitaryFieldData ℓ f K) (a : primaryFactors (x : Module.End K V)) :
    ℓ ^ f ≤ ℓ ^ (f * (a : K[X]).natDegree) := by
  have hd : 1 ≤ (a : K[X]).natDegree :=
    Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.2)
  exact Nat.pow_le_pow_right hK.prime.pos (by nlinarith)

theorem specialBlockFacts_of_selfDual (hq : 2 ≤ ℓ ^ f) (a : primaryFactors (x : Module.End K V))
    (hself : dualPoly hK.bar (a : K[X]) = a) (hS : SelfDualPrimaryBlock hK B x a)
    (hgood : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) →
      (primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 →
        4 ≤ ℓ ^ (f * (a : K[X]).natDegree)) ∧
      (primaryMultiplicity (x : Module.End K V) (a : K[X]) = 3 →
        3 ≤ ℓ ^ (f * (a : K[X]).natDegree))) :
    SpecialBlockFacts B x a := by
  obtain ⟨hE, Hf, hHf, hHfl, φ, hφ, hdetK⟩ := exists_selfDualFactor hself hS
  have hq' : 2 ≤ ℓ ^ (f * (a : K[X]).natDegree) := hq.trans (le_pow_natDegree hK a)
  let D : sesqUnitaryGroup Hf →* (AdjoinRoot (a : K[X]))ˣ :=
    (blockGLDet (x : Module.End K V) (a : K[X])).comp (sesqUnitaryGroup Hf).subtype
  have hcompat : ∀ s : orbitFactor B x (a : K[X]),
      ((φ s : sesqUnitaryGroup Hf) : blockGL (x : Module.End K V) (a : K[X])) =
        blockRestrict x (a : K[X]) ⟨s.1, orbitFactor_le_gl_centralizer s.2⟩ :=
    fun s => blockGL_ext fun v hv => hφ s v hv
  have hspec : specialBlock B x (a : K[X]) = kerImage (orbitFactor B x (a : K[X])) φ D := by
    ext g
    rw [mem_specialBlock, mem_kerImage]
    constructor
    · rintro ⟨hs, hg, h⟩
      refine ⟨hs, ?_⟩
      change blockGLDet (x : Module.End K V) (a : K[X]) ((φ ⟨g, hs⟩ : sesqUnitaryGroup Hf) :
        blockGL (x : Module.End K V) (a : K[X])) = 1
      rw [hcompat ⟨g, hs⟩]
      exact h
    · rintro ⟨hs, h⟩
      refine ⟨hs, orbitFactor_le_gl_centralizer hs, ?_⟩
      change blockGLDet (x : Module.End K V) (a : K[X]) ((φ ⟨g, hs⟩ : sesqUnitaryGroup Hf) :
        blockGL (x : Module.End K V) (a : K[X])) = 1 at h
      rw [hcompat ⟨g, hs⟩] at h
      exact h
  have hker : D.ker = (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf) := by
    ext δ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup]
    constructor
    · intro h
      refine ⟨δ.2, ?_⟩
      have := congrArg Units.val h
      simpa [D, blockGLDet] using this
    · rintro ⟨-, h⟩
      apply Units.ext
      simpa [D, blockGLDet] using h
  have hquasi : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) →
      CFSG.IsQuasisimple D.ker := fun hm => by
    rw [hker]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).symm
      (isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf hHfl hm (hgood hm))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rw [hspec, mem_kerImage] at hg
    obtain ⟨hs, h⟩ := hg
    refine hdetK ⟨g, hs⟩ ?_
    have h1 : ((φ ⟨g, hs⟩ : sesqUnitaryGroup Hf) : blockGL (x : Module.End K V) (a : K[X])) ∈
        sesqUnitaryGroup Hf := (φ ⟨g, hs⟩).2
    rw [mem_sesqSpecialUnitaryGroup]
    refine ⟨h1, ?_⟩
    have := congrArg Units.val h
    simpa [D, blockGLDet] using this
  · intro hm
    rw [hspec]
    exact (kerImage_eq_commutator _ φ _ (hquasi hm).1).symm
  · intro hm
    obtain ⟨e⟩ := nonempty_kerImage_mulEquiv (orbitFactor B x (a : K[X])) φ D
    rw [hspec]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (hquasi hm)
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
        ((blockRestrict x (a : K[X]) ⟨Y, hY.2⟩ : blockGL (x : Module.End K V) (a : K[X])) :
          Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X])))
      exact ⟨c, fun v => congrArg Subtype.val (hc v)⟩
    · obtain ⟨c, hc⟩ := exists_smul_of_commute_special_unitary hE hHf hHfl hm hq'
        ((blockRestrict x (a : K[X]) ⟨Y, hY.2⟩ : blockGL (x : Module.End K V) (a : K[X])) :
          Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X])))
        (fun δ hδ => by
          have hδU : δ ∈ sesqUnitaryGroup Hf := (mem_sesqSpecialUnitaryGroup.mp hδ).1
          obtain ⟨g, hgF, hg, hφg⟩ := exists_mem_kerImage (orbitFactor B x (a : K[X])) φ D
            (δ := ⟨δ, hδU⟩) (by
              apply Units.ext
              simpa [D, blockGLDet] using (mem_sesqSpecialUnitaryGroup.mp hδ).2)
          refine commute_blockRestrict_of_commute hY.2 (hcomm hm g (hspec ▸ hgF)) δ ?_
          intro v hv
          have := hφ ⟨g, hg⟩ v hv
          rw [hφg] at this
          exact this)
      exact ⟨c, fun v => congrArg Subtype.val (hc v)⟩

theorem specialBlockFacts (H : UnitaryPrimaryData hK.bar B x) (hq : 4 ≤ ℓ ^ f)
    (a : primaryFactors (x : Module.End K V)) : SpecialBlockFacts B x a := by
  by_cases hself : dualPoly hK.bar (a : K[X]) = a
  · exact specialBlockFacts_of_selfDual (by omega) a hself (selfDualPrimaryBlock H a hself)
      (fun _ => ⟨fun _ => hq.trans (le_pow_natDegree hK a),
        fun _ => (by omega : 3 ≤ ℓ ^ f).trans (le_pow_natDegree hK a)⟩)
  · exact specialBlockFacts_of_paired (by omega) a (pairedPrimaryBlock H a (Ne.symm hself))

end Cases

end CFSG.RankThree.PartOne.KCUnitary

module

public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicBlocks

public section

namespace CFSG.RankThree.PartOne.KCSpIsotypic

open Polynomial Module Matrix CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

variable {r : ℕ} {K : Type} [Field K] {ℓ f p : ℕ}

abbrev SpBlockIdx (x : StatedSp r K) : Type :=
  {a : primaryFactors (spEnd x) // 2 ≤ primaryMultiplicity (spEnd x) (a : K[X])}

theorem unitaryCentralizer_spForm_eq_map (x : StatedSp r K) :
    unitaryCentralizer (spForm r K) (spLin r K x) =
      (Subgroup.centralizer ({x} : Set (StatedSp r K))).map (spLin r K) := by
  ext g
  constructor
  · intro hg
    obtain ⟨hgs, hgc⟩ := mem_unitaryCentralizer.mp hg
    obtain ⟨g₀, rfl⟩ : g ∈ (spLin r K).range := by rw [range_spLin]; exact hgs
    refine ⟨g₀, Subgroup.mem_centralizer_singleton_iff.mpr (spLin_injective ?_), rfl⟩
    rw [map_mul, map_mul]
    exact Units.ext (by rw [Units.val_mul, Units.val_mul]; exact hgc.eq)
  · rintro ⟨g₀, hg₀, rfl⟩
    refine mem_unitaryCentralizer.mpr ⟨spLin_mem g₀, ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp hg₀
    change spEnd g₀ * spEnd x = spEnd x * spEnd g₀
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, this]

theorem directProduct_GL {x : StatedSp r K} (blocks : SpPrimaryBlocks ℓ f p x (proj r K x)) :
    (∀ O ∈ reciprocalOrbits (spEnd x), ∀ O' ∈ reciprocalOrbits (spEnd x), O ≠ O' →
      ∀ g ∈ supportedUnitary (spForm r K) (spLin r K x) O,
        ∀ g' ∈ supportedUnitary (spForm r K) (spLin r K x) O', Commute g g') ∧
    (⨆ O : reciprocalOrbits (spEnd x),
      supportedUnitary (spForm r K) (spLin r K x) (O : Set K[X])) =
      unitaryCentralizer (spForm r K) (spLin r K x) := by
  obtain ⟨hcomm, -, hgen⟩ := blocks.directProduct
  refine ⟨fun O hO O' hO' hne g hg g' hg' => ?_, ?_⟩
  · rw [← map_spSupported] at hg hg'
    obtain ⟨g₀, hg₀, rfl⟩ := hg
    obtain ⟨g₀', hg₀', rfl⟩ := hg'
    have := hcomm O hO O' hO' hne g₀ hg₀ g₀' hg₀'
    exact this.map (spLin r K)
  · rw [unitaryCentralizer_spForm_eq_map, ← hgen, Subgroup.map_iSup]
    exact iSup_congr fun O => (map_spSupported x _).symm

variable {x : StatedSp r K}

theorem commutator_unitaryCentralizer_eq_iSup
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (facts : ∀ h : primaryFactors (spEnd x), SpBlockFacts (spForm r K) (spLin r K x) h) :
    ⁅unitaryCentralizer (spForm r K) (spLin r K x),
        unitaryCentralizer (spForm r K) (spLin r K x)⁆ =
      ⨆ a : SpBlockIdx x, specialBlock (spForm r K) (spLin r K x) (a.1 : K[X]) := by
  obtain ⟨hcomm, hgen⟩ := directProduct_GL blocks
  rw [← hgen, commutator_iSup_commuting
    (fun O : reciprocalOrbits (spEnd x) =>
      supportedUnitary (spForm r K) (spLin r K x) (O : Set K[X]))
    (fun i j hij => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)))]
  apply le_antisymm
  · refine iSup_le fun O => ?_
    obtain ⟨a₀, ha₀, hO⟩ := O.2
    let a : primaryFactors (spEnd x) := ⟨a₀, ha₀⟩
    have hOa : supportedUnitary (spForm r K) (spLin r K x) (O : Set K[X]) =
        orbitFactor (spForm r K) (spLin r K x) (a : K[X]) := by
      rw [orbitFactor_spForm]
      exact congrArg _ hO.symm
    rw [hOa]
    by_cases hm : 2 ≤ primaryMultiplicity (spEnd x) (a : K[X])
    · rw [(facts a).commutator_eq hm]
      exact le_iSup (fun b : SpBlockIdx x =>
        specialBlock (spForm r K) (spLin r K x) (b.1 : K[X])) ⟨a, hm⟩
    · have : ⁅orbitFactor (spForm r K) (spLin r K x) (a : K[X]),
          orbitFactor (spForm r K) (spLin r K x) (a : K[X])⁆ = ⊥ := by
        refine le_antisymm (Subgroup.commutator_le.mpr fun g hg g' hg' => ?_) bot_le
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
        have hle : primaryMultiplicity (spEnd x) (a : K[X]) ≤ 1 := by omega
        exact (facts a).abelian hle g hg g' hg'
      rw [this]
      exact bot_le
  · refine iSup_le fun ⟨a, hm⟩ => ?_
    have hO : ({(a : K[X]), reciprocalPolynomial (a : K[X])} : Set K[X]) ∈
        reciprocalOrbits (spEnd x) := ⟨a, a.2, rfl⟩
    rw [← (facts a).commutator_eq hm]
    have hOa : orbitFactor (spForm r K) (spLin r K x) (a : K[X]) =
        supportedUnitary (spForm r K) (spLin r K x)
          (({(a : K[X]), reciprocalPolynomial (a : K[X])} : Set K[X])) :=
      orbitFactor_spForm x _
    rw [hOa]
    exact le_iSup (fun O : reciprocalOrbits (spEnd x) =>
      ⁅supportedUnitary (spForm r K) (spLin r K x) (O : Set K[X]),
        supportedUnitary (spForm r K) (spLin r K x) (O : Set K[X])⁆) ⟨_, hO⟩

theorem commute_specialBlock_of_ne (blocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (a b : primaryFactors (spEnd x)) (hba : (b : K[X]) ≠ a)
    (hbd : (b : K[X]) ≠ reciprocalPolynomial (a : K[X]))
    {g g' : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)}
    (hg : g ∈ specialBlock (spForm r K) (spLin r K x) (a : K[X]))
    (hg' : g' ∈ specialBlock (spForm r K) (spLin r K x) (b : K[X])) : Commute g g' := by
  obtain ⟨hcomm, -⟩ := directProduct_GL blocks
  have hO : ({(a : K[X]), reciprocalPolynomial (a : K[X])} : Set K[X]) ∈
      reciprocalOrbits (spEnd x) := ⟨a, a.2, rfl⟩
  have hO' : ({(b : K[X]), reciprocalPolynomial (b : K[X])} : Set K[X]) ∈
      reciprocalOrbits (spEnd x) := ⟨b, b.2, rfl⟩
  have hne : ({(a : K[X]), reciprocalPolynomial (a : K[X])} : Set K[X]) ≠
      {(b : K[X]), reciprocalPolynomial (b : K[X])} := by
    intro h
    have hb : (b : K[X]) ∈ ({(a : K[X]), reciprocalPolynomial (a : K[X])} : Set K[X]) := by
      rw [h]
      exact Or.inl rfl
    rcases hb with hb | hb
    · exact hba hb
    · exact hbd hb
  have h1 := specialBlock_le_orbitFactor hg
  have h2 := specialBlock_le_orbitFactor hg'
  rw [orbitFactor_spForm] at h1 h2
  exact hcomm _ hO _ hO' hne g h1 g' h2

theorem specialBlock_reciprocal
    (facts : ∀ h : primaryFactors (spEnd x), SpBlockFacts (spForm r K) (spLin r K x) h)
    (hrr : ∀ a ∈ primaryFactors (spEnd x), reciprocalPolynomial (reciprocalPolynomial a) = a)
    (a b : primaryFactors (spEnd x)) (hb : (b : K[X]) = reciprocalPolynomial (a : K[X]))
    (hma : 2 ≤ primaryMultiplicity (spEnd x) (a : K[X]))
    (hmb : 2 ≤ primaryMultiplicity (spEnd x) (b : K[X])) :
    specialBlock (spForm r K) (spLin r K x) (b : K[X]) =
      specialBlock (spForm r K) (spLin r K x) (a : K[X]) := by
  have hset : orbitFactor (spForm r K) (spLin r K x) (b : K[X]) =
      orbitFactor (spForm r K) (spLin r K x) (a : K[X]) := by
    rw [orbitFactor_spForm, orbitFactor_spForm, hb, hrr a a.2, Set.pair_comm]
  rw [← (facts a).commutator_eq hma, ← (facts b).commutator_eq hmb, hset]

theorem mem_center_of_commute_specialBlocks
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (facts : ∀ h : primaryFactors (spEnd x), SpBlockFacts (spForm r K) (spLin r K x) h)
    {Y : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)}
    (hY : Y ∈ gl_centralizer (spLin r K x))
    (hcomm : ∀ a : primaryFactors (spEnd x), 2 ≤ primaryMultiplicity (spEnd x) (a : K[X]) →
      ∀ g ∈ specialBlock (spForm r K) (spLin r K x) (a : K[X]), Commute Y g) :
    ∃ hz : (Y : Module.End K (Fin r ⊕ Fin r → K)) ∈ commutant (spEnd x),
      (⟨(Y : Module.End K (Fin r ⊕ Fin r → K)), hz⟩ : commutant (spEnd x)) ∈
        Subalgebra.center K (commutant (spEnd x)) :=
  ⟨mem_commutant_of_mem_gl_centralizer hY,
    (blocks.center_eq _).mpr fun a => (facts a).scalar Y hY (hcomm a)⟩

end CFSG.RankThree.PartOne.KCSpIsotypic

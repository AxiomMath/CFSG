module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSpecial

public section

namespace CFSG.RankThree.PartOne.KCUnitary

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne
open scoped commutatorElement

universe u

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K}
  {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}
  (H : UnitaryPrimaryData hK.bar B x)

include H in
theorem specialBlock_le_sesqSpecialUnitaryGroup (hq : 4 ≤ ℓ ^ f)
    (a : primaryFactors (x : Module.End K V)) :
    specialBlock B x (a : K[X]) ≤ sesqSpecialUnitaryGroup B := by
  intro g hg
  refine mem_sesqSpecialUnitaryGroup.mpr ⟨?_, (specialBlockFacts H hq a).detK g hg⟩
  exact (specialBlock_le_unitaryCentralizer hg).1

include H in
theorem commute_specialBlock_of_ne (a b : primaryFactors (x : Module.End K V))
    (hba : (b : K[X]) ≠ a) (hbd : (b : K[X]) ≠ dualPoly hK.bar (a : K[X]))
    {g g' : LinearMap.GeneralLinearGroup K V} (hg : g ∈ specialBlock B x (a : K[X]))
    (hg' : g' ∈ specialBlock B x (b : K[X])) : Commute g g' := by
  have hO : ({(a : K[X]), dualPoly hK.bar (a : K[X])} : Set K[X]) ∈ adjointOrbits hK x :=
    ⟨a, a.2, rfl⟩
  have hO' : ({(b : K[X]), dualPoly hK.bar (b : K[X])} : Set K[X]) ∈ adjointOrbits hK x :=
    ⟨b, b.2, rfl⟩
  have hne : ({(a : K[X]), dualPoly hK.bar (a : K[X])} : Set K[X]) ≠
      {(b : K[X]), dualPoly hK.bar (b : K[X])} := by
    intro h
    have hb : (b : K[X]) ∈ ({(a : K[X]), dualPoly hK.bar (a : K[X])} : Set K[X]) := by
      rw [h]
      exact Or.inl rfl
    rcases hb with hb | hb
    · exact hba hb
    · exact hbd hb
  exact commute_of_disjoint H (adjointOrbits_disjoint H hO hO' hne)
    (specialBlock_le_orbitFactor hg) (specialBlock_le_orbitFactor hg')

include H in
theorem specialBlock_dualFactor (hq : 4 ≤ ℓ ^ f) (a : primaryFactors (x : Module.End K V))
    (hm : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])) :
    specialBlock B x (dualFactor H a : K[X]) = specialBlock B x (a : K[X]) := by
  have hmb : primaryMultiplicity (x : Module.End K V) ((dualFactor H a : primaryFactors
      (x : Module.End K V)) : K[X]) = primaryMultiplicity (x : Module.End K V) (a : K[X]) :=
    primaryMultiplicity_dualPoly H a.2
  have hset : orbitFactor B x ((dualFactor H a : primaryFactors (x : Module.End K V)) : K[X]) =
      orbitFactor B x (a : K[X]) := by
    unfold orbitFactor
    have : dualPoly hK.bar (dualPoly hK.bar (a : K[X])) = a := dualPoly_dualPoly_of_mem H a.2
    change supportedUnitary B x {dualPoly hK.bar (a : K[X]),
      dualPoly hK.bar (dualPoly hK.bar (a : K[X]))} = _
    rw [this, Set.pair_comm]
  rw [← (specialBlockFacts H hq a).commutator_eq hm,
    ← (specialBlockFacts H hq (dualFactor H a)).commutator_eq (by omega), hset]

include H in
theorem commutator_unitaryCentralizer_eq_iSup_specialBlock (hq : 4 ≤ ℓ ^ f) :
    ⁅unitaryCentralizer B x, unitaryCentralizer B x⁆ =
      ⨆ a : {a : primaryFactors (x : Module.End K V) //
        2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])}, specialBlock B x (a : K[X]) := by
  have hF := r3e_unitary_semisimple_primary_algebra_and_full_centralizer hK B H.symm H.sep x
    H.isom H.squarefree
  obtain ⟨hcomm, -, hgen⟩ := hF.directProduct
  have hM : (⨆ O : adjointOrbits hK x, supportedUnitary B x (O : Set K[X])) =
      unitaryCentralizer B x := hgen
  have hA : ∀ (a : primaryFactors (x : Module.End K V)) (O : adjointOrbits hK x),
      (O : Set K[X]) = {(a : K[X]), dualPoly hK.bar (a : K[X])} →
        supportedUnitary B x (O : Set K[X]) = orbitFactor B x (a : K[X]) := by
    intro a O hO
    rw [hO]
    rfl
  rw [← hM, commutator_iSup_commuting (fun O : adjointOrbits hK x =>
    supportedUnitary B x (O : Set K[X]))
    (fun i j hij => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)))]
  apply le_antisymm
  · refine iSup_le fun O => ?_
    obtain ⟨a₀, ha₀, hO⟩ := O.2
    let a : primaryFactors (x : Module.End K V) := ⟨a₀, ha₀⟩
    have hOa : (O : Set K[X]) = {(a : K[X]), dualPoly hK.bar (a : K[X])} := hO.symm
    rw [hA a O hOa]
    by_cases hm : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])
    · rw [(specialBlockFacts H hq a).commutator_eq hm]
      exact le_iSup (fun b : {a : primaryFactors (x : Module.End K V) //
        2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])} => specialBlock B x (b : K[X]))
        ⟨a, hm⟩
    · have : ⁅orbitFactor B x (a : K[X]), orbitFactor B x (a : K[X])⁆ = ⊥ := by
        refine le_antisymm (Subgroup.commutator_le.mpr fun g hg g' hg' => ?_) bot_le
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
        exact (specialBlockFacts H hq a).abelian (by omega) g hg g' hg'
      rw [this]
      exact bot_le
  · refine iSup_le fun ⟨a, hm⟩ => ?_
    have hO : ({(a : K[X]), dualPoly hK.bar (a : K[X])} : Set K[X]) ∈ adjointOrbits hK x :=
      ⟨a, a.2, rfl⟩
    rw [← (specialBlockFacts H hq a).commutator_eq hm]
    exact le_iSup (fun O : adjointOrbits hK x =>
      ⁅supportedUnitary B x (O : Set K[X]), supportedUnitary B x (O : Set K[X])⁆) ⟨_, hO⟩

include H in
theorem mem_center_of_commute_specialBlocks (hq : 4 ≤ ℓ ^ f) {Y : LinearMap.GeneralLinearGroup K V}
    (hY : Y ∈ unitaryCentralizer B x)
    (hcomm : ∀ a : primaryFactors (x : Module.End K V),
      2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) →
        ∀ g ∈ specialBlock B x (a : K[X]), Commute Y g) :
    Y ∈ sesqUnitaryGroup B ∧ ∃ hz : (Y : Module.End K V) ∈ commutant (x : Module.End K V),
      (⟨(Y : Module.End K V), hz⟩ : commutant (x : Module.End K V)) ∈
        Subalgebra.center K (commutant (x : Module.End K V)) := by
  have hF := r3e_unitary_semisimple_primary_algebra_and_full_centralizer hK B H.symm H.sep x
    H.isom H.squarefree
  exact (hF.center_group Y).mp ⟨hY, fun a => (specialBlockFacts H hq a).scalar Y hY (hcomm a)⟩

section CenterUnitary

variable {σ : K →+* K}

@[expose] def centerUnitary (B : V →ₛₗ[σ] V →ₗ[K] K) (x : LinearMap.GeneralLinearGroup K V) :
    Subgroup (LinearMap.GeneralLinearGroup K V) where
  carrier := {g | g ∈ sesqUnitaryGroup B ∧
    ∃ hz : (g : Module.End K V) ∈ commutant (x : Module.End K V),
      (⟨(g : Module.End K V), hz⟩ : commutant (x : Module.End K V)) ∈
        Subalgebra.center K (commutant (x : Module.End K V))}
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    have hz : ((1 : LinearMap.GeneralLinearGroup K V) : Module.End K V) ∈
        commutant (x : Module.End K V) := one_mem _
    exact ⟨hz, Subalgebra.one_mem _⟩
  mul_mem' := by
    rintro g g' ⟨hg, hz, hc⟩ ⟨hg', hz', hc'⟩
    refine ⟨mul_mem hg hg', ?_⟩
    have hzz : ((g * g' : LinearMap.GeneralLinearGroup K V) : Module.End K V) ∈
        commutant (x : Module.End K V) := by
      rw [Units.val_mul]
      exact mul_mem hz hz'
    exact ⟨hzz, Subalgebra.mul_mem _ hc hc'⟩
  inv_mem' := by
    rintro g ⟨hg, hz, hc⟩
    refine ⟨inv_mem hg, ?_⟩
    have hgc : Commute ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V)
        (x : Module.End K V) := (mem_commutant _).mp hz
    have hzz : ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) ∈
        commutant (x : Module.End K V) := (mem_commutant _).mpr (Commute.units_inv_left hgc)
    refine ⟨hzz, Subalgebra.mem_center_iff.mpr fun r => ?_⟩
    have h1 := Subalgebra.mem_center_iff.mp hc r
    have h2 : Commute ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V)
        (r : Module.End K V) := by
      have := congrArg Subtype.val h1
      exact this.symm
    exact Subtype.ext (Commute.units_inv_left h2).symm.eq

omit [FiniteDimensional K V] in
theorem mem_centerUnitary {B : V →ₛₗ[σ] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}
    {g : LinearMap.GeneralLinearGroup K V} :
    g ∈ centerUnitary B x ↔ g ∈ sesqUnitaryGroup B ∧
      ∃ hz : (g : Module.End K V) ∈ commutant (x : Module.End K V),
        (⟨(g : Module.End K V), hz⟩ : commutant (x : Module.End K V)) ∈
          Subalgebra.center K (commutant (x : Module.End K V)) := Iff.rfl

variable {B : V →ₛₗ[σ] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

omit [FiniteDimensional K V] in
theorem centerUnitary_le_unitaryCentralizer : centerUnitary B x ≤ unitaryCentralizer B x := by
  rintro g ⟨hg, hz, -⟩
  exact mem_unitaryCentralizer.mpr ⟨hg, (mem_commutant _).mp hz⟩

omit [FiniteDimensional K V] in
theorem commute_of_mem_centerUnitary {g m : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ centerUnitary B x) (hm : m ∈ unitaryCentralizer B x) : Commute g m := by
  obtain ⟨-, hz, hc⟩ := hg
  have hmc : (m : Module.End K V) ∈ commutant (x : Module.End K V) :=
    (mem_commutant _).mpr (mem_unitaryCentralizer.mp hm).2
  have h1 := Subalgebra.mem_center_iff.mp hc ⟨(m : Module.End K V), hmc⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact (congrArg Subtype.val h1).symm

omit [FiniteDimensional K V] in
theorem smul_mem_centerUnitary {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ sesqUnitaryGroup B)
    (c : K) (hc : ∀ v, (g : Module.End K V) v = c • v) : g ∈ centerUnitary B x := by
  have hg' : (g : Module.End K V) = algebraMap K (Module.End K V) c :=
    LinearMap.ext fun v => by simp [hc v, Module.algebraMap_end_apply]
  refine ⟨hg, ?_, ?_⟩
  · rw [hg']
    exact Subalgebra.algebraMap_mem _ c
  · refine Subalgebra.mem_center_iff.mpr fun r => ?_
    apply Subtype.ext
    change (r : Module.End K V) * (g : Module.End K V) = (g : Module.End K V) * (r : Module.End K V)
    rw [hg']
    exact (Algebra.commutes c _).symm

end CenterUnitary

end CFSG.RankThree.PartOne.KCUnitary

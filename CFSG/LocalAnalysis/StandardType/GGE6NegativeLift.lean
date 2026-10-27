module

public import CFSG.LocalAnalysis.StandardType.GGLieM6cDescent
public import CFSG.LocalAnalysis.StandardType.GGReflCentralLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeTorality
public import CFSG.LieType.Steinberg.Isogeny.E6Algebraic
public import CFSG.LieType.Steinberg.Minuscule.E6BCBlocks
public import CFSG.RankThree.PartOne.KF.ClsLiftS3
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyCenter
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.PairAuxSc
public import CFSG.RankThree.PartOne.KE.D4LayerAlgebraic
public import CFSG.LieType.AlgebraicGroups.ClosedIdentityComponentFunctorial
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.OrderOfElement
public import CFSG.LocalAnalysis.StandardType.GGReflectionBasic
public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofSL3BT

public noncomputable section

namespace CFSG.StandardType

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem GGIsReflection.commute_e6Sc_lifts_of_negative_of_mem_range
    (k : Type) [Field k] [Finite k] {Ω : Type} [Field Ω] (ι : k →+* Ω)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {E : Subgroup (ModGL .E6 Ω)} [Finite E] (hE : IsElemAbelian p E)
    (hEπ : E ≤ (e6ScToBar k ι).range) (φ : MulAut E) (hφ : GGIsReflection p φ)
    {g : ModGL .E6 Ω} (hgπ : g ∈ (e6ScToBar k ι).range)
    (hact : ∀ x : E, g * (x : ModGL .E6 Ω) * g⁻¹ = φ x)
    {e : E} (he : φ e = e⁻¹)
    {u v : e6Data_valid.minGroup k} (hu : e6ScToBar k ι u = (e : ModGL .E6 Ω))
    (hv : e6ScToBar k ι v ∈ E) : u * v = v * u := by
  let Φ := e6ScToBar k ι
  let π := Φ.rangeRestrict
  let D := e6ScToBar_centralThree k ι
  have hker : π.ker ≤ Subgroup.center (e6Data_valid.minGroup k) := by
    intro z hz
    have hz' : Φ z = 1 := congrArg Subtype.val (show π z = 1 from hz)
    exact Subgroup.mem_center_iff.mpr (D.central z hz')
  let η : E →* Φ.range := E.subtype.codRestrict Φ.range fun x => hEπ x.property
  let g' : Φ.range := ⟨g, hgπ⟩
  have hact' (x : E) : g' * η x * g'⁻¹ = η (φ x) := Subtype.ext (hact x)
  have hu' : π u = η e := Subtype.ext hu
  have hv' : ∃ y : E, π v = η y := ⟨⟨Φ v, hv⟩, Subtype.ext rfl⟩
  exact GGIsReflection.commute_lifts_of_equivariant_negative π
    Φ.rangeRestrict_surjective hker hp2 hE η φ hφ g' hact' he hu' hv'

theorem exists_finite_e6Sc_lift_centralizing_of_negative_reflection
    {Ω : Type} [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω]
    (k₀ : Type) [Field k₀] [Finite k₀] (ι₀ : k₀ →+* Ω)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {E : Subgroup (ModGL .E6 Ω)} [Finite E] (hEG : E ≤ adjointGroup .E6 Ω)
    (hE : IsElemAbelian p E) (φ : MulAut E) (hφ : GGIsReflection p φ)
    {g : ModGL .E6 Ω} (hg : g ∈ adjointGroup .E6 Ω)
    (hact : ∀ x : E, g * (x : ModGL .E6 Ω) * g⁻¹ = φ x)
    {e : E} (he : φ e = e⁻¹) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (κ : k₀ →+* k) (ι : k →+* Ω),
      ι.comp κ = ι₀ ∧ E ≤ (e6ScToBar k ι).range ∧ g ∈ (e6ScToBar k ι).range ∧
        ∀ u v : e6Data_valid.minGroup k,
          e6ScToBar k ι u = (e : ModGL .E6 Ω) →
          e6ScToBar k ι v ∈ E → u * v = v * u := by
  classical
  let : Fintype E := Fintype.ofFinite E
  let S := insert g (Finset.univ.image fun x : E => (x : ModGL .E6 Ω))
  have hS : (S : Set (ModGL .E6 Ω)) ⊆ adjointGroup .E6 Ω := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hg
    · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
      exact hEG y.property
  obtain ⟨k, hk, hkfin, κ, ι, hικ, hdesc⟩ :=
    LieCore.M6c.exists_finite_subfield_lift_adjoint S hS k₀ ι₀
  let : Field k := hk
  let : Finite k := hkfin
  let β : adjointGroup .E6 k →* ModGL .E6 Ω :=
    (baseChangeGL ι).comp (adjointGroup .E6 k).subtype
  have hEdesc (x : E) : ∃ y : adjointGroup .E6 k, β y = x := by
    obtain ⟨y, hy, hyeq⟩ := hdesc x (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩))
    exact ⟨⟨y, hy⟩, hyeq⟩
  obtain ⟨gk, hgk, hgkeq⟩ := hdesc g (Finset.mem_insert_self _ _)
  let g' : adjointGroup .E6 k := ⟨gk, hgk⟩
  have hg' : β g' = g := hgkeq
  let π := e6Isogeny k
  have hπ : Function.Surjective π := e6Isogeny_surjective k
  have hΦ (x : e6Data_valid.minGroup k) : e6ScToBar k ι x = β (π x) := rfl
  have hEΦ : E ≤ (e6ScToBar k ι).range := by
    intro x hx
    obtain ⟨y, hy⟩ := hEdesc ⟨x, hx⟩
    obtain ⟨u, hu⟩ := hπ y
    exact ⟨u, by rw [hΦ, hu, hy]⟩
  have hgΦ : g ∈ (e6ScToBar k ι).range := by
    obtain ⟨u, hu⟩ := hπ g'
    exact ⟨u, by rw [hΦ, hu, hg']⟩
  exact ⟨k, hk, hkfin, κ, ι, hικ, hEΦ, hgΦ, fun u v hu hv =>
    GGIsReflection.commute_e6Sc_lifts_of_negative_of_mem_range
      k ι hp2 hE hEΦ φ hφ hgΦ hact he hu hv⟩

end CFSG.StandardType

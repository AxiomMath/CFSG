module

public import CFSG.LocalAnalysis.StandardType.GGE0ModelFrameOn
public import CFSG.LocalAnalysis.StandardType.GGE0ExcNoSuzukiReeAt
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PExcNormCore
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag
public import CFSG.Assembly.OpenBridges
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU2Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6CompAct
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ggE0_twE6_mem_inn_of_pow
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {p : ℕ} (hp : p.Prime)
    (hsh : ¬ (p = 3 ∧ 3 ∣ 2 ^ f + 1)) {β : MulAut ↥(twistedE6RootGroup K σ)}
    (hβI : β ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ) (hβp : β ^ p = 1) :
    β ∈ twistedE6Inn K σ := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨-, -, -, -, -, hcube, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form
      (p := 2) Nat.prime_two hf K hK σ hσ
  have hpg : ¬ p ∣ Nat.gcd 3 (2 ^ f + 1) := by
    intro hd
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
      (hd.trans (Nat.gcd_dvd_left 3 (2 ^ f + 1)))
    have h3d : 3 ∣ 2 ^ f + 1 := by
      rw [← hp3]
      exact hd.trans (Nat.gcd_dvd_right 3 (2 ^ f + 1))
    exact hsh ⟨hp3, h3d⟩
  exact CFSG.HardMathSupport.Lang.Coordinator.mem_inner_of_mem_inn_sup_diag
    (ℓ := 2) hp hK hσ hpg hcube hβp hβI


private theorem fixSubgroup_conj_eq_centralizer {R : Type} [Group R] (x : R) :
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x) =
      Subgroup.centralizer ({x} : Set R) := by
  ext g
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, MulAut.conj_apply,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  · intro h
    rw [← h]
    group

theorem ggE0_twE6_normalizes
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsh : ¬ (p = 3 ∧ 3 ∣ 2 ^ f + 1)) {s : ↥(twistedE6RootGroup K σ)} (hs1 : s ≠ 1)
    (hsp : s ^ p = 1)
    {X : Subgroup ↥(twistedE6RootGroup K σ)} (hX : IsComponentOf X (Subgroup.centralizer {s})) :
    Subgroup.centralizer {s} ≤ Subgroup.normalizer (X : Set ↥(twistedE6RootGroup K σ)) := by
  classical
  let C := ↥(twistedE6RootGroup K σ)
  let β : MulAut C := MulAut.conj s
  obtain ⟨-, -, -, -, -, -, -, -, ⟨-, -, -, -, -, -, -⟩, -, -, hZ, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form
      (p := 2) Nat.prime_two hf K hK σ hσ
  have hβp : β ^ p = 1 := by
    have h1 : (MulAut.conj : C →* MulAut C) (s ^ p) = (MulAut.conj s) ^ p := map_pow _ s p
    rw [hsp, map_one] at h1
    simpa [β] using h1.symm
  have hβ1 : β ≠ 1 := by
    intro h
    apply hs1
    have hz : s ∈ Subgroup.center C := by
      rw [Subgroup.mem_center_iff]
      intro c
      have hc : s * c * s⁻¹ = c := by
        have h' := congrArg (fun f : MulAut C => f c) h
        simpa [β, MulAut.conj_apply] using h'
      calc c * s = (s * c * s⁻¹) * s := by rw [hc]
        _ = s * c := by group
    have hbot : Subgroup.center C = ⊥ := hZ
    rw [hbot] at hz
    exact Subgroup.mem_bot.mp hz
  have hβmem : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived C :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived C
      (show β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner C from ⟨s, rfl⟩)
  have hCN : CFSG.LocalAnalysis.GLTheoremA.S267.Gen.CompNormal β := by
    by_cases hp3 : p = 3
    · subst hp3
      have h3f : ¬ 3 ∣ 2 ^ f + 1 := fun h => hsh ⟨rfl, h⟩
      let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf⟩
      exact CFSG.LocalAnalysis.GLTheoremA.F151.compNormal_twE6_charTwo_three
        (q := q) rfl σ hK hσ h3f s hs1 hsp
    · exact CFSG.LocalAnalysis.GLTheoremA.S267.Gen.compNormal_twistedE6
        (ℓ := 2) Nat.prime_two hf hK σ hσ hp hp2 hp3 hp2 β hβmem hβp hβ1
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β =
      Subgroup.centralizer ({s} : Set C) := fixSubgroup_conj_eq_centralizer s
  have hX' : CFSG.Open.IsComponentOf X
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) := by
    rw [hfix]
    exact CFSG.Assembly.isComponentOf_iff_open.mp hX
  have hmain : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β ≤
      Subgroup.normalizer (X : Set C) := hCN X hX'
  rw [hfix] at hmain
  exact hmain


end CFSG.StandardType

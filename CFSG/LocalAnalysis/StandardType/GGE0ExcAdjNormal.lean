module

public import CFSG.LocalAnalysis.StandardType.GGE0Frame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenInner
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcRed
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
public import Certificates.Certificate13604
public import Certificates.Certificate13605
public import Certificates.Certificate13691
public import Certificates.Certificate13723
public import Certificates.Certificate13724
public import Certificates.Certificate17002
public import Certificates.Certificate17951

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator

private theorem fixSubgroup_conj_eq_centralizer {R : Type} [Group R] (x : R) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set R) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  · intro h
    rw [← h]
    group

theorem ggE0_adjoint_normalizes {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {s : ↥(adjointGroup τ K)} (hs1 : s ≠ 1) (hsp : s ^ p = 1)
    {X : Subgroup ↥(adjointGroup τ K)} (hX : IsComponentOf X (Subgroup.centralizer {s})) :
    Subgroup.centralizer {s} ≤ Subgroup.normalizer (X : Set ↥(adjointGroup τ K)) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hqK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hqK]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  let C := ↥(adjointGroup τ K)
  let β : MulAut C := MulAut.conj s
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h <;> simp [h]
  have hG2 : τ = .G2 → 3 ≤ Nat.card K := by
    intro h
    rw [h] at hτ
    rcases hτ with h' | h' | h' <;> exact absurd h' (by decide)
  have hE6 : τ = .E6 → p ≠ 3 := by
    intro h
    rw [h] at hτ
    rcases hτ with h' | h' | h' <;> exact absurd h' (by decide)
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
    have hbot : Subgroup.center C = ⊥ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    rw [hbot] at hz
    exact Subgroup.mem_bot.mp hz
  have hβmem : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived C :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived C
      (show β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner C from ⟨s, rfl⟩)
  have hCN : CFSG.LocalAnalysis.GLTheoremA.S267.Gen.CompNormal β :=
    CFSG.LocalAnalysis.GLTheoremA.S267.Gen.compNormal_adjointGroup hτ' hG2 hp hp2 hpK hE6
      β hβmem hβp hβ1
  have hfix : fixSubgroup β = Subgroup.centralizer ({s} : Set C) :=
    fixSubgroup_conj_eq_centralizer s
  have hX' : CFSG.Open.IsComponentOf X (fixSubgroup β) := by
    rw [hfix]
    exact CFSG.Assembly.isComponentOf_iff_open.mp hX
  have hmain : fixSubgroup β ≤ Subgroup.normalizer (X : Set C) := hCN X hX'
  rw [hfix] at hmain
  exact hmain

end CFSG.StandardType

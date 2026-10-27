module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12A6Num
public import CFSG.Quasithin.Vol2.Ch12Sec6L12A6Transport
public import CFSG.Quasithin.Vol2.KGFact12617L52Leaf.CardPCore
public import CFSG.Quasithin.Vol2.KGFact12617L52Leaf.Five
public import CFSG.Quasithin.Vol2.KGFact12617L52Leaf.TwoElt
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Fischer.NoF25.Local
public import CFSG.LargeExtraspecial.AS35DFinal
public import CFSG.LargeExtraspecial.AS35EResid
public import CFSG.LargeExtraspecial.AS62EnumInputs
public import CFSG.LargeExtraspecial.AS62Iso2
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.GLRElimInv
public import CFSG.LargeExtraspecial.GLRTransfer
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S10Five
public import CFSG.LargeExtraspecial.S10FourA
public import CFSG.LargeExtraspecial.S10SixA
public import CFSG.LargeExtraspecial.S10Three
public import CFSG.LargeExtraspecial.S14W4LocInst
public import CFSG.LargeExtraspecial.S14W4LocRed
public import CFSG.LargeExtraspecial.S4EightA
public import CFSG.LargeExtraspecial.S4EightB
public import CFSG.LargeExtraspecial.S4EightC
public import CFSG.LargeExtraspecial.S4EightD
public import CFSG.LargeExtraspecial.S4EightE
public import CFSG.LargeExtraspecial.S5Three
public import CFSG.LargeExtraspecial.S6SevenC
public import CFSG.LargeExtraspecial.S8FusE
public import CFSG.LargeExtraspecial.S8Lin
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum
public import CFSG.Quasithin.Background.F3
public import CFSG.Quasithin.Recognition.F4Moufang
public import CFSG.Quasithin.Recognition.F4Thirtyone
public import CFSG.Quasithin.Vol2.Ch12Sec6L12R1Defs
public import CFSG.RankThree.Literature.FSmithTheorem2
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Th.KernelPlanes
public import CFSG.Sporadic.Th.Local
public import CFSG.Sporadic.ThSchreier.AutCore
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.Quasithin.H13.K1262Two

open CFSG.Open CFSG.Blueprint

section Proj

variable {K : Type} [Field K] [Finite K]

private theorem eq_one_of_ne_zero_of_card_two' (hK : Nat.card K = 2) {a : K} (ha : a ≠ 0) :
    a = 1 := by
  have := Fintype.ofFinite K
  have h := FiniteField.pow_card a
  rw [← Nat.card_eq_fintype_card, hK] at h
  have h2 : a * (a - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 ha
  · exact sub_eq_zero.mp h3

theorem statedScalars_eq_bot (hK : Nat.card K = 2) (n : ℕ) : StatedScalars (Fin n) K = ⊥ := by
  ext g
  rw [Subgroup.mem_bot]
  constructor
  · rintro ⟨u, rfl⟩
    have hu : u = 1 := Units.ext (eq_one_of_ne_zero_of_card_two' hK u.ne_zero)
    rw [hu, map_one]
  · rintro rfl
    exact (StatedScalars (Fin n) K).one_mem

noncomputable def statedProjEquivOfCardTwo (hK : Nat.card K = 2) {n : ℕ}
    (H : Subgroup (GL (Fin n) K)) : StatedProj H ≃* ↥H := by
  have hsub : (StatedScalars (Fin n) K).subgroupOf H = ⊥ := by
    rw [statedScalars_eq_bot hK, Subgroup.bot_subgroupOf]
  exact (QuotientGroup.quotientMulEquivOfEq hsub).trans QuotientGroup.quotientBot

end Proj

theorem a6LocL52_holds : A6LocL52 := by
  intro X _ _ hX Y F h
  obtain ⟨-, K, _, _, hKc, ⟨e⟩⟩ := hX
  have hK : Nat.card K = 2 := by simpa using hKc
  let ψ : X ≃* ↥(StatedSL 5 K) := e.trans (statedProjEquivOfCardTwo hK (StatedSL 5 K))
  obtain ⟨j, hY, hFj⟩ := a6Config_card h
  obtain ⟨hperf, hiso, -⟩ := h
  have hBperf := commutator_map_mulEquiv_self ψ hperf
  have hBiso := quasithinO2QuotientIso_map_mulEquiv ψ hiso
  have hBcard : Nat.card ↥(Y.map ψ.toMonoidHom) = 360 * 2 ^ j := by
    rw [Subgroup.card_map_of_injective ψ.injective, hY]
  have hfin : Finite ↥(StatedSL 5 K) := Finite.of_equiv X ψ.toEquiv
  have hpc : Nat.card ↥(pCoreOf 2 (Y.map ψ.toMonoidHom)) = 2 ^ j := by
    have h1 := card_eq_pCore_mul_of_iso hBiso
    rw [hBcard] at h1
    have h2 : Nat.card ↥(pCore 2 ↥(Y.map ψ.toMonoidHom)) = 2 ^ j := by omega
    rw [pCoreOf, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), h2]
  rcases CFSG.Quasithin.H13.KG12617L52.leafCardPCore_of
      CFSG.Quasithin.H13.KG12617L52.leafFive_holds CFSG.Quasithin.H13.KG12617L52.leafTwoElt_holds
      K hK _ hBperf hBiso with h1 | ⟨h16, -⟩
  · have : 2 ^ j = 1 := hpc ▸ h1
    have hj : 2 ^ j ≤ 16 := by omega
    exact (Nat.le_of_dvd (by positivity) hFj).trans hj
  · have : 2 ^ j = 16 := hpc ▸ h16
    exact (Nat.le_of_dvd (by positivity) hFj).trans this.le

end CFSG.Quasithin.H13.K1262Two

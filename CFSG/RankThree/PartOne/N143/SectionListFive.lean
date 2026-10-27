module

public import CFSG.RankThree.PartOne.N143.SectionListProof
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
import CFSG.Adapters.RankTwoModelTransports
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

noncomputable section

namespace CFSG.RankThree.PartOne.N143

open Matrix TauCeti CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports CFSG.ClassicalModels

theorem oddCentralCoverListFive : OddCentralCoverListFive := by
  intro Y _ _ hK hperf he hc5 n hn hmodel
  obtain ⟨hadm, K, hfield, hfinite, hK', ⟨e⟩⟩ := hmodel
  let _ := hfield
  let _ := hfinite
  have hp : (2 : ℕ).Prime := hadm.1
  have hf : 1 ≤ n := hadm.2.1
  let _ : Fact (2 : ℕ).Prime := ⟨hp⟩
  let q : PrimePower := ⟨2, n, hp, by omega⟩
  let L := GaloisField 2 (2 * n)
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card K = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK',
      GaloisField.card 2 (2 * n) (by omega), ← pow_mul, mul_comm]
  let φ : K ≃+* L := FiniteField.ringEquivOfCardEq hcard
  let e1 := statedProjCongr (glCongr (ι := Fin 5) φ) (glCongr_statedSU φ 5 (2 ^ n))
    (glCongr_statedScalars φ)
  have hv' : (LieTypeIndex.twistedA 4 q).Valid := by simp
  let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 4 q hv'
  exact Census3.TheoremThreeList.of_twistedA4_even hv' rfl ((e.trans e1).trans eT.symm)

end CFSG.RankThree.PartOne.N143

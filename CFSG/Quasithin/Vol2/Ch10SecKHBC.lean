module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CBc
public import CFSG.Quasithin.Vol2.Ch10SecKHBCa
public import CFSG.Quasithin.Vol2.Ch10SecKHBCb
public import CFSG.Quasithin.Vol2.Ch10SecKHBCc
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import Certificates.Certificate43
public import Certificates.Certificate113
public import CFSG.Foundations
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsH
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Bender1970.S3.Setup
public import CFSG.Walter.JRFacts
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate8026Base
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace C10KH

theorem sub_one_dvd_div_gcd (q : ℕ) : q - 1 ∣ (q ^ 2 - 1) / Nat.gcd 3 (q + 1) := by
  obtain ⟨r, hr⟩ := Nat.gcd_dvd_right 3 (q + 1)
  have hg : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have h : q ^ 2 - 1 = Nat.gcd 3 (q + 1) * ((q - 1) * r) := by
    rw [show q ^ 2 - 1 = (q - 1) * (q + 1) by simpa [mul_comm] using Nat.sq_sub_sq q 1]
    conv_lhs => rw [hr]
    ring
  rw [h, Nat.mul_div_cancel_left _ hg]
  exact dvd_mul_right _ _

end C10KH

theorem factBorelCartan : FactBorelCartan := by
  intro Y _ _ n hn hY S hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hY with ⟨-, hY⟩ | hY | hY
  · have hidx : ¬ 2 ∣ S.index := by
      have h : ¬ 2 ∣ (S.subgroupOf ⊤).index := hS.2.2
      rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right _] at h
    let T : Sylow 2 Y := hS.2.1.toSylow hidx
    suffices h : ∃ D : Subgroup Y, CFSG.Goldschmidt.G3a.BorelSetup T D ∧
        2 ^ n - 1 ∣ Nat.card D by
      obtain ⟨D, hD, hdvd⟩ := h
      exact C10KH.exists_mem_normalizer_orderOf_of_borelSetup hD hdvd
    rcases hY with hY | hY | hY
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hY
      let e' := e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 2 2 n (by omega) hK)
      obtain ⟨D, hD⟩ := CFSG.Goldschmidt.G3a.exists_borelSetup (Or.inl ⟨n, hn, ⟨e'⟩⟩) T
      exact ⟨D, hD, by rw [(hD.orders_psl2 hn e').2.1]⟩
    · obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := hY
      let e' : Y ≃* Sz a := e.trans ((MulEquiv.subgroupCongr
        (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
          (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hK))
      obtain ⟨D, hD⟩ :=
        CFSG.Goldschmidt.G3a.exists_borelSetup (Or.inr (Or.inr ⟨a, ha, ⟨e'⟩⟩)) T
      exact ⟨D, hD, by rw [(hD.orders_sz ha e').2.2]⟩
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hY
      have hcard : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
      let e₀ : Y ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ n)) := e
      let e' := e₀.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative n hn hcard)
      obtain ⟨D, hD⟩ :=
        CFSG.Goldschmidt.G3a.exists_borelSetup (Or.inr (Or.inl ⟨n, hn, ⟨e'⟩⟩)) T
      exact ⟨D, hD, by rw [(hD.orders_psu3 hn e').2.2]; exact C10KH.sub_one_dvd_div_gcd _⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hY
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (by omega) hK
    obtain ⟨P, hP⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_projUnitriangular
      (K := K) 2 (n := 3) (by norm_num)
    have hU₀ : IsSylowTwoOf (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projUnitriangular 3 K)
        ⊤ := hP ▸ isSylowTwoOf_top_of_sylow P
    obtain ⟨d₀, hd₀, hord⟩ := C10KH.exists_cartan_projectiveSL_three (K := K)
    obtain ⟨d, hd, hdo⟩ := C10KH.exists_mem_normalizer_orderOf_of_mulEquiv
      (e.trans (CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL 3 K)) hU₀ hd₀ hS
    exact ⟨d, hd, by rw [hdo, hord, hK]⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hY
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (by omega) hK
    obtain ⟨P, hP⟩ := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.exists_sylow_projUnipotent
      (K := K) 2 (r := 2) (by norm_num)
    have hU₀ : IsSylowTwoOf (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.projUnipotent 2 K)
        ⊤ := hP ▸ isSylowTwoOf_top_of_sylow P
    obtain ⟨d₀, hd₀, hord⟩ := C10KH.exists_cartan_projSp (K := K)
    obtain ⟨d, hd, hdo⟩ := C10KH.exists_mem_normalizer_orderOf_of_mulEquiv e hU₀ hd₀ hS
    exact ⟨d, hd, by rw [hdo, hord, hK]⟩

end CFSG.Quasithin.Vol2.Ch10.SecB

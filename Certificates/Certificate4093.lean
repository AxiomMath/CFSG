module

public import CFSG.Sporadic.Schreier.M12Data
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporM12CheckInputs
import Certificates.Kernel.LocalQT.Pairs.C4093c0
import Certificates.Kernel.LocalQT.Pairs.C4093c1
import Certificates.Kernel.LocalQT.Pairs.C4093c2
import Certificates.Data.Kernel.LocalQT.Pairs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.LocalQTPairsSound
public import CFSG.Sporadic.Schreier.ImagePairs
import CFSG.Certificates.Kernel.LocalQTLatMSound
import CFSG.Certificates.Kernel.LocalQTListLemmas
import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3LatSixCheck
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenBundle
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenCT
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Basic
import CFSG.Monster.Code.Weights
import CFSG.Quasithin.Background.A3Structure318Red
import CFSG.Quasithin.Background.A3Structure36A
import CFSG.Quasithin.Background.A3Structure36BAction
import CFSG.Quasithin.Background.A3Structure36BBase
import CFSG.Quasithin.Background.A3Structure36BCase3Base
import CFSG.Quasithin.Background.A3Structure36BCasesBase
import CFSG.Quasithin.Background.A3Structure36BCommonBase
import CFSG.Quasithin.Background.A3Structure36BFrattini
import CFSG.Quasithin.Background.A3Structure36BHeisBase
import CFSG.Quasithin.Background.A3Structure36BHomocyclic
import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
import CFSG.Quasithin.Background.A3Structure36BStarBase
import CFSG.Quasithin.Background.A3Structure36Base
import CFSG.Quasithin.Background.A3Structure38Part3
import CFSG.Quasithin.Background.B1MoreElevenE
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Quasithin.Background.C2Basic
import CFSG.Quasithin.Background.E1
import CFSG.Quasithin.Background.E1Sec4
import CFSG.Quasithin.Background.E1Sec5
import CFSG.Quasithin.Background.E1Sec8
import CFSG.Quasithin.Background.E1Solv
import CFSG.Quasithin.Background.E1Twelve
import CFSG.Quasithin.Background.E3Cent

set_option maxRecDepth 100000

public section

namespace Certificates

open CFSG.KD.LQT.C4093 CFSG.KC.LQT.Pairs CFSG.KC.LQT.L
  CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.M12Pairs
  CFSG.Sporadic.Mathieu in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.M12Pairs in
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint in
theorem certificate4093 : (S0X.length = 64 ∧ S0X.Nodup ∧ (1 : X12) ∈ S0X ∧
          (∀ x ∈ S0X, ∀ y ∈ S0X, x * y ∈ S0X) ∧ (∀ x ∈ S0X, x ^ (2 ^ 6) = 1))
    ∧ (A1X.length = 2 ∧ A2X.length = 16)
    ∧ (K1X.length = 192 ∧ K1X.Nodup ∧
          (∀ x ∈ K1X, nrmTest A1X (A1X.map enc) (A1X.take 3) x = true))
    ∧ ((enumeration m12Certificate).all (fun g =>
          decide (nrmTestP A1X (A1X.map enc) (A1X.take 3) g = true → encP g ∈ K1X.map enc)) = true)
    ∧ (K2X.length = 192 ∧ K2X.Nodup ∧
          (∀ x ∈ K2X, nrmTest A2X (A2X.map enc) (A2X.take 3) x = true))
    ∧ ((enumeration m12Certificate).all (fun g =>
          decide (nrmTestP A2X (A2X.map enc) (A2X.take 3) g = true → encP g ∈ K2X.map enc)) = true)
    ∧ (Q1X.length = 32 ∧ Q1X.Nodup ∧ (∀ q ∈ Q1X, q ∈ K1X) ∧ (1 : X12) ∈ Q1X ∧
          (∀ p ∈ Q1X, ∀ q ∈ Q1X, p * q ∈ Q1X) ∧ (∀ k ∈ K1X, ∀ q ∈ Q1X, k * q * k⁻¹ ∈ Q1X) ∧
          (∀ q ∈ Q1X, q ^ (2 ^ 5) = 1) ∧
          (∀ y ∈ K1X, (∀ q ∈ Q1X, y * q = q * y) → y ∈ Q1X) ∧
          (∀ b ∈ K1X, b ≠ 1 → b ^ 3 = 1 →
            4 < (Q1X.map fun q => q * b * q⁻¹ * b⁻¹).dedup.length) ∧
          K1X.length / Q1X.length = 6)
    ∧ (Q2X.length = 32 ∧ Q2X.Nodup ∧ (∀ q ∈ Q2X, q ∈ K2X) ∧ (1 : X12) ∈ Q2X ∧
          (∀ p ∈ Q2X, ∀ q ∈ Q2X, p * q ∈ Q2X) ∧ (∀ k ∈ K2X, ∀ q ∈ Q2X, k * q * k⁻¹ ∈ Q2X) ∧
          (∀ q ∈ Q2X, q ^ (2 ^ 5) = 1) ∧
          (∀ y ∈ K2X, (∀ q ∈ Q2X, y * q = q * y) → y ∈ Q2X) ∧
          (∀ b ∈ K2X, b ≠ 1 → b ^ 3 = 1 →
            4 < (Q2X.map fun q => q * b * q⁻¹ * b⁻¹).dedup.length) ∧
          K2X.length / Q2X.length = 6)
    ∧ ((jGens.all fun g => (K1X ++ K2X).any fun x => x.1 == g) = true ∧
          (wordA.map fun i => jGens.getD i 1).prod = m12gA ∧
          (wordB.map fun i => jGens.getD i 1).prod = m12gB) := by
  have hA : cX m12a = 184726996899603491 := by decide +kernel
  have hB : cX m12b = 365002956609719367 := by decide +kernel
  have hJ : jGens.map CFSG.KC.LQT.W.codeP = JC := by decide +kernel
  have hS : S0X.map cX = S0C := cl_codes hA hB s0Words 6
  have hK1 : K1X.map cX = K1C := by
    have e : K1X = closureList tabX enc ((s0Words ++ [tWords.getD 0 []]).map genX) 6 := by
      rw [List.map_append]; rfl
    rw [e]; exact cl_codes hA hB _ 6
  have hK2 : K2X.map cX = K2C := by
    have e : K2X = closureList tabX enc ((s0Words ++ [tWords.getD 1 []]).map genX) 6 := by
      rw [List.map_append]; rfl
    rw [e]; exact cl_codes hA hB _ 6
  have hQ1 : Q1X.map cX = Q1C := cl_codes hA hB q1Words 5
  have hQ2 : Q2X.map cX = Q2C := cl_codes hA hB q2Words 7
  have hA1 : A1X.map cX = A1C := center_codes S0X hS
  have hA2 : A2X.map cX = A2C := centD_codes S0X hS
  have hp1 : (A1X.take 3).map cX = List.take 3 A1C := by rw [List.map_take, hA1]
  have hp2 : (A2X.take 3).map cX = List.take 3 A2C := by rw [List.map_take, hA2]
  have hcl : ∀ j < 12, chainChunk 12 CFSG.KD.LQT.M12Chain.C clP j = true := Cl.all
  have hc1 : ∀ j < 12, chainChunk 12 CFSG.KD.LQT.M12Chain.C cp1 j = true := P1.all
  have hc2 : ∀ j < 12, chainChunk 12 CFSG.KD.LQT.M12Chain.C cp2 j = true := P2.all
  have hKK : (K1X ++ K2X).map cX = K1C ++ K2C := by rw [List.map_append, hK1, hK2]
  obtain ⟨l1, n1⟩ := lenNodup_sound K1X 192 hK1 kK1
  obtain ⟨l2, n2⟩ := lenNodup_sound K2X 192 hK2 kK2
  exact ⟨sub_sound S0X 6 hS kS, lens_sound A1X A2X 2 16 hA1 hA2 kA,
    ⟨l1, n1, nrm_sound A1X (A1X.take 3) K1X hA1 hp1 hK1 kN1⟩,
    compl_sound hA hB CFSG.KD.LQT.M12Chain.C CFSG.KD.LQT.M12Chain.W A1X (A1X.take 3) K1X hA1 hp1
      hK1 kC kg hcl hc1,
    ⟨l2, n2, nrm_sound A2X (A2X.take 3) K2X hA2 hp2 hK2 kN2⟩,
    compl_sound hA hB CFSG.KD.LQT.M12Chain.C CFSG.KD.LQT.M12Chain.W A2X (A2X.take 3) K2X hA2 hp2
      hK2 kC kg hcl hc2,
    norm_sound K1X Q1X 5 6 hK1 hQ1 kQ1, norm_sound K2X Q2X 5 6 hK2 hQ2 kQ2,
    ⟨memAll_sound jGens (K1X ++ K2X) hJ hKK kJ, by decide +kernel, by decide +kernel⟩⟩

end Certificates

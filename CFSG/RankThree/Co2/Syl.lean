module

public import CFSG.RankThree.Co2.Enum
public import CFSG.RankThree.Co2.CensusData
public meta import CFSG.RankThree.Co2.Enum
public meta import CFSG.RankThree.Co2.CensusData
public meta import CFSG.RankThree.Co2.Rows
public meta import CFSG.Monster.B.TwoA.Co2Inv.ConjCert
public meta import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.RankThree.Co2.SylInputs
public import CFSG.RankThree.Co2.CrMat
public import Certificates.Certificate8108
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3054
public import Certificates.Certificate16022
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3138

public noncomputable section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv

theorem tFacts_cert :
    (∀ x ∈ matGrp sylWords, x ^ 32 = 1) ∧ Nat.card (matGrp sylWords) = 2 ^ 18 ∧
      matGrp jWords ≤ matGrp sylWords :=
  Certificates.certificate8108

theorem sylWords_letters : ∀ k < sylWords.size, ∀ l ∈ sylWords[k]!, l < 42 := by
  decide +kernel

theorem card_sylT :
    Nat.card (subW sylWords) = 262144 := by
  have hc : Nat.card (matGrp sylWords) = 262144 := by rw [tFacts_cert.2.1]; norm_num
  refine le_antisymm ?_ (by rw [← hc]; exact card_matGrp_le sylWords_letters)
  rw [← hc, ← card_map_subW]
  exact Nat.card_mono (Set.toFinite _) (map_subW_le sylWords_letters)

theorem matGrp_sylWords_eq :
    matGrp sylWords = (subW sylWords).toSubmonoid.map crMat :=
  matGrp_eq_map sylWords_letters (by rw [card_sylT, tFacts_cert.2.1]; norm_num)

@[expose] def sylT :
    Sylow 2 Cr :=
  Sylow.ofCard (subW sylWords) (by rw [card_sylT, factorization_card_Cr]; norm_num)

theorem coe_sylT :
    (sylT : Subgroup Cr) = subW sylWords := rfl

theorem exists_conj_mem_sylT
    (x : Cr) (hx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ g : Cr, g * x * g⁻¹ ∈ subW sylWords := by
  have hp : IsPGroup 2 (Subgroup.zpowers x) := by
    have ho : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx) hx1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Cr Q sylT
  refine ⟨g, ?_⟩
  rw [← coe_sylT, ← hg, Sylow.coe_subgroup_smul]
  exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (Q : Subgroup Cr)
    (hQ (Subgroup.mem_zpowers x))

end CFSG.RankThree.Co2

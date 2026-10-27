module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.LocalAnalysis.SectionRank.Sporadic.HSLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.HeLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4Local
public import CFSG.LocalAnalysis.SectionRank.Sporadic.RuLocal
public import CFSG.RankThree.PartOne.CTP.StrongPLinear
public import Certificates.Certificate14954
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.PartOne.StrongP CFSG.Blueprint
open scoped commutatorElement

theorem hasNoncommPair_of_cubic {G : Type*} [Group G] {r : ℕ} (hr : r.Prime) {x y : G}
    (hx : x ^ r = 1) (hy : y ^ r = 1) (hz : ⁅x, y⁆ ≠ 1)
    (hc : Nat.card (Subgroup.closure ({x, y} : Set G)) = r ^ 3) : HasNoncommPair r G := by
  have : Fact r.Prime := ⟨hr⟩
  have hfin : Finite (Subgroup.closure ({x, y} : Set G)) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hr.ne_zero)
  refine ⟨x, y, hx, hy, fun h => hz ?_, IsPGroup.of_card hc⟩
  exact commutatorElement_eq_one_iff_mul_comm.2 h

theorem mcl_sylow5_check :
    (ops3 21).cubicCheck mclSylow5Data = true :=
  Certificates.certificate14954.1

theorem hasNoncommPair_McL :
    HasNoncommPair 5 NativeSporadic.McL := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ :=
    (spec3 21).cubic_of_check mclSylow5Data mcl_sylow5_check
  exact hasNoncommPair_of_cubic Nat.prime_five hx hy hz hc

theorem ly_sylow5_check :
    (opsP 5 111).cubicCheck lySylow5Data = true :=
  Certificates.certificate14954.2.1

theorem hasNoncommPair_Ly :
    HasNoncommPair 5 NativeSporadic.Ly := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ :=
    (specP 5 111).cubic_of_check lySylow5Data ly_sylow5_check
  exact hasNoncommPair_of_cubic Nat.prime_five hx hy hz hc

theorem on_sylow7_check :
    (ops3 154).cubicCheck onSylow7Data = true :=
  Certificates.certificate14954.2.2.1

theorem hasNoncommPair_ON :
    HasNoncommPair 7 NativeSporadic.ON := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ :=
    (spec3 154).cubic_of_check onSylow7Data on_sylow7_check
  exact hasNoncommPair_of_cubic (by norm_num) hx hy hz hc

theorem co3_sylow5_check :
    (ops2 22).cubicCheck co3Sylow5Data = true :=
  Certificates.certificate14954.2.2.2.1

theorem hasNoncommPair_Co3 :
    HasNoncommPair 5 NativeSporadic.Co3 := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ :=
    (spec2 22).cubic_of_check co3Sylow5Data co3_sylow5_check
  exact hasNoncommPair_of_cubic Nat.prime_five hx hy hz hc

theorem co2_sylow5_check :
    (ops2 22).cubicCheck co2Sylow5Data = true :=
  Certificates.certificate14954.2.2.2.2.1

theorem hasNoncommPair_Co2 :
    HasNoncommPair 5 NativeSporadic.Co2 := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ :=
    (spec2 22).cubic_of_check co2Sylow5Data co2_sylow5_check
  exact hasNoncommPair_of_cubic Nat.prime_five hx hy hz hc

theorem hn_sylow5_check :
    (opsP 5 133).cubicCheck hnSylow5Data = true :=
  Certificates.certificate14954.2.2.2.2.2.1

theorem hasNoncommPair_HN :
    HasNoncommPair 5 NativeSporadic.HN := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ :=
    (specP 5 133).cubic_of_check hnSylow5Data hn_sylow5_check
  exact hasNoncommPair_of_cubic Nat.prime_five hx hy hz hc

theorem th_sylow5_check :
    (ops2 248).cubicCheck thSylow5Data = true :=
  Certificates.certificate14954.2.2.2.2.2.2

theorem hasNoncommPair_Th :
    HasNoncommPair 5 NativeSporadic.Th := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ :=
    (spec2 248).cubic_of_check thSylow5Data th_sylow5_check
  exact hasNoncommPair_of_cubic Nat.prime_five hx hy hz hc

theorem hasNoncommPair_HS :
    HasNoncommPair 5 NativeSporadic.HS := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := HS_sylow5_cubic_witness
  exact hasNoncommPair_of_cubic Nat.prime_five hx hy hz hc

theorem hasNoncommPair_He :
    HasNoncommPair 7 NativeSporadic.He := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := He_sylow7_cubic_witness
  exact hasNoncommPair_of_cubic (by norm_num) hx hy hz hc

theorem hasNoncommPair_J4 :
    HasNoncommPair 11 NativeSporadic.J4 := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := J4_sylow11_cubic_witness
  exact hasNoncommPair_of_cubic (by norm_num) hx hy hz hc

theorem hasNoncommPair_Ru :
    HasNoncommPair 5 NativeSporadic.Ru := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := Ru_sylow5_cubic_witness
  exact hasNoncommPair_of_cubic Nat.prime_five hx hy hz hc

end CFSG.RankThree.PartOne.CTP

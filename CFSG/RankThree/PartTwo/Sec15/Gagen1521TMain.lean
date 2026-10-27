module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1521TDefs
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14
import CFSG.RankThree.PartTwo.Sec15.Gagen1521TMul
import CFSG.RankThree.PartTwo.Sec15.Gagen1521TExt
import CFSG.RankThree.PartTwo.Sec15.Gagen1521THall
import CFSG.RankThree.PartTwo.Sec15.Gagen1521TAb
import CFSG.RankThree.PartTwo.Sec15.Gagen1521TChar
import CFSG.RankThree.PartTwo.Sec15.Gagen1521KSylAut
public import CFSG.RankThree.PartTwo.Sec15.Gagen1521Defs
public import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.LocalRank
  CFSG.GH74.GLS

theorem step1521T_of (h1520 : Step1520R) (h1517 : Step1517R) (h138 : Item138N)
    (h146 : Item146S14) (h1444 : Item1444S14)
    (hst : StellmacherKP) : Step1521T := by
  intro G _ _ A c L h Y hctx p P hP X₁ hX₁ hPX₁ _
  have hp : p.Prime := hP.1
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := hP.2.1
  have hp2 : p ≠ 2 := by omega
  have hp3' : p ≠ 3 := by omega
  have hA : Late.IsE27 A := h.toSec14Std.isE27
  have h146' : Item146 A (lB A) := h146 G A c L h.toSec14Std
  have h1444' : Item1444 A (lB A) := h1444 G A c L h.toSec14Std
  have hsimp : IsSimpleGroup G := h.isSimpleGroup
  have hnab : ∃ a b : G, a * b ≠ b * a := h.nonabelian
  have hPe : CFSG.Assembly.IsElemAbelian p P := hP.2.2.2.1
  have hPcard : Nat.card P = p ^ 2 := hP.2.2.2.2.1
  have hPmem : P ∈ scriptQPi A (lB A) L (piOf p) := hP.2.2.2.2.2.1
  have hPQ : P ∈ scriptQ A (lB A) := hPmem.1.1
  have hPp : IsPGroup p P := isPGroup_of_mem_scriptQPi hp hPmem
  have hP1 : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard
    have := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  obtain ⟨X, T₀, hE₀⟩ := Proof1521T.exists_ext1521 hsimp hnab hX₁ hPX₁
  have hPR := h1520 G A c L h Y hctx p P hP X hE₀.mem_y2 hE₀.le_x
  obtain ⟨H, T, Q, hHQ, hHX, hHsolv, hHp, hPH, hT, -, hE, hQ, hPQ', hAQ⟩ :=
    Proof1521T.exists_two_p_of_ext1521 hA h146' hp3' hE₀ hPQ hPp hPR
  have hLs : IsSimpleGroup ↥L := (h1517 G A c L h Y hctx).2.1
  obtain ⟨hQab, hΩ⟩ := Proof1521T.isMulCommutative_and_mem_of_le ks1521SylAut h hLs hP
    hE.mem_y2 (hQ.1.trans hHX) hQ.2.1 hPQ' (hAQ h.mem_A)
  have hTP := Proof1521T.coe_sup_eq_mul_of_two_p hp2 hHsolv hHp hQ hQab hPQ' hPe.2 hΩ hT
  have hPTH : P ⊔ T ≤ H := sup_le hPH hT.1
  have hsolv : Group.IsSolvable ↥(P ⊔ T) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hPTH)
  have hprimes : ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥(P ⊔ T) → r = 2 ∨ r = p :=
    fun r hr hrd => hHp r hr (hrd.trans (Subgroup.card_dvd_of_le hPTH))
  have hPA : P = ⁅P, A⁆ := step1520Comm_of_item138N h1517 h138 G A c L h Y hctx p P hP
  obtain ⟨hchar, hT1⟩ := Proof1521T.isCharacteristicP_sup_of_ext1521 h h146' h1444' hp2 hp3' hE
    hPQ hPe hP1 hPA hTP hsolv hprimes
  have hTsyl : CFSG.Open.fusionIsSylowIn 2 T (P ⊔ T) :=
    ⟨le_sup_right, hT.2.1, fun S hS hS2 hTS => hT.2.2 S (hS.trans hPTH) hS2 hTS⟩
  have h3 : ¬ 3 ∣ Nat.card ↥(P ⊔ T) := fun h3 =>
    (isPiSubgroup_piCompl_iff Nat.prime_three H).mp hHQ.1.2.1
      (h3.trans (Subgroup.card_dvd_of_le hPTH))
  exact ⟨T, Proof1521T.mem_scriptQPiStar_top_of_ext1521 hst h.toTheoremFourHyp hsimp hnab hE hT1
    hTsyl h3 hchar, hTP⟩

end CFSG.RankThree.PartTwo.Sec15

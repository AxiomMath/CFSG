module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res6ProofTools
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofCent
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofM12Q
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJM12
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.Asc83Table.Automizer
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.Sporadic.Mathieu.M22
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofPoints
public import Certificates.Certificate18952
public import Certificates.Certificate8165
import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open CFSG.GH74.M12.Hyp (G12)

namespace Proof1413Res6

open Proof1413Res2 in
theorem step1421M12QR_of_c
    (h1413 : Item1413CR)
    (h135 : Item135) (h142 : Concl142S14) : Step1421M12QR := by
  intro G _ _ A c L hR hfail c' hc' L' hL' hM hcL h9 hAa hS3
  obtain ⟨φ⟩ := hM
  have hS := Proof1413.sec14Std_at hR.toSec14Std hc'.1 hL'
  have hD := hS.toSec13Data
  have hθ := theta_eq_bot_of_gammaC h1413 h135 hR hfail hc' hL' (Or.inl ⟨φ⟩)
  have ψ : ↥L' ≃* G12 := QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hθ.symm).trans φ)
  obtain ⟨χ, hχ⟩ := exists_equiv_basisA hD.le_centralizer hD.isElemAbelian hD.mem_A hAa h9 hS3 ψ
  exact m12_conclusion hD.le_centralizer hD.isElemAbelian hD.mem_A hcL hD.card_eq hAa χ hχ
    fun R hRL hAR hR2 => mem_scriptQPi_of_concl142 h142 hR.toSec14Std hc'.1 hL' hRL hAR hR2

end Proof1413Res6

theorem step1421M12R_of_c
    (h131 : Item131) (h1413 : Item1413CR) (h135 : Item135)
    (h142 : Concl142S14) : Step1421M12R :=
  step1421M12R_of h131 (Proof1413Res6.step1421M12QR_of_c h1413 h135 h142)

open Proof1413Res3 Proof1413Res6 in
theorem step1422CentR_of_c
    (h1413 : Item1413CR) (h135 : Item135) (h142 : Concl142S14)
    (hbot : Item145BotS14) (h131 : Item131) (hK : KS1422M22Cent) : Step1422CentR := by
  intro G _ _ A c₀ L₀ hR hfail c hcΓ L hL hM
  obtain ⟨φ⟩ := hM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := Proof1413.sec14Std_at hR.toSec14Std hcΓ.1 hL
  have hD := hS.toSec13Data
  have hA : IsE27 A := hS.isE27
  obtain ⟨-, h9, hAa, -⟩ := Proof1413Res2.m22_point h131 hD φ
  have h3 : 3 ∣ Nat.card L := three_dvd_card_of_card_inf h9
  have hθ := theta_eq_bot_of_gammaC h1413 h135 hR hfail hcΓ hL (Or.inr (Or.inr ⟨φ⟩))
  have ψ : ↥L ≃* ↥CFSG.Blueprint.NativeSporadic.M22 := QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hθ.symm).trans φ)
  obtain ⟨d, hdAL, hd1⟩ : ∃ d ∈ A ⊓ L, d ≠ 1 := by
    by_contra hall
    push Not at hall
    have h0 : A ⊓ L = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hall x hx)
    rw [h0, Subgroup.card_bot] at h9
    norm_num at h9
  have hdA : d ∈ A := hdAL.1
  have hdL : d ∈ L := hdAL.2
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hA.1.2 d hdA) hd1
  have hψd : orderOf (ψ ⟨d, hdL⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hd3
  obtain ⟨V, hV0, hV2, hVC, hCV⟩ := hK _ hψd
  set U := Proof1413Res2.preM ψ V with hUdef
  have hUL : U ≤ L := Proof1413Res2.preM_le ψ V
  have hU2 : IsPGroup 2 U := by
    obtain ⟨k, hk⟩ := hV2.exists_card_eq
    exact IsPGroup.of_card (n := k) (by rw [Proof1413Res2.card_preM, hk])
  have hU0 : U ≠ ⊥ := by
    intro h0
    apply hV0
    have h1 := Proof1413Res2.card_preM ψ V
    rw [← hUdef, h0, Subgroup.card_bot] at h1
    exact Subgroup.eq_bot_of_card_eq V h1.symm
  have hUd : U ≤ Subgroup.centralizer ({d} : Set G) := by
    intro u hu
    have huL := hUL hu
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp
      (hVC ((Proof1413Res2.mem_preM ψ huL).mp hu))
    rw [← map_mul, ← map_mul] at h1
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (ψ.injective h1))
  have hCdU : L ⊓ Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (U : Set G) := by
    rintro l ⟨hlL, hld⟩
    refine (Proof1413Res2.mem_normalizer_preM_iff ψ hlL).mpr (hCV ?_)
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hld
    have h2 : (⟨l, hlL⟩ : ↥L) * ⟨d, hdL⟩ = ⟨d, hdL⟩ * ⟨l, hlL⟩ := Subtype.ext h1
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, h2]
  set P := CFSG.Open.pCoreOf 2 (L ⊓ Subgroup.centralizer ({d} : Set G)) with hPdef
  have hUP : U ≤ P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_inf hUL hUd) hCdU hU2
  set K := Subgroup.centralizer ({c, d} : Set G) with hKdef
  set O := CFSG.Open.pCoreOf 2 K with hOdef
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) := fun x hx => (mem_centralizer_pair.mp hx).1
  have hKd : K ≤ Subgroup.centralizer ({d} : Set G) := fun x hx => (mem_centralizer_pair.mp hx).2
  have hLdK : L ⊓ Subgroup.centralizer ({d} : Set G) ≤ K := fun x hx =>
    mem_centralizer_pair.mpr ⟨hD.le_centralizer hx.1, hx.2⟩
  have hLN : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_mem_lA hS hcΓ.1 hL h3
  have hKN : K ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) :
      Set G) :=
    le_normalizer_inf (hKc.trans hLN) (hKd.trans Subgroup.le_normalizer)
  have hPO : P ≤ O := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hLdK)
    (hKN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hO0 : O ≠ ⊥ := by
    intro h0
    apply hU0
    rw [eq_bot_iff, ← h0]
    exact hUP.trans hPO
  have hAK : A ≤ K := fun x hx => mem_centralizer_pair.mpr
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hD.mem_A),
      Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hdA)⟩
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    (hAK.trans Subgroup.le_normalizer).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hOK : O ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hOL : O ≤ L := le_of_le_centralizer_gammaC h1413 h142 hbot hR hfail hcΓ hL h3 hAa
    (hOK.trans hKc) hAO hO2
  have hOP : O ≤ P := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (le_inf hOL (hOK.trans hKd)) (hLdK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K))
    hO2
  have hAP : A ≤ Subgroup.normalizer (P : Set G) :=
    (le_normalizer_inf hD.le_normalizer ((hAK.trans hKd).trans Subgroup.le_normalizer)).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hPmem : P ∈ scriptQPi A (lB A) L (piOf 2) :=
    Proof1413Res2.mem_scriptQPi_of_concl142 h142 hR.toSec14Std hcΓ.1 hL
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left) hAP
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  obtain ⟨R, hPR, hR'⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) L (piOf 2))) hPmem
  exact ⟨R, hR', d, hdAL, hd1, hO0, hOP.trans hPR⟩

end CFSG.RankThree.PartTwo.Sec14

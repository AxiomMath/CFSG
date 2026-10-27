module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res5ProofOdd
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofTools
import CFSG.LocalAnalysis.AGLEmbedding.CoprimeSup
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofSimple

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

namespace Proof1413Res6

variable {G : Type} [Group G] [Finite G]

open Proof1413Res3 in
theorem le_of_le_centralizerC (h142 : Concl142S14) {A L : Subgroup G} {c : G}
    (hS : Sec14Std G A c L) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) {c' : G}
    (hc' : Subgroup.zpowers c' ∈ omegaA A) {L' : Subgroup G} (hL' : L' ∈ lA A c')
    (h3 : 3 ∣ Nat.card L')
    (hodd : ¬ 2 ∣ Nat.card ↥(Subgroup.centralizer ({c'} : Set G) ⊓
      Sec4.thetaQuotCentralizer L'))
    (hX : ¬ 2 ∣ Nat.card ↥(xA A)) (hAa : A = Subgroup.zpowers c' ⊔ (A ⊓ L'))
    {Q : Subgroup G} (hQc : Q ≤ Subgroup.centralizer ({c'} : Set G))
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hQ2 : IsPGroup 2 Q) : Q ≤ L' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsE27 A := hS.isE27
  have hc'A : c' ∈ A := (zpowers_mem_omegaA_iff.mp hc').1
  have hCN : Subgroup.centralizer ({c'} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c' : Set G) :=
    centralizer_singleton_le_normalizer_zpowers c'
  have hQ𝓠 : Q ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le_normalizer h142 hS hc' (hQc.trans hCN) hAQ
      (not_three_dvd_of_isPGroup_two hQ2)
  have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1.1
  have hCQA : Q ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
    have hmem : Q ⊓ Subgroup.centralizer (A : Set G) ∈ scriptQ A (lB A) :=
      mem_scriptQ_of_le hQ𝓠 inf_le_left
        (le_normalizer_inf hAQ (hAC.trans Subgroup.le_normalizer))
    exact eq_bot_of_isPGroup_two_of_le (hQ2.to_le inf_le_left)
      (le_pPrimeCoreOf_centralizer hbot hmem inf_le_right) hX
  set N := Subgroup.centralizer ({c'} : Set G) ⊓ Sec4.thetaQuotCentralizer L' with hNdef
  set M := L' ⊔ N with hMdef
  have hLN : Subgroup.centralizer ({c'} : Set G) ≤ Subgroup.normalizer (L' : Set G) :=
    centralizer_le_normalizer_of_mem_lA hS hc' hL' h3
  have hCM : Subgroup.centralizer ({c'} : Set G) ≤ Subgroup.normalizer (M : Set G) := by
    refine le_normalizer_sup hLN ?_
    exact le_normalizer_inf Subgroup.le_normalizer
      (hLN.trans (Sec6.normalizer_le_normalizer_thetaQuotCentralizer L'))
  have hAcent : A ≤ Subgroup.centralizer ({c'} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨c', hc'A⟩))
  have hAM : A ≤ M := by
    rw [hAa]
    refine sup_le ?_ (inf_le_right.trans le_sup_left)
    refine (Subgroup.zpowers_le.mpr ?_).trans le_sup_right
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, mem_thetaQuotCentralizer_of_mem hL'.1⟩
  have hQM : Q ≤ M := by
    have hle := le_of_commutator_mem (A := A) (Q := Q) (N := Q ⊓ M) hA.isPGroup inf_le_left
      (le_normalizer_inf hAQ (hAcent.trans hCM))
      (not_three_dvd_of_isPGroup_two (hQ2.to_le inf_le_left)) (fun q hq a ha => ?_) hCQA
    · exact hle.trans inf_le_right
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h1 : a * q⁻¹ * a⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp (hAQ ha) _).mp (inv_mem hq)
        have h2 := mul_mem hq h1
        rwa [show q * (a * q⁻¹ * a⁻¹) = q * a * q⁻¹ * a⁻¹ by group] at h2
      · have h1 : q * a * q⁻¹ ∈ M :=
          (Subgroup.mem_normalizer_iff.mp (hCM (hQc hq)) _).mp (hAM ha)
        exact mul_mem h1 (inv_mem (hAM ha))
  have hNM : N ≤ M := le_sup_right
  have hLM : L' ≤ M := le_sup_left
  have hMc : M ≤ Subgroup.centralizer ({c'} : Set G) :=
    sup_le (Sec6.le_centralizer_of_mem_thetaComponentsAt hL'.1) inf_le_left
  have hnormal : (L'.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mpr (hMc.trans hLN)
  have hcop : (Nat.card N).Coprime 2 :=
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd))
  exact CFSG.AGLEmbedding.le_of_le_sup_of_coprime_card_of_le hQM hLM hNM hnormal hQ2 hcop hQM

theorem le_of_le_centralizer_gammaC (h1413 : Item1413CR) (h142 : Concl142S14)
    (hbot : Item145BotS14) {A : Subgroup G} {c₀ : G} {L₀ : Subgroup G}
    (hR : Sec15R G A c₀ L₀) (hfail : Fail1411 A (lB A)) {c' : G}
    (hc' : Subgroup.zpowers c' ∈ gammaA A (lB A)) {L' : Subgroup G} (hL' : L' ∈ lA A c')
    (h3 : 3 ∣ Nat.card L') (hAa : A = Subgroup.zpowers c' ⊔ (A ⊓ L'))
    {Q : Subgroup G} (hQc : Q ≤ Subgroup.centralizer ({c'} : Set G))
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hQ2 : IsPGroup 2 Q) : Q ≤ L' := by
  obtain ⟨hodd, hX⟩ := h1413 G A c₀ L₀ hR hfail c' hc' L' hL'
  exact le_of_le_centralizerC h142 hR.toSec14Std (hbot G A c₀ L₀ hR.toSec14Std) hc'.1 hL' h3
    hodd hX hAa hQc hAQ hQ2

theorem odd_card_thetaC (h1413 : Item1413CR) {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L) (hfail : Fail1411 A (lB A)) {c' : G}
    (hc' : Subgroup.zpowers c' ∈ gammaA A (lB A)) {L' : Subgroup G} (hL' : L' ∈ lA A c') :
    ¬ 2 ∣ Nat.card (aschbacherSolvableCore 3 ↥L') := by
  have hodd := (h1413 G A c L hR hfail c' hc' L' hL').1
  have hle : inSubgroup (aschbacherSolvableCore 3) L' ≤
      Subgroup.centralizer ({c'} : Set G) ⊓ Sec4.thetaQuotCentralizer L' :=
    le_inf ((Sec6.theta_le L').trans (Sec6.le_centralizer_of_mem_thetaComponentsAt hL'.1))
      (Sec6.theta_le_thetaQuotCentralizer L')
  intro h2
  apply hodd
  refine h2.trans ?_
  have h := Subgroup.card_dvd_of_le hle
  rwa [inSubgroup, Subgroup.card_map_of_injective L'.subtype_injective] at h

theorem theta_eq_bot_of_gammaC (h1413 : Item1413CR) (h135 : Item135) {A : Subgroup G} {c : G}
    {L : Subgroup G} (hR : Sec15R G A c L) (hfail : Fail1411 A (lB A)) {c' : G}
    (hc' : Subgroup.zpowers c' ∈ gammaA A (lB A)) {L' : Subgroup G} (hL' : L' ∈ lA A c')
    (htype : Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    aschbacherSolvableCore 3 ↥L' = ⊥ := by
  have hS := Proof1413.sec14Std_at hR.toSec14Std hc'.1 hL'
  exact Proof1413Res2.theta_eq_bot_of_odd h135 hS.toSec13Data hS.hypS_or_hypT
    (odd_card_thetaC h1413 hR hfail hc' hL') htype

end Proof1413Res6

end CFSG.RankThree.PartTwo.Sec14

module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315xFacts
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14
public import CFSG.RankThree.PartTwo.Sec16.Item165ProofTools
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec15.Gagen147Sub
import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Sylow
public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315xDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Proof155Wx

theorem stellmacherSub_subgroupOf_characteristic (R : Subgroup G) :
    ((Sec16.Proof165.stellmacherSub R).subgroupOf R).Characteristic := by
  have h : ((S4Free.stellmacherWSz.{0, 0} ↥R).map R.subtype).subgroupOf R =
      S4Free.stellmacherWSz.{0, 0} ↥R := by
    rw [← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self (f := R.subtype)
      (by rw [Subgroup.ker_subtype]; exact bot_le)
  rw [Sec16.Proof165.stellmacherSub, h]
  exact S4Free.stellmacherWSz_characteristic

private theorem mem_scriptQ_w155 {A M X : Subgroup G} (hE27 : Late.IsE27 A)
    (h146 : Item146 A (lB A)) (h1444 : Item1444 A (lB A)) (hMY : M ∈ scriptY A)
    (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hWI₀Δ : w155 A M X ≤ deltaZero A (lB A) M)
    (hWO : w155 A M X ≤ pPrimeCoreOf 3 M) :
    w155 A M X ∈ scriptQ A (lB A) :=
  Sub147.mem_scriptQ_of_isPerfect hE27 h1444 h146 hMY.2
    (le_normalizer_w155 (le_normalizer_delta M) hAX) (isPerfect_w155 A M X) hWI₀Δ hWO

theorem w155_le_normalizer_of_le_core
    (hst : StellmacherKP) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) (h146 : Item146 A (lB A))
    (h1444 : Item1444 A (lB A)) (h148 : Item148 A (lB A)) (h149 : Item149 A (lB A))
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P) (hWO : w155 A M X ≤ pPrimeCoreOf 3 M) :
    w155 A M X = delta A (lB A) (w155 A M X) ∧
      ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ CFSG.Open.pCoreOf 2 Y ∧
        (C.subgroupOf (CFSG.Open.pCoreOf 2 Y)).Characteristic ∧
        w155 A M X ≤ Subgroup.normalizer (C : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := facts155W_of h h148 h149 hC hE hRP
  have hWM : w155 A M X ≤ M :=
    hf.w_le_i0.trans ((Sec14.oPrimeResidualOf_le_self 3 _).trans (delta_le M))
  have hPM : P ≤ M := hf.le_p.trans inf_le_left
  have hW𝓠 : w155 A M X ∈ scriptQ A (lB A) :=
    mem_scriptQ_w155 h.isE27 h146 h1444 hf.mem_m2.1 hf.mem_x4.1.2
      (hf.w_le_i0.trans hf.i0_le_deltaZero) hWO
  have hWΔ : w155 A M X = delta A (lB A) (w155 A M X) :=
    le_antisymm (le_delta hW𝓠 le_rfl) (delta_le _)
  have hPW𝓠 : P ⊔ w155 A M X ∈ scriptQ A (lB A) :=
    sup_mem_scriptQ_of_item146 h.isE27 h146 hf.mem_p hW𝓠 hf.p_le_normalizer_w
  have hPW3 : ¬ 3 ∣ Nat.card ↥(P ⊔ w155 A M X) :=
    (isPiSubgroup_piCompl_iff Nat.prime_three (P ⊔ w155 A M X)).mp hPW𝓠.1.2.1
  have hPWle : P ⊔ w155 A M X ≤ M ⊓ Subgroup.normalizer (X : Set G) :=
    le_inf (sup_le hPM hWM)
      (sup_le (hf.le_p.trans inf_le_right) (hf.w_le_i0.trans hf.i0_le_normalizer_x))
  have hstar : P ∈ scriptQPiStar A (lB A) (P ⊔ w155 A M X) (piOf 2) := by
    refine ⟨⟨⟨hf.mem_p, le_sup_left⟩, hE.mem_p.prop.2⟩, fun S hS hPS => ?_⟩
    exact le_of_eq (hE.mem_p.eq_of_le ⟨⟨hS.1.1, hS.1.2.trans hPWle⟩, hS.2⟩ hPS).symm
  have hPsyl : CFSG.Open.fusionIsSylowIn 2 P (P ⊔ w155 A M X) :=
    Sec16.Proof165.fusionIsSylowIn_of_mem_scriptQPiStar h.isE27 hPW𝓠 hPW3 hstar
  set R := CFSG.Open.pCoreOf 2 Y with hRdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hPR : P ≤ Subgroup.normalizer (R : Set G) := hf.p_le_normalizer_r
  have hPWD : P ⊔ w155 A M X ≤
      Subgroup.normalizer ((R ⊔ w155 A M X : Subgroup G) : Set G) :=
    sup_le (CFSG.RankThree.PartTwo.Sec14.le_normalizer_sup hPR hf.p_le_normalizer_w)
      ((le_sup_right : w155 A M X ≤ R ⊔ w155 A M X).trans Subgroup.le_normalizer)
  have hsylD : CFSG.Open.fusionIsSylowIn 2 (P ⊓ (R ⊔ w155 A M X))
      (R ⊔ w155 A M X) :=
    CFSG.LocalAnalysis.EvenBN.Tits.N.P6.fusionIsSylowIn_inf_of_normal hPsyl
      (sup_le_sup hRP le_rfl) hPWD
  have hinfR : P ⊓ (R ⊔ w155 A M X) = R := hf.inf_sup_eq
  have hsylR : CFSG.Open.fusionIsSylowIn 2 R (R ⊔ w155 A M X) := by
    have h' := hsylD
    rw [hinfR] at h'
    exact h'
  have hWchar : IsCharacteristicP 2 ↥(w155 A M X) :=
    (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥(w155 A M X) 2).mpr hf.fit_w
  have hRWchar : IsCharacteristicP 2 ↥(R ⊔ w155 A M X) := by
    rw [sup_comm]
    exact Sec16.Proof165.isCharacteristicP_sup (D := w155 A M X) (T := R)
      (hRP.trans hf.p_le_normalizer_w) hR2 hWchar
  have hRW3 : ¬ 3 ∣ Nat.card ↥(R ⊔ w155 A M X) := fun hdvd =>
    hPW3 (hdvd.trans (Subgroup.card_dvd_of_le (sup_le_sup hRP le_rfl)))
  obtain ⟨hCR, hCne, -, hCU⟩ :=
    Sec16.Proof165.stellmacherSub_spec hst h.toTheoremFourHyp hR2
      (by rw [hRdef]; exact hC.isY.1.1.2)
  have hWD : w155 A M X ≤
      Subgroup.normalizer (Sec16.Proof165.stellmacherSub R : Set G) :=
    le_sup_right.trans (hCU (R ⊔ w155 A M X) le_sup_left hRW3 hsylR hRWchar)
  exact ⟨hWΔ, Sec16.Proof165.stellmacherSub R, hCne, hCR,
    stellmacherSub_subgroupOf_characteristic R, hWD⟩

end Proof155Wx

open Proof155Wx

theorem step155W315x_of_P
    (hst : StellmacherKP) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h146 : Item146 A (lB A)) (h1444 : Item1444 A (lB A))
    (h148 : Item148 A (lB A)) (h149 : Item149 A (lB A)) (hP : Step155W315P A c L) :
    Step155W315x A c L := by
  intro h X K Y M T P hC hmax hab hE hRP _
  by_cases hWO : w155 A M X ≤ pPrimeCoreOf 3 M
  · obtain ⟨hWΔ, hCex⟩ :=
      w155_le_normalizer_of_le_core hst h h146 h1444 h148 h149 hC hE hRP hWO
    exact ⟨hWΔ, Or.inr (Or.inr hCex)⟩
  · exact hP h X K Y M T P hC hmax hab hE hRP hWO

theorem step155W315xR_of_P
    (hst : StellmacherKP) (h146 : Item146S14)
    (h1444 : Item1444S14) (h148 : Item148R) (h149 : Sec16.Item149S14) (hP : Step155W315PR) :
    Step155W315xR :=
  fun G _ _ A c L hR => step155W315x_of_P hst (h146 G A c L hR.toSec14Std)
    (h1444 G A c L hR.toSec14Std) (h148 G A c L hR) (h149 G A c L hR.toSec14Std) (hP G A c L hR)

end CFSG.RankThree.PartTwo.Sec15

module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148CLayer
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagGriess
public import CFSG.RankThree.PartTwo.Sec4.Item45Closed
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Census
public import CFSG.RankThree.PartTwo.Sec4.Item423StepsProof432Use
import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgForward

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.Ronan148C
open CFSG.GH74.GLS (pPrimeCoreOf)


section Certs


variable {H : Type} [Group H] [Finite H]

theorem map_le_normalizer_component
    (hH : SectionFourHyp H) {A : Subgroup H} (hA : Late.IsE27 A)
    {J : Subgroup (H ⧸ CFSG.pPrimeCore 3 H)} (hJ : IsComponent J) :
    A.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)) ≤
      Subgroup.normalizer (J : Set (H ⧸ CFSG.pPrimeCore 3 H)) := by
  obtain ⟨L, hL, rfl⟩ := Sec4.exists_mem_thetaComponents_map_eq KFacts.kpSz hH.kGroup
    (Sec4.localRank_theta_quotient_le hH) hJ
  have hAL : A ≤ Subgroup.normalizer (L : Set H) :=
    Sec4.rank3II_4_5 H hH A hA.isPGroup (Or.inr ⟨hA.1, 3, le_rfl, by rw [hA.2]; norm_num⟩) L hL
  exact (Subgroup.map_mono hAL).trans (Subgroup.le_normalizer_map _)

theorem rowS148_component
    (R : K148RowsS) (hH : SectionFourHyp H)
    {J : Subgroup (H ⧸ CFSG.pPrimeCore 3 H)} (hJ : IsComponent J) :
    RowS148 (J ⧸ Subgroup.center J) := by
  have hJS := Sec4.Item432Proof.sectionFourHyp_component_quot_pPrimeCore
    Sec4.diag_item41LargePrime_holds hH hJ
  exact R.rowS_of_list42 hJ.1.2.1 hJ.1.2.2 (Sec4.RonanK432.list42_quotient_center hJ.1 hJS)

theorem layer_le_centralizer_of_sectionFourHyp
    (R : K148RowsS) (hH : SectionFourHyp H)
    (N : Subgroup H) [N.Normal] (hN : N = CFSG.pPrimeCore 3 H) {A B : Subgroup H}
    (hA : Late.IsE27 A) (hBA : B ≤ A) (hB : Nat.card B = 9) {Q : Subgroup (H ⧸ N)}
    (hAQ : A.map (QuotientGroup.mk' N) ≤ Subgroup.normalizer (Q : Set (H ⧸ N)))
    (hQA : Q = ⁅Q, A.map (QuotientGroup.mk' N)⁆)
    (hQB : ∀ b ∈ B, b ≠ 1 →
      Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({QuotientGroup.mk' N b} : Set (H ⧸ N))))
    (hQO : CFSG.pCore 3 (H ⧸ N) ≤ Subgroup.centralizer (Q : Set (H ⧸ N))) :
    CFSG.layer (H ⧸ N) ≤ Subgroup.centralizer (Q : Set (H ⧸ N)) := by
  subst hN
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 H) with hπ
  have hinj : ∀ {W : Subgroup H}, W ≤ A → Function.Injective (π.comp W.subtype) := by
    intro W hWA
    rw [injective_iff_map_eq_one]
    intro w hw
    have hwN : (w : H) ∈ CFSG.pPrimeCore 3 H := (QuotientGroup.eq_one_iff _).mp hw
    have hdisj : A ⊓ CFSG.pPrimeCore 3 H = ⊥ := by
      refine Subgroup.inf_eq_bot_of_coprime ?_
      rw [hA.2, show (27 : ℕ) = 3 ^ 3 by norm_num]
      exact Nat.Coprime.pow_left _ CFSG.pPrimeCore_coprime_card
    have : (w : H) ∈ A ⊓ CFSG.pPrimeCore 3 H := ⟨hWA w.2, hwN⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hcard : ∀ {W : Subgroup H}, W ≤ A → Nat.card (W.map π) = Nat.card W := fun hWA =>
    (Nat.card_congr (Sec4.RonanK429.equivMapOfInjOn π _ (hinj hWA)).toEquiv).symm
  have hAbar : Late.IsE27 (A.map π) :=
    ⟨CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 π A hA.1,
      by rw [hcard le_rfl, hA.2]⟩
  refine layer_le_centralizer_of_rows (CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three) hAbar
    (Subgroup.map_mono hBA) (by rw [hcard hBA, hB]) hAQ hQA ?_ hQO
    (fun J hJ => map_le_normalizer_component hH hA hJ) (fun J hJ => rowS148_component R hH hJ)
  rintro _ ⟨b, hb, rfl⟩ hb1
  have hb1' : b ≠ 1 := fun h => hb1 (by rw [h, map_one])
  exact hQB b hb hb1'

end Certs

end CFSG.RankThree.PartTwo.Sec14.Ronan148C

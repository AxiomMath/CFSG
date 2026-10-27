module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res6ProofTools
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofPoints

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

structure Pt (A : Subgroup G) (c : G) (L : Subgroup G) : Prop where
  std : Sec14Std G A c L
  four : TheoremFourHyp G
  theta : aschbacherSolvableCore 3 ↥L = ⊥
  m22 : Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.M22)
  not_mem : c ∉ L
  card_B : Nat.card (A ⊓ L : Subgroup G) = 9
  eq_sup : A = Subgroup.zpowers c ⊔ (A ⊓ L)
  cent_le : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G)
  two_le : ∀ Q : Subgroup G, Q ≤ Subgroup.centralizer ({c} : Set G) →
    A ≤ Subgroup.normalizer (Q : Set G) → IsPGroup 2 Q → Q ≤ L
  x_odd : ¬ 2 ∣ Nat.card (xA A)
  wb : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G)
  transv : ∀ d ∈ A ⊓ L, ∃ w ∈ Subgroup.normalizer (A : Set G),
    w * d = d * w ∧ w * c * w⁻¹ = c * d
  omega : omegaA A = orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c)
  iq : ∀ U : Subgroup G, IsPGroup 2 U → A ≤ Subgroup.normalizer (U : Set G) →
    U ∈ scriptQ A (lB A)

theorem pt_of
    (h1413 : Item1413CR) (h135 : Item135) (h142 : Concl142S14)
    (hbot : Item145BotS14) (h131 : Item131) {A : Subgroup G} {c₀ : G} {L₀ : Subgroup G}
    (hR : Sec15R G A c₀ L₀) (hfail : Fail1411 A (lB A)) {c : G}
    (hcΓ : Subgroup.zpowers c ∈ gammaA A (lB A)) {L : Subgroup G} (hL : L ∈ lA A c)
    (hM : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22))
    (hWB : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G))
    (hTr : ∀ d ∈ A ⊓ L, ∃ w ∈ Subgroup.normalizer (A : Set G),
      w * d = d * w ∧ w * c * w⁻¹ = c * d)
    (hΩ : omegaA A = orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c))
    (hIQ : ∀ U : Subgroup G, IsPGroup 2 U → A ≤ Subgroup.normalizer (U : Set G) →
      U ∈ scriptQ A (lB A)) :
    Pt A c L := by
  obtain ⟨φ⟩ := hM
  have hS := Proof1413.sec14Std_at hR.toSec14Std hcΓ.1 hL
  obtain ⟨hcL, h9, hAa, -⟩ := Proof1413Res2.m22_point h131 hS.toSec13Data φ
  have h3 := Proof1413Res3.three_dvd_card_of_card_inf h9
  have hθ := Proof1413Res6.theta_eq_bot_of_gammaC h1413 h135 hR hfail hcΓ hL
    (Or.inr (Or.inr ⟨φ⟩))
  refine ⟨hS, hR.toTheoremFourHyp, hθ, ⟨QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hθ.symm).trans φ)⟩, hcL, h9, hAa,
    Proof1413Res3.centralizer_le_normalizer_of_mem_lA hS hcΓ.1 hL h3,
    fun Q hQ hAQ hQ2 => Proof1413Res6.le_of_le_centralizer_gammaC h1413 h142 hbot hR hfail hcΓ
      hL h3 hAa hQ hAQ hQ2,
    (h1413 G A c₀ L₀ hR hfail c hcΓ L hL).2, hWB, hTr, hΩ, hIQ⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S

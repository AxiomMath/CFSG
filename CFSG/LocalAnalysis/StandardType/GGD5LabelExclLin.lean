module

public import CFSG.LocalAnalysis.StandardType.GGD5LabelGlue
import CFSG.LocalAnalysis.StandardType.GGTwAutHolds
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeVac
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSmall
import CFSG.LocalAnalysis.StandardType.GGCSRLabels
import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
public import Certificates.Certificate8032
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsOrder

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

private theorem lup10eA_not_of_cardLt {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ lab, LargeEvenInLambda2 lab → S 3 lab →
      LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
        (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 3)
    (hsp : ∀ lab, S 3 lab → LargeEvenSplit 3 lab)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) : ¬ GGInnerDiagOnLabel S 3 Bs L := fun hq =>
  ggThmIHyp_false_of_labelAll (S := fun p lab => p = 3 ∧ S 3 lab)
    (fun _ lab _ hlab hs _ => by
      obtain ⟨rfl, hs⟩ := hs
      exact hS lab hlab hs) hC.1
    (largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨⟨rfl, hP.1⟩, hsp lab hP.1,
      hC.2.1.1.trans hP.2.1, fun b hb => hP.2.2 b (hC.2.1.1 hb)⟩) hq)

private theorem lup10eA_labelAll_autCard {l r ε : ℕ} (hr : 3 ≤ r) (hε : ε ≤ 1)
    (hl : l = 2 * r - 1 + ε) :
    LargeEvenLabelAll ⟨.A, l, 1⟩ fun R _ I _ => GGTorusAutCardSC 3 R I r (2 ^ r * r.factorial) := by
  subst hl
  exact ggTwSL_label (f := 1) hr (by norm_num) ε hε

private theorem lup10eA_labelAll_subsetInn {l : ℕ} :
    LargeEvenLabelAll ⟨.A, l, 1⟩
      (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R) := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact recipeLinear_subsetInn (d := l + 1) (N := 2) (Nat.coprime_one_left (l + 1)) hQ

private theorem lup10eA_torusAutCard_rank_false {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hxL : x ∉ L) {y : G} {H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (hbas : M.toLin.Basis) {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    {r N : ℕ} (hSC : GGTorusAutCardSC 3 R I r N) (hr : 5 ≤ r) : False := by
  have hrle := (lup10c_torusAutCard hS hxL M e hbas θ hBsN hBs3 hSC).1
  omega

private theorem lup10eA_autCard_false {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hxL : x ∉ L) {y : G} {H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.a = e 0)
    (hbas : M.toLin.Basis) {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    {r N : ℕ} (hSC : GGTorusAutCardSC 3 R I r N) (hIinn : I ⊆ LargeEvenInnSet R)
    (hN : N ≠ 192) : False := by
  have hcardN := (lup10c_torusAutCard hS hxL M e hbas θ hBsN hBs3 hSC).2 hIinn
  have h192 := lup10c_card_automizer M e hecart he0 hbas
  rw [h192] at hcardN
  exact hN hcardN.symm

theorem lup10e_not_lin
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hxL : x ∉ L) {y : G}
    {H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.a = e 0)
    (hbas : M.toLin.Basis) :
    ¬ GGInnerDiagOnLabel (fun _ lab =>
        (lab.tag = .A ∨ (lab.tag = .twD ∧ lab.rank = 2) ∨ lab.tag = .triD4 ∨
          lab.tag = .G2 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .B2der ∨
          lab.tag = .G2der ∨ lab.tag = .twF4der) ∧ lab.n = 1) 3 Bs L := by
  intro h
  obtain ⟨hL, lab, hlab, hraw⟩ := h
  obtain ⟨_, _, _, _, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, _, hP⟩ := hQ
  obtain ⟨⟨hdisj, hn1⟩, _, _⟩ := hP
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hdisj hn1
  subst hn1
  have relabel : ∀ (T : ℕ → LargeEvenLabel → Prop), T 3 ⟨t, l, 1⟩ →
      GGInnerDiagOnLabel T 3 Bs L := by
    intro T hT
    exact ⟨hL, ⟨t, l, 1⟩, hlab, largeEvenRawDatum_mono (fun R _ I F hQ' => by
      obtain ⟨hs', hna', θ', hP'⟩ := hQ'
      exact ⟨hs', hna', θ', ⟨hT, hP'.2⟩⟩) hraw⟩
  rcases hdisj with hA | htwD | htri | hG2 | htwB2 | htwF4 | hB2der | hG2der | htwF4der
  ·
    subst hA
    have hl1 : 1 ≤ l := hlab.2.1
    rcases (show l ≤ 4 ∨ 5 ≤ l by omega) with hl4 | hl5
    ·
      have hq : GGInnerDiagOnLabel (fun _ lab => (lab.tag = .A ∧ lab.rank ≤ 4) ∧ lab.n = 1)
          3 Bs L := relabel _ ⟨⟨rfl, hl4⟩, rfl⟩
      exact (lup10eA_not_of_cardLt
        (S := fun _ lab => (lab.tag = .A ∧ lab.rank ≤ 4) ∧ lab.n = 1)
        (fun lab hlab' hs => StdSubRestThree.largeEvenLabelAll_card_lt_twoThreeSmall
          ⟨rfl, hs.2, Or.inl ⟨hs.1.1, hs.1.2⟩⟩)
        (fun lab hs => Or.inr (Or.inr (Or.inr ⟨hs.2, rfl⟩))) hS.1.1 hq).elim
    · rcases (show l ≤ 8 ∨ 9 ≤ l by omega) with hl8 | hl9
      ·
        rcases (show l = 5 ∨ l = 6 ∨ l = 7 ∨ l = 8 by omega) with rfl | rfl | rfl | rfl
        · have hraw2 := (largeEvenLabelAll_and
            (lup10eA_labelAll_autCard (l := 5) (r := 3) (ε := 0)
              (by omega) (by omega) (by norm_num))
            (lup10eA_labelAll_subsetInn (l := 5))) _ hraw
          obtain ⟨R', _, I', F', hQ'⟩ := largeEvenRawDatum_exists hraw2
          obtain ⟨hQ0, hSC, hguard⟩ := hQ'
          obtain ⟨hs', hna', θ', hP'⟩ := hQ0
          obtain ⟨_, hBsN', hBs3'⟩ := hP'
          exact lup10eA_autCard_false hS hxL M e hecart he0 hbas θ' hBsN' hBs3' hSC
            (hguard hs' hna') (by decide)
        · have hraw2 := (largeEvenLabelAll_and
            (lup10eA_labelAll_autCard (l := 6) (r := 3) (ε := 1)
              (by omega) (by omega) (by norm_num))
            (lup10eA_labelAll_subsetInn (l := 6))) _ hraw
          obtain ⟨R', _, I', F', hQ'⟩ := largeEvenRawDatum_exists hraw2
          obtain ⟨hQ0, hSC, hguard⟩ := hQ'
          obtain ⟨hs', hna', θ', hP'⟩ := hQ0
          obtain ⟨_, hBsN', hBs3'⟩ := hP'
          exact lup10eA_autCard_false hS hxL M e hecart he0 hbas θ' hBsN' hBs3' hSC
            (hguard hs' hna') (by decide)
        · have hraw2 := (largeEvenLabelAll_and
            (lup10eA_labelAll_autCard (l := 7) (r := 4) (ε := 0)
              (by omega) (by omega) (by norm_num))
            (lup10eA_labelAll_subsetInn (l := 7))) _ hraw
          obtain ⟨R', _, I', F', hQ'⟩ := largeEvenRawDatum_exists hraw2
          obtain ⟨hQ0, hSC, hguard⟩ := hQ'
          obtain ⟨hs', hna', θ', hP'⟩ := hQ0
          obtain ⟨_, hBsN', hBs3'⟩ := hP'
          exact lup10eA_autCard_false hS hxL M e hecart he0 hbas θ' hBsN' hBs3' hSC
            (hguard hs' hna') (by decide)
        · have hraw2 := (largeEvenLabelAll_and
            (lup10eA_labelAll_autCard (l := 8) (r := 4) (ε := 1)
              (by omega) (by omega) (by norm_num))
            (lup10eA_labelAll_subsetInn (l := 8))) _ hraw
          obtain ⟨R', _, I', F', hQ'⟩ := largeEvenRawDatum_exists hraw2
          obtain ⟨hQ0, hSC, hguard⟩ := hQ'
          obtain ⟨hs', hna', θ', hP'⟩ := hQ0
          obtain ⟨_, hBsN', hBs3'⟩ := hP'
          exact lup10eA_autCard_false hS hxL M e hecart he0 hbas θ' hBsN' hBs3' hSC
            (hguard hs' hna') (by decide)
      ·
        rcases Nat.even_or_odd l with ⟨k, hk⟩ | ⟨k, hk⟩
        · subst hk
          have hk5 : 5 ≤ k := by omega
          have hraw2 := (lup10eA_labelAll_autCard (l := k + k) (r := k) (ε := 1)
            (by omega) (by omega) (by omega)) _ hraw
          obtain ⟨R', _, I', F', hQ'⟩ := largeEvenRawDatum_exists hraw2
          obtain ⟨hQ0, hSC⟩ := hQ'
          obtain ⟨_, _, θ', hP'⟩ := hQ0
          obtain ⟨_, hBsN', hBs3'⟩ := hP'
          exact lup10eA_torusAutCard_rank_false hS hxL M e hbas θ' hBsN' hBs3' hSC hk5
        · subst hk
          have hk5 : 5 ≤ k + 1 := by omega
          have hraw2 := (lup10eA_labelAll_autCard (l := 2 * k + 1) (r := k + 1) (ε := 0)
            (by omega) (by omega) (by omega)) _ hraw
          obtain ⟨R', _, I', F', hQ'⟩ := largeEvenRawDatum_exists hraw2
          obtain ⟨hQ0, hSC⟩ := hQ'
          obtain ⟨_, _, θ', hP'⟩ := hQ0
          obtain ⟨_, hBsN', hBs3'⟩ := hP'
          exact lup10eA_torusAutCard_rank_false hS hxL M e hbas θ' hBsN' hBs3' hSC hk5
  ·
    obtain ⟨rfl, rfl⟩ := htwD
    have hq : GGInnerDiagOnLabel (fun _ lab => (lab.tag = .twD ∧ lab.rank = 2) ∧ lab.n = 1)
        3 Bs L := relabel _ ⟨⟨rfl, rfl⟩, rfl⟩
    exact (lup10eA_not_of_cardLt
      (S := fun _ lab => (lab.tag = .twD ∧ lab.rank = 2) ∧ lab.n = 1)
      (fun lab hlab' hs => largeEvenLabelAll_card_lt_linearTwo Nat.prime_three (by norm_num)
        hlab' (Or.inr ⟨hs.1.1, hs.1.2⟩))
      (fun lab hs => Or.inr (Or.inr (Or.inr ⟨hs.2, rfl⟩))) hS.1.1 hq).elim
  ·
    subst htri
    have hq : GGInnerDiagOnLabel (fun _ lab => lab.tag = .triD4 ∧ lab.n = 1) 3 Bs L :=
      relabel _ ⟨rfl, rfl⟩
    exact (lup10eA_not_of_cardLt (S := fun _ lab => lab.tag = .triD4 ∧ lab.n = 1)
      (fun lab hlab' hs => NbrInnerNine.largeEvenLabelAll_card_lt_triD4_of Nat.prime_three
        hlab' hs.1 (Or.inl rfl))
      (fun lab hs => Or.inr (Or.inr (Or.inr ⟨hs.2, rfl⟩))) hS.1.1 hq).elim
  ·
    subst hG2
    have h : l = 0 ∧ 2 ≤ 1 := hlab.2
    omega
  ·
    subst htwB2
    have h : l = 0 ∧ Odd 1 ∧ 3 ≤ 1 := hlab.2
    omega
  ·
    subst htwF4
    have h : l = 0 ∧ Odd 1 ∧ 3 ≤ 1 := hlab.2
    omega
  ·
    subst hB2der
    have hq : GGInnerDiagOnLabel (fun _ lab => lab.tag = .B2der ∧ lab.n = 1) 3 Bs L :=
      relabel _ ⟨rfl, rfl⟩
    exact (lup10eA_not_of_cardLt (S := fun _ lab => lab.tag = .B2der ∧ lab.n = 1)
      (fun lab hlab' hs => ggCSR_B2der hlab' hs.1)
      (fun lab hs => Or.inr (Or.inr (Or.inr ⟨hs.2, rfl⟩))) hS.1.1 hq).elim
  ·
    subst hG2der
    have hq : GGInnerDiagOnLabel (fun _ lab => lab.tag = .G2der ∧ lab.n = 1) 3 Bs L :=
      relabel _ ⟨rfl, rfl⟩
    exact (lup10eA_not_of_cardLt (S := fun _ lab => lab.tag = .G2der ∧ lab.n = 1)
      (fun lab hlab' hs => ggCSR_G2der hlab' hs.1)
      (fun lab hs => Or.inr (Or.inr (Or.inr ⟨hs.2, rfl⟩))) hS.1.1 hq).elim
  ·
    subst htwF4der
    have hq : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twF4der ∧ lab.n = 1) 3 Bs L :=
      relabel _ ⟨rfl, rfl⟩
    exact (lup10eA_not_of_cardLt (S := fun _ lab => lab.tag = .twF4der ∧ lab.n = 1)
      (fun lab hlab' hs => TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4der_holds
        Nat.prime_three hlab' hs.1 (Or.inr (Or.inr (Or.inr ⟨hs.2, rfl⟩))))
      (fun lab hs => Or.inr (Or.inr (Or.inr ⟨hs.2, rfl⟩))) hS.1.1 hq).elim

end CFSG.StandardType

end

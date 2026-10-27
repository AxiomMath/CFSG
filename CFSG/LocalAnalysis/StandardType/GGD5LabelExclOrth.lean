module

public import CFSG.LocalAnalysis.StandardType.GGD5LabelGlue
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFinal
import CFSG.LocalAnalysis.StandardType.GGTwOmPlusHolds
import CFSG.LocalAnalysis.StandardType.GGTwAutHolds
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeVac
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas
import CFSG.LocalAnalysis.StandardType.GGQTwoVACOrth

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

private theorem lup10eO_labelAll_inn_D {l : ℕ} (hl : 4 ≤ l) :
    LargeEvenLabelAll ⟨.D, l, 1⟩ fun R _ I _ => I = LargeEvenInnSet R := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  simp only [show l ≠ 3 by omega, ↓reduceIte] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  exact ⟨K, i1, i2, hK, hq, rfl⟩

private theorem lup10eO_labelAll_inn_twD {l : ℕ} (hl : 4 ≤ l) :
    LargeEvenLabelAll ⟨.twD, l, 1⟩ fun R _ I _ => I = LargeEvenInnSet R := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  simp only [show l ≠ 2 by omega, show l ≠ 3 by omega, ↓reduceIte] at hQ ⊢
  obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := hQ
  exact ⟨K, i1, i2, hK, b, c, hbc, hq, rfl⟩

private theorem lup10eO_labelAll_torusLift5_orth
    {t : LargeEvenLieTag} (ht : t = .D ∨ t = .twD) {l : ℕ} (hl : 6 ≤ l) :
    LargeEvenLabelAll ⟨t, l, 1⟩ fun R _ _ _ => GGTorusLift 3 5 R := by
  have h : GGOrthRestLabel 3 ⟨t, l, 1⟩ := by
    refine ⟨by dsimp only; omega, ?_⟩
    rcases ht with rfl | rfl
    · exact Or.inr ⟨rfl, rfl, rfl⟩
    · exact Or.inl ⟨rfl, by norm_num⟩
  exact (OrthRest.labelAll ggOrthRestTorusLiftInput_holds Nat.prime_three h).mono
    fun _ _ _ _ hP => ggTorusLift_mono Nat.prime_three hP.2 (by dsimp only; omega)

private theorem lup10eO_labelAll_D5 :
    LargeEvenLabelAll ⟨.D, 5, 1⟩ fun R _ I _ =>
      GGTorusAutCardSC 3 R I 4 384 ∧ I = LargeEvenInnSet R := by
  have h := ggTwOmPlus_label (r := 4) (f := 1) (by norm_num) (by norm_num)
    (by norm_num : 3 ∣ 2 ^ 1 + 1)
  have h' : LargeEvenLabelAll ⟨.D, 5, 1⟩ fun R _ I _ =>
      GGTorusAutCardSC 3 R I 4 384 := by
    simpa only [show 2 ^ 4 * Nat.factorial 4 = 384 by norm_num] using h
  exact largeEvenLabelAll_and h' (lup10eO_labelAll_inn_D (l := 5) (by norm_num))

private theorem lup10eO_labelAll_twD4 :
    LargeEvenLabelAll ⟨.twD, 4, 1⟩ fun R _ I _ =>
      GGTorusAutCardSC 3 R I 3 48 ∧ I = LargeEvenInnSet R := by
  have h := ggTwOm_label (r := 3) (f := 1) (by norm_num) (by norm_num)
    (Or.inr ⟨by decide, by norm_num⟩)
  have h' : LargeEvenLabelAll ⟨.twD, 4, 1⟩ fun R _ I _ =>
      GGTorusAutCardSC 3 R I 3 48 := by
    simpa only [show 2 ^ 3 * Nat.factorial 3 = 48 by norm_num] using h
  exact largeEvenLabelAll_and h' (lup10eO_labelAll_inn_twD (l := 4) (by norm_num))

private theorem lup10eO_not_of_torusLift {S : ℕ → LargeEvenLabel → Prop}
    (hSall : ∀ lab, LargeEvenInLambda2 lab → S 3 lab →
      LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hSset : GGQTwoSetting 3 B Bs x L D J) {y : G} {H : Subgroup G}
    (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι) (hbas : M.toLin.Basis) :
    ¬ GGInnerDiagOnLabel S 3 Bs L := by
  intro hq
  have hq' := largeEvenMarking_and_labelAll (S := fun lab => S 3 lab)
    (P' := fun R _ _ _ => GGTorusLift 3 5 R)
    (fun lab hlab hs => hSall lab hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hq
  obtain ⟨-, lab, -, hraw⟩ := hq'
  obtain ⟨R, _, I, F, -, -, θ, -, hlift⟩ := largeEvenRawDatum_exists hraw
  exact lup10c_not_torusLift hSset M e hbas θ (le_refl 5) hlift

private theorem lup10eO_not_of_cardLt {S : ℕ → LargeEvenLabel → Prop}
    (hSall : ∀ lab, LargeEvenInLambda2 lab → S 3 lab →
      LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
        (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 3)
    (hsp : ∀ lab, S 3 lab → LargeEvenSplit 3 lab)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) : ¬ GGInnerDiagOnLabel S 3 Bs L := fun hq =>
  ggThmIHyp_false_of_labelAll (S := fun p lab => p = 3 ∧ S 3 lab)
    (fun _ lab _ hlab hs _ => by
      obtain ⟨rfl, hs⟩ := hs
      exact hSall lab hlab hs) hC.1
    (largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨⟨rfl, hP.1⟩, hsp lab hP.1,
      hC.2.1.1.trans hP.2.1, fun b hb => hP.2.2 b (hC.2.1.1 hb)⟩) hq)

private theorem lup10eO_not_of_torusAutCard {S : ℕ → LargeEvenLabel → Prop} {r N : ℕ}
    (hN : N ≠ 192)
    (hSall : ∀ lab, LargeEvenInLambda2 lab → S 3 lab →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusAutCardSC 3 R I r N ∧ I = LargeEvenInnSet R)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hSset : GGQTwoSetting 3 B Bs x L D J) (hxL : x ∉ L) {y : G} {H : Subgroup G}
    (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.a = e 0)
    (hbas : M.toLin.Basis) : ¬ GGInnerDiagOnLabel S 3 Bs L := by
  intro hq
  have hq' := largeEvenMarking_and_labelAll (S := fun lab => S 3 lab)
    (P' := fun R _ I _ => GGTorusAutCardSC 3 R I r N ∧ I = LargeEvenInnSet R)
    (fun lab hlab hs => hSall lab hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hq
  obtain ⟨-, lab, -, hraw⟩ := hq'
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, hBsN, hBs3⟩, ⟨hSC, hInn⟩⟩⟩ :=
    largeEvenRawDatum_exists hraw
  have hcard := (lup10c_torusAutCard hSset hxL M e hbas θ hBsN hBs3 hSC).2 (le_of_eq hInn)
  have h192 := lup10c_card_automizer M e hecart he0 hbas
  rw [hcard] at h192
  exact hN h192

private theorem lup10eO_not_twD5
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hxL : x ∉ L) {y : G} {H : Subgroup G}
    (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι) (hbas : M.toLin.Basis)
    (hq : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twD, 5, 1⟩) 3 Bs L) : False := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hq
  obtain ⟨_, _, _, _, _, _, _, hP⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hlabel, -, -⟩ := hP
  subst hlabel
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, hfield, hfinite, hK, b, c, hbc, hQ⟩ := hraw
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨-, hBsN, hBsI⟩ := hP
  have hK2 : Nat.card K = 2 := hK.trans (pow_one 2)
  have hγ := ggQ2OrthMinus_gamma_card (m := 5) (θ := θ) hS hK2 (by norm_num) (by norm_num)
    hbc hperf hBsN hBsI
  have hγ4 := lup10c_card_range_ggGamma hS hxL M e hbas hBsN
  rw [hγ] at hγ4
  norm_num at hγ4

theorem lup10e_not_orth
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hxL : x ∉ L) {y : G}
    {H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.a = e 0)
    (hbas : M.toLin.Basis) :
    ¬ GGInnerDiagOnLabel (fun _ lab =>
        ((lab.tag = .D ∧ lab.rank ≠ 4) ∨ (lab.tag = .twD ∧ 4 ≤ lab.rank)) ∧ lab.n = 1) 3 Bs L := by
  intro hq
  obtain ⟨hperf, lab, hlab, hraw⟩ := hq
  obtain ⟨_, _, _, _, _, _, _, hP⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hdisj, hn1⟩ := hP.1
  have hfix : ∀ S' : ℕ → LargeEvenLabel → Prop, S' 3 lab → GGInnerDiagOnLabel S' 3 Bs L :=
    fun S' hS' => ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _, hQ⟩ => ⟨hs, hna, θ, hS', hQ⟩) hraw⟩
  obtain ⟨t, l, n⟩ := lab
  simp only at hdisj hn1
  subst hn1
  rcases hdisj with ⟨rfl, hne⟩ | ⟨rfl, hge⟩
  · have hl3 : 3 ≤ l := hlab.2
    rcases (show l = 3 ∨ l = 5 ∨ 6 ≤ l by omega) with rfl | rfl | hl6
    · exact (lup10eO_not_of_cardLt
        (S := fun _ lab => lab = ⟨.D, 3, 1⟩)
        (fun lab _ hs => by
          subst hs
          exact StdSubRestThree.largeEvenLabelAll_card_lt_twoThreeSmall
            ⟨rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩)
        (fun lab hs => by subst hs; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
        hS.1.1 (hfix _ rfl)).elim
    · exact lup10eO_not_of_torusAutCard (r := 4) (N := 384) (by norm_num)
        (S := fun _ lab => lab = ⟨.D, 5, 1⟩)
        (fun lab _ hs => by subst hs; exact lup10eO_labelAll_D5)
        hS hxL M e hecart he0 hbas (hfix _ rfl)
    · exact lup10eO_not_of_torusLift
        (S := fun _ lab => lab = ⟨.D, l, 1⟩)
        (fun lab _ hs => by subst hs; exact lup10eO_labelAll_torusLift5_orth (Or.inl rfl) hl6)
        hS M e hbas (hfix _ rfl)
  · rcases (show l = 4 ∨ l = 5 ∨ 6 ≤ l by omega) with rfl | rfl | hl6
    · exact lup10eO_not_of_torusAutCard (r := 3) (N := 48) (by norm_num)
        (S := fun _ lab => lab = ⟨.twD, 4, 1⟩)
        (fun lab _ hs => by subst hs; exact lup10eO_labelAll_twD4)
        hS hxL M e hecart he0 hbas (hfix _ rfl)
    · exact lup10eO_not_twD5 hS hxL M e hbas (hfix _ rfl)
    · exact lup10eO_not_of_torusLift
        (S := fun _ lab => lab = ⟨.twD, l, 1⟩)
        (fun lab _ hs => by
          subst hs
          exact lup10eO_labelAll_torusLift5_orth (Or.inr rfl) hl6)
        hS M e hbas (hfix _ rfl)

end CFSG.StandardType

end

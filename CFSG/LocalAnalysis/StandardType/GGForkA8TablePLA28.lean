module

public import CFSG.LocalAnalysis.StandardType.GGForkA8TablePLMark
public import CFSG.LocalAnalysis.StandardType.GGForkA8TablePLRank
public import CFSG.LocalAnalysis.StandardType.GGForkA8TablePLTorus
public import CFSG.LocalAnalysis.StandardType.GGForkA8TablePLCard

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

@[expose] def GGForkA8TablePLA28Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 7 B Bs x L D J → GGInnerDiagAll 7 B Bs x L D J →
      ∀ (y : G) (K : Subgroup G), GGNbr 7 B x D J y K →
        GGHasLabel ⟨.A, 8, 1⟩ (K ⧸ Subgroup.center K) →
        GGHasLabel ⟨.A, 2, 3⟩ (J ⧸ Subgroup.center J) →
          GGHasLabel ⟨.A, 3, 3⟩ (L ⧸ Subgroup.center L) ∨
          GGHasLabel ⟨.C, 3, 3⟩ (L ⧸ Subgroup.center L) ∨
          GGHasLabel ⟨.twD, 4, 3⟩ (L ⧸ Subgroup.center L)

private theorem ta4_labelAll_true (lab : LargeEvenLabel) :
    LargeEvenLabelAll lab fun _ _ _ _ => True := by
  intro Q hQ
  exact largeEvenRawDatum_mono (fun R _ I F h => ⟨h, trivial⟩) hQ

private theorem ta4_labelAll_mono {lab : LargeEvenLabel} {P P' : LargeEvenRawCont}
    (h : LargeEvenLabelAll lab P)
    (hPP' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), P R I F → P' R I F) :
    LargeEvenLabelAll lab P' := by
  intro Q hQ
  exact largeEvenRawDatum_mono (fun R inst I F hq => ⟨hq.1, @hPP' R inst I F hq.2⟩) (h Q hQ)

private theorem ta4_labelAll_imp {lab : LargeEvenLabel} (c : Prop) {P : LargeEvenRawCont}
    (hc : c → LargeEvenLabelAll lab P) :
    LargeEvenLabelAll lab (fun R _ I F => c → P R I F) := by
  by_cases h : c
  · refine ta4_labelAll_mono (hc h) ?_
    intro R inst I F hp _
    exact hp
  · refine ta4_labelAll_mono (ta4_labelAll_true lab) ?_
    intro R inst I F _ hc'
    exact absurd hc' h

private def ta4_Q (lab : LargeEvenLabel) : LargeEvenRawCont :=
  fun R _ I _ =>
    (lab.n = 3 → GGTAPBig lab → GGTorusLift 7 4 R) ∧
    (lab.n = 3 → GGTAPSmall lab → ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian 7 X → Nat.card X < 7 ^ 3)

private theorem ta4_big_false {G : Type} [Group G] [Finite G] {B : Subgroup G} {x : G}
    {L : Subgroup G} {R : Type} [Group R] {I F : Set (MulAut R)}
    {θ : L ⧸ Subgroup.center L ≃* R} {lab : LargeEvenLabel}
    (hSS : LargeEvenSStar 7 B x L) (hLperf : commutator L = ⊤)
    (hQlab : ta4_Q lab R I F) (hn : lab.n = 3) (hbig : GGTAPBig lab)
    (hm : LargeEvenTwoLocalRank 7 G = 4) : False := by
  have hlift : GGTorusLift 7 4 R := hQlab.1 hn hbig
  have hle := succ_le_twoLocalRank_of_torusLift Nat.prime_seven hSS.2.2.2.1.1
    (hSS.1.1.2 x hSS.2.1) hSS.2.2.1 hLperf θ hlift
  omega

private theorem ta4_small_false {G : Type} [Group G] [Finite G] {B : Subgroup G} {x : G}
    {L : Subgroup G} {R : Type} [Group R] {I F : Set (MulAut R)}
    {θ : L ⧸ Subgroup.center L ≃* R} {lab : LargeEvenLabel}
    (hSS : LargeEvenSStar 7 B x L) (hLperf : commutator L = ⊤)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hβI : ∀ b : B, ggBeta L θ hBN b ∈ I)
    (hQlab : ta4_Q lab R I F) (hn : lab.n = 3) (hsmall : GGTAPSmall lab)
    (hB : Nat.card B = 7 ^ 4) : False := by
  let X : Subgroup (MulAut R) := (ggBeta L θ hBN).range
  have hXcard : Nat.card X * 7 = Nat.card B :=
    card_range_ggBeta_mul L θ Nat.prime_seven hSS hLperf hBN
  have hX : IsElemAbelian 7 X := isElemAbelian_range_ggBeta θ hSS.1.1 hBN
  have hXI : (X : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨b, rfl⟩
    exact hβI b
  have hlt : Nat.card X < 7 ^ 3 := hQlab.2 hn hsmall X hXI hX
  have hcard : Nat.card X = 7 ^ 3 := by
    have hmul : Nat.card X * 7 = 7 ^ 3 * 7 := by
      rw [hXcard, hB]
      norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 7) hmul
  omega

private theorem ta4_split_false_of_not_untwisted {t : LargeEvenLieTag} {r : ℕ}
    (ht : ¬ LargeEvenUntwisted t) (htri : t ≠ .triD4) (htw : t ≠ .twD)
    (h : LargeEvenSplit 7 ⟨t, r, 3⟩) : False := by
  unfold LargeEvenSplit at h
  rcases h with ⟨hu, -⟩ | ⟨-, htri', h7⟩ | ⟨htw', -⟩ | ⟨hn, -⟩
  · exact ht hu
  · exact absurd h7 (ggA8Nbr_not_seven_dvd_two_pow_add_one 3)
  · rcases htw' with h | h
    · exact htw h
    · exact htri h
  · exact absurd hn (by norm_num)

private theorem ta4_classify {G : Type} [Group G] [Finite G] {B : Subgroup G} {x : G}
    {L : Subgroup G} {R : Type} [Group R] {I F : Set (MulAut R)}
    {θ : L ⧸ Subgroup.center L ≃* R} {lab : LargeEvenLabel}
    (hSS : LargeEvenSStar 7 B x L) (hLperf : commutator L = ⊤)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hβI : ∀ b : B, ggBeta L θ hBN b ∈ I)
    (hQlab : ta4_Q lab R I F) (hlab : LargeEvenInLambda2 lab)
    (hsplit : LargeEvenSplit 7 lab) (hhasL : GGHasLabel lab (L ⧸ Subgroup.center L))
    (hn : lab.n = 3) (hB : Nat.card B = 7 ^ 4)
    (hm : LargeEvenTwoLocalRank 7 G = 4) :
    GGHasLabel ⟨.A, 3, 3⟩ (L ⧸ Subgroup.center L) ∨
    GGHasLabel ⟨.C, 3, 3⟩ (L ⧸ Subgroup.center L) ∨
    GGHasLabel ⟨.twD, 4, 3⟩ (L ⧸ Subgroup.center L) := by
  obtain ⟨t, r, n⟩ := lab
  have hn' : n = 3 := hn
  subst n
  cases t
  ·
    have hr1 : 1 ≤ r := by
      simp only [LargeEvenInLambda2] at hlab
      exact hlab.2.1
    by_cases hbig : GGTAPBig ⟨.A, r, 3⟩
    · exact (ta4_big_false (θ := θ) hSS hLperf hQlab rfl hbig hm).elim
    · by_cases hsmall : GGTAPSmall ⟨.A, r, 3⟩
      · exact (ta4_small_false (θ := θ) hSS hLperf hBN hβI hQlab rfl hsmall hB).elim
      · have hr3 : r = 3 := by
          simp [GGTAPBig] at hbig
          simp [GGTAPSmall] at hsmall
          omega
        subst r
        exact Or.inl hhasL
  ·
    exact (ta4_split_false_of_not_untwisted (t := .twA)
      (by simp [LargeEvenUntwisted]) (by decide) (by decide) hsplit).elim
  ·
    have hr2 : 2 ≤ r := by
      simp only [LargeEvenInLambda2] at hlab
      exact hlab.2.1
    by_cases hbig : GGTAPBig ⟨.B, r, 3⟩
    · exact (ta4_big_false (θ := θ) hSS hLperf hQlab rfl hbig hm).elim
    · by_cases hsmall : GGTAPSmall ⟨.B, r, 3⟩
      · exact (ta4_small_false (θ := θ) hSS hLperf hBN hβI hQlab rfl hsmall hB).elim
      · have hr3 : r = 3 := by
          simp [GGTAPBig] at hbig
          simp [GGTAPSmall] at hsmall
          omega
        subst r
        exact Or.inr (Or.inl hhasL)
  ·
    have hr2 : 2 ≤ r := by
      simp only [LargeEvenInLambda2] at hlab
      exact hlab.2.1
    by_cases hbig : GGTAPBig ⟨.C, r, 3⟩
    · exact (ta4_big_false (θ := θ) hSS hLperf hQlab rfl hbig hm).elim
    · by_cases hsmall : GGTAPSmall ⟨.C, r, 3⟩
      · exact (ta4_small_false (θ := θ) hSS hLperf hBN hβI hQlab rfl hsmall hB).elim
      · have hr3 : r = 3 := by
          simp [GGTAPBig] at hbig
          simp [GGTAPSmall] at hsmall
          omega
        subst r
        exact Or.inr (Or.inl hhasL)
  ·
    have hr3' : 3 ≤ r := by
      simp only [LargeEvenInLambda2] at hlab
      exact hlab.2
    by_cases hbig : GGTAPBig ⟨.D, r, 3⟩
    · exact (ta4_big_false (θ := θ) hSS hLperf hQlab rfl hbig hm).elim
    · have hr3 : r = 3 := by
        simp [GGTAPBig] at hbig
        omega
      subst r
      exact Or.inl ((ggHasLabel_D3_iff_A3 (f := 3)).1 hhasL)
  ·
    have hr2 : 2 ≤ r := by
      simp only [LargeEvenInLambda2] at hlab
      exact hlab.2
    by_cases hbig : GGTAPBig ⟨.twD, r, 3⟩
    · exact (ta4_big_false (θ := θ) hSS hLperf hQlab rfl hbig hm).elim
    · by_cases hsmall : GGTAPSmall ⟨.twD, r, 3⟩
      · exact (ta4_small_false (θ := θ) hSS hLperf hBN hβI hQlab rfl hsmall hB).elim
      · have hr4 : r = 4 := by
          simp [GGTAPBig] at hbig
          simp [GGTAPSmall] at hsmall
          omega
        subst r
        exact Or.inr (Or.inr hhasL)
  ·
    exact (ta4_big_false (θ := θ) hSS hLperf hQlab rfl (by simp [GGTAPBig]) hm).elim
  ·
    exact (ta4_big_false (θ := θ) hSS hLperf hQlab rfl (by simp [GGTAPBig]) hm).elim
  ·
    exact (ta4_big_false (θ := θ) hSS hLperf hQlab rfl (by simp [GGTAPBig]) hm).elim
  ·
    exact (ta4_big_false (θ := θ) hSS hLperf hQlab rfl (by simp [GGTAPBig]) hm).elim
  ·
    exact (ta4_split_false_of_not_untwisted (t := .twE6)
      (by simp [LargeEvenUntwisted]) (by decide) (by decide) hsplit).elim
  ·
    exact (ta4_small_false (θ := θ) hSS hLperf hBN hβI hQlab rfl (by simp [GGTAPSmall]) hB).elim
  ·
    exact (ta4_small_false (θ := θ) hSS hLperf hBN hβI hQlab rfl (by simp [GGTAPSmall]) hB).elim
  ·
    exact (ta4_split_false_of_not_untwisted (t := .twB2)
      (by simp [LargeEvenUntwisted]) (by decide) (by decide) hsplit).elim
  ·
    exact (ta4_split_false_of_not_untwisted (t := .twF4)
      (by simp [LargeEvenUntwisted]) (by decide) (by decide) hsplit).elim
  ·
    exact absurd hlab.2.2 (by norm_num)
  ·
    exact absurd hlab.2.2 (by norm_num)
  ·
    exact absurd hlab.2.2 (by norm_num)

theorem ggForkA8TablePLA28_holds
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) : GGForkA8TablePLA28Input := by
  intro G _ _ B Bs x L D J hC hID y K hK hKA8 hJA2
  have hSS : LargeEvenSStar 7 B x L := hC.1.2.2.2.2.2.2.1
  have hKd : GGInnerDiagOn Bs K := hID.2 y K hK
  have hB : Nat.card B = 7 ^ 4 := ggA8Nbr_card_B hRig hC hK hKd hKA8
  have hBc : Nat.card B = 7 ^ LargeEvenTwoLocalRank 7 G := hSS.1.2.1
  have hm : LargeEvenTwoLocalRank 7 G = 4 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 7) (hBc.symm.trans hB)
  have hQbig : ∀ lab, LargeEvenInLambda2 lab →
      LargeEvenLabelAll lab
        (fun R _ I F => lab.n = 3 → GGTAPBig lab → GGTorusLift 7 4 R) := by
    intro lab hlab
    refine ta4_labelAll_mono (ta4_labelAll_imp (lab.n = 3 ∧ GGTAPBig lab)
      (fun hc => largeEvenLabelAll_torusLift_seven_four hlab hc.1 hc.2)) ?_
    intro R inst I F h a b
    exact h ⟨a, b⟩
  have hQsmall : ∀ lab, LargeEvenInLambda2 lab →
      LargeEvenLabelAll lab
        (fun R _ I F => lab.n = 3 → GGTAPSmall lab → ∀ X : Subgroup (MulAut R),
          (X : Set (MulAut R)) ⊆ I → IsElemAbelian 7 X → Nat.card X < 7 ^ 3) := by
    intro lab hlab
    refine ta4_labelAll_mono (ta4_labelAll_imp (lab.n = 3 ∧ GGTAPSmall lab)
      (fun hc => largeEvenLabelAll_card_lt_seven_small hlab hc.1 hc.2)) ?_
    intro R inst I F h a b
    exact h ⟨a, b⟩
  have hQ : ∀ lab, LargeEvenInLambda2 lab → LargeEvenLabelAll lab (ta4_Q lab) := by
    intro lab hlab
    exact largeEvenLabelAll_and (hQbig lab hlab) (hQsmall lab hlab)
  obtain ⟨hLperf, lab, labJ, hlab, hsplit, hhasL, hlabJ, hdvd, hhasJ,
    R, _, I, F, θ, hBN, hβI, hQlab⟩ :=
    ggNbr_label_J_of_tcj_and (Q := ta4_Q) hTCJ hC hK hQ
  have hlabJ' : labJ = ⟨.A, 2, 3⟩ := by
    rcases ggLabelIso_typeA_cases hRig (r := 2) (f := 3) (by norm_num) hlabJ
      (by simp [LargeEvenInLambda2]) hhasJ hJA2 with h | ⟨h23, -⟩
    · exact h
    · omega
  have hdvd3 : lab.n ∣ 3 := by
    rw [hlabJ'] at hdvd
    exact hdvd
  have h3 : 3 ∣ lab.n := largeEvenSplit_seven_dvd hsplit
  have hn : lab.n = 3 := (Nat.dvd_antisymm h3 hdvd3).symm
  exact ta4_classify hSS hLperf hBN hβI hQlab hlab hsplit hhasL hn hB hm

end CFSG.StandardType

end

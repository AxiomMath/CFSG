module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourDom
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRankExc
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Helpers

private theorem not_largeEvenMarking_and_or {X : Type} [Group X] {p : ℕ}
    {P Q : LargeEvenLabel → Prop}
    (hP : ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => P lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E))
    (hQ : ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => Q lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E)) :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => (P lab ∨ Q lab) ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) := by
  intro h
  have h' := largeEvenMarking_mono
    (P' := fun lab R _ I _ _ => (P lab ∧ ∃ E : Subgroup (MulAut R),
      (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E) ∨
      (Q lab ∧ ∃ E : Subgroup (MulAut R),
        (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E))
    (fun _ _ _ _ _ _ hPQE => by
      rcases hPQE with ⟨hPQ, hE⟩
      exact hPQ.elim (fun hP' => Or.inl ⟨hP', hE⟩) (fun hQ' => Or.inr ⟨hQ', hE⟩)) h
  rcases largeEvenMarking_or h' with hP' | hQ'
  · exact hP hP'
  · exact hQ hQ'

private theorem not_largeEvenMarking_of_imp {X : Type} [Group X] {p : ℕ}
    {P Q : LargeEvenLabel → Prop}
    (hQ : ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => Q lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E))
    (hPQ : ∀ lab, P lab → Q lab) :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => P lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) :=
  fun h => hQ (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hPQ _ hP.1, hP.2⟩) h)

private theorem dvd_twoPow_sub_or_add_of_dvd_fourPow {p n : ℕ} (hp : p.Prime)
    (h : p ∣ 4 ^ n - 1) : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h4 : 4 ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  have hprod : (2 ^ n - 1) * (2 ^ n + 1) = 4 ^ n - 1 := by
    rw [h4]
    zify [h1, Nat.one_le_iff_ne_zero.mpr (by positivity : 2 ^ n * 2 ^ n ≠ 0)]
    ring
  rw [← hprod] at h
  exact hp.dvd_mul.mp h

end Helpers

@[expose] def GGRootGenSmallRankLabel (_p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ (lab.rank = 1 ∨ lab.rank = 2)) ∨
    ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2) ∨ (lab.tag = .twA ∧ lab.rank = 2) ∨
    (lab.tag = .twD ∧ lab.rank = 2) ∨ lab.tag = .B2der ∨ lab.tag = .twB2

@[expose] def GGRootGenSmallExcLabel (_p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twF4

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {S : ℕ → LargeEvenLabel → Prop}

theorem ggInnerDiagOnLabel_L_pRank_ge_three (hcfg : GGConfig p B Bs x L D J)
    (hL : GGInnerDiagOnLabel S p Bs L) :
    StandardType.LargeEvenMarking ↥L (fun lab R _ I _ _ => S p lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) := by
  refine largeEvenMarking_mono ?_ hL
  rintro lab R _ I _ θ ⟨hSl, hBsN, h3⟩
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hBsN
  refine ⟨hSl, (ggBeta L θ hBN).range, ?_,
    isElemAbelian_range_ggBeta θ hS.1.1 hBN, ?_⟩
  · rintro _ ⟨b, rfl⟩
    exact ggBeta_mem L θ hBN (fun b hb => h3 b (hBBs hb)) b
  · refine Nat.le_of_mul_le_mul_right ?_ hp.pos
    calc p ^ 3 * p = p ^ 4 := by ring
      _ ≤ Nat.card B := pow_four_le_card_of_bmax hp hS.1 hcfg.1.2.2.2.2.2.1.2.2.2
      _ = Nat.card (ggBeta L θ hBN).range * p :=
        (card_range_ggBeta_mul L θ hp hS hL.1 hBN).symm

theorem ggInnerDiagOnLabel_nbr_pRank_ge_three (hcfg : GGConfig p B Bs x L D J) {y : G}
    {K : Subgroup G} (hnb : GGNbr p B x D J y K) (hK : GGInnerDiagOnLabel S p Bs K) :
    StandardType.LargeEvenMarking ↥K (fun lab R _ I _ _ => S p lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) := by
  refine largeEvenMarking_mono ?_ hK
  rintro lab R _ I _ θ ⟨hSl, hN, h3⟩
  exact ⟨hSl, NbrInnerRest.exists_large_elemAbelian_subset hcfg hnb hK.1 θ hN
    (fun b hb => ggLAut_mem_of_induces K θ hN h3 hb)⟩

end Config

section SmallRank

theorem not_largeEvenMarking_smallRank {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => GGRootGenSmallRankLabel p lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) := by
  have hA := not_largeEvenMarking_and_or
    (ggInndiag_pRank_le_two_A1 (X := X) hp hp2)
    (ggInndiag_pRank_le_two_A2 (X := X) hp hp2)
  have hA' := not_largeEvenMarking_of_imp
    (P := fun lab => lab.tag = .A ∧ (lab.rank = 1 ∨ lab.rank = 2)) hA
    (fun _ h => by
      rcases h with ⟨hA, h1 | h2⟩
      · exact Or.inl ⟨hA, h1⟩
      · exact Or.inr ⟨hA, h2⟩)
  exact not_largeEvenMarking_and_or hA'
    (not_largeEvenMarking_and_or (ggInndiag_pRank_le_two_B2 (X := X) hp hp2)
      (not_largeEvenMarking_and_or (ggInndiag_pRank_le_two_twA2 (X := X) hp hp2)
        (not_largeEvenMarking_and_or (ggInndiag_pRank_le_two_twD2 (X := X) hp hp2)
          (not_largeEvenMarking_and_or (ggInndiag_pRank_le_two_B2der (X := X) hp hp2)
            (ggInndiag_pRank_le_two_twB2 (X := X) hp hp2)))))

theorem ggRootGenLInputOnQFour_of_notSmallRank {X : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenLInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧
      ¬ (X p lab ∨ GGRootGenSmallRankLabel p lab)) :
    GGRootGenLInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧ ¬ X p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL
  have hp : p.Prime := hHyp.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hHyp.1.1.2.2.2.2.2.1.2.1
  rcases (GGInnerDiagOnLabel.mono_label (T := fun p lab => GGRootGenSmallRankLabel p lab ∨
      (GGRootGenOpenLabel p lab ∧ ¬ (X p lab ∨ GGRootGenSmallRankLabel p lab)))
      (fun lab hlab => (em (GGRootGenSmallRankLabel p lab)).imp_right fun hn =>
        ⟨hlab.1, fun h' => h'.elim hlab.2 hn⟩) hL).elim_or with h₁ | h₂
  · exact absurd (ggInnerDiagOnLabel_L_pRank_ge_three hHyp.1 h₁)
      (not_largeEvenMarking_smallRank (X := ↥L) hp hp2)
  · exact h G p B Bs x L D J hHyp hq hN h₂

theorem ggRootGenNbrInputOnQFour_of_notSmallRank {X : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenNbrInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧
      ¬ (X p lab ∨ GGRootGenSmallRankLabel p lab)) :
    GGRootGenNbrInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧ ¬ X p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN y K hnb hK
  have hp : p.Prime := hHyp.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hHyp.1.1.2.2.2.2.2.1.2.1
  rcases (GGInnerDiagOnLabel.mono_label (T := fun p lab => GGRootGenSmallRankLabel p lab ∨
      (GGRootGenOpenLabel p lab ∧ ¬ (X p lab ∨ GGRootGenSmallRankLabel p lab)))
      (fun lab hlab => (em (GGRootGenSmallRankLabel p lab)).imp_right fun hn =>
        ⟨hlab.1, fun h' => h'.elim hlab.2 hn⟩) hK).elim_or with h₁ | h₂
  · exact absurd (ggInnerDiagOnLabel_nbr_pRank_ge_three hHyp.1 hnb h₁)
      (not_largeEvenMarking_smallRank (X := ↥K) hp hp2)
  · exact h G p B Bs x L D J hHyp hq hN y K hnb h₂

end SmallRank

section SmallExc

theorem not_largeEvenMarking_smallExc {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ =>
      (GGRootGenSmallExcLabel p lab ∧ GGRootGenOpenLabel p lab) ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) := by
  have hG2 := not_largeEvenMarking_of_imp
    (P := fun lab => lab.tag = .G2 ∧ GGRootGenOpenLabel p lab)
    (Q := fun lab => lab.tag = .G2)
    (ggInndiag_pRank_le_two_G2 (X := X) hp hp2) (fun _ h => h.1)
  have hTri := not_largeEvenMarking_of_imp
    (P := fun lab => lab.tag = .triD4 ∧ GGRootGenOpenLabel p lab)
    (Q := fun lab => lab.tag = .triD4 ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1))
    (ggInndiag_pRank_le_two_triD4 (X := X) hp)
    (fun _ h => ⟨h.1, dvd_twoPow_sub_or_add_of_dvd_fourPow hp h.2.1⟩)
  have hTwF4 := not_largeEvenMarking_of_imp
    (P := fun lab => lab.tag = .twF4 ∧ GGRootGenOpenLabel p lab)
    (Q := fun lab => lab.tag = .twF4 ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1))
    (ggInndiag_pRank_le_two_twF4 (X := X) hp hp2)
    (fun _ h => ⟨h.1, dvd_twoPow_sub_or_add_of_dvd_fourPow hp h.2.1⟩)
  refine not_largeEvenMarking_of_imp
    (P := fun lab => GGRootGenSmallExcLabel p lab ∧ GGRootGenOpenLabel p lab)
    (not_largeEvenMarking_and_or hG2 (not_largeEvenMarking_and_or hTri hTwF4)) ?_
  rintro lab ⟨hS, hO⟩
  rcases hS with hG2 | hTri | hF4
  · exact Or.inl ⟨hG2, hO⟩
  · exact Or.inr (Or.inl ⟨hTri, hO⟩)
  · exact Or.inr (Or.inr ⟨hF4, hO⟩)

theorem ggRootGenLInputOnQFour_of_notSmallExc {X : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenLInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧
      ¬ (X p lab ∨ GGRootGenSmallExcLabel p lab)) :
    GGRootGenLInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧ ¬ X p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL
  have hp : p.Prime := hHyp.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hHyp.1.1.2.2.2.2.2.1.2.1
  rcases (GGInnerDiagOnLabel.mono_label (T := fun p lab =>
      (GGRootGenSmallExcLabel p lab ∧ GGRootGenOpenLabel p lab) ∨
        (GGRootGenOpenLabel p lab ∧ ¬ (X p lab ∨ GGRootGenSmallExcLabel p lab)))
      (fun lab hlab => (em (GGRootGenSmallExcLabel p lab)).elim
        (fun hs => Or.inl ⟨hs, hlab.1⟩)
        (fun hn => Or.inr ⟨hlab.1, fun h' => h'.elim hlab.2 hn⟩)) hL).elim_or with h₁ | h₂
  · exact absurd (ggInnerDiagOnLabel_L_pRank_ge_three hHyp.1 h₁)
      (not_largeEvenMarking_smallExc (X := ↥L) hp hp2)
  · exact h G p B Bs x L D J hHyp hq hN h₂

theorem ggRootGenNbrInputOnQFour_of_notSmallExc {X : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenNbrInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧
      ¬ (X p lab ∨ GGRootGenSmallExcLabel p lab)) :
    GGRootGenNbrInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧ ¬ X p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN y K hnb hK
  have hp : p.Prime := hHyp.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hHyp.1.1.2.2.2.2.2.1.2.1
  rcases (GGInnerDiagOnLabel.mono_label (T := fun p lab =>
      (GGRootGenSmallExcLabel p lab ∧ GGRootGenOpenLabel p lab) ∨
        (GGRootGenOpenLabel p lab ∧ ¬ (X p lab ∨ GGRootGenSmallExcLabel p lab)))
      (fun lab hlab => (em (GGRootGenSmallExcLabel p lab)).elim
        (fun hs => Or.inl ⟨hs, hlab.1⟩)
        (fun hn => Or.inr ⟨hlab.1, fun h' => h'.elim hlab.2 hn⟩)) hK).elim_or with h₁ | h₂
  · exact absurd (ggInnerDiagOnLabel_nbr_pRank_ge_three hHyp.1 hnb h₁)
      (not_largeEvenMarking_smallExc (X := ↥K) hp hp2)
  · exact h G p B Bs x L D J hHyp hq hN y K hnb h₂

end SmallExc

end CFSG.StandardType

end

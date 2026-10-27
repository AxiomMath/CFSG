module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaE6PatCox
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaE6PatRows
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMember
public import CFSG.LocalAnalysis.StandardType.GGNSJoinRMDefs
public import CFSG.LocalAnalysis.StandardType.GGNSJoinByType
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCubeHolds
import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCube
import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRank
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6

public section

namespace CFSG.StandardType.NSJoin

open CFSG CFSG.Assembly

theorem nsNbr_two_le_n_of_qFour
    (hRig : GGLabelRigidInput)
    {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop} (hNQ4 : NSNbrQFourInputOf T)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hnsL : ¬ GGSplitLie p L) (hguard : NSJoinGuardOf T p L Bs 𝒦) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K)) (hrk : 3 ≤ lab.rank)
    (hdvd : p ∣ 2 ^ lab.n + 1) : 2 ≤ lab.n := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  by_contra h
  simp only [not_le] at h
  have hn_cases : lab.n = 0 ∨ lab.n = 1 := by omega
  rcases hn_cases with h0 | h1
  · rw [h0] at hdvd
    norm_num at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd)
  · rw [h1] at hdvd
    norm_num at hdvd
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd
    subst hp3
    have hQ : GGInnerDiagOnLabel GGLabQFour 3 Bs K :=
      hNQ4 G B Bs x L D J 𝒦 ⟨hcfg, hnsL, hguard⟩ y K hnb
    obtain ⟨lab', hΛ', hhas', R, _, I, F, θ, hS'⟩ := largeEvenMarking_exists_hasLabel hQ
    have hQ4 : 2 ≤ lab'.n := hS'.1
    have hiso : GGLabelIso lab lab' :=
      hRig lab lab' (↥K ⧸ Subgroup.center ↥K) hΛ hΛ' hhas hhas'
    rcases hiso.n_cases with h_eq | ⟨h_tag, h_rank⟩ | h_dbl
    · omega
    · omega
    · omega

theorem nsWeakNbr_orthMarking_typeD
    (hRk : GGTwE6ThreeNbrRankInput) (hNQ4 : NSNbrQFourInputOf (fun {ι} M => NSTypeD M))
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hnsL : ¬ GGSplitLie p L) (hguard : NSJoinGuardOf (fun {ι} M => NSTypeD M) p L Bs 𝒦)
    {K : Subgroup G} (hK : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K) (hns : ¬ GGSplitLie p K)
    (hnU : ¬ GGMemberUnitary p Bs K) :
    GGInnerDiagOnLabel (fun p lab => (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ 2 ≤ lab.n)
      p Bs K := by
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  obtain ⟨hp, hodd⟩ := ggRouteCfg_prime hcfg
  obtain ⟨ι, M, e, hpres, hD, -⟩ := id hguard
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := GGIsWeylMatrixAD.le_three (Or.inr hD)
  obtain ⟨⟨y, hnb⟩, hKA⟩ := id hK
  have hX : K = L ∨ ∃ y, GGNbr p B x D J y K := Or.inr ⟨y, hnb⟩
  have hNP : GGNoReflE6Pat p Bs K := ggX_noReflE6Pat_typeD hcfg hpres hD hKA
  have hq4 : ∀ lab, LargeEvenInLambda2 lab → GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) →
      3 ≤ lab.rank → p ∣ 2 ^ lab.n + 1 → 2 ≤ lab.n := fun lab hΛ hhas hrk hdvd =>
    nsNbr_two_le_n_of_qFour hRig hNQ4 hcfg hnsL hguard hnb hΛ hhas hrk hdvd
  have h5 : p = 3 ∨ 5 ≤ p := by
    by_cases h3 : p = 3
    · exact Or.inl h3
    · exact Or.inr (hp.five_le_of_ne_two_of_ne_three hodd h3)
  have h6 : GGInnerDiagOnLabel (fun p lab =>
      (ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))) ∨
      ((ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ 2 ≤ lab.n) ∨
      (ggRowP_ETwE6 p lab ∧ 5 ≤ p) ∨ (ggRowP_ETwE6 p lab ∧ p = 3) ∨ ggRowP_EE7 p lab ∨
      ggRowP_EE8 p lab ∨ (ggRowP_NF4 p lab ∧ p = 3 ∧ p ∣ 2 ^ lab.n + 1)) p Bs K := by
    refine (ggX_ennola_of_nonSplit hcfg hpres hle3 (Or.inr hK) hns).mono_label_of_hasLabel
      fun lab hΛ hhas h => ?_
    rcases h with (hESU | hOmP | hOmM | hTw | hE7 | hE8) | hF4
    · have hrk : 3 ≤ lab.rank := by
        rcases hESU.1 with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
      have hn := hq4 lab hΛ hhas hrk hESU.2
      exact Or.inl ⟨hESU, fun h => by omega⟩
    · exact Or.inr (Or.inl ⟨Or.inl hOmP,
        hq4 lab hΛ hhas (by have := hOmP.2.1; omega) hOmP.2.2.2⟩)
    · exact Or.inr (Or.inl ⟨Or.inr hOmM,
        hq4 lab hΛ hhas (by have := hOmM.2.1; omega) hOmM.2.2.2⟩)
    · rcases h5 with h3 | h5
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hTw, h3⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨hTw, h5⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE7))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE8)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hF4)))))
  rcases GGInnerDiagOnLabel.elim_or
      (S := fun p lab => ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)))
      h6 with h | h
  · exact absurd h hnU
  rcases GGInnerDiagOnLabel.elim_or
      (S := fun p lab => (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ 2 ≤ lab.n) h with h | h
  · exact h
  exfalso
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_ETwE6 p lab ∧ 5 ≤ p) h with h | h
  · exact ggX_row_absurd_of_noReflE6Pat hRig ggRowE6Pat_ETwE6_ge5 hcfg hX hNP h
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_ETwE6 p lab ∧ p = 3) h with h | h
  ·
    have hLab : GGInnerDiagOnLab GGTableBTwE6ThreeLabel p Bs K := by
      refine largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ?_) h
      obtain ⟨⟨htag, hdvd⟩, hp3⟩ := hP.1
      refine ⟨⟨htag, hp3, hp3 ▸ hdvd⟩, Or.inr (Or.inl ⟨by rw [htag]; exact fun h => h,
        by rw [htag]; simp, hdvd⟩), hP.2.1, hP.2.2⟩
    have hp3 : p = 3 := by
      obtain ⟨lab, -, -, R, _, I, -, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel h
      exact hS.2
    subst hp3
    have hLab' : GGInnerDiagOnLab GGTwE6BadLabel 3 Bs K := hLab
    have hrk : ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G), 3 ^ 5 ≤ Nat.card (ggGamma K hN).range :=
      fun hN => hRk G 3 B Bs x L D J hcfg.1.1 rfl y K hnb hLab' hN
        (ggTorusSelfCent_ggGamma hN hcfg.1.1.2.1.2.2.2)
    exact ggX_row_absurd_of_noReflE6PatAt hRig (by norm_num) ggRowE6PatAt_ETwE6_three hcfg hX hNP
      hrk h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_EE7) h with h | h
  · exact ggX_row_absurd_of_noReflE6Pat hRig ggRowE6Pat_EE7 hcfg hX hNP h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_EE8) h with h | h
  · exact ggX_row_absurd_of_noReflE6Pat hRig ggRowE6Pat_EE8 hcfg hX hNP h
  obtain ⟨-, hp3⟩ : ∃ _ : True, p = 3 := by
    obtain ⟨lab, -, -, R, _, I, -, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel h
    exact ⟨trivial, hS.2.1⟩
  subst hp3
  have hF4 : GGF4ThreeMarking Bs K := by
    refine largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ?_) h
    obtain ⟨⟨htag, -⟩, -, hdvd⟩ := hP.1
    exact ⟨⟨htag, rfl, hdvd⟩, hP.2.1, hP.2.2⟩
  exact ggRow_absurd_F4Three_of_KG1 (ggF4ThreeSCTransvInput_of_cube ggF4ThreeSCCubeInput_holds)
    hcfg hpres hle3 hKA hF4

end CFSG.StandardType.NSJoin

end

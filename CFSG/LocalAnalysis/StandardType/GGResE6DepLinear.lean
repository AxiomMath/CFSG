module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabels
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySplitRefl
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
public import CFSG.LocalAnalysis.StandardType.GGAutomizerGammaCard
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBCard
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBWeyl
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclicHolds
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeAltArith

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Certs

theorem not_splitLinear_of_automizer_card
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (hCP : GGLabelCenterPCyclicInput)
    {X : Subgroup G}
    (hX : X = L ∨ ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧ X = K)
    (hcard : Nat.card ↥(ggAutomizer X Bs) = 51840)
    (hMark : GGInnerDiagOnLabel (fun p lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) p Bs X) :
    False := by
  classical
  have hInnX : GGInnerDiagOn Bs X :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.2.1, h.2.2⟩) hMark
  obtain ⟨hperfX, lab, hΛ, hraw⟩ := hMark
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨R₀, _, I₀, F₀, hs₀, hna₀, θ₀, hS₀, hN₀, hind₀⟩ :=
    largeEvenRawDatum_exists hraw
  have htag : tag = .A := hS₀.1
  subst htag
  have hsplit : p ∣ 2 ^ n - 1 := hS₀.2
  have hCardAll : LargeEvenLabelAll (⟨.A, rank, n⟩ : LargeEvenLabel)
      (fun R _ I _ => ∃ r, GGTorusLift p r R ∧
        GGTorusAutCardSCr p r R I (rank + 1).factorial) :=
    ggNbrTableBCardInput_holds p hp hp2 rank n hΛ hsplit
  have hn1 : 1 ≤ n := by simpa using hΛ.1
  have hn2 : 2 ≤ n := by
    by_contra h
    have hn : n = 1 := by omega
    subst hn
    norm_num at hsplit
    exact hp.ne_one hsplit
  have hSplitLabel : GGNbrSplitLabel p (⟨.A, rank, n⟩ : LargeEvenLabel) :=
    ⟨by simp [LargeEvenUntwisted], hn2, hsplit⟩
  have hWeylAll : LargeEvenLabelAll (⟨.A, rank, n⟩ : LargeEvenLabel)
      (fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I) :=
    ggNbrTableBWeylInputOn_typeA_holds p hp hp2 ⟨.A, rank, n⟩ hΛ rfl
      (GGNbrSplitLabel.halfSplit hSplitLabel) hSplitLabel
  have hBoth := largeEvenLabelAll_and hCardAll hWeylAll
  obtain ⟨R, _, I, F, hbody⟩ :=
    largeEvenRawDatum_exists (hBoth _ hraw)
  obtain ⟨hs, hna, θ, hS, hN', hind⟩ := hbody.1
  obtain ⟨r₀, hlift₀, hcardInner⟩ := hbody.2.1
  obtain ⟨r₁, hlift₁, hweyl₁⟩ := hbody.2.2
  have hBsI : ∀ (b : G) (hb : b ∈ Bs),
      ggLAut X θ ⟨b, hN' hb⟩ ∈ I := fun b hb =>
    ggLAut_mem_of_induces X θ hN' hind hb
  have hTB₀ : GGTorusTBGroup p r₀ R I X (ggQuotHom θ) (ggGamma X hN').range := by
    rcases hX with hXL | ⟨y, K, hnb, hXK⟩
    · subst hXL
      exact ggTorusTBGroup_of_L hcfg hperfX θ hN' hBsI hlift₀
    · subst hXK
      exact ggTorusTBGroup_of_nbr hcfg hnb hperfX θ hN' hBsI hlift₀
  have hTB₁ : GGTorusTBGroup p r₁ R I X (ggQuotHom θ) (ggGamma X hN').range := by
    rcases hX with hXL | ⟨y, K, hnb, hXK⟩
    · subst hXL
      exact ggTorusTBGroup_of_L hcfg hperfX θ hN' hBsI hlift₁
    · subst hXK
      exact ggTorusTBGroup_of_nbr hcfg hnb hperfX θ hN' hBsI hlift₁
  have hInnerCard :
      Nat.card ↥(ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range
        (ggGamma X hN').range) = (rank + 1).factorial :=
    hcardInner X (ggQuotHom θ) (ggGamma X hN').range hTB₀
  have hW : ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range
        (ggGamma X hN').range ≤
      Subgroup.closure (ggTorusReflSet p (ggGamma X hN').range) :=
    hweyl₁ X (ggQuotHom θ) (ggGamma X hN').range hTB₁
  have hZ : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ p := by
    rcases hX with hXL | ⟨y, K, hnb, hXK⟩
    · rw [hXL]
      have hle : Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G) ≤
          Bs ⊓ Subgroup.centralizer (L : Set G) := by
        intro z hz
        exact ⟨hz.1.1, hz.2⟩
      have h := Subgroup.card_le_of_le hle
      rwa [hcfg.card_bstar_inf_centralizer_L] at h
    · rw [hXK] at hInnX ⊢
      exact ggNbr_card_center_le_of_centerPCyclic hCP hcfg hInnX
  have hactual : Nat.card ↥(ggAutomizer X Bs) = (rank + 1).factorial :=
    (card_ggAutomizer_eq_gamma_of_weylReflSet hp hp2 hcfg.tableB_facts.2.1
      hcfg.2.1.2.2.2 hNoTr hN' hZ hW).trans hInnerCard
  have hfact : (rank + 1).factorial = 51840 := by
    rw [← hInnerCard]
    exact hInnerCard.trans (hactual.symm.trans hcard)
  have h5 : 5 ≤ rank + 1 := by
    by_contra h
    have hle : (rank + 1).factorial ≤ (4 : ℕ).factorial :=
      Nat.factorial_le (by omega)
    rw [hfact] at hle
    norm_num at hle
  have hfact' : (rank + 1).factorial = 2 * 25920 := by
    rw [hfact]
  exact (CFSG.HardMathSupport.Curtis.Coordinator.PLType.factorial_ne_51840 h5) hfact'

theorem GGResHyp.not_splitLinear_of_card_automizer_E6
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hcard : Nat.card ↥(ggAutomizer X Bs) = 51840)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs X) :
    False := by
  have hCP : GGLabelCenterPCyclicInput := ggLabelCenterPCyclicInput_holds
  have hX' : X = L ∨ ∃ (y' : G) (K' : Subgroup G), GGNbr 3 B x D J y' K' ∧ X = K' := by
    rcases hX with hXL | hXK
    · exact Or.inl hXL
    · exact Or.inr ⟨y, K, hH.2.2.2.2.1, hXK⟩
  exact not_splitLinear_of_automizer_card Nat.prime_three (by norm_num) hH.1 hH.2.2.2.1
    hCP hX' hcard hMark

end Certs

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBRes
public import Certificates.Certificate13657
import CFSG.LocalAnalysis.StandardType.GGForkA8NotReflHolds
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLabel
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermReflSigma
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniNbrLabel
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseLinLabel
import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMemberNoPair
import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrConj
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylInputHolds
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLabelRows
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMemberAux
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNCells
import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneHolds
import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase
import CFSG.LocalAnalysis.StandardType.GGResNonsingF4Three
import CFSG.LocalAnalysis.StandardType.GGTwE6BadWeyl
import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrHolds
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGResIPumpLineTransfer
import CFSG.LocalAnalysis.StandardType.GGPumpTwExcKnownHolds
import CFSG.LocalAnalysis.StandardType.GGAutomizerGammaCard
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1DSmall
import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
import CFSG.LocalAnalysis.StandardType.GGSignedCoordReflGroup
import CFSG.LocalAnalysis.StandardType.GGResLeaf
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclReal
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNFrame
public import Certificates.Certificate7769

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem card_fix_aPermutationFull {n p : ℕ} (hn : 1 ≤ n) :
    Nat.card {v : Fin n → Multiplicative (ZMod p) // ∀ u ∈ aPermutationFull n p, u v = v} = p := by
  have h := card_fix_aPermutationOn (p := p) (n := n) (I := Finset.univ)
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  rw [aPermutationOn_univ, Finset.card_univ, Fintype.card_fin] at h
  simpa using h

private theorem card_bstar_inf_center_le_of_aPermutationFull {G : Type} [Group G] {p n : ℕ}
    {Bs X : Subgroup G} [Finite ↥Bs] (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hn : 1 ≤ n)
    (hAut : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p) :
    Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ p := by
  refine card_bstar_inf_center_le_of_fixedPoints eta (H := aPermutationFull n p) ?_ ?_
  · rw [← hAut]
  · simpa using (card_fix_aPermutationFull (p := p) (n := n) hn).le

section Label


theorem GGConfig.false_of_twE6Dvd_aPermutationFull {G : Type} [Group G] [Finite G] {p n : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hAK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hp3 : p = 3) {labK : LargeEvenLabel}
    (hKmark : GGInnerDiagOnLabel (fun _ lab => lab = labK) p Bs K)
    (htag : labK.tag = .twE6) (hdiv : 3 ∣ 2 ^ labK.n - 1) : False := by
  subst hp3
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hM := largeEvenMarking_and_labelAll_simple
    (S := fun lab => lab = labK)
    (P' := fun R _ I _ =>
      Subgroup.center R = ⊥ ∧ GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I ∧
        KGA.GGF4AutOrderAt 3 R ∧ GGTorusLift 3 4 R ∧ GGTorusReflGenW 3 4 R I)
    (fun lab hlab heq => by
      subst lab
      exact largeEvenLabelAll_facts_reflGenW_twE6Dvd hlab ⟨htag, hdiv⟩)
    (fun _ _ _ _ _ _ h => h.1) hKmark
  obtain ⟨hKperf, lab, hlab, hraw⟩ := hM
  obtain ⟨R, _, I, F, _, _, θ, hP, hFacts⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, hN, hind⟩ := hP
  obtain ⟨hRZ, _, hout, hAO, hLift, hWR⟩ := hFacts
  have hBs : IsElemAbelian 3 Bs := hcfg.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hBI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces K θ hN hind hb
  have hTB : GGTorusTBGroup 3 4 R I K (ggQuotHom θ) (ggGamma K hN).range :=
    ggTorusTBGroup_of_nbr hcfg hnb hKperf θ hN hBI hLift
  have hInner : Nat.card (ggAutomizer (MulAut.conj : ↥K →* MulAut ↥K).range
      (ggGamma K hN).range) = 1152 :=
    ggPumpTwExc_transport hRZ hout hAO (ggQuotHom θ) (ggQuotHom_surjective θ)
      (by rw [ker_ggQuotHom]) hKperf (ggGamma K hN).range hTB.2.2.2.1
      hTB.2.2.2.2.1 hTB.2.2.2.2.2.1
  have hW : ggAutomizer (MulAut.conj : ↥K →* MulAut ↥K).range
      (ggGamma K hN).range ≤ Subgroup.closure (ggTorusReflSet 3 (ggGamma K hN).range) :=
    hWR K (ggQuotHom θ) (ggGamma K hN).range hTB
  have hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ 3 :=
    card_bstar_inf_center_le_of_aPermutationFull eta (by omega) hAK
  have hActual : Nat.card ↥(ggAutomizer K Bs) = 1152 :=
    (card_ggAutomizer_eq_gamma_of_weylReflSet Nat.prime_three (by norm_num)
      hBs hSC hNoTr hN hZ hW).trans hInner
  have hPerm : Nat.card ↥(ggAutomizer K Bs) = n.factorial :=
    card_ggAutomizer_of_aPermutationFull (p := 3) (by norm_num) (by omega) eta hAK
  have hnf : ∀ {c a : ℕ}, a.factorial < c → c < (a + 1).factorial →
      Nat.card ↥(ggAutomizer K Bs) ≠ c := fun h1 h2 hc =>
    factorial_succ_ne_of_between (k := n - 1) h1 h2
      (by rw [Nat.sub_add_cancel (by omega : 1 ≤ n), ← hPerm, hc])
  exact (hnf (c := 1152) (a := 6) (by norm_num [Nat.factorial])
    (by norm_num [Nat.factorial]) hActual).elim

private theorem permNbr_label_of_cov
    {G : Type} [Group G] [Finite G] {p n : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {y : G} {K : Subgroup G}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hn : 4 ≤ n)
    (hnb : GGNbr p B x D J y K) (hInnK : GGInnerDiagOn Bs K)
    (hcardK : Nat.card ↥(ggAutomizer K Bs) = n.factorial)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K))
    (hfin : ∀ S : ℕ → LargeEvenLabel → Prop, S p lab → GGInnerDiagOnLabel S p Bs K)
    (hcov : GGTBTorCov p lab) :
    GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermLabel n p lab) p Bs K := by
  have : Fact p.Prime := ⟨(ggRouteCfg_prime hR).1⟩
  have hH : GGResHyp p B Bs x L D J y K :=
    ⟨hR.1.1, hR.1.2.1, hR.1.2.2.1, hR.1.2.2.2.1, hnb, hR.2.1 y K hnb, Or.inr hR.2.1⟩
  have hfinOf : ∀ {lab' : LargeEvenLabel}, LargeEvenInLambda2 lab' →
      GGHasLabel lab' (↥K ⧸ Subgroup.center ↥K) →
      ∀ {T : ℕ → LargeEvenLabel → Prop}, T p lab' → GGInnerDiagOnLabel T p Bs K := by
    intro lab' hl hh T hTl
    unfold GGInnerDiagOnLabel
    refine largeEvenMarking_mono ?_ (ggInnerDiagOn_relabel ggLabelRigidInput_holds hInnK hl hh)
    rintro lab'' R _ I F θ ⟨rfl, hQ⟩
    exact ⟨hTl, hQ⟩
  unfold GGTBTorCov at hcov
  obtain ⟨r, m, N, C, M, hrow⟩ := hcov
  have hL : GGInnerDiagOnLabel (fun p lab' => ∃ (r m N : ℕ)
      (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
        GGTBTorRowAt p lab' r m N C M ∧ GGTBTorRowAt p lab r m N C M) p Bs K :=
    hfin _ ⟨r, m, N, C, M, hrow, hrow⟩
  obtain ⟨r', m', N', C', M', hrow', hcardM⟩ :=
    hH.exists_row_card_automizer_K (ggTBTorAll_of_remaining trivial) ggTBTorLiftRows_holds hL
  obtain ⟨t, l, f⟩ := lab
  rcases ggTBTorRowAt_perm_of_card hlab hrow' hn (hcardM ▸ hcardK) with
    hperm | ⟨rfl, hrank3, ⟨htD, hdvd⟩ | ⟨httwD, hdvd⟩⟩
  · exact hfin _ hperm
  · obtain rfl : t = .D := htD
    obtain rfl : l = 3 := hrank3
    exact hfinOf ((Q1DSmall.inLambda2_D3_iff_A3 f).mp hlab)
      (largeEvenRawDatum_of_ggLabelIso (Q1DSmall.labelIso_D3_A3 f) hhas)
      (Or.inl ⟨rfl, rfl, hdvd⟩)
  · obtain rfl : t = .twD := httwD
    obtain rfl : l = 3 := hrank3
    exact hfinOf ((Q1DSmall.inLambda2_twD3_iff_twA3 f).mp hlab)
      (largeEvenRawDatum_of_ggLabelIso (Q1DSmall.labelIso_twD3_twA3 f) hhas)
      (Or.inr ⟨rfl, rfl, hdvd⟩)

private theorem permNbr_label_of_split
    {G : Type} [Group G] [Finite G] {p n : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {y : G} {K : Subgroup G}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hAutK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hnb : GGNbr p B x D J y K) (hInnK : GGInnerDiagOn Bs K)
    (hcardK : Nat.card ↥(ggAutomizer K Bs) = n.factorial)
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K))
    (hfin : ∀ S : ℕ → LargeEvenLabel → Prop, S p lab → GGInnerDiagOnLabel S p Bs K)
    (hweak : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K)
    (hSplit : LargeEvenSplit p lab) (hcov : ¬ GGTBTorCov p lab) :
    GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermLabel n p lab) p Bs K := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  have hNoTr : GGNoTransvection p Bs := hR.1.2.2.2.1
  obtain ⟨t, l, f⟩ := lab
  rcases ggSplit_not_tbTorCov_cases hp hp2 hlab hSplit hcov with hres | hsm | hsp
  · obtain ⟨hp3, hcat⟩ := hres
    subst hp3
    have hnf : ∀ {c a : ℕ}, a.factorial < c → c < (a + 1).factorial →
        Nat.card ↥(ggAutomizer K Bs) ≠ c := fun h1 h2 hc =>
      factorial_succ_ne_of_between (k := n - 1) h1 h2
        (by rw [Nat.sub_add_cancel (by omega : 1 ≤ n), ← hcardK, hc])
    rcases hcat with ⟨ht, hr6, hn1⟩ | ⟨ht, hn1⟩ | ⟨ht, hn1⟩ | ⟨ht, h3dvd⟩ | ⟨ht, hr5, h3dvd⟩
    · have hF : GGRowFrame (fun p lab => lab.tag = .A ∧ 5 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1) :=
        fun p hp' hp2' lab hlab' h =>
          ggNbrFrameInputOne_holds p hp' hp2' lab hlab' (Or.inr (Or.inl h))
      have hNP : GGNoReflFramePair 3 Bs K :=
        ggNoReflFramePair_of_aPermutationFull Nat.prime_three (by norm_num) eta hAutK
      have hA' : GGInnerDiagOnLabel (fun p lab => lab.tag = .A ∧ 5 ≤ lab.rank ∧
          p ∣ 2 ^ lab.n + 1) 3 Bs K := by
        refine GGInnerDiagOnLabel.mono_label (S := fun _ lab =>
          lab.tag = .A ∧ 6 ≤ lab.rank ∧ lab.n = 1) ?_ (hfin _ ⟨ht, hr6, hn1⟩)
        intro lab h
        obtain ⟨h1, h2, h3⟩ := h
        exact ⟨h1, by omega, by rw [h3]; norm_num⟩
      exact (ggX_row_absurd_of_frame_of_noPair ggLabelRigidInput_holds hF hR (Or.inr hweak)
        hNP hA').elim
    · exact (hnf (c := 1152) (a := 6) (by norm_num [Nat.factorial])
        (by norm_num [Nat.factorial])
        (card_ggAutomizer_of_e6Two_nbr hR.1.1 hNoTr hnb (hfin _ ⟨ht, hn1⟩) hZ)).elim
    · have hF4' : GGF4ThreeLabel 3 ⟨t, l, f⟩ := ⟨ht, rfl, by rw [hn1]; norm_num⟩
      exact (hnf (c := 1152) (a := 6) (by norm_num [Nat.factorial])
        (by norm_num [Nat.factorial])
        (card_ggAutomizer_of_f4Three hR.1.1 hNoTr (hfin _ hF4') hZ)).elim
    · exact (hnf (c := 51840) (a := 8) (by norm_num [Nat.factorial])
        (by norm_num [Nat.factorial])
        (card_ggAutomizer_of_twE6Bad_nbr ggLabelRigidInput_holds
          ggTwE6ThreeNbrRankInput_holds hR.1.1 hNoTr hnb hInnK
          (hfin _ ⟨ht, rfl, h3dvd⟩) hZ)).elim
    · have h720 : Nat.card ↥(ggAutomizer K Bs) = 720 :=
        card_ggAutomizer_of_twA5Three_nbr ggLabelRigidInput_holds ggLBalanceInput_holds
          ggStdSubPrimeInput_holds hR.1.1 hnb hInnK hlab hhas ⟨ht, hr5, h3dvd⟩
      have h720' : (6 : ℕ).factorial = 720 := by norm_num [Nat.factorial]
      have hn6 : n = 6 := (Nat.factorial_inj' (Or.inr (by norm_num : 1 < 6))).mp
        ((hcardK.symm.trans h720).trans h720'.symm)
      subst hn6
      exact hfin _ (Or.inr ⟨ht, by omega, h3dvd⟩)
  · exact (ggX_absurd_of_small_halfSplit (c := Subgroup.center ↥K = ⊥) hR (Or.inr hweak)
      (hfin _ ⟨hsm, Or.inl hSplit⟩)).elim
  · exact (ggX_row_absurd_of_pRank ggRowPRankLeTwo_smallPlus hR (Or.inr hweak)
      (hfin _ hsp)).elim

private theorem permNbr_label_of_tagsPlus
    {G : Type} [Group G] [Finite G] {p n : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {K : Subgroup G}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hn : 4 ≤ n)
    (hcardK : Nat.card ↥(ggAutomizer K Bs) = n.factorial)
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p)
    {lab : LargeEvenLabel}
    (hfin : ∀ S : ℕ → LargeEvenLabel → Prop, S p lab → GGInnerDiagOnLabel S p Bs K)
    (htags : lab.tag = .B ∨ lab.tag = .D ∨ lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
    (hplus : p ∣ 2 ^ lab.n + 1) (hcov : ¬ GGTBTorCov p lab) :
    GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermLabel n p lab) p Bs K := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  have hNoTr : GGNoTransvection p Bs := hR.1.2.2.2.1
  have htor : ∀ {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)},
      GGTBTorRowAt p lab r m N C M → False := fun hrow => hcov ⟨_, _, _, _, _, hrow⟩
  have hnf : ∀ {c a : ℕ}, a.factorial < c → c < (a + 1).factorial →
      Nat.card ↥(ggAutomizer K Bs) ≠ c := fun h1 h2 hc =>
    factorial_succ_ne_of_between (k := n - 1) h1 h2
      (by rw [Nat.sub_add_cancel (by omega : 1 ≤ n), ← hcardK, hc])
  rcases htags with hB | hD | hF4 | hE7 | hE8
  · exact (htor (GGTBTorRowAt.c (Or.inl hB) (dvd_mul_of_dvd_right hplus _))).elim
  · by_cases heven : Even lab.rank
    · exact (htor (GGTBTorRowAt.d (Or.inl ⟨hD, Or.inr ⟨hplus, heven⟩⟩))).elim
    · exact (htor (GGTBTorRowAt.relD
        (Or.inl ⟨hD, hplus, Nat.not_even_iff_odd.mp heven⟩))).elim
  · by_cases hp3 : p = 3
    · have hF4' : GGF4ThreeLabel p lab := ⟨hF4, hp3, by simpa only [hp3] using hplus⟩
      exact (hnf (c := 1152) (a := 6) (by norm_num [Nat.factorial])
        (by norm_num [Nat.factorial])
        (card_ggAutomizer_of_f4Three hR.1.1 hNoTr (hfin _ hF4') hZ)).elim
    · exact (htor (GGTBTorRowAt.f4 hF4 (dvd_mul_of_dvd_right hplus _)
        (by rintro ⟨h3, -⟩; exact hp3 h3))).elim
  · exact (htor (GGTBTorRowAt.e7 hE7 (dvd_mul_of_dvd_right hplus _))).elim
  · by_cases hp3 : p = 3
    · exact (htor (GGTBTorRowAt.e8Three hE8 hp3)).elim
    · exact (htor (GGTBTorRowAt.e8Ind hp3 hE8 (dvd_mul_of_dvd_right hplus _))).elim

private theorem permNbr_label_of_tagsMinus
    {G : Type} [Group G] [Finite G] {p n : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {y : G} {K : Subgroup G}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hAutK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hnb : GGNbr p B x D J y K)
    {lab : LargeEvenLabel}
    (hfin : ∀ S : ℕ → LargeEvenLabel → Prop, S p lab → GGInnerDiagOnLabel S p Bs K)
    (htw : (lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)
    (hsub : p ∣ 2 ^ lab.n - 1) (hcov : ¬ GGTBTorCov p lab) :
    GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermLabel n p lab) p Bs K := by
  have htor : ∀ {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)},
      GGTBTorRowAt p lab r m N C M → False := fun hrow => hcov ⟨_, _, _, _, _, hrow⟩
  rcases htw with ⟨htwA, hr5⟩ | htwE6
  · exact (htor (GGTBTorRowAt.relA5 hr5 (Or.inr ⟨htwA, hsub⟩))).elim
  · by_cases hp3 : p = 3
    · exact (GGConfig.false_of_twE6Dvd_aPermutationFull hR.1.1 hR.1.2.2.2.1 hnb hn eta hAutK
        hp3 (hfin (fun _ l => l = lab) rfl) htwE6 (by simpa only [hp3] using hsub)).elim
    · exact (htor (GGTBTorRowAt.relE6 hp3 (Or.inr ⟨htwE6, hsub⟩))).elim

private theorem permNbr_label_of_a5
    {G : Type} [Group G] {p n : ℕ} {Bs : Subgroup G} {K : Subgroup G}
    {lab : LargeEvenLabel}
    (hfin : ∀ S : ℕ → LargeEvenLabel → Prop, S p lab → GGInnerDiagOnLabel S p Bs K)
    (hA : lab.tag = .A) (hr5 : lab.rank = 5) (hp5 : p = 5) (hn2 : lab.n = 2)
    (hcov : ¬ GGTBTorCov p lab) :
    GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermLabel n p lab) p Bs K := by
  have hdvd : p ∣ 2 ^ lab.n + 1 := by rw [hp5, hn2]; norm_num
  exact (hcov ⟨_, _, _, _, _, GGTBTorRowAt.relA5 hr5 (Or.inl ⟨hA, hdvd⟩)⟩).elim

private theorem permNbr_label_of_a8
    {G : Type} [Group G] [Finite G] {p n : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {K : Subgroup G}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hK𝒦 : K ∈ 𝒦)
    {lab : LargeEvenLabel} (hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K))
    (hA : lab.tag = .A) (hr8 : lab.rank = 8) (hn1 : lab.n = 1) (hp7 : p = 7) :
    GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermLabel n p lab) p Bs K := by
  obtain ⟨t, l, f⟩ := lab
  obtain rfl : t = .A := hA
  obtain rfl : l = 8 := hr8
  obtain rfl : f = 1 := hn1
  subst hp7
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hK𝒦
  exact (ggForkNbrSevenExcl'_of_notRefl (ggForkA8NotReflInput_of_mp ggInnerDiagMpInput_holds)
    G B Bs x L D J hR.1.1 hR.1.2.1 hR.1.2.2.1 hR.1.2.2.2.1 y K hnb
    (hR.2.1 y K hnb) hhas).elim

private theorem permNbr_label_of_e6
    {G : Type} [Group G] [Finite G] {p n : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {y : G} {K : Subgroup G}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hnb : GGNbr p B x D J y K)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K))
    (hE6 : lab.tag = .E6) (hn1 : lab.n = 1) (hp7 : p = 7) :
    GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermLabel n p lab) p Bs K := by
  obtain ⟨t, l, f⟩ := lab
  obtain rfl : t = .E6 := hE6
  have hrank : l = 0 := hlab.2
  subst hrank
  obtain rfl : f = 1 := hn1
  subst hp7
  have hH : GGResHyp 7 B Bs x L D J y K :=
    ⟨hR.1.1, hR.1.2.1, hR.1.2.2.1, hR.1.2.2.2.1, hnb, hR.2.1 y K hnb, Or.inr hR.2.1⟩
  exact (hH.false_of_e6_two_seven (by simpa using hhas)).elim

theorem GGSecFiveRouteCfg.permNbr_permLabel {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ} (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {K : Subgroup G} (hK𝒦 : K ∈ 𝒦)
    (hAutK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p) :
    GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermLabel n p lab) p Bs K := by
  classical
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hK𝒦
  have hInnK : GGInnerDiagOn Bs K := hR.1.2.2.1.2 y K hnb
  have hweak : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K := GGSecFiveWeakNbr.of_mem hR hK𝒦
  have hcardK : Nat.card ↥(ggAutomizer K Bs) = n.factorial :=
    card_ggAutomizer_of_aPermutationFull hp2 (by omega) eta hAutK
  have hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p :=
    card_bstar_inf_center_le_of_aPermutationFull eta (by omega) hAutK
  obtain ⟨lab, hlab, hHS, hfin⟩ :=
    ggNbr_exists_halfSplit_innerDiagLabel ggLabelRigidInput_holds ggRawInnFieldInput_holds
      (ggRawInndiagIsoInput_of_rest (ggRawInndiagIsoRestInput_of_round5
        ggRawInndiagIsoRound5_holds)) hR.1.1 hnb hInnK
  have hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) := by
    obtain ⟨lab', -, hhas', R, _, I, F, θ, hlab', -⟩ :=
      largeEvenMarking_exists_hasLabel (hfin (fun _ l => l = lab) rfl)
    rw [hlab'] at hhas'
    exact hhas'
  by_cases hsm : ggRowP_Small p lab
  · exact (ggX_absurd_of_small_halfSplit hR (Or.inr hweak) (hfin _ ⟨hsm, hHS⟩)).elim
  by_cases hcov : GGTBTorCov p lab
  · exact permNbr_label_of_cov hR hn hnb hInnK hcardK hlab hhas hfin hcov
  · rcases hHS with hSplit | ⟨htags, hplus⟩ | ⟨htw, hsub⟩ | ⟨hA5, hr5, hn2, _, hp5⟩ |
      ⟨hA8, hr8, hn1, hp7⟩ | ⟨hE6, hn1, hp7⟩
    · exact permNbr_label_of_split hR hn eta hAutK hnb hInnK hcardK hZ hlab hhas hfin hweak
        hSplit hcov
    · exact permNbr_label_of_tagsPlus hR hn hcardK hZ hfin htags hplus hcov
    · exact permNbr_label_of_tagsMinus hR hn eta hAutK hnb hfin htw hsub hcov
    · exact permNbr_label_of_a5 hfin hA5 hr5 hp5 hn2 hcov
    · exact permNbr_label_of_a8 hR hK𝒦 hhas hA8 hr8 hn1 hp7
    · exact permNbr_label_of_e6 hR hnb hlab hhas hE6 hn1 hp7

end Label

end CFSG.StandardType

end

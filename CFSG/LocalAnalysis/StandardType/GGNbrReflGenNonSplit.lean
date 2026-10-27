module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclicHolds
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRankDefs
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2265
public import Certificates.Certificate2266
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
import CFSG.LocalAnalysis.StandardType.GGExclNoIso
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
import CFSG.LocalAnalysis.StandardType.GGNbrU63
import CFSG.LocalAnalysis.StandardType.GGF4AutWeylTableB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGNbrNonSplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  LargeEvenHalfSplit p lab True ∧ p ∣ (2 ^ lab.n) ^ 2 - 1 ∧ ¬ GGNbrSplitLabel p lab ∧
    ¬ GGTwE6BadLabel p lab

@[expose] def GGNbrTableBWeylNonSplitOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S p lab →
    GGNbrNonSplitLabel p lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
        ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I)

theorem ggF4ThreeNbrWeylInput_holds :
    ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGF4ThreeLabel 3 lab →
      LargeEvenLabelAll lab fun R _ I _ => GGTorusReflGenW 3 4 R I :=
  fun _ hlab h => NbrTableBExc.largeEvenLabelAll_reflGenW_F4_all Nat.prime_three (by norm_num) hlab
    h.1

@[expose] def GGUSixThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ lab.rank = 5 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1

@[expose] def GGUSixThreeNbrRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGNoTransvection p Bs → p = 3 → ∀ (y : G) (K : Subgroup G),
      GGNbr p B x D J y K → GGInnerDiagOnLab GGUSixThreeLabel p Bs K →
        ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
          GGTorusSelfCent 3 (ggGamma K hN).range → 3 ^ 4 ≤ Nat.card (ggGamma K hN).range

@[expose] def GGUSixThreeNbrWeylInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGUSixThreeLabel 3 lab →
    LargeEvenLabelAll lab fun R _ I _ => GGTorusReflGenW 3 4 R I

theorem ggUSixThreeNbrRankInput_of_balance
    (hL : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) : GGUSixThreeNbrRankInput := by
  intro G _ _ p B Bs x L D J hcfg _ hp y K hK hInnL hN _
  subst hp
  refine ggUnitDvd63NbrRankInput_holds hL hPJ G 3 B Bs x L D J hcfg y K hK hN
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ?_) hInnL)
  obtain ⟨⟨ht, hr, -, hd⟩, -, hN', hind⟩ := hP
  exact ⟨⟨⟨ht, by omega, hd, by rw [hr]; norm_num⟩, hr, rfl⟩, hN', hind⟩

theorem eq_of_ggLabelIso_of_twE6 {lab lab' : LargeEvenLabel} (hex : lab.tag = .twE6)
    (h : GGLabelIso lab' lab) : lab' = lab := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨t', r', n'⟩ := lab'
  simp only at hex
  subst hex
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

theorem ggInnerDiagOnLab_of_hasLabel (hRig : GGLabelRigidInput) {G : Type} [Group G]
    {S : ℕ → LargeEvenLabel → Prop} {p : ℕ} {Bs K : Subgroup G} (hInnK : GGInnerDiagOn Bs K)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K)) (hS : S p lab)
    (hsp : LargeEvenSplit p lab) : GGInnerDiagOnLab S p Bs K :=
  largeEvenMarking_mono (fun _ _ _ _ _ _ hP => by
      obtain ⟨rfl, hN, hind⟩ := hP
      exact ⟨hS, hsp, hN, hind⟩)
    (ggInnerDiagOn_relabel hRig hInnK hlab hhas)

theorem exists_innerDiagDatum_of_labelAll_simple (hRig : GGLabelRigidInput) {G : Type} [Group G]
    {Bs K : Subgroup G} (hInnK : GGInnerDiagOn Bs K) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K))
    {P : LargeEvenRawCont} (hP : LargeEvenLabelAll lab (LargeEvenSimpleGuard P))
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    ∃ (R : Type) (_ : Group R) (θ : K ⧸ Subgroup.center K ≃* R) (I F : Set (MulAut R)),
      (∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I) ∧ P R I F := by
  have hmark := ggInnerDiagOn_relabel hRig hInnK hlab hhas
  have hmark' := largeEvenMarking_and_labelAll_simple (S := fun lab' => lab' = lab) (P' := P)
    (fun lab' _ h' => by rw [h']; exact hP) (fun lab' R _ I F θ hPm => hPm.1) hmark
  obtain ⟨-, lab', hlab', hraw'⟩ := hmark'
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, hN', hind⟩, hPP⟩⟩ := largeEvenRawDatum_exists hraw'
  refine ⟨R, ‹Group R›, θ, I, F, fun b hb => ?_, hPP⟩
  obtain ⟨φ, hφI, hindφ⟩ := hind b⁻¹ (Bs.inv_mem hb)
  have hφeq : φ = ggLAut K θ ⟨b⁻¹⁻¹,
      (Subgroup.normalizer (K : Set G)).inv_mem (hN' (Bs.inv_mem hb))⟩ :=
    eq_ggLAut_of_induces K θ (hN' (Bs.inv_mem hb)) hindφ
  have hb_eq : (⟨b⁻¹⁻¹, (Subgroup.normalizer (K : Set G)).inv_mem
      (hN' (Bs.inv_mem hb))⟩ : Subgroup.normalizer (K : Set G)) = ⟨b, hN hb⟩ :=
    Subtype.ext (inv_inv b)
  rw [hφeq, hb_eq] at hφI
  exact hφI

theorem exists_nonSplitLabel_of_nbr
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (h : GGSecFiveRestHyp p B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K)
    (hns : ¬ LargeEvenMarking ↥K (fun lab _ _ _ _ _ => GGNbrSplitLabel p lab))
    (hq : LargeEvenMarking ↥K
      (fun lab _ _ _ _ _ => p ∣ (2 ^ lab.n) ^ 2 - 1 ∧ ¬ GGTwE6BadLabel p lab)) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) ∧
      GGNbrNonSplitLabel p lab := by
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hiso : GGRawInndiagIsoInput :=
    ggRawInndiagIsoInput_of_rest (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds)
  obtain ⟨lab, hlab, hhas, -, -, -, -, -, hHS⟩ := largeEvenMarking_exists_hasLabel
    (ggNbr_halfSplit_of_secFiveRest ggRawInnFieldInput_holds hiso h hK)
  have hdvd : p ∣ (2 ^ lab.n) ^ 2 - 1 :=
    ggHalfSplit_dvd_of_marking hRig hlab hhas hHS
      (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => by exact hP.1) hq)
  refine ⟨lab, hlab, hhas, largeEvenHalfSplit_true hHS, hdvd, fun hsp => hns ?_, fun hbad => ?_⟩
  · exact largeEvenMarking_mono (fun _ _ _ _ _ _ hP => by rw [hP.1]; exact hsp)
      (ggInnerDiagOn_relabel hRig (h.2.2.1.2 y K hK) hlab hhas)
  · obtain ⟨labq, hlq, hhq, -, -, -, -, -, -, hnb⟩ := largeEvenMarking_exists_hasLabel hq
    exact hnb (eq_of_ggLabelIso_of_twE6 hbad.1 (hRig labq lab _ hlq hlab hhq hhas) ▸ hbad)

theorem ggNbrReflGenNonSplitInput_of_weyl
    (hW : GGNbrTableBWeylNonSplitOn fun p lab =>
      ¬ GGF4ThreeLabel p lab ∧ ¬ GGUSixThreeLabel p lab)
    (hF4R : GGF4ThreeNbrRankInput) (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hU6W : GGUSixThreeNbrWeylInput) :
    GGNbrReflGenNonSplitInput := by
  intro G _ _ p B Bs x L D J h y K hK hns hq
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hcfg : GGConfig p B Bs x L D J := h.1
  have hNoTr : GGNoTransvection p Bs := h.2.2.2.1
  have hInnK : GGInnerDiagOn Bs K := h.2.2.1.2 y K hK
  have hZK := ggNbrBstarCenterInput_of_centerPCyclic ggLabelCenterPCyclicInput_holds
    G p B Bs x L D J h y K hK
  obtain ⟨-, -, -, -, -, -, -, -, hN, -⟩ := largeEvenMarking_exists_hasLabel hInnK
  obtain ⟨lab, hlab, hhas, hns'⟩ := exists_nonSplitLabel_of_nbr h hK hns hq
  by_cases hF4 : GGF4ThreeLabel p lab
  ·
    obtain rfl : p = 3 := hF4.2.1
    have hInnL : LargeEvenMarking ↥K (fun lab' _ _ I _ θ => GGF4ThreeLabel 3 lab' ∧
        Bs ≤ Subgroup.normalizer (K : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :=
      largeEvenMarking_mono (fun _ _ _ _ _ _ hP => by
          obtain ⟨rfl, hN', hind⟩ := hP
          exact ⟨hF4, hN', hind⟩)
        (ggInnerDiagOn_relabel hRig hInnK hlab hhas)
    obtain ⟨R, _, θ, I, F, hBsI, hWR⟩ :=
      exists_innerDiagDatum_of_labelAll hRig hInnK hlab hhas
        (ggF4ThreeNbrWeylInput_holds lab hlab hF4) hN
    exact ggReflGenerated_of_ggTorusReflGenW_card hcfg (by norm_num) hNoTr hK hInnK.1 θ hN hBsI
      (hF4R G 3 B Bs x L D J hcfg hNoTr rfl y K hK hInnL hN
        (ggTorusSelfCent_ggGamma hN hcfg.2.1.2.2.2)) hWR hZK
  by_cases hU6 : GGUSixThreeLabel p lab
  ·
    obtain rfl : p = 3 := hU6.2.2.1
    have hInnL := ggInnerDiagOnLab_of_hasLabel hRig hInnK hlab hhas hU6
      (Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted, hU6.1], by simp [hU6.1], hU6.2.2.2⟩))
    obtain ⟨R, _, θ, I, F, hBsI, hWR⟩ :=
      exists_innerDiagDatum_of_labelAll hRig hInnK hlab hhas (hU6W lab hlab hU6) hN
    exact ggReflGenerated_of_ggTorusReflGenW_card hcfg (by norm_num) hNoTr hK hInnK.1 θ hN hBsI
      (ggUSixThreeNbrRankInput_of_balance hL hPJ G 3 B Bs x L D J hcfg hNoTr rfl y K hK hInnL hN
        (ggTorusSelfCent_ggGamma hN hcfg.2.1.2.2.2)) hWR hZK
  obtain ⟨R, _, θ, I, F, hBsI, r, hlift, hT⟩ := exists_innerDiagDatum_of_labelAll_simple hRig hInnK
    hlab hhas (hW p hcfg.1.2.2.2.2.2.1.1 hcfg.1.2.2.2.2.2.1.2.1 lab hlab ⟨hF4, hU6⟩ hns') hN
  exact ggReflGenerated_of_ggTorusReflGenW hcfg hNoTr hK hInnK.1 θ hN hBsI hlift hT hZK

end CFSG.StandardType

end

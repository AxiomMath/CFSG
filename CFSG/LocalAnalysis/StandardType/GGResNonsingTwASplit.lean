module

public import CFSG.LocalAnalysis.StandardType.GGResJTwE6Lagrange
public import CFSG.LocalAnalysis.StandardType.GGResThreeSettledDefs
public import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameW
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclic
import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitOddE
import CFSG.LocalAnalysis.StandardType.GGPZWeylB
import CFSG.LocalAnalysis.StandardType.GGTBRowFrame
import CFSG.LocalAnalysis.StandardType.GGTBJWeyl
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySplitRefl
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
import CFSG.LocalAnalysis.StandardType.GGNbrTableBExcInduced
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

section Frame


theorem ggTwASplit_recipe_signedFrameW {d n p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n - 1)
    (hn : 1 ≤ n) (hd : 6 ≤ d) {Q : LargeEvenRawCont} (hQ : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F => Q R I F ∧ ∃ r, 3 ≤ r ∧
      GGTorusLift p r R ∧ GGTorusSignedFrameW p r R {φ | φ ∈ I ∧ φ ^ p = 1} := by
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpq
  have : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hK
  have hpq' : ¬ p ∣ 2 ^ n + 1 := not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
  have hd3 : 3 ≤ d := by omega
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun h => by
    have := congrArg Prod.fst h
    simp only at this
    omega
  have hZ := TableBUE.center_proj_eq_bot hK hd3 hdq
  have hIp : GGOutdiagPrime p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) :=
    fun φ hφ hφp =>
      NbrInnerMore.ggOutdiagPrime_unitary_of_not_dvd hK hn hd3
        (fun h => hdq (Prod.ext h.1 h.2)) hp hpq' φ hφ hφp
  obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' d
  · exact ⟨r, by omega, ggTorusLift_unitarySplit_even hK hn (by omega) hp hp2 hpq,
      ggTorusSignedFrameW_of_signedElt hp hp2 (fun φ hφ => hIp φ hφ.1 hφ.2) hZ
        (ggTorusSignedElt_unitary_split_even hK hn (by omega) hp hp2 hpq)⟩
  · exact ⟨r, by omega, ggTorusLift_unitarySplit_odd hK hn (by omega) hp hp2 hpq,
      ggTorusSignedFrameW_of_signedElt hp hp2 (fun φ hφ => hIp φ hφ.1 hφ.2) hZ
        (ggTorusSignedElt_unitary_split_odd hK hn (by omega) hp hp2 hpq)⟩

theorem largeEvenLabelAll_signedFrameW_twASplit {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTwASplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, 3 ≤ r ∧ GGTorusLift p r R ∧
      GGTorusSignedFrameW p r R {φ | φ ∈ I ∧ φ ^ p = 1} := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpn⟩ := h
  dsimp only at ht hl hpn
  subst ht
  intro Q hQ
  exact ggTwASplit_recipe_signedFrameW (d := l + 1) hp hpn hlab.1 (by omega) hQ

theorem card_ggAutomizer_of_twASplit {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hNoTr : GGNoTransvection p Bs) {X : Subgroup G} {y : G}
    (hXo : X = L ∨ GGNbr p B x D J y X) (hX : GGInnerDiagOnLabel GGTwASplitLabel p Bs X)
    (hZ : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ p) :
    ∃ k : ℕ, 3 ≤ k ∧ Nat.card ↥(ggAutomizer X Bs) = 2 ^ k * k.factorial := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hM := largeEvenMarking_and_labelAll (S := GGTwASplitLabel p)
    (P' := fun R _ I _ => ∃ r, 3 ≤ r ∧ GGTorusLift p r R ∧
      GGTorusSignedFrameW p r R {φ | φ ∈ I ∧ φ ^ p = 1})
    (fun _ hlab h => largeEvenLabelAll_signedFrameW_twASplit hp hlab h)
    (fun _ _ _ _ _ _ hP => hP.1) hX
  obtain ⟨hperf, lab, -, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hN, hind⟩, r, -, hlift, hF⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hN hind hb
  have hTB : GGTorusTBGroup p r R I ↥X (ggQuotHom θ) (ggGamma X hN).range := by
    rcases hXo with rfl | hnb
    · exact ggTorusTBGroup_of_L hcfg hperf θ hN hBsI hlift
    · exact ggTorusTBGroup_of_nbr hcfg hnb hperf θ hN hBsI hlift
  obtain ⟨k, hk, -, hFr⟩ := hF ↥X (ggQuotHom θ) (ggGamma X hN).range
    (NbrTableBExc.ggTorusTBGroup_pow hTB)
  obtain ⟨e, -⟩ := ggWeylOfType_of_frame hp hp2 hBs hSC hNoTr hN hZ hFr
  exact ⟨k, hk, by rw [← Nat.card_congr e.toEquiv, ggCoxeterB_card k (by omega)]⟩

end Frame

theorem ggResNonsingAut_of_twASplit {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    (hX : GGInnerDiagOnLabel GGTwASplitLabel p Bs X)
    (hc : ∃ k : ℕ, 3 ≤ k ∧ Nat.card ↥(ggAutomizer X Bs) = 2 ^ k * k.factorial) :
    GGResNonsingAut p Bs X := by
  obtain ⟨k, hk, hc⟩ := hc
  refine ⟨?_, fun hp3 _ _ _ _ => ?_⟩
  · rw [hc]
    rintro (⟨j, -, -, hj⟩ | ⟨-, hj⟩)
    · exact factorial_succ_ne_two_pow_mul_factorial (by omega) hj.symm
    · exact two_pow_mul_factorial_ne_E6 (by omega) hj
  · obtain ⟨lab, hΛ, hhas, _, _, _, _, _, ⟨htag, -, hpn⟩, -⟩ :=
      largeEvenMarking_exists_hasLabel hX
    refine ⟨lab, hΛ, hhas, ggTwE6ThreeFreeLabel_of_twA_even htag ?_⟩
    subst hp3
    obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' lab.n
    · exact ⟨m, hm⟩
    · exfalso
      have e : 2 ^ lab.n = 2 * 4 ^ m := by
        rw [hm, pow_succ, pow_mul, mul_comm]
        norm_num
      have h4 : 3 ∣ 4 ^ m - 1 := by
        have h := Nat.sub_dvd_pow_sub_pow 4 1 m
        rw [one_pow] at h
        exact h
      have h1 : 0 < 4 ^ m := by positivity
      rw [e] at hpn
      omega

section Exclusion


theorem ggResExact3_false_of_twASplit_L (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) (hP : GGStdSubPrimeInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {S : ℕ → LargeEvenLabel → Prop} (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel S p Bs J) (hL : GGInnerDiagOnLabel GGTwASplitLabel p Bs L)
    (hD : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) : False :=
  ggResExact3_false_of_nonsingAut_L hT hLift hTCJ hRig hP hH hJ
    (ggResNonsingAut_of_twASplit hL (card_ggAutomizer_of_twASplit hH.1 hH.2.2.2.1 (y := y)
      (Or.inl rfl) hL (card_bstar_inf_center_le hH.1))) hD

theorem ggResExact3_false_of_twASplit_K (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hcyc : GGLabelCenterPCyclicInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} {S : ℕ → LargeEvenLabel → Prop} (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel S p Bs J) (hK : GGInnerDiagOnLabel GGTwASplitLabel p Bs K)
    (hD : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) : False :=
  ggResExact3_false_of_nonsingAut_K hT hLift hTCJ hRig hLB hP hH hJ
    (ggResNonsingAut_of_twASplit hK (card_ggAutomizer_of_twASplit hH.1 hH.2.2.2.1
      (Or.inr hH.2.2.2.2.1) hK
      (ggNbr_card_center_le_of_centerPCyclic hcyc hH.1 (hH.2.2.1.2 y K hH.2.2.2.2.1)))) hD

end Exclusion

end CFSG.StandardType

end

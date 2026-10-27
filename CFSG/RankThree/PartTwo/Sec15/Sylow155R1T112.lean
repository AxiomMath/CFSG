module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1BarDefs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1PtDefs
public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofGen
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T114
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1V
import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofMaxT
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
import CFSG.RankThree.PartTwo.Sec16.Item16Res4ProofA7
import CFSG.RankThree.PartTwo.Sec16.Item16Res4ProofGenPGL
import CFSG.RankThree.PartTwo.Sec17.Item171GenProofA7
import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaTools

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCoreOf_two_host_le_n155_of_not_le {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L) (h146 : Item146 A (lB A)) (h149 : Item149 A (lB A))
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hab : Above155w A X)
    (hE : End155N A X K Y M T P) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hOA : pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      Subgroup.centralizer (A : Set G))
    (hLX : ¬ L ≤ X) (hL3 : L ≤ oPrimeResidualOf 3 L) (hLΔ : L ≤ delta A (lB A) L)
    (hLK : L ≤ K) (hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K)
    (hUK : CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 K) :
    pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      n155 A K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : Sec14Std G A c L := hR.toSec14Std
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hK4 : K ∈ scriptY4 A (lB A) := hC.mem_k.prop.1
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := h.mem_lA.2.1
  have hX'K : X ⊔ L ≤ K := sup_le hC.le_k hLK
  have hX'top : X ⊔ L ≠ ⊤ := fun htop => hK4.1.1 (top_le_iff.mp (htop ▸ hX'K))
  have hAX' : A ≤ Subgroup.normalizer ((X ⊔ L : Subgroup G) : Set G) :=
    Sec14.le_normalizer_sup hX4.1.2 hAL
  have hX'3 : oPrimeResidualOf 3 (X ⊔ L) = X ⊔ L :=
    le_antisymm (Sec14.oPrimeResidualOf_le_self 3 _)
      (sup_le (hX4.2.1.le.trans (Sec15.oPrimeResidualOf_mono 3 le_sup_left))
        (hL3.trans (Sec15.oPrimeResidualOf_mono 3 le_sup_right)))
  have hX'Δ : X ⊔ L = delta A (lB A) (X ⊔ L) :=
    le_antisymm (sup_le (hX4.2.2.1.le.trans (delta_mono le_sup_left))
      (hLΔ.trans (delta_mono le_sup_right))) (delta_le _)
  have hKX' : K = (X ⊔ L) ⊔ CFSG.Open.pCoreOf 2 K :=
    le_antisymm (hKL.le.trans (sup_le_sup_right le_sup_right _))
      (sup_le hX'K (CFSG.LieType.BorelTits.pCoreOf_le 2 K))
  obtain ⟨e⟩ := Proof155R2.isoQuot_of_le_sup hX'K hKX'.le
    (hX'K.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K))
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K)
  have hX'4 : X ⊔ L ∈ scriptY4 A (lB A) :=
    ⟨⟨hX'top, hAX'⟩, hX'3.symm, hX'Δ,
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hK4.2.2.2⟩
  have hU1 : CFSG.Open.pCoreOf 2 X ≠ ⊥ :=
    (isCharacteristicP_x_and_pCoreOf_ne_bot h h149 hC hIX).2
  have hnorm : X ⊔ L ≤
      Subgroup.normalizer (((X ⊔ L) ⊓ CFSG.Open.pCoreOf 2 K : Subgroup G) : Set G) := by
    intro x hx
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx)
    have h2 := Subgroup.mem_normalizer_iff.mp
      ((hX'K.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)) hx)
    exact Subgroup.mem_normalizer_iff.mpr fun g => by
      simp only [SetLike.mem_coe, Subgroup.mem_inf] at h1 h2 ⊢
      exact and_congr (h1 g) (h2 g)
  have hI : (X ⊔ L) ⊓ CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 (X ⊔ L) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K).to_le inf_le_right)
  have hO2 : CFSG.Open.pCoreOf 2 (X ⊔ L) ≠ ⊥ := fun h0 => hU1 (le_bot_iff.mp (h0 ▸
    (le_inf ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans le_sup_left) hUK).trans hI))
  have hY : IsY155 A (X ⊔ L) := by
    refine ⟨⟨⟨⟨hX'top, hAX'⟩, hO2⟩, hX'Δ⟩, ?_, ?_⟩
    · rw [hX'3]
      exact hX'4
    · rw [hX'3]
      exact (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 (X ⊔ L))).symm
  have hlt : X < oPrimeResidualOf 3 (X ⊔ L) := by
    rw [hX'3]
    exact lt_of_le_of_ne le_sup_left fun heq => hLX (heq ▸ le_sup_right)
  obtain ⟨M', hle, hM'⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge
    (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (X ⊔ L)) hO2)
  have hM'mem : M' ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ (X ⊔ L) : Subgroup G) : Set G) :=
    ⟨hM', fun x hx => hle ((sup_le (hAX'.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (X ⊔ L)))
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ L))) hx)⟩
  have hΓ : K ∈ gam155 A (lB A) (X ⊔ L) (oPrimeResidualOf 3 (X ⊔ L)) := by
    rw [hX'3]
    exact ⟨hC.mem_k, hX'K, hX'K.trans Subgroup.le_normalizer⟩
  have hhyp : omg155 A (oPrimeResidualOf 3 (X ⊔ L)) ∨
      K = oPrimeResidualOf 3 (X ⊔ L) ⊔ CFSG.Open.pCoreOf 2 K := by
    rw [hX'3]
    exact Or.inr hKX'
  have hΔ := (hab (X ⊔ L) hY hlt).2 K hΓ hhyp M' hM'mem
  have hOX : pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)))
      ≤ Subgroup.normalizer (X : Set G) :=
    ((pPrimeCoreOf_two_host_le_centralizer h h146 h149 hC hE hRP hIX).trans
      (Subgroup.centralizer_le fun x hx => x_le_oPrimeResidualOf_delta hC hx)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hOL : pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)))
      ≤ Subgroup.normalizer (L : Set G) :=
    (hOA.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr h.toSec13Data.mem_A))).trans
      (Sec17.Sec15R.centralizer_le_normalizer_L hR (Sec16.Proof1613.three_dvd_card_L h))
  have hOM' : pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)))
      ≤ M' :=
    ((Sec14.le_normalizer_sup hOX hOL).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (X ⊔ L))).trans hle
  exact (le_delta (pPrimeCoreOf_two_host_mem_scriptQ h h146 hC hE hRP) hOM').trans hΔ

@[expose] def Res1L112In (Q : ∀ (X : Type) [Group X], Prop) (P : ∀ (Y : Type) [Group Y], Prop) :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
    Sec14Std G A c L → ∀ X K Y M T P' : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → End155N A X K Y M T P' → Item146 A (lB A) →
    CFSG.Open.pCoreOf 2 Y ≤ P' →
    delta A (lB A) M ≤ Subgroup.normalizer (X : Set G) →
    ∀ Yc : Subgroup (Res1Q A L), Res1AtOf A c L M Yc → IsSimpleGroup ↥Yc → P ↥Yc →
    layerOddPreimage (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      Subgroup.centralizer (A : Set G) →
    layerOddPreimage (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) =
      pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) →
    (∀ u : ↥(Res1C A L), (u : G) ∈
        pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) →
      (∀ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u * y =
        y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u) → u = 1) →
    (∃ x : ↥(Res1C A L),
      (x : G) ∈ CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer (A : Set G) ∧
        ∃ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x * y ≠
          y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x) →
    ¬ L ≤ X →
      L ≤ delta A (lB A) L ∧ L ≤ K ∧ K = L ⊔ CFSG.Open.pCoreOf 2 K ∧
        CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 K

theorem step155HostE0WRes1TypeFBarNotLe_of_in
    (h149 : Sec16.Item149S14)
    {Q : ∀ (X : Type) [Group X], Prop} {P : ∀ (Y : Type) [Group Y], Prop}
    (hin : Res1L112In Q P) : Step155HostE0WRes1TypeFBarNotLe Q P := by
  intro G _ _ A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
    hEA hEO hcomm hfield hLX
  obtain ⟨hLΔ, hLK, hKL, hUK⟩ := hin G A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP
    hIX Yc hY hsimple hP hEA hEO hcomm hfield hLX
  exact pPrimeCoreOf_two_host_le_n155_of_not_le hR h146 (h149 G A c L hS) hC
    habove hE hRP hIX (hEO.symm.le.trans hEA) hLX (Sec16.eq_oPrimeResidualOf_of_sec15R hR).le hLΔ
    hLK hKL hUK

theorem le_delta_of_a7 {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L)
    (h142 : Concl142 A (lB A))
    (h7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))) :
    L ≤ delta A (lB A) L :=
  (Sec16.Proof163L4A7.eq_delta_of_gen' hR h142
    (Sec17.Proof171Gen.le_sSup_invariantPiSubgroups_of_sec13Data hR.toSec13Data h7)).le

theorem le_delta_of_gen {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L)
    (h142 : Concl142 A (lB A))
    (hgen : sSup {Z : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) | ¬ 3 ∣ Nat.card Z ∧
      ∀ σ ∈ Sec4.autThetaQuot A L, Z.map σ.toMonoidHom ≤ Z} = ⊤) :
    L ≤ delta A (lB A) L :=
  (Sec16.Proof163L4A7.eq_delta_of_gen' hR h142
    (Sec16.Proof1612PGL.le_sSup_of_autThetaQuot hR.toSec13Data.le_normalizer hgen)).le

theorem le_delta_of_m22 (h22 : Step142LowerGenM22) {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L) (h142 : Concl142 A (lB A))
    (hM : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    L ≤ delta A (lB A) L :=
  le_delta_of_gen hR h142 (h22 G A c L hR.toSec14Std hM)

theorem le_delta_of_j2 (hHJ : Step142LowerGenHJ) {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L) (h142 : Concl142 A (lB A))
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    L ≤ delta A (lB A) L :=
  le_delta_of_gen hR h142 (hHJ G A c L hR.toSec14Std hJ)

theorem le_delta_of_lThreePi (hL3g : Step142LowerGenL3) {A : Subgroup G} {c : G}
    {L : Subgroup G} (hR : Sec15R G A c L) (h142 : Concl142 A (lB A))
    (hL3 : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (h34 : ¬ Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2))) :
    L ≤ delta A (lB A) L :=
  le_delta_of_gen hR h142 (hL3g G A c L hR.toSec14Std hL3 h34)

@[expose] def Res1L112InPt
    (Pt : ∀ (G : Type) [Group G] [Finite G], Subgroup G → G → Subgroup G → Prop)
    (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Pt G A c L →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
    Sec14Std G A c L → ∀ X K Y M T P' : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → End155N A X K Y M T P' → Item146 A (lB A) →
    CFSG.Open.pCoreOf 2 Y ≤ P' →
    delta A (lB A) M ≤ Subgroup.normalizer (X : Set G) →
    ∀ Yc : Subgroup (Res1Q A L), Res1AtOf A c L M Yc → IsSimpleGroup ↥Yc → P ↥Yc →
    layerOddPreimage (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      Subgroup.centralizer (A : Set G) →
    layerOddPreimage (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) =
      pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) →
    (∀ u : ↥(Res1C A L), (u : G) ∈
        pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) →
      (∀ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u * y =
        y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u) → u = 1) →
    (∃ x : ↥(Res1C A L),
      (x : G) ∈ CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer (A : Set G) ∧
        ∃ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x * y ≠
          y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x) →
    ¬ L ≤ X →
      L ≤ delta A (lB A) L ∧ L ≤ K ∧ K = L ⊔ CFSG.Open.pCoreOf 2 K ∧
        CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 K

theorem step155HostE0WRes1TypeFPt_of_le_of_in
    (h149 : Sec16.Item149S14)
    {Q : ∀ (X : Type) [Group X], Prop}
    {Pt : ∀ (G : Type) [Group G] [Finite G], Subgroup G → G → Subgroup G → Prop}
    {P : ∀ (Y : Type) [Group Y], Prop}
    (hPQ : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Pt G A c L → Q (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hle : Step155HostE0WRes1TypeFBarLe Q P) (hin : Res1L112InPt Pt P) :
    Step155HostE0WRes1TypeFPt Pt P := by
  intro G _ _ A c L hR hPt hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
    hEA hEO hcomm hfield
  by_cases hLX : L ≤ X
  · exact hle G A c L hR (hPQ G A c L hPt) hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc
      hY hsimple hP hEA hEO hcomm hfield hLX
  · obtain ⟨hLΔ, hLK, hKL, hUK⟩ := hin G A c L hR hPt hN hS X K Y M T P' hC hmax habove hE h146
      hRP hIX Yc hY hsimple hP hEA hEO hcomm hfield hLX
    exact pPrimeCoreOf_two_host_le_n155_of_not_le hR h146 (h149 G A c L hS) hC
      habove hE hRP hIX (hEO.symm.le.trans hEA) hLX (Sec16.eq_oPrimeResidualOf_of_sec15R hR).le
      hLΔ hLK hKL hUK

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1

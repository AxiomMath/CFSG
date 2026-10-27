module

import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec4.T444.Lift
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec15.Item152ConfAProofD
public import CFSG.RankThree.PartTwo.Sec15.Item152ConfAProofP
public import CFSG.RankThree.PartTwo.Sec15.Item152ConfAProofTheta
public import CFSG.RankThree.PartTwo.Sec15.Item152ResProofPS
public import CFSG.RankThree.PartTwo.Sec15.Item152ResProofW
public import CFSG.RankThree.PartTwo.Sec15.Item152StepsEnd
public import CFSG.RankThree.PartTwo.Sec15.Item15No135

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

namespace Proof152Res2

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_sup_pCoreOf_eq {X P : Subgroup G} (hPX : P ≤ X)
    (hXN : X ≤ Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G)) :
    CFSG.Open.pCoreOf 2 (P ⊔ CFSG.Open.pCoreOf 2 X) = CFSG.Open.pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 X with hO
  have hOX : O ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hXO : X ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  apply le_antisymm
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le hPX hOX)) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact hXN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right
      (sup_le (hPX.trans hXO) Subgroup.le_normalizer)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)

theorem normalizer_sup_le_normalizer_pCoreOf {X P : Subgroup G} (hPX : P ≤ X)
    (hXN : X ≤ Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G)) :
    Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) := by
  have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2
    (P ⊔ CFSG.Open.pCoreOf 2 X)
  rwa [pCoreOf_sup_pCoreOf_eq hPX hXN] at h

theorem pCoreOf_le_pCoreOf_normalizer {X P : Subgroup G} (hPX : P ≤ X)
    (hXN : X ≤ Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G)) :
    CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2
      (Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXN)
    (normalizer_sup_le_normalizer_pCoreOf hPX hXN)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)

theorem normalizer_le_normalizer_sup_pCoreOf {X P : Subgroup G} (hPX : P ≤ X)
    (hXN : X ≤ Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G)) :
    Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2
        (Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G)) :
          Subgroup G) : Set G) := by
  set K := Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G) with hK
  have heq : P ⊔ CFSG.Open.pCoreOf 2 K =
      (P ⊔ CFSG.Open.pCoreOf 2 X) ⊔ CFSG.Open.pCoreOf 2 K := by
    rw [sup_assoc, sup_eq_right.mpr (pCoreOf_le_pCoreOf_normalizer hPX hXN)]
  rw [heq]
  exact Sec14.le_normalizer_sup le_rfl (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)

theorem normal_sup_pCoreOf_normalizer {X P : Subgroup G} (hPX : P ≤ X)
    (hXN : X ≤ Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G)) :
    ((P ⊔ CFSG.Open.pCoreOf 2
        (Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G))).subgroupOf
      (Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G))).Normal := by
  set K := Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G) with hK
  have hPK : P ≤ K := hPX.trans hXN
  have hle : P ⊔ CFSG.Open.pCoreOf 2 K ≤ K := sup_le hPK (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
    (normalizer_le_normalizer_sup_pCoreOf hPX hXN)

theorem le_normalizer_sup_pCoreOf_normalizer {X P : Subgroup G} (hPX : P ≤ X)
    (hXN : X ≤ Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G)) :
    X ≤ Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2
        (Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G)) :
          Subgroup G) : Set G) :=
  hXN.trans (normalizer_le_normalizer_sup_pCoreOf hPX hXN)

theorem false_of_le_normalizer {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {Y M X : Subgroup G} (hctx : Ctx152 A LB Y M X) {c' : G} {L' : Subgroup G} {d : G} {p : ℕ}
    {P T K S : Subgroup G} (hD : Data152 A LB X c' L' d p P T K S)
    (hSH : S ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G) ∈
      scriptQPiStar A LB (Subgroup.normalizer (Subgroup.zpowers c' : Set G)) (piOf 2))
    (hLJ : L' ≤ (S ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G)) ⊔ X)
    (hXN : X ≤ Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 K : Subgroup G) : Set G))
    (hAct : KS152HJAct) (hCover : Step152EndCover A LB) : False := by
  have : Fact p.Prime := ⟨hD.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCoreOf 2 K with hQ
  have hPp : IsPGroup p P := by
    rcases hD.type_p with ⟨-, h⟩ | ⟨-, h⟩
    · exact IsPGroup.of_card h
    · exact IsPGroup.of_card h
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hPK : P ≤ K := le_sup_right.trans hD.le_k
  have hPQK : P ⊔ Q ≤ K := sup_le hPK (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
  have hKN : K ≤ Subgroup.normalizer ((P ⊔ Q : Subgroup G) : Set G) :=
    Sec4.le_normalizer_of_subgroupOf_normal hPQK hD.normal_pk
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hQeq : CFSG.Open.pCoreOf 2 (P ⊔ Q) = Q := by
    apply le_antisymm
    · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hPQK) ?_
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
      exact hKN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
    · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right
        (sup_le (hPK.trans hKQ) Subgroup.le_normalizer) hQ2
  have hNQ : Subgroup.normalizer ((P ⊔ Q : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Q : Set G) := by
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (P ⊔ Q)
    rwa [hQeq] at h
  have hSN : S ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G) ≤
      Subgroup.normalizer ((P ⊔ Q : Subgroup G) : Set G) :=
    inf_le_left.trans (hD.mem_sk.prop.1.2.trans hKN)
  have hL'N : L' ≤ Subgroup.normalizer ((P ⊔ Q : Subgroup G) : Set G) :=
    hLJ.trans (sup_le hSN hXN)
  have hL'p : Group.IsPerfect ↥L' := isPerfect_of_mem_thetaComponentsIn hD.mem_lA.1
  have hact := hAct G L' P Q p hD.prime hD.odd hL'p hD.hj hQ2 (hPK.trans hKQ) hD.type_p hL'N
    (hL'N.trans hNQ)
  apply hCover Y M X hctx c' L' d p P T K S hD hSH hLJ
  intro x hx
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) := hXN.trans hNQ
  have hQX : Q ⊓ X ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (Late.le_normalizer_inf hXQ Subgroup.le_normalizer) (hQ2.to_le inf_le_left)
  refine mem_oTwoOddIn_of_commutator_mem hD.odd hD.le_px hPp hD.cent_p hx.1 fun u hu => ?_
  refine hQX ⟨hact x hx.2 u hu, ?_⟩
  rw [commutatorElement_def]
  exact X.mul_mem (X.mul_mem (X.mul_mem hx.1 (hD.le_px hu)) (X.inv_mem hx.1))
    (X.inv_mem (hD.le_px hu))

end Proof152Res2

open Proof152Res2

variable {G : Type} [Group G] [Finite G]

@[expose] def Step152ConfKX (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y M X : Subgroup G) (c' : G) (L' : Subgroup G) (p : ℕ) (P T : Subgroup G),
    Pt152 A LB Y M X c' L' → PData152 A X p P → TData152 A LB X P T →
      ∃ K S : Subgroup G, KData152 A LB P T K S ∧
        ((P ⊔ CFSG.Open.pCoreOf 2 K).subgroupOf K).Normal ∧
        X ≤ Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 K : Subgroup G) : Set G)

@[expose] noncomputable def Step152ConfKXR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152ConfKX A (lB A)

@[expose] def Step152ConfKN (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y M X : Subgroup G) (c' : G) (L' : Subgroup G) (p : ℕ) (P T : Subgroup G),
    Pt152 A LB Y M X c' L' → PData152 A X p P → TData152 A LB X P T →
      ∃ S : Subgroup G, KData152 A LB P T
        (Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G)) S

@[expose] noncomputable def Step152ConfKNR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152ConfKN A (lB A)

@[expose] def Step152ConfX (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y M X : Subgroup G, Ctx152 A LB Y M X →
    ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) →
      deltaZero A LB X = pPrimeCoreOf 3 (deltaZero A LB X) ⊔
        deltaZero A LB (X ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G)) →
      ∃ (d : G) (p : ℕ) (P T K S : Subgroup G), Data152 A LB X c' L' d p P T K S ∧
        X ≤ Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 K : Subgroup G) : Set G)

@[expose] noncomputable def Step152ConfXR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152ConfX A (lB A)

theorem step152ConfKX_of_KN {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h : Step152ConfKN A LB) : Step152ConfKX A LB := by
  intro Y M X c' L' p P T hpt hPd hTd
  have : Fact p.Prime := ⟨hPd.prime⟩
  obtain ⟨S, hKd⟩ := h Y M X c' L' p P T hpt hPd hTd
  have hXN := Proof152FX.le_normalizer_sup_pCoreOf hPd.char_p
  exact ⟨_, S, hKd, normal_sup_pCoreOf_normalizer hPd.le_px hXN,
    le_normalizer_sup_pCoreOf_normalizer hPd.le_px hXN⟩

theorem step152ConfKXR_of_KN (h : Step152ConfKNR) : Step152ConfKXR :=
  fun G _ _ A c L hR => step152ConfKX_of_KN (h G A c L hR)

theorem step152ConfX_of_KX
    {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hD : Step152ConfD A LB) (hP : Step152ConfP A LB) (hT : Step152ConfT A LB)
    (hKX : Step152ConfKX A LB) (hPS : Step152ConfPS A LB) (hF : Step152ConfF A LB)
    (hW : Step152ConfW A LB) : Step152ConfX A LB := by
  intro Y M X hctx c' L' hc' hL' hJ hdec
  have hpt : Pt152 A LB Y M X c' L' := ⟨hctx, hc', hL', hJ, hdec⟩
  obtain ⟨d, hd⟩ := hD Y M X c' L' hpt
  obtain ⟨p, P, hPd⟩ := hP Y M X c' L' hpt
  obtain ⟨T, hTd⟩ := hT Y M X c' L' p P hpt hPd
  obtain ⟨K, S, hKd, hn, hXN⟩ := hKX Y M X c' L' p P T hpt hPd hTd
  have : Fact p.Prime := ⟨hPd.prime⟩
  have hθ := Proof152ConfA.le_theta_of_normal_sup hPd.odd (Proof152ConfA.PData152.ne_three hctx hPd)
    ((le_sup_right : P ≤ T ⊔ P).trans hKd.le_k) (isPGroup_of_pData hPd) hn
  obtain ⟨hps, hfs⟩ := hPS Y M X c' L' p P T K S hpt hPd hTd hKd hθ hn
  have hfr := hF Y M X c' L' d p P T K S hpt hd hPd hTd hKd hθ hn hps hfs
  have hw := hW Y M X c' L' d p P T K S hpt hd hPd hTd hKd hθ hn hps hfs hfr
  exact ⟨d, p, P, T, K, S, ⟨hc', hL', hJ, hd.mem_d, hd.ne_d, hd.central_d, hd.cent, hPd.prime,
    hPd.odd, hPd.le_px, hPd.char_p, hPd.norm_p, hPd.type_p, hPd.cent_p, hTd.mem_t, hTd.tp_eq,
    hTd.eq_comm_p, hKd.le_k, hKd.mem_k, hKd.le_ts, hKd.mem_sk, hKd.s_max, hθ, hn, hps, hfs, hfr,
    hw⟩, hXN⟩

theorem step152ConfXR_of_res
    (h142 : Item142AllS14) (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS14)
    (h134 : Item134) (h135 : Item135) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hmult : KFacts.KS18Mult) (hKX : Step152ConfKXR) (hWd : Step152ConfWdR) :
    Step152ConfXR :=
  fun G _ _ A c L hR => step152ConfX_of_KX
    (step152ConfDR_of (item142R_of_wired h142) G A c L hR) (step152ConfPR_of G A c L hR)
    (step152ConfTR_of_items h1444 h146 hbot G A c L hR) (hKX G A c L hR)
    (step152ConfPSR_of_items h1444 h146 hbot G A c L hR)
    (step152ConfFR_of_item142 h142 h135 hmult G A c L hR)
    (step152ConfWR_of_Wd h134 h48 h415 h142 h135 hmult hWd G A c L hR)

theorem step152End_of_confX
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h148 : Item148 A (lB A))
    (h1411 : Item1411_1 A (lB A)) (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hst : StellmacherKP) (hgen : KS152HJGen) (hAct : KS152HJAct)
    (hCover : Step152EndCover A (lB A)) (hX : Step152ConfX A (lB A)) : Step152End A (lB A) := by
  intro Y M X hctx _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨c', hc', hdec, L', hL', hJ⟩ := exists_hj_of_sl25' h h148 h134 h48 h415 hctx
  obtain ⟨d, p, P, T, K, S, hD, hXN⟩ := hX Y M X hctx c' L' hc' hL' hJ hdec
  have hSG := hD.mem_scriptQPiStar_top hst h.isSimpleGroup
  have hSH := inf_mem_scriptQPiStar_of_transOn (isNaturalFamily_lB A) hD.norm_w h1411 hSG
  have h' : Sec14Std G A c' L' := { h with zpowers_mem_omegaA := hD.omega, mem_lA := hD.mem_lA }
  exact false_of_le_normalizer hctx hD hSH (hgen G A c' L' h' Y M X hctx d p P T K S hD hSH) hXN
    hAct hCover

theorem step152EndR_of_confX
    (h148 : Item148R) (h1411 : Item1411_1R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (hst : StellmacherKP)
    (hgen : KS152HJGen) (hAct : KS152HJAct) (hCover : Step152EndCoverR) (hX : Step152ConfXR) :
    Step152EndR :=
  fun G _ _ A c L hR => step152End_of_confX hR.toSec14Std (h148 G A c L hR) (h1411 G A c L hR)
    h134 h48 h415 hst hgen hAct (hCover G A c L hR) (hX G A c L hR)

end CFSG.RankThree.PartTwo.Sec15

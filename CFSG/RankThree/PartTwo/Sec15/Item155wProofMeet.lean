module

public import CFSG.RankThree.PartTwo.Sec15.Item155wProof
public import CFSG.RankThree.PartTwo.Sec15.Item153Twin3ProofFaith
import CFSG.RankThree.PartTwo.Sec15.Item155wProofTools
import CFSG.RankThree.PartTwo.Sec15.Item155wProofHJ
import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofMaxT
import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofON
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofTheta
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.CGT.PushingUp.TwoLocals

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof156 CFSG.RankThree.PartTwo.Sec15.Proof155w

variable {G : Type} [Group G] [Finite G]

namespace Proof155w

theorem pCoreOf_le_pCoreOf_of_eq_sup {X Y : Subgroup G} (hXY : X ≤ Y)
    (hY : Y = X ⊔ CFSG.Open.pCoreOf 2 Y) :
    CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.Open.pCoreOf 2 X ⊔ CFSG.Open.pCoreOf 2 Y with hP
  have hXOY : CFSG.Open.pCoreOf 2 X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXY).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hP2 : IsPGroup 2 P :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X).to_sup_of_normal_right'
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y) hXOY
  have hPY : P ≤ Y :=
    sup_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXY)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
  have hYP : Y ≤ Subgroup.normalizer (P : Set G) :=
    hY.le.trans (sup_le (le_normalizer_sup (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
      (hXY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)))
      ((le_sup_right : CFSG.Open.pCoreOf 2 Y ≤ P).trans Subgroup.le_normalizer))
  exact le_sup_left.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPY hYP hP2)

theorem inf_thetaQuotCentralizer_eq_bot
    (h142 : Item142AllS14)
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h152 : Item152 A (lB A))
    (h153 : Item153Main A (lB A)) (hw : Item155w A (lB A)) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) (htype : IsType156 Y) {c₀ : G} {L₀ : Subgroup G} {d : G}
    {X₁ : Subgroup G} (D : Data156 A (lB A) Y c₀ L₀ d X₁) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G)) {f : G}
    {Lf : Subgroup G} (hfΩ : Subgroup.zpowers f ∈ omegaA A)
    (hfcd : f ∈ Subgroup.closure ({c₀, d} : Set G)) (hLf : Lf ∈ lA A f)
    (hJf : Nonempty (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({f} : Set G) ⊓
      Sec4.thetaQuotCentralizer Lf = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : Sec14Std G A f Lf := { h with zpowers_mem_omegaA := hfΩ, mem_lA := hLf }
  have hD13 := hf.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD13.mem_partTwoE
  have hfA : f ∈ A := (zpowers_mem_omegaA_iff.mp hfΩ).1
  have hf3 : f ^ 3 = 1 := hA.1.2 f hfA
  have hAC : A ≤ Subgroup.centralizer ({f} : Set G) := fun a ha => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨f, hfA⟩ ⟨a, ha⟩)).symm
  set Q := CFSG.Open.pCoreOf 2 M with hQdef
  set W := Q ⊓ Subgroup.centralizer ({f} : Set G) ⊓ Sec4.thetaQuotCentralizer Lf with hWdef
  by_contra hW1
  have hYM : Y ≤ M := fun y hy => hM.2 (Subgroup.mem_sup_left hy)
  have hAM : A ≤ M := fun a ha => hM.2 (Subgroup.mem_sup_right ha)
  have hXM : X₁ ≤ M := D.le_x.trans hYM
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) M
  have hWQ : W ≤ Q := inf_le_left.trans inf_le_left
  have hWC : W ≤ Subgroup.centralizer ({f} : Set G) := inf_le_left.trans inf_le_right
  have hW2 : IsPGroup 2 W := hQ2.to_le hWQ
  have hCLf : Subgroup.centralizer ({f} : Set G) ≤ Subgroup.normalizer (Lf : Set G) :=
    centralizer_le_normalizer_of_j2 hf hJf
  have hNC : Subgroup.normalizer (Lf : Set G) ≤
      Subgroup.normalizer (Sec4.thetaQuotCentralizer Lf : Set G) :=
    Sec6.normalizer_le_normalizer_thetaQuotCentralizer Lf
  have hAW : A ≤ Subgroup.normalizer (W : Set G) :=
    Late.le_normalizer_inf
      (Late.le_normalizer_inf (hAM.trans hMQ) (hAC.trans Subgroup.le_normalizer))
      (hD13.le_normalizer.trans hNC)
  obtain ⟨hAX, hXΔ, hθO, -, -, -, -, -, -, -⟩ := facts_of_data156 D hA
  have hfsc : f ∈ Late.sectionCentralizer A X₁ (CFSG.Open.pCoreOf 2 X₁) := by
    rw [D.cent]
    exact hfcd
  set θL := inSubgroup (aschbacherSolvableCore 3) Lf with hθL
  have hθ2 : IsPGroup 2 θL := (Proof152Gen.isPGroup_theta_of_j2 hf hJf).map Lf.subtype
  have hNθ : Subgroup.normalizer (Lf : Set G) ≤ Subgroup.normalizer (θL : Set G) :=
    Sec6.normalizer_le_normalizer_theta Lf
  have hWθ : W ≤ Subgroup.normalizer (θL : Set G) := (hWC.trans hCLf).trans hNθ
  set T := W ⊔ θL with hTdef
  have hT2 : IsPGroup 2 T := hW2.to_sup_of_normal_right' hθ2 hWθ
  have hT1 : T ≠ ⊥ := fun h0 => hW1 (le_bot_iff.mp (h0 ▸ le_sup_left))
  have hLfT : Lf ≤ Subgroup.normalizer (T : Set G) := by
    have hcomm := commutator_le_theta_of_le_thetaQuotCentralizer (W := W) (L := Lf) inf_le_right
    have h2 : T = (W ⊔ ⁅W, Lf⁆) ⊔ θL := by rw [sup_assoc, sup_eq_right.mpr hcomm]
    rw [h2]
    exact le_normalizer_sup (le_normalizer_sup_commutator W Lf) (Sec6.le_normalizer_theta Lf)
  have hAT : A ≤ Subgroup.normalizer (T : Set G) :=
    le_normalizer_sup hAW (hD13.le_normalizer.trans hNθ)
  have hWT : W ≤ Subgroup.normalizer (T : Set G) := le_normalizer_sup Subgroup.le_normalizer hWθ
  set Z₀ := X₁ ⊓ Subgroup.centralizer ({f} : Set G) with hZ₀
  set Z := oPrimeResidualOf 3 Z₀ with hZdef
  have hZX : Z ≤ X₁ := (oPrimeResidualOf_le_self 3 _).trans inf_le_left
  have hZC : Z ≤ Subgroup.centralizer ({f} : Set G) :=
    (oPrimeResidualOf_le_self 3 _).trans inf_le_right
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_oPrimeResidualOf (Late.le_normalizer_inf hAX (hAC.trans Subgroup.le_normalizer))
  have hZW : Z ≤ Subgroup.normalizer (W : Set G) :=
    Late.le_normalizer_inf
      (Late.le_normalizer_inf ((hZX.trans hXM).trans hMQ) (hZC.trans Subgroup.le_normalizer))
      ((hZC.trans hCLf).trans hNC)
  have hZT : Z ≤ Subgroup.normalizer (T : Set G) :=
    le_normalizer_sup hZW ((hZC.trans hCLf).trans hNθ)
  have hfC : f ∈ Sec4.thetaQuotCentralizer X₁ := by
    refine mem_thetaQuotCentralizer_of_mem_sectionCentralizer hAX ?_
    rw [hθO]
    exact hfsc
  have hW₀ : ((X₁.subgroupOf X₁).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X₁))) = ⊤ := by
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  have hZ₀cov : X₁ ≤ Z₀ ⊔ CFSG.Open.pCoreOf 2 X₁ := by
    have h1 := le_sup_theta_of_map_eq_top
      (Proof152Gen.map_inf_centralizer_eq_top le_rfl (hAX hfA) hf3 hfC hW₀)
    rwa [hθO] at h1
  have hXcov : X₁ ≤ Z ⊔ CFSG.Open.pCoreOf 2 X₁ :=
    calc X₁ = oPrimeResidualOf 3 X₁ := D.mem_x.1.2.1
      _ ≤ oPrimeResidualOf 3 (Z₀ ⊔ CFSG.Open.pCoreOf 2 X₁) := oPrimeResidualOf_mono 3 hZ₀cov
      _ ≤ Z ⊔ CFSG.Open.pCoreOf 2 X₁ := oPrimeResidualOf_sup_le_sup
          (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X₁))
  have hZΔ : Z ≤ delta A (lB A) Z :=
    le_delta_of_cover_of_j2 hf hJf hZX hZC hAZ hAX hXΔ.le hXcov
  have h𝓠 : ∀ R : Subgroup G, R ≤ Subgroup.centralizer ({f} : Set G) → IsPGroup 2 R →
      A ≤ Subgroup.normalizer (R : Set G) → R ∈ scriptQ A (lB A) := by
    intro R hRC hR2 hAR
    have hR3 : ¬ 3 ∣ Nat.card R := by
      intro h3
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR2
      rw [hn] at h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    exact (mem_scriptQ_of_hj_point hf hJf
      ⟨hRC.trans (centralizer_singleton_le_normalizer_zpowers f),
        (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR⟩).1
  set Y' := Z ⊔ W with hY'def
  have hY'C : Y' ≤ Subgroup.centralizer ({f} : Set G) := sup_le hZC hWC
  have hAY' : A ≤ Subgroup.normalizer (Y' : Set G) := le_normalizer_sup hAZ hAW
  have hY'W : Y' ≤ Subgroup.normalizer (W : Set G) := sup_le hZW Subgroup.le_normalizer
  have hWO : W ≤ CFSG.Open.pCoreOf 2 Y' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right hY'W hW2
  have hY'top : Y' ≠ ⊤ := fun htop =>
    Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hD13.ne_one
      (top_le_iff.mp (htop ▸ hY'C))
  have hY'Δ : Y' ≤ delta A (lB A) Y' :=
    sup_le (hZΔ.trans (delta_mono le_sup_left)) (le_delta (h𝓠 W hWC hW2 hAW) le_sup_right)
  have hY'3 : Y' ∈ scriptY3 A (lB A) :=
    ⟨⟨⟨hY'top, hAY'⟩, fun h0 => hW1 (le_bot_iff.mp (h0 ▸ hWO))⟩,
      le_antisymm hY'Δ (delta_le Y')⟩
  set X' := oPrimeResidualOf 3 Y' with hX'def
  have hZZ' : Z ≤ X' :=
    calc Z = oPrimeResidualOf 3 Z := (Proof156Res4.oRes3_idem' Z₀).symm
      _ ≤ X' := oPrimeResidualOf_mono 3 le_sup_left
  have hX'Y' : X' ≤ Y' := oPrimeResidualOf_le_self 3 Y'
  have hX'le : X' ≤ Z ⊔ (X' ⊓ W) := le_sup_inf_of_le hZW hZZ' hX'Y'
  have hX'W : X' ≤ Subgroup.normalizer ((X' ⊓ W : Subgroup G) : Set G) :=
    Late.le_normalizer_inf Subgroup.le_normalizer (hX'Y'.trans hY'W)
  obtain ⟨e₁⟩ := Proof155R2.isoQuot_of_le_sup hZZ' hX'le (hZZ'.trans hX'W) hX'W
    (hW2.to_le inf_le_right)
  obtain ⟨e₂⟩ := Proof155R2.isoQuot_of_le_sup hZX hXcov
    (hZX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X₁))
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X₁)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X₁)
  set e : ↥X' ⧸ CFSG.pCore 2 ↥X' ≃* ↥X₁ ⧸ CFSG.pCore 2 ↥X₁ := e₁.symm.trans e₂ with he
  have hX'Δ : X' ≤ delta A (lB A) X' :=
    hX'le.trans (sup_le (hZΔ.trans (delta_mono hZZ'))
      (le_delta (h𝓠 _ (inf_le_right.trans hWC) (hW2.to_le inf_le_right)
        (Late.le_normalizer_inf (le_normalizer_oPrimeResidualOf hAY') hAW)) inf_le_left))
  have hX'4 : X' ∈ scriptY4 A (lB A) :=
    ⟨⟨fun htop => hY'top (top_le_iff.mp (htop ▸ hX'Y')), le_normalizer_oPrimeResidualOf hAY'⟩,
      (Proof156Res4.oRes3_idem' Y').symm, le_antisymm hX'Δ (delta_le X'),
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm D.mem_x.1.2.2.2⟩
  have hY'eq : Y' = X' ⊔ CFSG.Open.pCoreOf 2 Y' :=
    le_antisymm (sup_le (hZZ'.trans le_sup_left) (hWO.trans le_sup_right))
      (sup_le hX'Y' (CFSG.LieType.BorelTits.pCoreOf_le 2 Y'))
  have hYθ : Y ∈ thetaComponentsIn M := mem_thetaComponentsIn_of_item152 h h152 hY hM
  have hWY : W ≤ Subgroup.normalizer (Y : Set G) :=
    hWQ.trans (le_normalizer_of_mem_thetaComponentsIn_of_two hYθ
      (CFSG.LieType.BorelTits.pCoreOf_le 2 M) hMQ hQ2)
  have hZY : Z ≤ Y := hZX.trans D.le_x
  have hX'Y : X' ≤ Y :=
    Proof155R2.oPrimeResidualOf_le_of_le_sup hW2 hWY (sup_le_sup_right hZY W)
  have hΓ : Y ∈ gam155 A (lB A) Y' X' :=
    ⟨hY, hX'Y, sup_le (hZY.trans Subgroup.le_normalizer) hWY⟩
  have hhyp : omg155 A X' ∨ Y = X' ⊔ CFSG.Open.pCoreOf 2 Y := by
    rcases D.choice with h6 | hYX
    · have hX'1080 : Nat.card (↥X' ⧸ CFSG.pCore 2 ↥X') = 1080 := by
        rw [Nat.card_congr e.toEquiv, card_of_isTripleCover h6, card_alternatingGroup_six]
      refine Or.inl (Or.inl ⟨fun ⟨n, _, hiso⟩ =>
        not_isoLThreePi_of_card_small (Or.inr hX'1080) 2 n hiso, ⟨fun e5 => ?_⟩⟩)
      have h60 := Nat.card_congr e5.toEquiv
      rw [hX'1080, card_alternatingGroup_five] at h60
      norm_num at h60
    · refine Or.inr (le_antisymm ?_ (sup_le hX'Y (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)))
      have hO : CFSG.Open.pCoreOf 2 X₁ ≤ CFSG.Open.pCoreOf 2 Y :=
        pCoreOf_le_pCoreOf_of_eq_sup D.le_x hYX
      calc Y = X₁ ⊔ CFSG.Open.pCoreOf 2 Y := hYX
        _ ≤ X' ⊔ CFSG.Open.pCoreOf 2 Y :=
          sup_le (hXcov.trans (sup_le (hZZ'.trans le_sup_left) (hO.trans le_sup_right)))
            le_sup_right
  obtain ⟨M', hle, hM'⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge
    (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hT2 hT1)
  have hM'm : M' ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ Y' : Subgroup G) : Set G) :=
    ⟨hM', fun x hx => hle (sup_le hAT (sup_le hZT hWT) hx)⟩
  have hΔM' := (hw Y' hY'3 hX'4 hY'eq).2 Y hΓ hhyp M' hM'm
  have hLfΔ : Lf ≤ delta A (lB A) M' := le_delta_of_le_of_j2 hf hJf (hLfT.trans hle)
  have hLfY : Lf ≤ Subgroup.normalizer (Y : Set G) :=
    le_normalizer_of_isPerfect_of_le_n155 h h152 h153 hY
      (Sec6.isPerfect_of_mem_thetaComponentsAt hLf.1) (hLfΔ.trans hΔM')
  exact Proof153Twin2.not_le_normalizer_at_point h142 h htype D hfΩ hfcd hLf hJf hLfY

end Proof155w

open Proof155w

theorem step156QThetaMeet_of
    (h142 : Item142AllS14) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) (h152 : Item152 A (lB A))
    (h153 : Item153Main A (lB A)) (hw : Item155w A (lB A)) : Step156QThetaMeet A (lB A) := by
  intro Y hY htype c₀ L₀ d X₁ D _ h6 M hM f Lf hfΩ hfcd _ hLf hJf
  have hf : Sec14Std G A f Lf := { h with zpowers_mem_omegaA := hfΩ, mem_lA := hLf }
  have hXM : X₁ ≤ M := D.le_x.trans fun y hy => hM.2 (Subgroup.mem_sup_left hy)
  have hfsc : f ∈ Late.sectionCentralizer A X₁ (CFSG.Open.pCoreOf 2 X₁) := by
    rw [D.cent]
    exact hfcd (Subgroup.mem_zpowers f)
  have hUC := Proof153Twin3.inf_centralizer_le_thetaQuotCentralizer hf hJf (h142 G A f Lf hf)
    D.mem_x.1 h6 hfsc hXM
  have hbot := inf_thetaQuotCentralizer_eq_bot h142 h h152 h153 hw hY htype D hM hfΩ
    (hfcd (Subgroup.mem_zpowers f)) hLf hJf
  rw [inf_eq_left.mpr hUC] at hbot
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxQ, hxθ⟩ := Subgroup.mem_inf.mp hx
  have hxW : x ∈ CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({f} : Set G) :=
    ⟨hxQ, Sec6.le_centralizer_of_mem_thetaComponentsAt hLf.1 (Sec6.theta_le Lf hxθ)⟩
  rwa [hbot] at hxW

theorem step156QThetaMeetR_of
    (h142 : Item142AllS14) (h152 : Item152R)
    (h153 : Item153MainR) (hw : Item155wR) : Step156QThetaMeetR :=
  fun G _ _ A c L hR => step156QThetaMeet_of h142 hR.toSec14Std (h152 G A c L hR)
    (h153 G A c L hR) (hw G A c L hR)

end CFSG.RankThree.PartTwo.Sec15

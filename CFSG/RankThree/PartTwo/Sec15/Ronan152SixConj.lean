module

public import CFSG.RankThree.PartTwo.Sec15.Ronan152SixQN
import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofHJD
import CFSG.RankThree.PartTwo.Sec15.Item155wProofHJ
import CFSG.RankThree.PartTwo.Sec15.Item155wProofTools
import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofMaxT
import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofON
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofTheta
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.CGT.PushingUp.TwoLocals

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A L Y : Subgroup G} {c : G}

open Proof15Res4 Proof15Res7

section Certificates


theorem Conf1515HJ.le_normalizer_conj_big
    (h : Conf1515HJ A c L Y)
    (h152 : Item152Big A (lB A)) (h153 : Item153MainJ2 A (lB A)) (h155 : Item155wJ2 A (lB A))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdZ : IsZCentral L d) {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G))
    (hwd : w ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hwcB : w * c * w⁻¹ ∈ Subgroup.closure {c, d})
    (hU1 : ⁅CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({w * c * w⁻¹} : Set G),
      Subgroup.zpowers d⁆ ≠ ⊥) :
    L.map (MulAut.conj w).toMonoidHom ≤ Subgroup.normalizer (Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.sec13Data
  have hS := h.sec15R.toSec14Std
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hdL : d ∈ L := mem_of_isZCentral hdZ
  have hRa := h.sec15R_conj hwA
  have hSa := hRa.toSec14Std
  have hJa := nonempty_j2_conj h.j2 w
  have hθU := h.le_theta_conj hdA hd1 hdZ hwA hwd hwcB
  have hXB := h.residual_eq_conj hdA hd1 hdZ hwA hwd hwcB
  have hmap := h.map_zHJ hdA hd1 hdZ hdL
  obtain ⟨hdL', S, hdS, hSd⟩ := exists_sylow_of_isZCentral hdZ
  obtain ⟨eZ⟩ := h.zHJ_quot hdA hd1 hdZ hdL
  obtain ⟨hz1, hzc⟩ := h.quot_three_central hdA hd1 hdZ hdL
  have hCq : IsQuasisimple ↥(Subgroup.centralizer
      ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} :
        Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) :=
    (Item148HJ.centralizer_facts h.j2 hz1 hzc).1
  have hC1080 : Nat.card ↥(Subgroup.centralizer
      ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} :
        Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) = 1080 := by
    rw [card_of_isTripleCover (KFacts.KS14.Native.j2_centralizer_isTripleCover h.j2 hz1 hzc),
      card_alternatingGroup_six]
  set a := w * c * w⁻¹ with ha
  set Lw := L.map (MulAut.conj w).toMonoidHom with hLw
  set d' := w * d * w⁻¹ with hd'
  have haA : a ∈ A := (Subgroup.mem_normalizer_iff.mp hwA c).mp hD.mem_A
  have ha1 : a ≠ 1 := fun h1 => hD.ne_one (by
    have h3 : c = w⁻¹ * (w * c * w⁻¹) * w := by group
    rw [h3, show w * c * w⁻¹ = 1 from h1]
    group)
  have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx haA)
  have hAd : A ≤ Subgroup.centralizer ({d} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hdA)
  set U := ⁅CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({a} : Set G), Subgroup.zpowers d⁆
    with hUdef
  have hUC : U ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [hUdef, Subgroup.commutator_le]
    intro x hx y hy
    have hya : y ∈ Subgroup.centralizer ({a} : Set G) := hAa ((Subgroup.zpowers_le.mpr hdA) hy)
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx.2 hya) (inv_mem hx.2)) (inv_mem hya)
  have hUO : U ≤ CFSG.Open.pCoreOf 2 Y := by
    rw [hUdef, Subgroup.commutator_le]
    intro x hx y hy
    have hyN := h.A_le_normalizer_pCoreOf ((Subgroup.zpowers_le.mpr hdA) hy)
    have h1 : y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y :=
      (Subgroup.mem_normalizer_iff.mp hyN _).mp (inv_mem hx.1)
    rw [commutatorElement_def, show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
    exact mul_mem hx.1 h1
  have hU2 : IsPGroup 2 U := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le hUO
  have hAU : A ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_commutator
      (Late.le_normalizer_inf h.A_le_normalizer_pCoreOf (hAa.trans Subgroup.le_normalizer))
      (hAd.trans (centralizer_singleton_le_normalizer_zpowers d))
  have hU3 : ¬ 3 ∣ Nat.card U := by
    intro h3
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hU2
    rw [hn] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hUQ : U ∈ scriptQ A (lB A) :=
    (mem_scriptQ_of_hj_point hSa hJa ⟨hUC.trans (centralizer_singleton_le_normalizer_zpowers a),
      (isPiSubgroup_piCompl_iff Nat.prime_three U).mpr hU3, hAU⟩).1
  set T := inSubgroup (aschbacherSolvableCore 3) Lw with hTdef
  have hT2 : IsPGroup 2 T := (Proof152Gen.isPGroup_theta_of_j2 hSa hJa).map Lw.subtype
  have hT1 : T ≠ ⊥ := fun h0 => hU1 (le_bot_iff.mp (h0 ▸ hθU))
  have hLwT : Lw ≤ Subgroup.normalizer (T : Set G) := Sec6.le_normalizer_theta Lw
  have hAT : A ≤ Subgroup.normalizer (T : Set G) :=
    hSa.toSec13Data.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta Lw)
  obtain ⟨M, hle, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge
    (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hT2 hT1)
  set Z := zHJ L Y d with hZdef
  have hZle := zHJ_le L Y d
  have hZL : Z ≤ L := hZle.trans (inf_le_left.trans inf_le_left)
  have hZY : Z ≤ Y := hZle.trans (inf_le_left.trans inf_le_right)
  have hZd : Z ≤ Subgroup.centralizer ({d} : Set G) := hZle.trans inf_le_right
  have hZc : Z ≤ Subgroup.centralizer ({c} : Set G) := hZL.trans hD.le_centralizer
  have hZa : Z ≤ Subgroup.centralizer ({a} : Set G) :=
    (le_inf hZc hZd).trans (inf_centralizer_le_centralizer hwcB)
  have hZU : Z ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_commutator
      (Late.le_normalizer_inf (hZY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
        (hZa.trans Subgroup.le_normalizer))
      (hZd.trans (centralizer_singleton_le_normalizer_zpowers d))
  have hZLw : Z ≤ Lw := (zHJ_le_residual_inf L Y d).trans (hXB ▸ Item148HJ.residual_le Lw d')
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_zHJ hD.le_normalizer h.A_le_normalizer (hAd.trans Subgroup.le_normalizer)
  have hZΔ : Z ≤ delta A (lB A) Z :=
    le_delta_of_map_eq_centralizer hS h.j2 hdA hd1 hdL' ⟨S, hdS, hSd⟩ hZL hAZ hmap
  set Y' := Z ⊔ U with hY'def
  have hY'C : Y' ≤ Subgroup.centralizer ({a} : Set G) := sup_le hZa hUC
  have hAY' : A ≤ Subgroup.normalizer (Y' : Set G) := le_normalizer_sup hAZ hAU
  have hY'U : Y' ≤ Subgroup.normalizer (U : Set G) := sup_le hZU Subgroup.le_normalizer
  have hUO' : U ≤ CFSG.Open.pCoreOf 2 Y' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right hY'U hU2
  have hY'top : Y' ≠ ⊤ := fun htop =>
    Sec6.centralizer_ne_top_of_ne_one h.sec15R.toTheoremFourHyp ha1 (top_le_iff.mp (htop ▸ hY'C))
  have hY'Δ : Y' ≤ delta A (lB A) Y' :=
    sup_le (hZΔ.trans (delta_mono le_sup_left)) (le_delta hUQ le_sup_right)
  have hY'3 : Y' ∈ scriptY3 A (lB A) :=
    ⟨⟨⟨hY'top, hAY'⟩, fun h0 => hU1 (le_bot_iff.mp (h0 ▸ hUO'))⟩, le_antisymm hY'Δ (delta_le Y')⟩
  set Z' := oPrimeResidualOf 3 Z with hZ'def
  have hZ'Z : Z' = Z := by
    rw [hZ'def, hZdef, zHJ, Proof156Res4.oRes3_idem']
  set X' := oPrimeResidualOf 3 Y' with hX'def
  have hZX' : Z ≤ X' := hZ'Z ▸ oPrimeResidualOf_mono 3 le_sup_left
  have hX'Y' : X' ≤ Y' := oPrimeResidualOf_le_self 3 Y'
  have hX'le : X' ≤ Z ⊔ (X' ⊓ U) := Proof155w.le_sup_inf_of_le hZU hZX' hX'Y'
  have hX'U : X' ≤ Subgroup.normalizer ((X' ⊓ U : Subgroup G) : Set G) :=
    Late.le_normalizer_inf Subgroup.le_normalizer (hX'Y'.trans hY'U)
  obtain ⟨e₁⟩ := Proof155R2.isoQuot_of_le_sup hZX' hX'le (hZX'.trans hX'U) hX'U
    (hU2.to_le inf_le_right)
  set e : ↥X' ⧸ CFSG.pCore 2 ↥X' ≃* _ := e₁.symm.trans eZ with he
  have hX'Δ : X' ≤ delta A (lB A) X' :=
    hX'le.trans (sup_le (hZΔ.trans (delta_mono hZX'))
      (le_delta (mem_scriptQ_of_le hUQ inf_le_right
        (Late.le_normalizer_inf (le_normalizer_oPrimeResidualOf hAY') hAU)) inf_le_left))
  have hX'4 : X' ∈ scriptY4 A (lB A) :=
    ⟨⟨fun htop => hY'top (top_le_iff.mp (htop ▸ hX'Y')), le_normalizer_oPrimeResidualOf hAY'⟩,
      (Proof156Res4.oRes3_idem' Y').symm, le_antisymm hX'Δ (delta_le X'),
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hCq⟩
  have hY'eq : Y' = X' ⊔ CFSG.Open.pCoreOf 2 Y' :=
    le_antisymm (sup_le (hZX'.trans le_sup_left) (hUO'.trans le_sup_right))
      (sup_le hX'Y' (CFSG.LieType.BorelTits.pCoreOf_le 2 Y'))
  have hY'Y : Y' ≤ Y := sup_le hZY (hUO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 Y))
  have hΓ : Y ∈ gam155 A (lB A) Y' X' :=
    ⟨h.mem_scriptY0Star, hX'Y'.trans hY'Y, hY'Y.trans Subgroup.le_normalizer⟩
  have hX'1080 : Nat.card (↥X' ⧸ CFSG.pCore 2 ↥X') = 1080 := by
    rw [Nat.card_congr e.toEquiv, hC1080]
  have hhyp : omg155 A X' ∨ Y = X' ⊔ CFSG.Open.pCoreOf 2 Y := by
    refine Or.inl (Or.inl ⟨fun ⟨n, _, hiso⟩ =>
      not_isoLThreePi_of_card_small (Or.inr hX'1080) 2 n hiso, ⟨fun e5 => ?_⟩⟩)
    have h60 := Nat.card_congr e5.toEquiv
    rw [hX'1080, card_alternatingGroup_five] at h60
    norm_num at h60
  have hM'm : M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ Y' : Subgroup G) : Set G) :=
    ⟨hM, fun x hx => hle (sup_le hAT (sup_le (hZLw.trans hLwT)
      (hθU.trans Subgroup.le_normalizer)) hx)⟩
  have hX'b : Big152 X' := by
    unfold Big152
    rw [hX'1080]
    norm_num
  have hΔM := h155 Y' hY'3 hX'4 hX'b hY'eq Y hΓ h.isJ2Type hhyp M hM'm
  have hLwΔ : Lw ≤ delta A (lB A) M := Proof155w.le_delta_of_le_of_j2 hSa hJa (hLwT.trans hle)
  exact Ronan152Six.le_normalizer_of_isPerfect_of_le_n155_j2 hS h152 h153 h.mem_scriptY0Star
    h.isJ2Type
    (Sec6.isPerfect_of_mem_thetaComponentsAt hSa.toSec13Data.mem_thetaComponentsAt)
    (hLwΔ.trans hΔM)

end Certificates

theorem step1515HJConj_of_big
    (h152 : Item152BigR) (h153 : Item153MainJ2R) (h155 : Item155wJ2R) :
    Step1515HJConj := by
  intro G _ _ A c L Y h d hdA hd1 hdZ w hwA hwd hwcB hwcn hU
  have hR := h.sec15R
  exact (h.false_of_le_normalizer_conj hdA hd1 hdZ hwA hwd hwcB hwcn
    (h.le_normalizer_conj_big (h152 G A c L hR) (h153 G A c L hR) (h155 G A c L hR) hdA hd1 hdZ
      hwA hwd hwcB hU)).elim

end CFSG.RankThree.PartTwo.Sec15

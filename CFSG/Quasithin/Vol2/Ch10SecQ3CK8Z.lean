module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8E
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8F
public import CFSG.Quasithin.EmptyFaithful.T1515dC
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK7D
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8A
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8D

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique C11AmS.K8
open scoped commutatorElement IsMulCommutative

theorem factA7FFFix_of (h51 : AsB51) : FactA7FFFix := by
  intro G _ _ X T J hX hC hT hJ hJn hA hTJ h4
  obtain ⟨hWe, hred, hZJ, hB, hN⟩ := b51Hyp_setting hX hC hT hJ hJn hA hTJ
  set Z := quasithinOmegaOneCenter T with hZ
  set Y := J ⊔ T with hY
  set W := conjClosure Z Y with hWdef
  have := hWe.1
  have hV2 : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hWe.2 v v.2)
  obtain ⟨hP1, hP2, -⟩ := h51 ↥W hV2 _ _ hB
  set L := autOn J W with hL
  have hshape := part1_shape hP1 hN
  have hcard : Nat.card ↥L = 2520 := hshape.elim card_of_alt7 card_of_a7Four
  have hdir := part2_direct hP2 hcard
  have hZ0 : fixV L ⊓ commV L = ⊥ := by rw [inf_comm]; exact hdir.2
  rw [hZ0] at hshape
  have hJX : J ≤ X := le_of_mem_cComp hJ
  have hXJ : X ≤ Subgroup.normalizer (J : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJX).1 hJn
  have hYJ : Y ≤ Subgroup.normalizer (J : Set G) :=
    sup_le Subgroup.le_normalizer (hT.1.trans hXJ)
  have hJY : J ≤ Y := le_sup_left
  have hJN : J ≤ Subgroup.normalizer (W : Set G) := hJY.trans hred.2.1
  have hJW : ¬ J ≤ Subgroup.centralizer (W : Set G) := by
    intro hle
    apply hTJ
    have hb : ⁅Z, J⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact (Subgroup.mem_centralizer_iff.mp (hle hj) z (le_conjClosure Z Y hz)).symm
    rw [hb, Subgroup.coe_bot, Subgroup.centralizer_singleton_one]
    exact le_top
  have hA7 : IsAlt 7 (↥J ⧸ CFSG.pCore 2 ↥J) ∨
      IsHat (↥J ⧸ CFSG.pCore 2 ↥J) ↥(alternatingGroup (Fin 7)) := by
    obtain ⟨e⟩ := modO2_mulEquiv hJ
    rcases hA with hA | h
    · obtain ⟨f⟩ := hA
      exact Or.inl ⟨e.trans f⟩
    · exact Or.inr (IsHat.of_mulEquiv e.symm h)
  have hO2J : pCoreOf 2 L = ⊥ :=
    pCoreOf_autOn_L_eq_bot1527d hJY hYJ (Setup.pCoreOf_autOn_eq_bot hred)
  set B := baum T ⊓ J with hBdef
  have hBJ : B ≤ J := inf_le_right
  have hBN : B ≤ Subgroup.normalizer (W : Set G) := hBJ.trans hJN
  have hRL : autOn B W ≤ L := InternalSec.autOn_le_autOn_of_le hBJ
  have hB2 : IsPGroup 2 ↥B := hT.2.1.to_le (inf_le_left.trans inf_le_left)
  have hR2 : IsPGroup 2 ↥(autOn B W) :=
    hB2.of_surjective (InternalSec.autOnHom hBN) (InternalSec.autOnHom_surjective hBN)
  have hk : ∀ b ∈ B, b ∈ Subgroup.centralizer (W : Set G) → b ∈ pCoreOf 2 X := by
    intro b hb hbW
    obtain ⟨k, hk⟩ := hB2 ⟨b, hb⟩
    have hbk : b ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hk' : (⟨b, hb.2⟩ : ↥J) ^ 2 ^ k = 1 := Subtype.ext (by simp [hbk])
    have hmem : (⟨b, hb.2⟩ : ↥J) ∈ (InternalSec.autOnHom hJN).ker :=
      (InternalSec.mem_ker_autOnHom hJN _).2 hbW
    have h1 := mem_pCore_of_mem_ker hA7 (InternalSec.pCore_le_ker_autOnHom hJN hO2J)
      (InternalSec.ker_autOnHom_ne_top hJN hJW) hmem hk'
    exact CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 J X hJX hJn
      ⟨⟨b, hb.2⟩, h1, rfl⟩
  have h4' : 4 ≤ Nat.card ↥(autOn B W) := h4.trans (card_modO2Image_le (hBJ.trans hJX) hBN hk)
  have h8 : Nat.card ↥(commV L ⊓ fixV (autOn B W)) ≤ 8 := by
    rcases hshape with h7 | h7
    · exact alt7_fix_le h7 hRL hR2 h4'
    · refine a7Four_fix_le h7 hdir.1 hRL fun hbot => ?_
      rw [hbot, Subgroup.card_bot] at h4'
      omega
  refine le_trans ?_ h8
  have hcomm : ∀ x : ↥(⁅Z, J⁆ ⊓ Subgroup.centralizer (baum T : Set G)),
      (⟨x, hZJ x.2.1⟩ : ↥W) ∈ commV L ⊓ fixV (autOn B W) := by
    intro x
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [hL, commV_autOn_eq1527d hJN, Subgroup.mem_subgroupOf]
      exact Subgroup.commutator_mono (le_conjClosure Z Y) le_rfl x.2.1
    · rw [mem_fixV]
      intro σ hσ
      obtain ⟨g, hgB, rfl⟩ := Setup.mem_autOn_iff.1 hσ
      apply Subtype.ext
      rw [InternalSec.coe_conjAct_apply]
      have hgx : (g : G) * x = x * g := Subgroup.mem_centralizer_iff.mp x.2.2 g hgB.1
      rw [hgx, mul_inv_cancel_right]
  let ι : ↥(⁅Z, J⁆ ⊓ Subgroup.centralizer (baum T : Set G)) →
      ↥(commV L ⊓ fixV (autOn B W)) := fun x => ⟨⟨x, hZJ x.2.1⟩, hcomm x⟩
  refine Nat.card_le_card_of_injective ι fun x y hxy => ?_
  have h1 := congrArg (fun z : ↥(commV L ⊓ fixV (autOn B W)) => ((z : ↥W) : G)) hxy
  exact Subtype.ext h1

end CFSG.Quasithin.Vol2.Ch10.SecB

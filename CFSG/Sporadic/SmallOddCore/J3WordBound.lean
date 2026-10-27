
module

public import CFSG.Sporadic.SmallOddCore.J3WordBoundBase

public import CFSG.Sporadic.SmallOddCore.J3
public import CFSG.Sporadic.SmallOddCore.AutCount
public import CFSG.Sporadic.Schreier.PairJ3Pairs
public meta import CFSG.Sporadic.Schreier.PairJ3Check
public meta import Certificates.Data.CFSGNative.PairSchreier.Preds
public import CFSG.Sporadic.Schreier.PairJ3CertInputs
public import CFSG.Sporadic.Schreier.PairJ3CheckInputs
public meta import CFSG.Sporadic.Schreier.PairJ3Cert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Schreier.PairJ3Check
public import Certificates.Data.CFSGNative.PairSchreier.Preds
public import CFSG.Sporadic.SmallOddCore.J3WordBoundInputs
public import Certificates.Certificate2283
public import CFSG.Sporadic.SmallOddCore.J3CentFacts

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem j3_wOrderOK : ordB PairJ3.bs (patW PairJ3.wA PairJ3.wB j3WPat) 17 = true :=
  Certificates.certificate2283.1

theorem j3_wCountOK :
    PairJ3.parCount (pairPred PairJ3.bs 3 PairJ3.wA j3WConds) PairJ3.blocks = 3840 :=
  Certificates.certificate2283.2

theorem j3_word_order :
    orderOf (j3Gen 0 * j3Gen 1 * j3Gen 0 * j3Gen 1 * j3Gen 0 * j3Gen 1 ^ 2) = 17 := by
  have h := (ordB_iff j3_baseFaithful j3_bs_lt (repW_patW repW_j3wA repW_j3wB j3WPat)
    (patProd_mem _ (j3Gen_mem 0 (by norm_num)) (j3Gen_mem 1 (by norm_num)) j3WPat)
    (by norm_num)).1 j3_wOrderOK
  rwa [j3WPat_prod] at h

theorem j3_card_wordConds : Nat.card {y : j3P // WordConds j3a y} = 3840 := by
  classical
  have ha : orderOf (j3Gen 0) = 2 := AT_J3_image_pair_count.1
  have h := card_eq_countW j3ChainArrays (by norm_num) PairJ3.chain_check.1 j3_groups
    (f := pairPred PairJ3.bs 3 PairJ3.wA j3WConds) (Pr := fun g => WordConds (j3Gen 0) g)
    (fun w g hw hg => by
      rw [pairPred, Bool.and_eq_true, ordB_iff j3_baseFaithful j3_bs_lt hw hg (by norm_num),
        condsOK_iff j3_baseFaithful j3_bs_lt repW_j3wA hw (j3Gen_mem 0 (by norm_num)) hg
          (by decide)]
      exact wordConds_iff ha)
  rw [show blocksOf 6156 (rawLevels 6156 j3StrongArrs PairJ3.baseArr) PairJ3.groups =
    PairJ3.blocks from rfl, ← PairJ3.parCount_eq, j3_wCountOK, ← j3P_eq_original] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun y =>
    (wordConds_map j3P.subtype j3P.subtype_injective j3a y).symm)

theorem j3_card_mulAut_le : Nat.card (MulAut j3P) ≤ 100465920 := by
  classical
  have hgen : closure ({j3a, j3b} : Set j3P) = ⊤ :=
    CFSG.Sporadic.Mathieu.closure_pair_eq_top rfl _ _
  obtain ⟨ha, hb, hab, hc, h2, -, -⟩ := AT_J3_image_pair_count
  have hab' : WordConds j3a j3b := by
    refine (wordConds_map j3P.subtype j3P.subtype_injective j3a j3b).1 ?_
    exact ⟨hb, hab, hc, j3_word_order⟩
  have hbound := card_mulAut_le_classSize_mul j3a j3b hgen (fun x y => WordConds x y)
    (fun φ x y h => (wordConds_map φ.toMonoidHom φ.injective x y).2 h) hab'
    (fun φ => j3_involution_conj_a (by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact ha))
  have hclass : {x : j3P | ∃ g : j3P, x = g * j3a * g⁻¹}.ncard ≤ 26163 := by
    have h2' : {x : j3P | orderOf x = 2}.ncard = 26163 := by
      rw [← Nat.card_coe_set_eq]
      exact h2
    rw [← h2']
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro _ ⟨g, rfl⟩
    show orderOf (g * j3a * g⁻¹) = 2
    rw [show g * j3a * g⁻¹ = MulAut.conj g j3a from rfl, MulEquiv.orderOf_eq,
      ← Subgroup.orderOf_coe]
    exact ha
  calc Nat.card (MulAut j3P)
      ≤ {x : j3P | ∃ g : j3P, x = g * j3a * g⁻¹}.ncard * Nat.card {y // WordConds j3a y} :=
        hbound
    _ ≤ 26163 * 3840 := by
        rw [j3_card_wordConds]
        exact Nat.mul_le_mul_right _ hclass
    _ = 100465920 := by norm_num

theorem ctuc_j3_generator_image_word_bound :
    orderOf (j3Gen 0 * j3Gen 1 * j3Gen 0 * j3Gen 1 * j3Gen 0 * j3Gen 1 ^ 2) = 17 ∧
      Nat.card {y : j3P // orderOf y = 3 ∧ orderOf (j3a * y) = 19 ∧
        orderOf (j3a * y * j3a⁻¹ * y⁻¹) = 9 ∧ orderOf (j3a * y * j3a * y * j3a * y ^ 2) = 17} =
        3840 ∧
      Nat.card (MulAut j3P) ≤ 100465920 ∧ 100465920 = 2 * Nat.card j3P :=
  ⟨j3_word_order, j3_card_wordConds, j3_card_mulAut_le, by rw [card_j3P]⟩

end CFSG.Sporadic.SmallOddCore


module

public import CFSG.Sporadic.SmallOddCore.HSWordBoundBase

public import CFSG.Sporadic.SmallOddCore.HS
public import CFSG.Sporadic.SmallOddCore.AutCount
public import CFSG.Sporadic.Schreier.PairHSPairs
public import CFSG.Sporadic.Schreier.PairCounts
public meta import CFSG.Sporadic.Schreier.PairHSCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
public import CFSG.Sporadic.Schreier.PairHSCertInputs
public import CFSG.Sporadic.Schreier.PairHSCheckInputs
public meta import CFSG.Sporadic.Schreier.PairHSCert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.SmallOddCore.HSWordBoundInputs
public import Certificates.Certificate2274
public import CFSG.Sporadic.SmallOddCore.HSCheckInputs

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

theorem hs_wOrderOK : ordB PairHS.bs (patW PairHS.wA PairHS.wB [false, true, true]) 10 = true :=
  Certificates.certificate2274.1

theorem hs_wCountOK : countPair PairHS.bs 5 PairHS.wA hsWConds PairHS.blocks = 15360 :=
  Certificates.certificate2274.2

theorem hs_word_order_ab2 : orderOf (hsGen 0 * hsGen 1 ^ 2) = 10 := by
  have h1 := (ordB_iff hs_baseFaithful hs_bs_lt (repW_patW repW_hswA repW_hswB
    [false, true, true]) (patProd_mem _ (hsGen_mem 0 (by norm_num)) (hsGen_mem 1 (by norm_num)) _)
    (by norm_num)).1 hs_wOrderOK
  simpa [pow_two, mul_assoc] using h1

theorem hs_card_wordConds : Nat.card {y : hsP // HSWordConds hsa0 y} = 15360 := by
  classical
  have ha : orderOf (hsGen 0) = 2 := hs_word_orders.1
  have h := card_eq_countW hsChainArrays (by norm_num) PairHS.chain_check.1 hs_groups
    (f := pairPred PairHS.bs 5 PairHS.wA hsWConds) (Pr := fun g => HSWordConds (hsGen 0) g)
    (fun w g hw hg => by
      rw [pairPred, Bool.and_eq_true, ordB_iff hs_baseFaithful hs_bs_lt hw hg (by norm_num),
        condsOK_iff hs_baseFaithful hs_bs_lt repW_hswA hw (hsGen_mem 0 (by norm_num)) hg
          (by decide)]
      exact hsWordConds_iff ha)
  rw [show blocksOf 3850 (rawLevels 3850 hsStrongArrs PairHS.baseArr) PairHS.groups =
    PairHS.blocks from rfl, ← countPair_eq, hs_wCountOK, ← hsP_eq_original] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun y =>
    (hsWordConds_map hsP.subtype hsP.subtype_injective hsa0 y).symm)

theorem hs_card_mulAut_le : Nat.card (MulAut hsP) ≤ 88704000 := by
  classical
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := hs_involution_centralizers
  have hgen : closure ({hsa0, hsa1} : Set hsP) = ⊤ :=
    CFSG.Sporadic.Mathieu.closure_pair_eq_top rfl _ _
  obtain ⟨-, hb, hab, hc⟩ := hs_word_orders
  have hab' : HSWordConds hsa0 hsa1 := by
    refine (hsWordConds_map hsP.subtype hsP.subtype_injective hsa0 hsa1).1 ?_
    exact ⟨hb, hab, hc, hs_word_order_ab2⟩
  have hbound := card_mulAut_le_classSize_mul hsa0 hsa1 hgen (fun x y => HSWordConds x y)
    (fun φ x y h => (hsWordConds_map φ.toMonoidHom φ.injective x y).2 h) hab' hs_aut_conj_a
  have hclass : {x : hsP | ∃ g : hsP, x = g * hsa0 * g⁻¹}.ncard = 5775 := by
    rw [ncard_conj_set_eq]
    have h := (hrows _ List.mem_cons_self).2.2.2.2.2
    dsimp only at h
    rwa [hs_tp_rep_a] at h
  calc Nat.card (MulAut hsP)
      ≤ {x : hsP | ∃ g : hsP, x = g * hsa0 * g⁻¹}.ncard *
          Nat.card {y // HSWordConds hsa0 y} := hbound
    _ = 88704000 := by simp only [hclass, hs_card_wordConds]

end CFSG.Sporadic.SmallOddCore

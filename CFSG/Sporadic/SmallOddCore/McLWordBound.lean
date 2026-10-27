module

public import CFSG.Sporadic.SmallOddCore.McL
public import CFSG.Sporadic.SmallOddCore.AutCount
public import CFSG.Sporadic.SmallOddCore.CountSplit
public import CFSG.Sporadic.SmallOddCore.McLCountA
public import CFSG.Sporadic.Schreier.PairMcLPairs
public meta import CFSG.Sporadic.SmallOddCore.McLWords
public meta import CFSG.Sporadic.Schreier.PairMcLCheck
public import Certificates.Certificate2240
public import Certificates.Certificate2241
public import Certificates.Certificate2242
public import Certificates.Certificate2243
public import Certificates.Certificate2245
public import Certificates.Certificate2288
public import Certificates.Certificate2284
public import Certificates.Certificate2285

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem mcl_wOrderOK :
    ordB PairMcL.bs (patW PairMcL.wA PairMcL.wB [false, true, true]) 12 = true ∧
      ordB PairMcL.bs (patW PairMcL.wA PairMcL.wB mclWPat) 7 = true :=
  Certificates.certificate2288

theorem mcl_wCountOK : countPair PairMcL.bs 5 PairMcL.wA mclWConds PairMcL.blocks = 80640 :=
  mcl_wCountA

theorem mcl_word_orders' :
    orderOf (mclGen 0 * mclGen 1 ^ 2) = 12 ∧
      orderOf (mclGen 0 * mclGen 1 * mclGen 0 * mclGen 1 * mclGen 0 * mclGen 1 * mclGen 0 *
        mclGen 1 ^ 2 * mclGen 0 * mclGen 1 * mclGen 0 * mclGen 1 ^ 2 * mclGen 0 * mclGen 1 ^ 2) =
        7 := by
  have ha := mclGen_mem 0 (by norm_num)
  have hb := mclGen_mem 1 (by norm_num)
  have h1 := (ordB_iff mcl_baseFaithful mcl_bs_lt (repW_patW repW_mclwA repW_mclwB
    [false, true, true]) (patProd_mem _ ha hb _) (by norm_num)).1 mcl_wOrderOK.1
  have h2 := (ordB_iff mcl_baseFaithful mcl_bs_lt (repW_patW repW_mclwA repW_mclwB mclWPat)
    (patProd_mem _ ha hb _) (by norm_num)).1 mcl_wOrderOK.2
  rw [mclWPat_prod] at h2
  refine ⟨?_, h2⟩
  simpa [pow_two, mul_assoc] using h1

theorem mcl_card_wordConds : Nat.card {y : mclP // McLWordConds mcla0 y} = 80640 := by
  classical
  have ha : orderOf (mclGen 0) = 2 := mcl_word_orders.1
  have h := card_eq_countW mclChainArrays (by norm_num) PairMcL.chain_check.1 mcl_groups
    (f := pairPred PairMcL.bs 5 PairMcL.wA mclWConds) (Pr := fun g => McLWordConds (mclGen 0) g)
    (fun w g hw hg => by
      rw [pairPred, Bool.and_eq_true, ordB_iff mcl_baseFaithful mcl_bs_lt hw hg (by norm_num),
        condsOK_iff mcl_baseFaithful mcl_bs_lt repW_mclwA hw (mclGen_mem 0 (by norm_num)) hg
          (by decide)]
      exact mclWordConds_iff ha)
  rw [show blocksOf 275 (rawLevels 275 mclStrongArrs PairMcL.baseArr) PairMcL.groups =
    PairMcL.blocks from rfl, ← countPair_eq, mcl_wCountOK, ← mclP_eq_original] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun y =>
    (mclWordConds_map mclP.subtype mclP.subtype_injective mcla0 y).symm)

theorem mcl_involution_conj_a {t : mclP} (ht : orderOf t = 2) :
    ∃ g : mclP, t = g * mcla0 * g⁻¹ := by
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ := mcl_involution_centralizers
  have hPR : mclP ≤ mclR := le_sup_left
  have hinner : ∀ x ∈ mclP, orderOf x = 2 →
      ∃ g ∈ mclP, x = g * tp 275 (mclRows[0]'(by simp [mclRows])).rep * g⁻¹ := by
    intro x hx hx2
    obtain ⟨r, hr, g, hg, rfl⟩ := hcover x (hPR hx) hx2
    have hrP : tp 275 r.rep ∈ mclP := by
      have := mclP.mul_mem (mclP.mul_mem (mclP.inv_mem hg) hx) hg
      rwa [show g⁻¹ * (g * tp 275 r.rep * g⁻¹) * g = tp 275 r.rep by group] at this
    have hout : r.outer = false := by
      by_contra h
      rw [Bool.not_eq_false] at h
      exact (hrows r hr).2.2.1.1 h hrP
    have hr0 : r = mclRows[0]'(by simp [mclRows]) := by
      simp only [mclRows, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rfl
      · exact absurd hout (by decide)
    exact ⟨g, hg, by rw [hr0]⟩
  obtain ⟨g, hg, hgt⟩ := hinner t t.2 (by rw [Subgroup.orderOf_coe]; exact ht)
  obtain ⟨g', hg', hga⟩ := hinner (mclGen 0) (mclGen_mem_P 0 (by norm_num)) mcl_word_orders.1
  refine ⟨⟨g, hg⟩ * ⟨g', hg'⟩⁻¹, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hgt, show (mcla0 : Equiv.Perm (Fin 275)) = mclGen 0 from rfl, hga]
  group

theorem mcl_card_mulAut_le : Nat.card (MulAut mclP) ≤ 1796256000 := by
  classical
  have hgen : closure ({mcla0, mcla1} : Set mclP) = ⊤ :=
    CFSG.Sporadic.Mathieu.closure_pair_eq_top rfl _ _
  obtain ⟨ha, hb, hab, hc, h2, -, -⟩ := AT_McL_image_pair_count
  have hab' : McLWordConds mcla0 mcla1 := by
    refine (mclWordConds_map mclP.subtype mclP.subtype_injective mcla0 mcla1).1 ?_
    exact ⟨hb, hab, hc, mcl_word_orders'.1, mcl_word_orders'.2⟩
  have hbound := card_mulAut_le_classSize_mul mcla0 mcla1 hgen (fun x y => McLWordConds x y)
    (fun φ x y h => (mclWordConds_map φ.toMonoidHom φ.injective x y).2 h) hab'
    (fun φ => mcl_involution_conj_a (by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact ha))
  have hclass : {x : mclP | ∃ g : mclP, x = g * mcla0 * g⁻¹}.ncard ≤ 22275 := by
    have h2' : {x : mclP | orderOf x = 2}.ncard = 22275 := by
      rw [← Nat.card_coe_set_eq]
      exact h2
    rw [← h2']
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro _ ⟨g, rfl⟩
    show orderOf (g * mcla0 * g⁻¹) = 2
    rw [show g * mcla0 * g⁻¹ = MulAut.conj g mcla0 from rfl, MulEquiv.orderOf_eq,
      ← Subgroup.orderOf_coe]
    exact ha
  calc Nat.card (MulAut mclP)
      ≤ {x : mclP | ∃ g : mclP, x = g * mcla0 * g⁻¹}.ncard *
          Nat.card {y // McLWordConds mcla0 y} := hbound
    _ ≤ 22275 * 80640 := by
        rw [mcl_card_wordConds]
        exact Nat.mul_le_mul_right _ hclass
    _ = 1796256000 := by norm_num

end CFSG.Sporadic.SmallOddCore

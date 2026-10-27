
module

public import Certificates.Kernel.Co1B.Tri2045Base

public import Certificates.Kernel.Co1B.TriG2045
public import CFSG.Sporadic.Co1Block.TwoBCentBase2
public import Certificates.Kernel.Co1B.OrbK2045
public import CFSG.Certificates.Kernel.Spor.RawOrbSound
public import CFSG.Sporadic.Schreier.TitsChain
public import CFSG.Sporadic.Co1Block.TwoBCheckInputs
public meta import CFSG.Sporadic.Co1Block.TwoBData
public meta import CFSG.Sporadic.Co1Block.TwoBCheckDefs
public meta import CFSG.Sporadic.Co1Block.CentCheck
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheck
public meta import CFSG.Sporadic.Schreier.Co1ChainCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.Co1.TwoB
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.Schreier.Merge
public meta import Certificates.Data.CFSGNative.ONSchreier.Compact
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Tri2045

open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 Matrix
  CFSG.KC.Co1T CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelSporSch.Co1Packed
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

section Card

theorem card_E_le :
    Nat.card twoBE ≤ 2012774400 :=
  (Subgroup.card_le_of_le (brayE_le rep_A₁ A₁_mem Cent2045.twoB_cent_check)).trans
    card_GA_cent_A₁.le

theorem card_range_le :
    Nat.card φE.range ≤ 503193600 := by
  have h := Subgroup.card_ker_mul_card_range φE
  have hk := Nat.mul_le_mul_right (Nat.card φE.range) card_ker_ge
  have hE := card_E_le
  omega

theorem card_DD_le :
    Nat.card DD ≤ 251596800 := by
  obtain ⟨q, hq, h2⟩ := card_DD_dvd
  have hr := card_range_le
  have : Nat.card DD * 2 ≤ Nat.card DD * q := Nat.mul_le_mul_left _ h2
  omega

theorem conj_mem_DD
    (hD : Nat.card DD = 251596800) {g h : Equiv.Perm (Fin 1365)}
    (hg : g ∈ φE.range) (hh : h ∈ DD) : g * h * g⁻¹ ∈ DD := by
  obtain ⟨q, hq, h2⟩ := card_DD_dvd
  have hr := card_range_le
  have hq2 : q = 2 := by
    rw [hD] at hq
    omega
  set H : Subgroup φE.range := DD.subgroupOf φE.range
  have hH : Nat.card H = Nat.card DD :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe DD_le_range).toEquiv
  have hidx : H.index = 2 := by
    have := Subgroup.card_mul_index H
    rw [hH, hq, hq2] at this
    have hpos : 0 < Nat.card DD := Nat.card_pos
    have : Nat.card DD * H.index = Nat.card DD * 2 := this
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hN : H.Normal := Subgroup.normal_of_index_eq_two hidx
  have hm : (⟨h, DD_le_range hh⟩ : φE.range) ∈ H := Subgroup.mem_subgroupOf.2 hh
  have := hN.conj_mem _ hm ⟨g, hg⟩
  exact Subgroup.mem_subgroupOf.1 this

end Card

section Chain

theorem chainOK :
    rawChainOK 1365 (twoBStrong.extract 0 2) twoBStrong
      twoBChainBase.toArray (CFSG.Sporadic.Schreier.Tits.wordsArr 2 6 twoBChainWords) 4 = true := by
  refine rawChainK_of_card_orb 4 binds RO.head RO.ho (by norm_num) ?_
  rw [range_eq, orbits]
  exact card_DD_le.trans (by norm_num)

theorem chainOK' :
    rawChainOK 1365 (twoBStrong.extract 0 2) twoBStrong
      (CFSG.Sporadic.Schreier.Tits.baseArr 1365 twoBChainBase)
      (CFSG.Sporadic.Schreier.Tits.wordsArr 2 6 twoBChainWords) 4 = true := by
  rw [base_eq']
  exact chainOK

theorem card_DD :
    Nat.card DD = 251596800 := by
  rw [← orig_eq, CFSG.Sporadic.Schreier.Tits.card_ofArrays (hn := hn1) (hk := hk2) (hb := hnd)
    allPerms (by norm_num : 0 < 4) chainOK', base_eq', orbits]
  rfl

theorem sift_of
    {g : Array ℕ} {G : Equiv.Perm (Fin 1365)} (hG : Rep 1365 g G)
    (hmem : G ∈ DD) : siftA 1365 (rawLevels 1365 twoBStrong twoBChainBase.toArray)
      twoBChainBase.toArray 0 g = true := by
  have h := (CFSG.Sporadic.Schreier.Tits.siftA_iff_mem_ofArrays (hn := hn1) (hk := hk2) (hb := hnd)
    allPerms (by norm_num : 0 < 4) chainOK' hG).2 (by rw [orig_eq]; exact hmem)
  rwa [base_eq'] at h

end Chain

theorem twoB_tri_check :
    twoBTriCheckOf twoBTris twoBStrong
      (CFSG.Sporadic.Co1Block.Native.brayElts
        (CFSG.Sporadic.Co1Block.Native.brayRows CFSG.Sporadic.Co1Schreier.Native.aR twoBD1)
        twoBBray) twoBXYRows.1 twoBXYRows.2 twoBChainBase.toArray
      (CFSG.Sporadic.Schreier.Tits.wordsArr 2 6 twoBChainWords) = true := by
  have hX := okX.2
  have hY := okY.2
  simp only [twoBTriCheckOf, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, okX.1⟩, okY.1⟩, strong_facts.1⟩, ?_⟩, ?_⟩, chainOK⟩,
    orbits⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  ·
    unfold CFSG.Sporadic.Co1Block.Native.trisOK
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, bne_iff_ne,
      ne_eq]
    refine ⟨⟨tris_len, fun x hx => ⟨⟨(vecs.2.2 x hx).1, (vecs.2.2 x hx).2.1⟩, ?_⟩⟩,
      CFSG.KC.Co1B.vSorted_mergeSort vecs.2.1⟩
    rw [aR_u, act_unpack kTA']
    exact (vecs.2.2 x hx).2.2
  · exact CFSG.KC.Co1B.tableOK_triTable vecs.2.1 (fun y hy => (vecs.2.2 y hy).1)
  · intro r hr
    have hr' : r ∈ twoBBm := hr
    rw [bray_rows] at hr'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr'
    exact (okB (List.mem_range.1 hj)).1
  · rw [hX, strong_facts.2 0 (by norm_num), beq_of_true kS0]
    exact eqA_refl _ _
  · rw [hY, strong_facts.2 1 (by norm_num), beq_of_true kS1]
    exact eqA_refl _ _
  · rw [hX]
    exact isPrime_of rep_xE kOX kNX
  · rw [hY]
    exact isPrime_of rep_yE kOY kNY
  · rw [hX, hY, CFSG.KS.Prim.compEqK_sound kXY]
    have h := rep_compA rep_xE rep_yE
    rw [CFSG.KS.Prim.compEqK_sound kXY] at h
    exact isPrime_of h kOXY kNXY
  · intro r hr
    have hr' : r ∈ twoBBm := hr
    rw [bray_rows] at hr'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr'
    have hj' := List.mem_range.1 hj
    have hj12 : j < 12 := by omega
    have hinv := CFSG.KS.Prim.invEqK_sound (PP.all j hj12)
    have rb := rep_bE hj'
    have rbi := rep_inv_of_isInvA rb hinv.2
    rw [(okB hj').2, hinv.1, hX, hY]
    have hb : φE (bE j) ∈ φE.range := ⟨_, rfl⟩
    refine ⟨⟨hinv.2, sift_of (rep_compA (rep_compA rb rep_xE) rbi)
      (conj_mem_DD card_DD hb (Subgroup.subset_closure (by simp)))⟩,
      sift_of (rep_compA (rep_compA rb rep_yE) rbi)
      (conj_mem_DD card_DD hb (Subgroup.subset_closure (by simp)))⟩

end CertificateChecks.KernelCo1B.Tri2045

end

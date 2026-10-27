module

public import Certificates.Kernel.Co1Pump.Fix
public import Certificates.Kernel.Co1Pump.Block
public import Certificates.Kernel.Co1Pairs.Glue
public import Certificates.Kernel.Co1KOrb.Glue
public import Certificates.Kernel.Co1M.G16954
public import Certificates.Kernel.Co1FiveK.GlueB
public import CFSG.Certificates.Kernel.Co1PumpFixSound
public import CFSG.Certificates.Kernel.SporSch.Co1ActLemmas
public import CFSG.Sporadic.Co1Block.Perm
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1FiveBase
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeKit
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2BData
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1EndData
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.FischerOddCore.Basic
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.Sporadic.ThSchreier.ThSchreierCase
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate10027
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate16018
public import Certificates.Certificate2323
public import Certificates.Certificate6006
public import Certificates.Certificate8026Base
public import Certificates.Certificate9124

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Pump

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native CFSG.KS.SporSch.M24
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.KC.Co1Pairs CFSG.KD.Co1Pairs CFSG.KD.Co1PumpFix CertificateChecks.KernelCo1Pairs
open CFSG.Sporadic.SmallF2 (toVecD toVecD_injective rowsMatrix rowsMatrix_mulVec toVecD_xor)
open CFSG.Sporadic.Co1Block (certX ncard_certX mulVec_mem_certX certX_finite)
open CFSG.KS.Co1PumpFix (entsK_sound grayWs blockOK_sound)
open scoped Matrix

theorem actK_lt' (X v : Nat) : actK X v < 2 ^ 24 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [ActL.actK_eq_foldr, ActL.testBit_foldr_or]
  have : ¬ i < 24 := by omega
  simp [this]

theorem rows_mulVec (M v : ℕ) :
    rowsMatrix 24 (unpack 24 24 M) *ᵥ toVecD 24 v = toVecD 24 (actK M v) := by
  rw [rowsMatrix_mulVec, ActL.vecMulN_unpack]

theorem fix_facts {M J : ℕ} {F : List (ℕ × ℕ × ℕ)} (h : entsK M J F 0 = true) :
    Nat.card ↥{v : Vec24 | rowsMatrix 24 (unpack 24 24 M) *ᵥ v = v} = 2 ^ popK J ∧
      ∀ (S : Set Vec24) (mem : ℕ → Bool), (∀ x < 2 ^ 24, mem x = true ↔ toVecD 24 x ∈ S) →
        (S ∩ {v : Vec24 | rowsMatrix 24 (unpack 24 24 M) *ᵥ v = v}).ncard =
          cntK mem J F 0 0 0 := by
  obtain ⟨L, hnd, hlen, hlt, hiff, hcnt⟩ := entsK_sound h
  have hfix : ∀ v : Vec24, rowsMatrix 24 (unpack 24 24 M) *ᵥ v = v ↔ ∃ x ∈ L, toVecD 24 x = v := by
    intro v
    obtain ⟨x, hx, rfl⟩ := CFSG.KC.Co1Orb.toVecD_surj24 v
    rw [rows_mulVec]
    constructor
    · intro e
      exact ⟨x, (hiff x hx).1 (toVecD_injective (actK_lt' M x) hx e), rfl⟩
    · rintro ⟨y, hy, e⟩
      rw [← toVecD_injective (hlt y hy) hx e, (hiff y (hlt y hy)).2 hy]
  have hinj : ∀ P : ℕ → Prop, Set.InjOn (toVecD 24) {x | x ∈ L ∧ P x} :=
    fun _ a ha b hb e => toVecD_injective (hlt a ha.1) (hlt b hb.1) e
  refine ⟨?_, fun S mem hmem => ?_⟩
  · have e : {v : Vec24 | rowsMatrix 24 (unpack 24 24 M) *ᵥ v = v} =
        toVecD 24 '' {x | x ∈ L ∧ True} := by
      ext v
      rw [Set.mem_setOf_eq, hfix]
      simp
    rw [Nat.card_coe_set_eq, e, (hinj _).ncard_image]
    have e2 : {x | x ∈ L ∧ True} = (L.toFinset : Set ℕ) := by ext; simp
    rw [e2, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hlen]
  · have e : S ∩ {v : Vec24 | rowsMatrix 24 (unpack 24 24 M) *ᵥ v = v} =
        toVecD 24 '' {x | x ∈ L ∧ mem x = true} := by
      ext v
      rw [Set.mem_inter_iff, Set.mem_setOf_eq, hfix]
      constructor
      · rintro ⟨hv, x, hx, rfl⟩
        exact ⟨x, ⟨hx, (hmem x (hlt x hx)).2 hv⟩, rfl⟩
      · rintro ⟨x, ⟨hx, hm⟩, rfl⟩
        exact ⟨(hmem x (hlt x hx)).1 hm, x, hx, rfl⟩
    rw [e, (hinj _).ncard_image, hcnt mem]
    have e2 : {x | x ∈ L ∧ mem x = true} = ((L.filter mem).toFinset : Set ℕ) := by ext; simp
    rw [e2, Set.ncard_coe_finset, List.toFinset_card_of_nodup (hnd.filter _),
      List.countP_eq_length_filter]

section Facts


theorem memX (x : ℕ) (hx : x < 2 ^ 24) : ch36909X x = true ↔ toVecD 24 x ∈ certX :=
  CertificateChecks.KernelCo1M.mem_certX_iff hx

theorem rep_xC : MRep (unpack 24 24 R2) (Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] : GL24) := by
  have hr := ch214033r
  simp only [Bool.and_eq_true] at hr
  exact rep_elt [1, 1, 0, 0, 0, 0] (Nat.eq_of_beq_eq_true hr.2)

theorem K_le_GA : ThreeLocal.K ≤ GA :=
  Subgroup.closure_le _ |>.2 fun g hg => by
    rcases hg with rfl | rfl
    · exact threeLocal_mem.2.1
    · exact threeLocal_mem.2.2.1

theorem two_mem_certX : toVecD 24 2 ∈ certX := (memX 2 (by norm_num)).1 (by decide +kernel)

theorem orbit_eq_certX (h : CFSG.KC.F2Set24.orbOK CFSG.KD.Co1KOrb.cY CFSG.KD.Co1KOrb.cT
    CFSG.KD.Co1KOrb.opsY CFSG.KD.Co1KOrb.opsT 2 98280 28 = true) :
    kOrbit (Subgroup.closure {ThreeLocal.y⁻¹, ThreeLocal.t⁻¹}) (toVecD 24 2) = certX := by
  have hn := (CFSG.KS.F2Set24.orbit_of_orbOK CertificateChecks.KernelCo1KOrb.actsBy_yInv
    CertificateChecks.KernelCo1KOrb.actsBy_tInv h).1
  refine Set.eq_of_subset_of_ncard_le ?_ (by rw [ncard_certX, hn]) certX_finite
  rintro _ ⟨g, hg, rfl⟩
  rw [CertificateChecks.KernelCo1KOrb.closure_inv_eq] at hg
  exact mulVec_mem_certX (K_le_GA hg) two_mem_certX

@[expose] noncomputable def wsW : List ℕ := grayWs ch36909WB ch36909gray 0

theorem wsW_fix : wsW.all (fun w => Nat.beq (actK R2 w) w && Nat.blt w (2 ^ 24)) = true := by
  decide +kernel

theorem wsW_nodup : wsW.Nodup := by decide +kernel

theorem wsW_length : wsW.length = 64 := by decide +kernel

theorem w_facts :
    Nat.card ↥{v : Vec24 | ((Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] : GL24) :
      Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} = 64 ∧
    (certX ∩ {v : Vec24 | ((Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] : GL24) :
      Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v}).ncard = 27 ∧
    ∀ x ∈ certX, x ∉ {v : Vec24 | ((Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] : GL24) :
      Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} →
      {y | y ∈ certX ∧ y - x ∈ {v : Vec24 | ((Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] : GL24) :
        Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v}}.ncard ≤ 9 := by
  classical
  have hm : rowsMatrix 24 (unpack 24 24 R2) = ((Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] : GL24) :
      Matrix (Fin 24) (Fin 24) (ZMod 2)) := rep_xC
  rw [← hm]
  have hw : (entsK R2 JW FW 0 && (Nat.beq (popK JW) 6 &&
      Nat.beq (cntK ch36909X JW FW 0 0 0) 27)) = true := ch36909w
  simp only [Bool.and_eq_true] at hw
  obtain ⟨hents, hpop, hcnt⟩ := hw
  have hpop := Nat.eq_of_beq_eq_true hpop
  have hcnt := Nat.eq_of_beq_eq_true hcnt
  obtain ⟨hcard, hcntS⟩ := fix_facts hents
  refine ⟨by rw [hcard, hpop]; norm_num, by rw [hcntS certX ch36909X memX, hcnt], ?_⟩
  have hws : ∀ w ∈ wsW, actK R2 w = w ∧ w < 2 ^ 24 := by
    intro w hw
    have := List.all_eq_true.1 wsW_fix w hw
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at this
    exact this
  have hfixW : ∀ v : Vec24, rowsMatrix 24 (unpack 24 24 R2) *ᵥ v = v ↔
      ∃ w ∈ wsW, toVecD 24 w = v := by
    intro v
    constructor
    · intro hv
      by_contra hne
      simp only [not_exists, not_and] at hne
      have hsub : toVecD 24 '' {w | w ∈ wsW} ∪ {v} ⊆
          {v : Vec24 | rowsMatrix 24 (unpack 24 24 R2) *ᵥ v = v} := by
        rintro _ (⟨w, hw, rfl⟩ | rfl)
        · change _ = _
          rw [rows_mulVec, (hws w hw).1]
        · exact hv
      have hfin : {v : Vec24 | rowsMatrix 24 (unpack 24 24 R2) *ᵥ v = v}.Finite := Set.toFinite _
      have hle := Set.ncard_le_ncard hsub hfin
      rw [← Nat.card_coe_set_eq {v : Vec24 | rowsMatrix 24 (unpack 24 24 R2) *ᵥ v = v}, hcard,
        hpop] at hle
      have hnot : v ∉ toVecD 24 '' {w | w ∈ wsW} := by
        rintro ⟨w, hw, rfl⟩
        exact hne w hw rfl
      rw [Set.ncard_union_eq (Set.disjoint_singleton_right.2 hnot) (Set.toFinite _)
        (Set.toFinite _), Set.ncard_singleton] at hle
      have hinjW : Set.InjOn (toVecD 24) {w | w ∈ wsW} :=
        fun a ha b hb e => toVecD_injective (hws a ha).2 (hws b hb).2 e
      rw [hinjW.ncard_image] at hle
      have e2 : {w | w ∈ wsW} = (wsW.toFinset : Set ℕ) := by ext; simp
      rw [e2, Set.ncard_coe_finset, List.toFinset_card_of_nodup wsW_nodup, wsW_length] at hle
      omega
    · rintro ⟨w, hw, rfl⟩
      rw [rows_mulVec, (hws w hw).1]
  have hb := blockOK_sound CertificateChecks.KernelCo1KOrb.actsBy_yInv
    CertificateChecks.KernelCo1KOrb.actsBy_tInv ch36909b (by decide +kernel) (by decide +kernel)
  rw [orbit_eq_certX hb.1] at hb
  intro x hx hxW
  obtain ⟨x0, hx0, rfl⟩ := CFSG.KC.Co1Orb.toVecD_surj24 x
  have hx0W : x0 ∉ wsW := fun h => hxW ((hfixW _).2 ⟨x0, h, rfl⟩)
  have h9 := hb.2 x0 hx0 hx hx0W
  have hsub : {y | y ∈ certX ∧ y - toVecD 24 x0 ∈
      {v : Vec24 | rowsMatrix 24 (unpack 24 24 R2) *ᵥ v = v}} ⊆
      (fun w => toVecD 24 (x0 ^^^ w)) ''
        ((wsW.toFinset.filter fun w => toVecD 24 (x0 ^^^ w) ∈ certX : Finset ℕ) : Set ℕ) := by
    rintro y ⟨hy, hyW⟩
    obtain ⟨w, hw, hwy⟩ := (hfixW _).1 hyW
    have hy' : toVecD 24 (x0 ^^^ w) = y := by
      rw [toVecD_xor, hwy]
      abel
    refine ⟨w, ?_, hy'⟩
    simp only [Finset.coe_filter, List.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨hw, hy' ▸ hy⟩
  calc _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ _ := Set.ncard_image_le (Set.toFinite _)
    _ = _ := Set.ncard_coe_finset _
    _ ≤ 9 := h9

theorem gRows_eq' : Co1F.gRows = CertificateChecks.KernelCo1FiveK.rs :=
  congrArg Prod.fst CertificateChecks.KernelCo1FiveK.gDag_eq

theorem aw_nil (Js : List ℕ) (k : ℕ) : ch36909aw [] Js k = Nat.beq k 125 := rfl

theorem aw_cons (F : List (ℕ × ℕ × ℕ)) (Fs : List (List (ℕ × ℕ × ℕ))) (J : ℕ) (Js : List ℕ)
    (k : ℕ) : ch36909aw (F :: Fs) (J :: Js) k =
      Bool.rec (motive := fun _ => Bool) false (ch36909aw Fs Js (Nat.succ k))
        (ch36909a1 (CertificateChecks.KernelCo1FiveK.AT k) J F) := rfl

theorem aw_spec : ∀ (Fs : List (List (ℕ × ℕ × ℕ))) (Js : List ℕ) (k : ℕ),
    ch36909aw Fs Js k = true → ∀ i, k ≤ i → i < 125 →
      ∃ J F, ch36909a1 (CertificateChecks.KernelCo1FiveK.AT i) J F = true := by
  intro Fs
  induction Fs with
  | nil =>
    intro Js k h i hk hi
    rw [aw_nil] at h
    have := Nat.eq_of_beq_eq_true h
    omega
  | cons F Fs ih =>
    intro Js k h i hk hi
    cases Js with
    | nil => exact absurd h (by simp [ch36909aw])
    | cons J Js =>
      rw [aw_cons] at h
      have h' : (ch36909a1 (CertificateChecks.KernelCo1FiveK.AT k) J F &&
          ch36909aw Fs Js (Nat.succ k)) = true := h
      simp only [Bool.and_eq_true] at h'
      obtain ⟨h1, h2⟩ := h'
      rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · exact ⟨J, F, h1⟩
      · exact ih Js (Nat.succ k) h2 i hlt hi

theorem a0_facts : ∀ k < 125, k ≠ 0 →
    Nat.card ↥{v : Vec24 | rowsMatrix 24 (Timmesfeld.Co1Five.a0Row Co1F.gRows k) *ᵥ v = v} ≤ 256 ∧
    ((certX ∩ {v : Vec24 | rowsMatrix 24 (Timmesfeld.Co1Five.a0Row Co1F.gRows k) *ᵥ v = v}).ncard
        < 27 ∨
      54 < (certX ∩ {v : Vec24 | rowsMatrix 24 (Timmesfeld.Co1Five.a0Row Co1F.gRows k) *ᵥ v = v}).ncard) := by
  intro k hk hk0
  rw [gRows_eq', CertificateChecks.KernelCo1FiveK.AT_eq hk]
  obtain ⟨J, F, h⟩ := aw_spec FA JA 1 ch36909a k (by omega) hk
  have h' : (entsK (CertificateChecks.KernelCo1FiveK.AT k) J F 0 && (Nat.ble (popK J) 8 &&
      CFSG.KC.F2Set24.strict (cntK ch36909X J F 0 0 0) fun n =>
        Bool.rec (motive := fun _ => Bool) (Nat.blt 54 n) true (Nat.blt n 27))) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨hents, hpop, h⟩ := h'
  rw [CFSG.KS.F2Set24.strict_eq] at h
  obtain ⟨hcard, hcntS⟩ := fix_facts hents
  rw [hcard, hcntS certX ch36909X memX]
  refine ⟨le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_ble_eq_true hpop))
    (by norm_num), ?_⟩
  generalize cntK ch36909X J F 0 0 0 = n at h ⊢
  cases hn : Nat.blt n 27 with
  | true => exact Or.inl (Eq.mp Nat.blt_eq hn)
  | false =>
    rw [hn] at h
    exact Or.inr (Eq.mp Nat.blt_eq h)

end Facts

end CertificateChecks.KernelCo1Pump

end

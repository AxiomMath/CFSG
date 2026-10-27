
module

public import Certificates.Kernel.Co1FiveL.Glue
public import Certificates.Kernel.Co1FiveL.Bt
public import Certificates.Kernel.Co1FiveL.L0
public import Certificates.Kernel.Co1FiveL.L1
public import Certificates.Kernel.Co1FiveL.L2
public import Certificates.Kernel.Co1FiveL.TrA
public import Certificates.Kernel.Co1FiveL.TrB
public import Certificates.Kernel.Co1FiveL.ClB
public import Certificates.Kernel.Co1FiveK.GlueB
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1FiveBaseBase
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1FiveL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KC.Co1B
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.KC.Co1ClosP CFSG.KC.Co1FiveL Timmesfeld.Co1Five
open CertificateChecks.KernelCo1SevenK (comm_of_K)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F (Cen gE rep_gE)
open CertificateChecks.KernelCo1FiveK (rs gDag_eq rowAt_rs AT AT_eq)

local notation "U" => unpack 24 24

theorem gRows_eq : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F.gRows = rs := by
  have h := congrArg Prod.fst gDag_eq
  exact h

theorem hflag : (gDag CFSG.Sporadic.Co1Schreier.Native.aR
    CFSG.Sporadic.Co1Schreier.Native.bR).2.2 = true := by
  have h := congrArg (fun t => t.2.2) gDag_eq
  exact h

theorem rep_D {k : ℕ} (hk : k < 137) :
    MRep (U (CertificateChecks.KernelCo1FiveK.D.M k)) ((gE k : ↥GA) : GL24) := by
  have h := rep_gE hflag k
  rwa [gRows_eq, rowAt_rs hk] at h

@[expose] noncomputable def ggH (x y : ↥GA) (τ l : ℕ) : ↥GA :=
  if l = 0 then x else if l = 1 then y else gE (CFSG.KC.Co1F2.getL 0 (idxH.getD τ []) (l - 2))

theorem HG_ge {τ l : ℕ} (h : 2 ≤ l) : HG τ l =
    CertificateChecks.KernelCo1FiveK.D.M (CFSG.KC.Co1F2.getL 0 (idxH.getD τ []) (l - 2)) := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 2 := ⟨l - 2, by omega⟩
  rfl

theorem rep_HG {τ : ℕ}
    (hidx : ∀ j < (idxH.getD τ []).length, CFSG.KC.Co1F2.getL 0 (idxH.getD τ []) j < 137)
    {x y : ↥GA} (hx : MRep (U (HG τ 0)) (x : GL24)) (hy : MRep (U (HG τ 1)) (y : GL24)) :
    ∀ l < 2 + (idxH.getD τ []).length, MRep (U (HG τ l)) (ggH x y τ l : GL24) := by
  intro l hl
  rcases (by omega : l = 0 ∨ l = 1 ∨ 2 ≤ l) with rfl | rfl | h2
  · rw [ggH, if_pos rfl]
    exact hx
  · rw [ggH, if_neg (by omega), if_pos rfl]
    exact hy
  · rw [ggH, if_neg (by omega), if_neg (by omega), HG_ge h2]
    exact rep_D (hidx _ (by omega))

section Facts

theorem facts_of {τ ng N : ℕ} {BT : List ℕ} {Es : List (List ℕ)} {Ms Us : List ℕ}
    {Ts IMS CLs : List (List (List ℕ))} {SL : List ℕ} {UIT : ℕ} {P PAR LAB W S : ℕ → ℕ}
    (hng : 2 + (idxH.getD τ []).length = ng)
    (hidx : ∀ j < (idxH.getD τ []).length, CFSG.KC.Co1F2.getL 0 (idxH.getD τ []) j < 137)
    (hL : CFSG.KC.Co1LeafQ.leafQK CertificateChecks.KernelCo1B.Bound17591.XB BT Es Ms Us Ts IMS
      CLs SL UIT N = true)
    (hB : btK ATL (repA.getD τ 0) (repB.getD τ 0) BT = true)
    (hG : bAnd(commGK (HG τ) ng (HG τ 0), commGK (HG τ) ng (HG τ 1)) = true)
    (hT : gtPinK (HG τ) ng 100000 N P PAR LAB W S = true)
    {x y : ↥GA} (hx : MRep (U (HG τ 0)) (x : GL24)) (hy : MRep (U (HG τ 1)) (y : GL24)) :
    Nat.card (Cen x y) = N ∧ ∃ f : ℕ → ↥GA, (∀ i < N, MRep (U (P i)) (f i : GL24) ∧
      f i ∈ Cen x y) ∧ ∀ c ∈ Cen x y, ∃ i < N, c = f i := by
  subst hng
  have hrep := rep_HG hidx hx hy
  rw [MatL.bAnd_eq, Bool.and_eq_true] at hG
  exact cen_tree2 hT hrep (comm_of_K hG.1 hrep hx) (comm_of_K hG.2 hrep hy)
    (card_le_of_leaf hL hB hx hy)

theorem planes {τ : ℕ} (hτ : τ < 3) {x y : ↥GA}
    (hx : MRep (a0Row (gDag CFSG.Sporadic.Co1.Native.co1Data.rowsA
      CFSG.Sporadic.Co1.Native.co1Data.rowsB).1 (repA.getD τ 0)) (x : GL24))
    (hy : MRep (a0Row (gDag CFSG.Sporadic.Co1.Native.co1Data.rowsA
      CFSG.Sporadic.Co1.Native.co1Data.rowsB).1 (repB.getD τ 0)) (y : GL24)) :
    Nat.card (Subgroup.centralizer ({x, y} : Set ↥GA)) = 125 * leafR.getD τ 0 ∧
      GLAPPrimeCoreOf 5 (Subgroup.centralizer ({x, y} : Set ↥GA)) = ⊥ := by
  have : Finite ↥GA := CertificateChecks.KernelCo1SevenK.finite_GA
  have hA : repA.getD τ 0 < 125 := by interval_cases τ <;> with_unfolding_all decide
  have hB : repB.getD τ 0 < 125 := by interval_cases τ <;> with_unfolding_all decide
  rw [gDag_eq, AT_eq hA] at hx
  rw [gDag_eq, AT_eq hB] at hy
  have hx' : MRep (U (HG τ 0)) (x : GL24) := hx
  have hy' : MRep (U (HG τ 1)) (y : GL24) := hy
  change Nat.card (Cen x y) = _ ∧ GLAPPrimeCoreOf 5 (Cen x y) = ⊥
  interval_cases τ
  · have hT := kHT0
    rw [MatL.bAnd_eq, Bool.and_eq_true] at hT
    obtain ⟨hcard, -⟩ := facts_of (by with_unfolding_all decide) (by with_unfolding_all decide)
      kLeaf0 kBT0 kHG0 hT.2 hx' hy'
    refine ⟨by rw [hcard]; rfl, ?_⟩
    have hp : IsPGroup 5 ↥(Cen x y) := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
    exact gLAPPrimeCoreOf_eq_bot_of_isPGroup Nat.prime_five hp
  · have hT := kHT1
    rw [MatL.bAnd_eq, Bool.and_eq_true] at hT
    obtain ⟨hcard, f, hf, hall⟩ := facts_of (by with_unfolding_all decide)
      (by with_unfolding_all decide) kLeaf1 kBT1 kHG1 hT.2 hx' hy'
    refine ⟨by rw [hcard]; rfl, bot_tree5 hf hall ?_ kCl1⟩
    rw [hcard]
    norm_num
  · have hT := kHT2
    rw [MatL.bAnd_eq, Bool.and_eq_true] at hT
    obtain ⟨hcard, f, hf, hall⟩ := facts_of (by with_unfolding_all decide)
      (by with_unfolding_all decide) kLeaf2 kBT2 kHG2 hT.2 hx' hy'
    refine ⟨by rw [hcard]; rfl, bot_tree5 hf hall ?_ kCl2⟩
    rw [hcard]
    norm_num

end Facts

end CertificateChecks.KernelCo1FiveL

end

module

public import CFSG.Sporadic.Recognition.SuzMultiplierIndex
import Certificates.Kernel.CosetJ.Suz2Facts
import Certificates.Kernel.CosetJ.Suz2Lab
import Certificates.Kernel.CosetJ.Suz
public import Certificates.Kernel.CosetJ.Cover
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Rels
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.T_Sel
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.B_Sel
public import Certificates.Kernel.Bounds.Suz.Binding
public import Certificates.Kernel.Multipliers.Ent
public import CFSG.Certificates.Kernel.LceSTabSound
import CFSG.Certificates.Kernel.LceSHeRuSound
import CFSG.Certificates.Kernel.CosetBounds
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import all CFSG.Sporadic.Recognition.SuzMultiplierInputs
import all CFSG.LieType.Multipliers.CoverWords
import all CFSG.Certificates.CentralizerRelations
import all CFSG.Certificates.CosetTablePresented
import all CFSG.Sporadic.Presentation.SuzInputs
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Suzuki
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
public import CFSG.Sporadic.Presentation.Common

public section

namespace CertificateChecks.KernelCosetJ.Suz2

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE CFSG.CosetTable
  CFSG.Sporadic.Recognition.SuzMultiplier CFSG.LieType.Multipliers CertificateChecks.KernelMult

instance : NeZero gcS := ⟨by decide⟩

noncomputable abbrev gen : ℕ → PG _ suzCover2 := CFSG.KC.MiscCoset.pgGen suzCover2

theorem suzCover2_eq : suzCover2 = restrictWords (subsetOf _ [0, 1, 2, 3, 4])
    (restrictWords (subsetOf gcS [0, 1, 2, 3, 4, 6])
      (coverWords (KernelCosetJ.decodeW gcS CFSG.KBRoute.Suz.rels) suzCommWord)) := by
  rw [← Suz.suzCover_eq]

theorem length_eq : suzCover2.length = 90 := by
  rw [suzCover2_eq]
  decide +kernel

theorem rel_ent : ∀ r < 90, CFSG.KC.CJSuz2.rel r = ent (suzCover2.getD r []) ∧
    (suzCover2.getD r []).length < 1024 := by
  rw [suzCover2_eq]
  decide +kernel

theorem rel_one : ∀ r < 90,
    bval gen (wWord (CFSG.KD.CJSuz2T.selRT r)) (wLen (CFSG.KD.CJSuz2T.selRT r)) = 1 := by
  intro r hr
  have hr' : r < suzCover2.length := length_eq ▸ hr
  obtain ⟨he, hl⟩ := rel_ent r hr
  change bval gen (wWord (CFSG.KC.CJSuz2.rel r)) (wLen (CFSG.KC.CJSuz2.rel r)) = 1
  have hm : (subsetOf (subsetOf gcS [0, 1, 2, 3, 4, 6]).length [0, 1, 2, 3, 4]).length < 127 :=
    lt_of_eq_of_lt (rfl : _ = 5) (by norm_num)
  rw [bval_ent hm suzCover2 _ he hl, List.getD_eq_getElem _ _ hr']
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem (List.getElem_mem hr'))

theorem bval_one {G : Type*} [Group G] (g : ℕ → G) (c : ℕ) (hc : c < 256) :
    bval g c 1 = letV g c := by
  have h0 : bval g (c / 256) 0 = 1 := by simp [bval]
  rw [bval_succ, h0, mul_one, wLet_eq, Nat.mul_zero, pow_zero, Nat.div_one, Nat.mod_eq_of_lt hc]

@[expose] def rep1 : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + 256 * rep1 n

theorem bval_rep1 {G : Type*} [Group G] (g : ℕ → G) :
    ∀ n, bval g (rep1 n) n = (g 0)⁻¹ ^ n
  | 0 => by simp [bval]
  | n + 1 => by
    have h1 : wLet (rep1 (n + 1)) 0 = 1 := by
      rw [wLet_eq, Nat.mul_zero, pow_zero, Nat.div_one, rep1]
      omega
    have h2 : rep1 (n + 1) / 256 = rep1 n := by
      rw [rep1]
      omega
    rw [bval_succ, h1, h2, bval_rep1 g n, pow_succ']
    rfl

theorem card_le_step' {G : Type*} [Group G] {H K : Subgroup G} {N M : ℕ}
    (h : H.relIndex K ≠ 0 ∧ H.relIndex K ≤ N) (hH : Nat.card H ≠ 0 ∧ Nat.card H ≤ M) :
    Nat.card K ≠ 0 ∧ Nat.card K ≤ N * M := by
  have hfin : Finite H := Nat.finite_of_card_ne_zero hH.1
  have hle : Nat.card (H ⊓ K : Subgroup G) ≤ Nat.card H := Subgroup.card_le_of_le inf_le_left
  have h0 : Nat.card (H ⊓ K : Subgroup G) ≠ 0 := by
    have : Finite (H ⊓ K : Subgroup G) := Finite.of_injective _
      (Subgroup.inclusion_injective (inf_le_left : H ⊓ K ≤ H))
    exact Nat.card_pos.ne'
  rw [← Subgroup.inf_relIndex_right] at h
  exact KB.card_le_step ⟨inf_le_right, h⟩ ⟨h0, hle.trans hH.2⟩

theorem card : SuzCardP2 := by
  have hT : (Subgroup.closure ((fun j => bval gen (wWord (CFSG.KD.CJSuz2T.selST j))
        (wLen (CFSG.KD.CJSuz2T.selST j))) '' {j | j < 1})).relIndex
        (Subgroup.closure (gen '' {g | 2 * g < 10})) ≠ 0 ∧
      (Subgroup.closure ((fun j => bval gen (wWord (CFSG.KD.CJSuz2T.selST j))
        (wLen (CFSG.KD.CJSuz2T.selST j))) '' {j | j < 1})).relIndex
        (Subgroup.closure (gen '' {g | 2 * g < 10})) ≤ CFSG.KD.CJSuz2T.nLive :=
    lceOk_sound T.ok gen rel_one
  let w : ℕ → PG _ suzCover2 := fun j =>
    bval gen (wWord (CFSG.KD.CJSuz2T.selST j)) (wLen (CFSG.KD.CJSuz2T.selST j))
  have hTL : ∀ {c wid R k : ℕ}, c < 2 ^ 20 → wid < 2048 →
      CFSG.KC.LabF.cycOK CFSG.KD.CJSuz2T.blk CFSG.KD.CJSuz2T.selWT CFSG.KD.CJSuz2T.LB 1169643 c wid
        R (CFSG.KC.LabF.entStk (CFSG.KD.CJSuz2B.selRT k)) = true →
      bval w (wWord (CFSG.KD.CJSuz2B.selRT k)) (wLen (CFSG.KD.CJSuz2B.selRT k)) = 1 :=
    fun hc0 hwid hc => LS.LabF.labOk_sound gen w TL.ok rel_one (fun j _ => rfl) hc0 hwid hc
  have hBrel : ∀ r < 4,
      bval w (wWord (CFSG.KD.CJSuz2B.selRT r)) (wLen (CFSG.KD.CJSuz2B.selRT r)) = 1 := by
    intro r hr
    interval_cases r
    · exact hTL (by decide +kernel) (by decide +kernel) (CFSG.KD.CJSuz2T.okY_all 0 (by norm_num))
    · exact hTL (by decide +kernel) (by decide +kernel) (CFSG.KD.CJSuz2T.okY_all 1 (by norm_num))
    · exact hTL (by decide +kernel) (by decide +kernel) (CFSG.KD.CJSuz2T.okY_all 2 (by norm_num))
    · exact hTL (by decide +kernel) (by decide +kernel) (CFSG.KD.CJSuz2T.okY_all 3 (by norm_num))
  have hB : (Subgroup.closure ((fun j => bval w (wWord (CFSG.KD.CJSuz2B.selST j))
        (wLen (CFSG.KD.CJSuz2B.selST j))) '' {j | j < 1})).relIndex
        (Subgroup.closure (w '' {g | 2 * g < 2})) ≠ 0 ∧
      (Subgroup.closure ((fun j => bval w (wWord (CFSG.KD.CJSuz2B.selST j))
        (wLen (CFSG.KD.CJSuz2B.selST j))) '' {j | j < 1})).relIndex
        (Subgroup.closure (w '' {g | 2 * g < 2})) ≤ CFSG.KD.CJSuz2B.nLive :=
    lceOk_sound B.ok w hBrel
  have e1 : {j : ℕ | j < 1} = {0} := by
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    omega
  have hBsub : (fun j => bval w (wWord (CFSG.KD.CJSuz2B.selST j)) (wLen (CFSG.KD.CJSuz2B.selST j))) ''
      {j | j < 1} = {w 0} := by
    rw [e1, Set.image_singleton, Nat.eq_of_beq_eq_true CFSG.KC.CJSuz2.Route.bot_sub,
      (by decide : wWord 4 = 0), (by decide : wLen 4 = 1), bval_one w 0 (by norm_num)]
    simp [letV]
  rw [hBsub] at hB
  have hpow : w 0 ^ 30 = 1 := by
    have h := hBrel 0 (by norm_num)
    rw [Nat.eq_of_beq_eq_true CFSG.KC.CJSuz2.Route.bot_pow, (by decide : wWord
      28380414028753969466561515933501938199330878594519746088102349021547335800 = rep1 30),
      (by decide : wLen
      28380414028753969466561515933501938199330878594519746088102349021547335800 = 30),
      bval_rep1, inv_pow, inv_eq_one] at h
    exact h
  have hcyc : Nat.card (Subgroup.closure ({w 0} : Set (PG _ suzCover2))) ≠ 0 ∧
      Nat.card (Subgroup.closure ({w 0} : Set (PG _ suzCover2))) ≤ 30 := by
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
    have hd : orderOf (w 0) ∣ 30 := orderOf_dvd_of_pow_eq_one hpow
    exact ⟨fun h => by rw [h] at hd; norm_num at hd, Nat.le_of_dvd (by norm_num) hd⟩
  have cB := card_le_step' hB hcyc
  have eW : w '' {g | 2 * g < 2} =
      (fun j => bval gen (wWord (CFSG.KD.CJSuz2T.selST j)) (wLen (CFSG.KD.CJSuz2T.selST j))) ''
        {j | j < 1} := by
    have e : {g : ℕ | 2 * g < 2} = {j | j < 1} := by
      ext g
      simp only [Set.mem_ofPred_eq]
      omega
    rw [e]
  rw [eW] at cB
  have cT := card_le_step' hT cB
  have hm : (subsetOf (subsetOf gcS [0, 1, 2, 3, 4, 6]).length [0, 1, 2, 3, 4]).length = 5 := rfl
  have e10 : {g : ℕ | 2 * g < 10} =
      {g | g < (subsetOf (subsetOf gcS [0, 1, 2, 3, 4, 6]).length [0, 1, 2, 3, 4]).length} := by
    ext g
    simp only [Set.mem_ofPred_eq, hm]
    omega
  have htop : Subgroup.closure (gen '' {g | 2 * g < 10}) = ⊤ := by
    rw [e10]
    exact CFSG.KC.MiscCoset.closure_pgGen _
  have hord : CFSG.KD.CJSuz2T.nLive * (CFSG.KD.CJSuz2B.nLive * 30) = 1209600 := by
    rw [← Nat.mul_assoc]
    exact Nat.eq_of_beq_eq_true CFSG.KC.CJSuz2.Route.order
  rw [hord] at cT
  exact KB.finite_card_le_of_top htop cT

end CertificateChecks.KernelCosetJ.Suz2

end

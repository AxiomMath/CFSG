module

public import CFSG.Sporadic.Recognition.SuzMultiplierInputs
public import Certificates.Kernel.Misc.Coset.SuzRhoJ2A.All
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Misc.Coset.ActPermRep
import Certificates.Kernel.CosetJ.Suz
public import Certificates.Kernel.CosetJ.Cover
public import Certificates.Kernel.Bounds.Suz.Binding
import Certificates.Kernel.CosetJ.RhoPerm
import CFSG.Sporadic.Recognition.CoverTransferWords
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import all CFSG.Sporadic.Recognition.SuzMultiplierInputs
import all CFSG.LieType.Multipliers.CoverWords
import all CFSG.Certificates.CentralizerRelations
import all CFSG.Certificates.CosetTablePresented
import all CFSG.Sporadic.Presentation.SuzInputs
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Suzuki
meta import CFSG.Sporadic.Recognition.SuzMultiplierData
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Presentation.Common

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelCosetJ.RhoJ2Text CFSG.Sporadic.Recognition.SuzMultiplier.suzRhoJ2Text

#kmisc_hexflat CertificateChecks.KernelCosetJ.RhoJ2Text
  CFSG.Sporadic.Recognition.SuzMultiplier.suzRhoJ2Text 2 200 8 5

namespace CertificateChecks.KernelCosetJ.RhoJ2

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Sporadic.Recognition.SuzMultiplier
  CFSG.LieType.Multipliers CFSG.Certificates CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.LieType.Multipliers.Tits
  CFSG.Sporadic.Schreier.Tits
open CertificateChecks.KernelCosetJ.RhoJ2Text (F chars)
open CFSG.Monster.B.Co2 (Rep eqA_iff rep_idA getElem!_ofFn_nat allLt_iff)

instance : NeZero gcS := ⟨by decide⟩

abbrev m2 : ℕ := (subsetOf (subsetOf gcS [0, 1, 2, 3, 4, 6]).length [0, 1, 2, 3, 4]).length

private theorem m2_eq : m2 = 5 := rfl

theorem suzCover2_eq : suzCover2 = restrictWords (subsetOf _ [0, 1, 2, 3, 4])
    (restrictWords (subsetOf gcS [0, 1, 2, 3, 4, 6])
      (coverWords (KernelCosetJ.decodeW gcS CFSG.KBRoute.Suz.rels) suzCommWord)) := by
  rw [← Suz.suzCover_eq]

theorem hrels : suzCover2.map Act.revCodes = CFSG.KAct.SuzRhoJ2.rels := by
  rw [suzCover2_eq]
  decide +kernel

theorem hletters : ∀ w ∈ suzCover2, lettersOK 5 (zword w) = true := by
  rw [suzCover2_eq]
  decide +kernel

theorem bind : Act.allR 0 200 (fun x => Act.andB
    (Nat.beq (CFSG.KAct.SuzRhoJ2.A (x * (5 + 5) + 2 * 0)) (pg 8 (mask 8) (F 0) x))
    (Act.andB (Nat.beq (CFSG.KAct.SuzRhoJ2.A (x * (5 + 5) + 2 * 1)) (pg 8 (mask 8) (F 1) x))
    (Act.andB (Nat.beq (CFSG.KAct.SuzRhoJ2.A (x * (5 + 5) + 2 * 2)) (pg 8 (mask 8) (F 2) x))
    (Act.andB (Nat.beq (CFSG.KAct.SuzRhoJ2.A (x * (5 + 5) + 2 * 3)) (pg 8 (mask 8) (F 3) x))
      (Nat.beq (CFSG.KAct.SuzRhoJ2.A (x * (5 + 5) + 2 * 4)) (pg 8 (mask 8) (F 4) x)))))) =
    true := by
  quickRfl

private def d6 : List (Fin m2 × Bool) := List.replicate 6 (⟨3, m2_eq ▸ (by decide : 3 < 5)⟩, true)

theorem moved : Act.distinctOK CFSG.KAct.SuzRhoJ2.A (Nat.add 5 5) 200 [[], [6, 6, 6, 6, 6, 6]] [0]
    [0, 1] = true := by
  quickRfl

theorem suzRhoJ2Arrs_get {g : ℕ} (hg : g < 5) : suzRhoJ2Arrs[g]! = unpack 200 8 (F g) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound RhoJ2Text.all g hg
  rw [← RhoJ2Text.eq] at h
  rw [suzRhoJ2Arrs, getElem!_pos _ g (by simpa using hg), Array.getElem_ofFn]
  exact h

theorem check : suzRhoJ2Check = true := by
  have hpt := Act.pointOK_of_allR CFSG.KAct.SuzRhoJ2.all
  have hpt' : ∀ x < 200, Act.pointOK CFSG.KAct.SuzRhoJ2.A m2 200 CFSG.KAct.SuzRhoJ2.rels x = true := by
    rw [m2_eq]
    exact hpt
  obtain ⟨σ, hσ⟩ := Act.exists_rep hpt'
  have hb := Act.allR_spec bind
  have hrep : ∀ g (hg : g < 5), Rep 200 suzRhoJ2Arrs[g]! (σ ⟨g, m2_eq ▸ hg⟩) := by
    intro g hg x
    have hx := hb x.val (Nat.zero_le _) (by simp)
    simp only [Act.andB_eq, Bool.and_eq_true] at hx
    rw [suzRhoJ2Arrs_get hg, unpack, getElem!_ofFn_nat _ x.2]
    have hr := (hσ ⟨g, m2_eq ▸ hg⟩ x).1
    simp only [m2_eq] at hr
    interval_cases g
    · exact (Nat.eq_of_beq_eq_true hx.1).symm.trans hr
    · exact (Nat.eq_of_beq_eq_true hx.2.1).symm.trans hr
    · exact (Nat.eq_of_beq_eq_true hx.2.2.1).symm.trans hr
    · exact (Nat.eq_of_beq_eq_true hx.2.2.2.1).symm.trans hr
    · exact (Nat.eq_of_beq_eq_true hx.2.2.2.2).symm.trans hr
  let gs : ℕ → Equiv.Perm (Fin 200) := fun i => if h : i < 5 then σ ⟨i, m2_eq ▸ h⟩ else 1
  have hgs : ∀ i < 5, Rep 200 suzRhoJ2Arrs[i]! (gs i) := fun i hi => by
    simp only [gs, hi, ↓reduceDIte]
    exact hrep i hi
  have hsize : suzRhoJ2Arrs.size = 5 := rfl
  have hinv : ∀ i < 5, isInvA 200 suzRhoJ2Arrs[i]! (invCand 200 suzRhoJ2Arrs[i]!) = true :=
    fun i hi => RhoPerm.isInvA_of_rep (hgs i hi)
  have hval : ∀ w : List (Fin m2 × Bool), wordIn 5 gs (zword w) = signedProd σ w := by
    intro w
    have e5 : wordIn 5 gs (zword w) = wordIn m2 gs (zword w) :=
      congrArg (fun k => wordIn k gs (zword w)) m2_eq.symm
    rw [e5, ← CFSG.Sporadic.Recognition.CoverTransfer.lift_mk_eq_wordIn, lift_mk_eq_signedProd]
    congr 1
    funext i
    have hi : (i : ℕ) < 5 := lt_of_lt_of_eq i.2 m2_eq
    simp only [gs, hi, ↓reduceDIte, Fin.eta]
  have hw := Act.relsAt_sound hσ suzCover2 hrels
    (fun x hx => Act.relsAt_of_pointOK (hpt' x hx))
  have hne : signedProd σ d6 ≠ 1 := by
    have h := Act.distinctOK_sound hσ [[], d6] (rels := [[], [6, 6, 6, 6, 6, 6]]) (by decide)
      (by rw [m2_eq]; exact moved) 0 1 (by decide) (by decide)
    intro h1
    exact absurd (h (by rw [List.getElem_cons_zero, signedProd_nil, List.getElem_cons_succ,
      List.getElem_cons_zero, h1])) (by decide)
  unfold suzRhoJ2Check
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  refine ⟨⟨?_, fun w hwm => ⟨hletters w hwm, ?_⟩⟩, ?_⟩
  · rw [allPermsOK, hsize, CFSG.Monster.B.Co2.allLt_iff]
    exact hinv
  · rw [eqA_iff (rep_wordArr (by omega) hgs hinv (hletters w hwm)) rep_idA, hval]
    exact hw w hwm
  · cases he : eqA 200 (wordArr 200 suzRhoJ2Arrs [4, 4, 4, 4, 4, 4]) (idA 200)
    · rfl
    · have hl : lettersOK 5 [4, 4, 4, 4, 4, 4] = true := by decide
      have hz : ([4, 4, 4, 4, 4, 4] : List ℤ) = zword d6 := rfl
      rw [eqA_iff (rep_wordArr (by omega) hgs hinv hl) rep_idA, hz, hval] at he
      exact absurd he hne

end CertificateChecks.KernelCosetJ.RhoJ2

end

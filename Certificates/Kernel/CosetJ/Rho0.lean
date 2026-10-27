module

public import CFSG.Sporadic.Recognition.SuzMultiplierInputs
public import Certificates.Kernel.Misc.Coset.SuzRho0A.All
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import Certificates.Kernel.CosetJ.Cover
public import Certificates.Kernel.Bounds.Suz.Binding
import Certificates.Kernel.CosetJ.Suz
import Certificates.Kernel.CosetJ.RhoPerm
import Certificates.Kernel.CosetJ.RhoCover
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

#ks_chars CertificateChecks.KernelCosetJ.Rho0Text CFSG.Sporadic.Recognition.SuzMultiplier.suzRho0Text

#kmisc_hexflat CertificateChecks.KernelCosetJ.Rho0Text
  CFSG.Sporadic.Recognition.SuzMultiplier.suzRho0Text 4 5346 13 7

namespace CertificateChecks.KernelCosetJ.Rho0

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Sporadic.Recognition.SuzMultiplier
  CFSG.LieType.Multipliers CFSG.Certificates CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.LieType.Multipliers.Tits
  CFSG.Sporadic.Schreier.Tits CFSG.Certificates.CosetEnumeration
open CertificateChecks.KernelCosetJ.Rho0Text (F chars)
open CFSG.Monster.B.Co2 (Rep eqA_iff rep_idA getElem!_ofFn_nat allLt_iff)

instance : NeZero gcS := ⟨by decide⟩

private theorem gcS_eq : gcS = 7 := by decide

theorem hR : codes (KernelCosetJ.decodeW gcS CFSG.KBRoute.Suz.rels) = CFSG.KAct.SuzRho0.R := by
  decide +kernel

theorem hW : codes ((List.finRange gcS).map fun i => (i, false) :: suzCommWord i) ++
    codes [suzR3 ++ suzR3 ++ suzR3] = CFSG.KAct.SuzRho0.W := by
  decide +kernel

theorem hletters : ∀ w ∈ suzCover, lettersOK gcS (zword w) = true := by
  rw [Suz.suzCover_eq]
  decide +kernel

theorem hl1 : lettersOK gcS (zword suzR3) = true := by decide +kernel

theorem hl3 : lettersOK gcS (zword (suzR3 ++ suzR3 ++ suzR3)) = true := by decide +kernel

theorem hR3 : suzR3.map letterCode = [2, 10, 12, 2, 10, 12, 2, 10, 12, 2, 10, 12, 2, 10, 12] := by
  decide +kernel

theorem bind : Act.allR 0 5346 (fun x => Act.andB
    (Nat.beq (CFSG.KAct.SuzRho0.A (x * (7 + 7) + (2 * 0 + 1))) (pg 13 (mask 13) (F 0) x))
    (Act.andB (Nat.beq (CFSG.KAct.SuzRho0.A (x * (7 + 7) + (2 * 1 + 1))) (pg 13 (mask 13) (F 1) x))
    (Act.andB (Nat.beq (CFSG.KAct.SuzRho0.A (x * (7 + 7) + (2 * 2 + 1))) (pg 13 (mask 13) (F 2) x))
    (Act.andB (Nat.beq (CFSG.KAct.SuzRho0.A (x * (7 + 7) + (2 * 3 + 1))) (pg 13 (mask 13) (F 3) x))
    (Act.andB (Nat.beq (CFSG.KAct.SuzRho0.A (x * (7 + 7) + (2 * 4 + 1))) (pg 13 (mask 13) (F 4) x))
    (Act.andB (Nat.beq (CFSG.KAct.SuzRho0.A (x * (7 + 7) + (2 * 5 + 1))) (pg 13 (mask 13) (F 5) x))
      (Nat.beq (CFSG.KAct.SuzRho0.A (x * (7 + 7) + (2 * 6 + 1))) (pg 13 (mask 13) (F 6) x)))))))) =
    true := by
  quickRfl

theorem moved : Act.distinctOK CFSG.KAct.SuzRho0.A (Nat.add 7 7) 5346
    [[], [2, 10, 12, 2, 10, 12, 2, 10, 12, 2, 10, 12, 2, 10, 12]] [0] [0, 1] = true := by
  quickRfl

theorem suzRho0Arrs_get {g : ℕ} (hg : g < 7) : suzRho0Arrs[g]! = unpack 5346 13 (F g) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound Rho0Text.all g hg
  rw [← Rho0Text.eq] at h
  rw [suzRho0Arrs, getElem!_pos _ g (by simpa using hg), Array.getElem_ofFn]
  exact h

theorem check : suzRho0Check = true := by
  have hpt := Act.coverPointOK_of_allR CFSG.KAct.SuzRho0.all
  have hpt' : ∀ x < 5346, Act.coverPointOK CFSG.KAct.SuzRho0.A CFSG.KAct.SuzRho0.B gcS 5346
      CFSG.KAct.SuzRho0.R CFSG.KAct.SuzRho0.W x = true := by
    rw [gcS_eq]
    exact hpt
  obtain ⟨σ, hσ, hw⟩ := RhoCover.cover_trivial _ suzCommWord [suzR3 ++ suzR3 ++ suzR3] hR hW hpt'
  have hb := Act.allR_spec bind
  have hrep : ∀ g (hg : g < 7), Rep 5346 suzRho0Arrs[g]! (σ ⟨g, gcS_eq ▸ hg⟩)⁻¹ := by
    intro g hg x
    have hx := hb x.val (Nat.zero_le _) (by simp)
    simp only [Act.andB_eq, Bool.and_eq_true] at hx
    rw [suzRho0Arrs_get hg, unpack, getElem!_ofFn_nat _ x.2]
    have hr := (hσ ⟨g, gcS_eq ▸ hg⟩ x).2
    simp only [gcS_eq] at hr
    interval_cases g
    · exact (Nat.eq_of_beq_eq_true hx.1).symm.trans hr
    · exact (Nat.eq_of_beq_eq_true hx.2.1).symm.trans hr
    · exact (Nat.eq_of_beq_eq_true hx.2.2.1).symm.trans hr
    · exact (Nat.eq_of_beq_eq_true hx.2.2.2.1).symm.trans hr
    · exact (Nat.eq_of_beq_eq_true hx.2.2.2.2.1).symm.trans hr
    · exact (Nat.eq_of_beq_eq_true hx.2.2.2.2.2.1).symm.trans hr
    · exact (Nat.eq_of_beq_eq_true hx.2.2.2.2.2.2).symm.trans hr
  let gs : ℕ → Equiv.Perm (Fin 5346) := fun i => if h : i < 7 then (σ ⟨i, gcS_eq ▸ h⟩)⁻¹ else 1
  have hgs : ∀ i < gcS, Rep 5346 suzRho0Arrs[i]! (gs i) := fun i hi => by
    have hi' : i < 7 := gcS_eq ▸ hi
    simp only [gs, hi', ↓reduceDIte]
    exact hrep i hi'
  have hsize : suzRho0Arrs.size = gcS := by rw [suzRho0Arrs, Array.size_ofFn, gcS_eq]
  have hinv : ∀ i < gcS, isInvA 5346 suzRho0Arrs[i]! (invCand 5346 suzRho0Arrs[i]!) = true :=
    fun i hi => RhoPerm.isInvA_of_rep (hgs i hi)
  have hval : ∀ w : List (Fin gcS × Bool),
      wordIn gcS gs (zword w) = signedProd (fun g => (σ g)⁻¹) w := by
    intro w
    rw [← CFSG.Sporadic.Recognition.CoverTransfer.lift_mk_eq_wordIn, lift_mk_eq_signedProd]
    congr 1
    funext i
    have hi : (i : ℕ) < 7 := lt_of_lt_of_eq i.2 gcS_eq
    simp only [gs, hi, ↓reduceDIte, Fin.eta]
  have hne := RhoCover.ne_one_of_distinct hσ suzR3 (by rw [hR3]) (by rw [gcS_eq]; exact moved)
  unfold suzRho0Check
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  refine ⟨⟨⟨⟨?_, fun w hwm => ⟨hletters w hwm, ?_⟩⟩, hl1⟩, ?_⟩, ?_⟩
  · rw [allPermsOK, hsize, allLt_iff]
    exact hinv
  · rw [eqA_iff (rep_wordArr hsize.symm.le hgs hinv (hletters w hwm)) rep_idA, hval]
    have hwm' : w ∈ coverWords (KernelCosetJ.decodeW gcS CFSG.KBRoute.Suz.rels) suzCommWord := by
      rw [← Suz.suzCover_eq]
      exact hwm
    exact hw w (List.mem_append_left _ hwm')
  · cases he : eqA 5346 (wordArr 5346 suzRho0Arrs (zword suzR3)) (idA 5346)
    · rfl
    · rw [eqA_iff (rep_wordArr hsize.symm.le hgs hinv hl1) rep_idA, hval] at he
      exact absurd he hne
  · rw [eqA_iff (rep_wordArr hsize.symm.le hgs hinv hl3) rep_idA, hval]
    exact hw _ (List.mem_append_right _ (List.mem_singleton_self _))

end CertificateChecks.KernelCosetJ.Rho0

end

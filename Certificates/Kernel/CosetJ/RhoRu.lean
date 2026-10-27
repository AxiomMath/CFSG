module

public import CFSG.Sporadic.Recognition.RuMultiplierInputs
public import Certificates.Kernel.Misc.Coset.RuRhoA.All
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import Certificates.Kernel.CosetJ.Cover
public import CFSG.Certificates.Kernel.Orders.Ru.Rels
import Certificates.Kernel.CosetJ.Ru
import Certificates.Kernel.CosetJ.RhoPerm
import Certificates.Kernel.CosetJ.RhoCover
import CFSG.Sporadic.Recognition.CoverTransferWords
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import all CFSG.Sporadic.Recognition.RuMultiplierInputs
import all CFSG.Sporadic.Presentation.RuExactInputs
import all CFSG.LieType.Multipliers.CoverWords
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Rudvalis
public import Certificates.Kernel.LocalComp.SurjGen
public import CFSG.Certificates.Kernel.SurjKSound
meta import CFSG.Sporadic.Recognition.RuMultiplierData
meta import Certificates.Data.CFSGNative.Bridge.SurjD
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Certificates.SeededRelations
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.Sporadic.Presentation.Common

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelCosetJ.RhoRuText CFSG.Sporadic.Recognition.RuMultiplier.ruRhoText

#kmisc_hexflat CertificateChecks.KernelCosetJ.RhoRuText
  CFSG.Sporadic.Recognition.RuMultiplier.ruRhoText 4 16240 14 3

#ks_chars CertificateChecks.KernelCosetJ.RuSurjT CFSG.Sporadic.Bridge.SurjD.Native.ruSurjText

#lc_words CertificateChecks.KernelCosetJ.RuSurjT CFSG.Sporadic.Bridge.SurjD.Native.ruSurjText

namespace CertificateChecks.KernelCosetJ.RhoRu

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Sporadic.Recognition.RuMultiplier
  CFSG.LieType.Multipliers CFSG.Certificates CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.LieType.Multipliers.Tits
  CFSG.Sporadic.Schreier.Tits CFSG.Certificates.CosetEnumeration CFSG.Sporadic.Presentation.Ru.Exact
open CertificateChecks.KernelCosetJ.RhoRuText (F chars)
open CFSG.Monster.B.Co2 (Rep eqA_iff rep_idA getElem!_ofFn_nat allLt_iff toLetters)

instance : NeZero gc := ⟨by decide⟩

private theorem gc_eq : gc = 3 := by decide

theorem W0_eq : W0 = KernelCosetJ.decodeW gc CFSG.KD.OrdRu.rels := eq_decodeW Ru.w0_eq

theorem hR : codes (KernelCosetJ.decodeW gc CFSG.KD.OrdRu.rels) = CFSG.KAct.RuRho.R := by
  decide +kernel

theorem hW : codes ((List.finRange gc).map fun i => (i, false) :: ruCommWord i) ++
    codes ([] : List (List (Fin gc × Bool))) = CFSG.KAct.RuRho.W := by
  decide +kernel

theorem hletters : ∀ w ∈ ruCover, lettersOK gc (zword w) = true := by
  rw [ruCover, W0_eq]
  decide +kernel

theorem surj_words :
    CFSG.KC.SurjK.wordsK CertificateChecks.KernelCosetJ.RuSurjT.chars CertificateChecks.KernelCosetJ.RuSurjT.W = true := by
  quickRfl

theorem ruP0_eq : ruP0 = toLetters gc CertificateChecks.KernelCosetJ.RuSurjT.W.toArray[0]! := by
  have h := CFSG.KC.SurjK.wordsK_sound surj_words
  rw [← CertificateChecks.KernelCosetJ.RuSurjT.eq] at h
  have e : CFSG.Sporadic.Bridge.SurjD.Native.ruSpec.surjWords =
      CFSG.Sporadic.Bridge.SurjD.Native.parseWords
        CFSG.Sporadic.Bridge.SurjD.Native.ruSurjText := rfl
  rw [ruP0, e, h]

theorem hl : lettersOK gc (zword (ruP0 ++ ruP0)) = true := by
  rw [ruP0_eq]
  decide +kernel

@[expose] def p0sq : List ℕ :=
    [0, 5, 1, 1, 5, 1, 5, 1, 1, 5, 1, 3, 1, 2, 1, 4, 0, 2, 4, 0, 4, 2, 4, 0, 0, 4, 1, 4, 0, 0, 4,
    1, 5, 1, 5, 1, 5, 1, 1, 5, 1, 5, 0, 5, 1, 1, 5, 1, 1, 1, 5, 1, 1, 5, 2, 1, 4, 0, 0, 4, 0, 4, 2,
    5, 3, 3, 3, 3, 3, 3, 1, 5, 1, 1, 3, 5, 1, 5, 5, 5, 3, 3, 3, 5, 0, 5, 1, 5, 1, 1, 5, 1, 1, 5, 1,
    1, 5, 1, 5, 1, 5, 1, 1, 5, 0, 5, 1, 1, 5, 3, 5, 1, 1, 5, 3, 5, 0, 3, 1, 5, 3, 5, 1, 1, 5, 3, 5,
    1, 1, 5, 3, 0, 3, 1, 3, 3, 5, 1, 5, 1, 1, 3, 1, 5, 3, 3, 5, 3, 1, 3, 5, 3, 5, 1, 5, 1, 5, 1, 1,
    5, 0, 5, 0, 5, 2, 4, 1, 2, 4, 1, 4, 1, 4, 3, 1, 1, 5, 1, 3, 5, 0, 5, 1, 1, 5, 1, 5, 1, 1, 5, 1,
    3, 1, 2, 1, 4, 0, 2, 4, 0, 4, 2, 4, 0, 0, 4, 1, 4, 0, 0, 4, 1, 5, 1, 5, 1, 5, 1, 1, 5, 1, 5, 0,
    5, 1, 1, 5, 1, 1, 1, 5, 1, 1, 5, 2, 1, 4, 0, 0, 4, 0, 4, 2, 5, 3, 3, 3, 3, 3, 3, 1, 5, 1, 1, 3,
    5, 1, 5, 5, 5, 3, 3, 3, 5, 0, 5, 1, 5, 1, 1, 5, 1, 1, 5, 1, 1, 5, 1, 5, 1, 5, 1, 1, 5, 0, 5, 1,
    1, 5, 3, 5, 1, 1, 5, 3, 5, 0, 3, 1, 5, 3, 5, 1, 1, 5, 3, 5, 1, 1, 5, 3, 0, 3, 1, 3, 3, 5, 1, 5,
    1, 1, 3, 1, 5, 3, 3, 5, 3, 1, 3, 5, 3, 5, 1, 5, 1, 5, 1, 1, 5, 0, 5, 0, 5, 2, 4, 1, 2, 4, 1, 4,
    1, 4, 3, 1, 1, 5, 1, 3, 5]

theorem hP0 : (ruP0 ++ ruP0).map letterCode = p0sq := by
  rw [ruP0_eq]
  decide +kernel

theorem bind : Act.allR 0 16240 (fun x => Act.andB
    (Nat.beq (CFSG.KAct.RuRho.A (x * (3 + 3) + (2 * 0 + 1))) (pg 14 (mask 14) (F 0) x))
    (Act.andB (Nat.beq (CFSG.KAct.RuRho.A (x * (3 + 3) + (2 * 1 + 1))) (pg 14 (mask 14) (F 1) x))
      (Nat.beq (CFSG.KAct.RuRho.A (x * (3 + 3) + (2 * 2 + 1))) (pg 14 (mask 14) (F 2) x)))) =
    true := by
  quickRfl

theorem moved : Act.distinctOK CFSG.KAct.RuRho.A (Nat.add 3 3) 16240 [[], p0sq] [0] [0, 1] =
    true := by
  quickRfl

theorem ruRhoArrs_get {g : ℕ} (hg : g < 3) : ruRhoArrs[g]! = unpack 16240 14 (F g) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound RhoRuText.all g hg
  rw [← RhoRuText.eq] at h
  rw [← h]
  interval_cases g <;> rfl

theorem check : ruRhoCheck = true := by
  have hpt := Act.coverPointOK_of_allR CFSG.KAct.RuRho.all
  have hpt' : ∀ x < 16240, Act.coverPointOK CFSG.KAct.RuRho.A CFSG.KAct.RuRho.B gc 16240
      CFSG.KAct.RuRho.R CFSG.KAct.RuRho.W x = true := by
    rw [gc_eq]
    exact hpt
  obtain ⟨σ, hσ, hw⟩ := RhoCover.cover_trivial _ ruCommWord [] hR hW hpt'
  have hb := Act.allR_spec bind
  have hrep : ∀ g (hg : g < 3), Rep 16240 ruRhoArrs[g]! (σ ⟨g, gc_eq ▸ hg⟩)⁻¹ := by
    intro g hg x
    have hx := hb x.val (Nat.zero_le _) (by simp)
    simp only [Act.andB_eq, Bool.and_eq_true] at hx
    rw [ruRhoArrs_get hg, unpack, getElem!_ofFn_nat _ x.2]
    have hr := (hσ ⟨g, gc_eq ▸ hg⟩ x).2
    simp only [gc_eq] at hr
    interval_cases g
    · exact (Nat.eq_of_beq_eq_true hx.1).symm.trans hr
    · exact (Nat.eq_of_beq_eq_true hx.2.1).symm.trans hr
    · exact (Nat.eq_of_beq_eq_true hx.2.2).symm.trans hr
  let gs : ℕ → Equiv.Perm (Fin 16240) := fun i => if h : i < 3 then (σ ⟨i, gc_eq ▸ h⟩)⁻¹ else 1
  have hgs : ∀ i < gc, Rep 16240 ruRhoArrs[i]! (gs i) := fun i hi => by
    have hi' : i < 3 := gc_eq ▸ hi
    simp only [gs, hi', ↓reduceDIte]
    exact hrep i hi'
  have hsize : ruRhoArrs.size = gc := by rw [gc_eq]; rfl
  have hinv : ∀ i < gc, isInvA 16240 ruRhoArrs[i]! (invCand 16240 ruRhoArrs[i]!) = true :=
    fun i hi => RhoPerm.isInvA_of_rep (hgs i hi)
  have hval : ∀ w : List (Fin gc × Bool),
      wordIn gc gs (zword w) = signedProd (fun g => (σ g)⁻¹) w := by
    intro w
    rw [← CFSG.Sporadic.Recognition.CoverTransfer.lift_mk_eq_wordIn, lift_mk_eq_signedProd]
    congr 1
    funext i
    have hi : (i : ℕ) < 3 := lt_of_lt_of_eq i.2 gc_eq
    simp only [gs, hi, ↓reduceDIte, Fin.eta]
  have hne := RhoCover.ne_one_of_distinct hσ (ruP0 ++ ruP0) (by rw [hP0])
    (by rw [gc_eq]; exact moved)
  unfold ruRhoCheck
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  refine ⟨⟨⟨?_, fun w hwm => ⟨hletters w hwm, ?_⟩⟩, hl⟩, ?_⟩
  · rw [allPermsOK, hsize, allLt_iff]
    exact hinv
  · rw [eqA_iff (rep_wordArr hsize.symm.le hgs hinv (hletters w hwm)) rep_idA, hval]
    have hwm' : w ∈ coverWords (KernelCosetJ.decodeW gc CFSG.KD.OrdRu.rels) ruCommWord := by
      rw [← W0_eq]
      exact hwm
    exact hw w (List.mem_append_left _ hwm')
  · cases he : eqA 16240 (wordArr 16240 ruRhoArrs (zword (ruP0 ++ ruP0))) (idA 16240)
    · rfl
    · rw [eqA_iff (rep_wordArr hsize.symm.le hgs hinv hl) rep_idA, hval] at he
      exact absurd he hne

end CertificateChecks.KernelCosetJ.RhoRu

end

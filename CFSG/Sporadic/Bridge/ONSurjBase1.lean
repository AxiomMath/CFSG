
module

public import CFSG.Sporadic.Bridge.ONSurjBase
import all CFSG.Sporadic.Bridge.ONSurjBase

public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.Presentation.ONan
public import Certificates.Data.CFSGNative.Bridge.ONGPL
public meta import Certificates.Data.CFSGNative.Bridge.ONGPL
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Presentation.ONanInputs
public import Certificates.Certificate9217
public import Certificates.Data.CFSGNative.ON.Certificate
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate9217Base

@[expose] public section

namespace CFSG.Sporadic.Bridge.ON

open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm.Native CFSG.Sporadic.Bridge.ONGPL.Native TauCeti

theorem bridge_check : bridgeCheck () = true := by
  exact Certificates.certificate9217

theorem image_checks :
    imageChecks orb.alpha orb.beta imgT imgTv = true := by
  have h : seedChecks orb.alpha orb.beta (invT nPts orb.alpha) (invT nPts orb.beta) = true :=
    bridge_check
  have e : seedChecks orb.alpha orb.beta (invT nPts orb.alpha) (invT nPts orb.beta) =
      (invOK nPts orb.alpha (invT nPts orb.alpha) && invOK nPts orb.beta (invT nPts orb.beta) &&
        imageChecks orb.alpha orb.beta
          (imgWords.map (wordT nPts (seedLetter
            #[orb.alpha, invT nPts orb.alpha, orb.beta, invT nPts orb.beta])))
          ((imgWords.map (wordT nPts (seedLetter
            #[orb.alpha, invT nPts orb.alpha, orb.beta, invT nPts orb.beta]))).map (invT nPts))) :=
    rfl
  rw [e, seedLetter_eq, Bool.and_eq_true] at h
  exact h.2

theorem bridge_facts : BridgeFacts := by
  have h := image_checks
  unfold imageChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Array.all_eq_true,
    bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h8⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, ?_, h3, h4, h5, h6⟩
  intro w hw z hz
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hw
  exact h8 i hi z hz

theorem imgT_getElem
    {k : ℕ} (hk : k < 7) : imgT[k]! = wordT nPts (genT orb) imgWords[k]! := by
  have hk' : k < imgWords.size := by rw [bridge_facts.sizeImg]; exact hk
  rw [getElem!_pos imgT k (by rw [Array.size_map]; exact hk'), Array.getElem_map,
    getElem!_pos imgWords k hk']

theorem surjWords_mem
    {i : ℕ} (hi : i < 2) : surjWords[i]! ∈ surjWords := by
  have hi' : i < surjWords.size := by rw [bridge_facts.sizeSurj]; exact hi
  rw [getElem!_pos surjWords i hi']
  exact Array.getElem_mem hi'

end CFSG.Sporadic.Bridge.ON

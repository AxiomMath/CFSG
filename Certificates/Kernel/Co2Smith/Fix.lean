module

public import Certificates.Kernel.Co2Smith.W
public import Certificates.Kernel.Co2Smith.Pts
public import Certificates.Kernel.Co2Smith.FixK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith CFSG.KC.Enum
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native

theorem fxIdx_spec {Y j : Nat} (h : fxIdx Y = some j) : j < FXN 0 ∧ eqK Y (FXM j) = true := by
  unfold fxIdx at h
  have hm := List.mem_of_find?_eq_some h
  exact ⟨List.mem_range.1 hm, by simpa using List.find?_some h⟩

theorem fx_facts {Y j : Nat} (h : fxIdx Y = some j) :
    glPermOK (unpackR 22 Y) (glPermArr (unpackR 22 Y)) = true ∧
      glMkFixCount (glPermArr (unpackR 22 Y)) = fixCntK (FXP j) := by
  obtain ⟨hj, he⟩ := fxIdx_spec h
  have hb := CFSG.KS.allN_spec fxBind_k j hj
  rw [eq_unpack_of_eqK he]
  exact ⟨permOK_of hb, by rw [permArr_eq hb, fixCount_eq]⟩

theorem fxIs_sound {Y k : Nat} (h : fxIs Y k = true) : glMkFixIs (unpackR 22 Y) k = true := by
  unfold fxIs at h
  cases e : fxIdx Y with
  | none => rw [e] at h; exact absurd h Bool.false_ne_true
  | some j =>
    rw [e] at h
    obtain ⟨h1, h2⟩ := fx_facts e
    unfold glMkFixIs
    simp only
    rw [h1, h2, Bool.true_and]
    exact h

theorem tany_sound {Y : Nat} (h : (List.range 15).any (fun j => eqK Y (TP j)) = true) :
    glMkT.contains (unpackR 22 Y) = true := by
  obtain ⟨j, hj, he⟩ := List.any_eq_true.1 h
  rw [List.mem_range] at hj
  rw [Array.contains_iff, Array.mem_iff_getElem]
  refine ⟨j, by simp [glMkT, hj], ?_⟩
  rw [← getElem!_pos glMkT j (by simp [glMkT, hj]), mkT_get hj]
  exact (eq_unpack_of_eqK he).symm

theorem fixAll_ok : glMkFixAllOK = true := by
  have hK := fixAll_k
  unfold fixAllK at hK
  simp only [Bool.and_eq_true, List.all_eq_true] at hK
  obtain ⟨⟨h1, h2⟩, h3⟩ := hK
  unfold glMkFixAllOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [glZ_eq]
    exact fxIs_sound h1
  · rw [dc_eq, List.all_map, List.all_eq_true]
    intro Y hY
    have hy := h2 Y hY
    simp only [Function.comp, mulRows_unpack, idRows_eq, beq_unpack, bne_unpack, glZ_eq]
    change (!(eqK (mulV Y Y) IDP && !eqK Y IDP && !eqK Y zK) || _) = true
    cases hg : (eqK (mulV Y Y) IDP && !eqK Y IDP && !eqK Y zK)
    · rfl
    · rw [hg] at hy
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true] at hy
      obtain ⟨hs, hr⟩ := hy
      obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 hs
      obtain ⟨hp, hc⟩ := fx_facts hj
      simp only [Bool.not_true, Bool.false_or, hp, Bool.true_and, Bool.or_eq_true]
      rcases hr with (hr | hr) | hr
      · left; left
        unfold fxIs at hr
        rw [hj] at hr
        rw [hc]
        simpa using hr
      · left; right
        exact tany_sound hr
      · right
        exact fxIs_sound hr
  · rw [dc_eq, List.all_map, List.all_eq_true]
    intro B hB
    have hb := h3 B hB
    simp only [Function.comp, mulRows_unpack, idRows_eq, beq_unpack, bne_unpack]
    cases hg : (!eqK (mulV B B) IDP && eqK (mulV (mulV B B) (mulV B B)) IDP)
    · simp only [Bool.not_false, Bool.true_or]
    · rw [hg] at hb
      simp only [Bool.not_true, Bool.false_or] at hb ⊢
      exact fxIs_sound hb

theorem a0_ok : glMkA0OK = true := by
  rw [← a0_k]
  unfold glMkA0OK a0K
  simp only [glR_eq (w := glMkA0Word) (by decide), glR_eq (w := glMkC1Word) (by decide),
    mkT_get (j := 0) (by decide), glZ_eq, mulRows_unpack, commRows_unpack, idRows_eq, bne_unpack,
    beq_unpack]
  rfl

theorem fix_ok : glMkFixOK = true := by
  unfold glMkFixOK
  rw [fixAll_ok, a0_ok]
  rfl

end CertificateChecks.KernelCo2Smith

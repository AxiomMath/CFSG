module

public import Certificates.Kernel.Co2Smith.Root
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co2Smith.GlDataF0Inputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native

@[expose] noncomputable def hK (i : Nat) : Nat := wK SM hWords[i]!

@[expose] noncomputable def qK (e : Nat) : Nat :=
  let m := (List.range 8).foldr (fun i acc => if (e % 256).testBit i then mulV (hK i) acc else acc)
    IDP
  if e / 256 == 1 then mulV (SM 0) m else m

@[expose] noncomputable def SZ : Nat := Nat.xor zK IDP

theorem hWords_k : (hWords.size == 8 && (List.range 8).all fun i => (hWords[i]!).all (· < 4)) =
    true := by decide +kernel

theorem glHR_get {i : Nat} (hi : i < 8) : glHR[i]! = unpackR 22 (hK i) := by
  have h := hWords_k
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  unfold glHR hRows
  have hw : hWords[i]! = hWords[i]'(by rw [h.1]; exact hi) := getElem!_pos hWords i _
  rw [getElem!_pos _ i (by simp [h.1, hi]), Array.getElem_map, mRows, ← hw,
    wRows_unpack _ SM _ (fun k hk => letters_get k (h.2 i hi k hk)), hK]

theorem glQRows_eq (e : Nat) : glQRows e = unpackR 22 (qK e) := by
  unfold glQRows nfRows qK
  have hm : ((List.range 8).foldr (fun i acc => if (e % 256).testBit i then
      mulRows 22 glHR[i]! acc else acc) (idRows 22)) = unpackR 22 ((List.range 8).foldr
      (fun i acc => if (e % 256).testBit i then mulV (hK i) acc else acc) IDP) := by
    have : ∀ l : List Nat, (∀ i ∈ l, i < 8) → (l.foldr (fun i acc => if (e % 256).testBit i then
        mulRows 22 glHR[i]! acc else acc) (idRows 22)) = unpackR 22 (l.foldr
        (fun i acc => if (e % 256).testBit i then mulV (hK i) acc else acc) IDP) := by
      intro l hl
      induction l with
      | nil => exact idRows_eq
      | cons a l ih =>
        rw [List.foldr_cons, List.foldr_cons, ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))]
        split_ifs
        · rw [glHR_get (hl a List.mem_cons_self), mulRows_unpack]
        · rfl
    exact this _ (fun i hi => List.mem_range.1 hi)
  simp only
  rw [hm]
  split_ifs
  · rw [seeds_get 0 (by decide), mulRows_unpack]
  · rfl

theorem subId_zK : subId (unpackR 22 (wK LP [0])) = unpackR 22 SZ := by
  decide +kernel

theorem validM_unpack (X : Nat) : validM (unpackR 22 X) = true := by
  simp only [validM, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]
  refine ⟨by simp [unpackR], fun i hi => ?_⟩
  simp only [unpackR, Array.getElem_ofFn]
  exact Nat.mod_lt _ (by norm_num)

theorem glHRows_eq (k : Nat) : glHRows k = unpackR 22 (if k == 1 then d1K else if k == 2 then
    mulV d0K d1K else if k == 4 then mulV d1K w1K else mulV (mulV d0K d1K) w1K) := by
  obtain ⟨-, h0, h1, -⟩ := el_eqs
  obtain ⟨e1, -⟩ := frame_eqs
  unfold glHRows
  split_ifs <;> simp only [h0, h1, e1, mulRows_unpack]

theorem f0_neg : ((((List.range 512).filter fun e =>
    commK (mulV (mulV d1K (qK e)) (frameConjK 1)) zK).length != 127) &&
    !eqK (qK 1) (qK 2)) = true := by
  decide +kernel

theorem f0_ok : glF0OK = true := by
  unfold glF0OK glF0kOK glF0Conj glFixZ glF0Valid
  simp only [glHRows_eq, glFrameConjRows_eq, glQRows_eq, glRootRows_eq, glZ_eq, subId_zK, mulRows_unpack, commRows_unpack, beq_unpack, bne_unpack, validM_unpack, idRows_eq]
  decide +kernel

end CertificateChecks.KernelCo2Smith


module

public import CFSG.Sporadic.Co1.Module.OddCentCardInputs
public import Certificates.Kernel.Co1Cover.Bridge
public import Certificates.Kernel.Co1M.K10072
public import Certificates.Kernel.Co1M.Regs10072
public import Certificates.Kernel.Co1M.C10071
public import CFSG.Certificates.Kernel.Co1M.VTreeLitSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.J4.ParSpec
public import CFSG.Sporadic.J4.Setup
public import Certificates.Data.Kernel.J4Q.MatChk

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.J4Q CFSG.KC.Co1M CFSG.KD.Co1M CFSG.KC.LQT.Syl CFSG.KC.Co1F2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative CFSG.Sporadic.Co1.OddCentNative
  CFSG.Sporadic.Co1.Module.Odd CertificateChecks.KernelCo1Cover

theorem cm_prog3L : PROG3L = prog3 := eq_of_beq (by quickRfl)

theorem cm_rr27 : rr 27 = unpackR 24 (getL 0 cmRP71 27) := c71_rr (by rw [c71_len]; decide)

theorem cm_regs3 : regsRows3 = (cmRP3.map (unpackR 24)).toArray := by
  rw [regsRows3, initRows3, rowsA_eq, rowsB_eq, cm_rr27, ← cm_prog3L, ← prog_sound cm_prog3_chk]
  rfl

theorem cm_getL_eq (x : Nat) : ∀ (L : List Nat) (i : Nat), getL x L i = L.getD i x
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => cm_getL_eq x L i

theorem cm_get_map {L : List Nat} {i : Nat} (hi : i < L.length) :
    (L.map (unpackR 24)).toArray[i]?.getD (idRows 24) = unpackR 24 (getL 0 L i) := by
  rw [cm_getL_eq, List.getD_eq_getElem _ _ hi]
  simp [hi]

theorem cm_len3 : cmRP3.length = 15 := Nat.eq_of_beq_eq_true (by quickRfl)

@[expose] noncomputable def cm72G : Array (Array Nat) :=
  #[unpackR 24 (getL 0 cmRP3 6), unpackR 24 (getL 0 cmRP3 10), unpackR 24 (getL 0 cmRP3 14)]

theorem cm72_gens : genRows3 = cm72G := by
  unfold genRows3 rr3
  rw [cm_regs3]
  simp only [genIdx3, List.map_cons, List.map_nil]
  rw [cm_get_map (by rw [cm_len3]; decide), cm_get_map (by rw [cm_len3]; decide),
    cm_get_map (by rw [cm_len3]; decide)]
  rfl

theorem cm72_rs : GT3 = cm72G.toList.map fun M => (transposeRows 24 M).toList :=
  eq_of_beq (by quickRfl)

theorem cm72_valid : ∀ M ∈ cm72G.toList, validRows M = true := by
  intro M hM
  simp only [cm72G, List.mem_cons, List.mem_nil_iff, or_false] at hM
  rcases hM with rfl | rfl | rfl <;> exact validRows_unpackR _

theorem cm_andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem cm_allR_spec {n : Nat} {f : Nat → Bool} (h : allR n f = true) : ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro i hi
    change andB (allR n f) (f n) = true at h
    rw [cm_andB_eq, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h.1 i hi
    · exact h.2

theorem cm72_forall_mem {α : Type} {f : α → Bool} {d : α} {l : List α}
    (h : ∀ i < l.length, f (l.getD i d) = true) : ∀ x ∈ l, f x = true := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  have := h i hi
  rwa [List.getD_eq_getElem _ _ hi] at this

@[expose] noncomputable def cm72Tree : VTree := vtLit RM112 cmCode4 CH72.flatten

theorem cm72_tree : vtreeOK genRows3 code4 cm72Tree = true ∧ cm72Tree.pts.size = 32400 := by
  have hs := cm72_size
  simp only [cm_andB_eq, Bool.and_eq_true] at hs
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  have hl : CH72.flatten.length + 1 = 32400 := Nat.eq_of_beq_eq_true h1
  have hc : code4 = cmCode4 := rfl
  have := vtLit_sound (Gr := cm72G) (Rs := GT3) (rm := RM112) (root := cmCode4)
    (chs := CH72) (p0s := FCP0) (SPch := SPC72) rfl cm72_rs cm72_valid (by decide) (by decide)
    (fun i hi => Nat.eq_of_beq_eq_true (cm_allR_spec h3 i (by
      have : CH72.length = 32 := rfl
      omega)))
    (fun ch hch => Nat.le_of_ble_eq_true (List.all_eq_true.1 h4 ch hch)) T72.all cm72_sinc
    (by rw [Nat.eq_of_beq_eq_true h2, hl])
    (fun sc hsc => Nat.le_of_ble_eq_true (List.all_eq_true.1 h5 sc hsc))
    (cm72_forall_mem (f := fun pc => inSK pc SPC72.flatten) I72.all)
    (cm72_forall_mem (f := fun sc => spInK sc (pchK RM112 cmCode4 CH72)) S72.all)
  refine ⟨?_, ?_⟩
  · rw [cm72_gens, hc]
    exact this
  · rw [cm72Tree, vtLit_size, hl]

theorem cm72_comm : (genIdx3.all fun i => mulRows 24 (rr3 i) (rr 27) == mulRows 24 (rr 27) (rr3 i)) =
    true := by
  unfold rr3
  rw [cm_regs3, cm_rr27]
  quickRfl

end CertificateChecks.KernelCo1M

end

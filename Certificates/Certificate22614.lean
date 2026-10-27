module

public import Certificates.Kernel.HS3850.C22614
public import Certificates.Kernel.SporSch.PairHS.HS2272Main
public import CFSG.Certificates.Kernel.SporSch.SporXElemSound

public section

namespace CertificateChecks.Batch22614

open CFSG.Sporadic.SmallOddCore CFSG.KS.SporXE CFSG.KD.HS3850.C22614 Subgroup
open CertificateChecks.KernelSporSch.HS72

theorem row_elem {r : ClassRow} (hr : r ∈ hsRows) {c nl : Nat} (hc : c + nl ≤ 43)
    (hgen : ∀ l < nl, hsCentTbl (c + l) ∈ r.centGens) {words : List (List Nat × Nat)}
    (hck : ckE bsR (lr c) nl words = true) :
    ∃ E : Subgroup (Equiv.Perm (Fin 3850)), E ≤ hsC r ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧
      (∀ a ∈ E, a ^ 2 = 1) ∧ 2 ^ words.length ≤ Nat.card E := by
  have hKH : hsC r ≤ hsR := by
    rw [(rows_all r hr).2.2.2.2.1]
    exact inf_le_left.trans P_le_R
  refine elem_of_ckE faithR bsR_lt hKH (g := fun l => T (c + l)) (fun l hl => ?_)
    (fun l hl => ?_) hck
  · exact (T_rep (k := c + l) (by omega)).1
  · exact subset_closure ⟨hsCentTbl (c + l), List.mem_toArray.mpr (hgen l hl), rfl⟩

theorem elem_all : ∀ r ∈ hsRows, ∃ E : Subgroup (Equiv.Perm (Fin 3850)), E ≤ hsC r ∧
    (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧
    (r.outer = false → 2 ^ 4 ≤ Nat.card E) ∧ 2 ^ 3 ≤ Nat.card E := by
  intro r hr
  have hr' := hr
  simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl
  · obtain ⟨E, hE, hc, hs, hcard⟩ := row_elem hr (c := 6) (nl := 2) (by norm_num)
      (fun l hl => by
        interval_cases l
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self) ck0
    have hl : w0.length = 4 := rfl
    rw [hl] at hcard
    exact ⟨E, hE, hc, hs, fun _ => hcard, le_trans (by norm_num) hcard⟩
  · obtain ⟨E, hE, hc, hs, hcard⟩ := row_elem hr (c := 13) (nl := 4) (by norm_num)
      (fun l hl => by
        interval_cases l
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ List.mem_cons_self))) ck1
    have hl : w1.length = 4 := rfl
    rw [hl] at hcard
    exact ⟨E, hE, hc, hs, fun _ => hcard, le_trans (by norm_num) hcard⟩
  · obtain ⟨E, hE, hc, hs, hcard⟩ := row_elem hr (c := 22) (nl := 4) (by norm_num)
      (fun l hl => by
        interval_cases l
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ List.mem_cons_self))) ck2
    exact ⟨E, hE, hc, hs, fun h => absurd h (by decide), hcard⟩
  · obtain ⟨E, hE, hc, hs, hcard⟩ := row_elem hr (c := 35) (nl := 4) (by norm_num)
      (fun l hl => by
        interval_cases l
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ List.mem_cons_self))) ck3
    exact ⟨E, hE, hc, hs, fun h => absurd h (by decide), hcard⟩

end CertificateChecks.Batch22614

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallOddCore in
theorem certificate22614 : ∀ r ∈ hsRows, ∃ E : Subgroup (Equiv.Perm (Fin 3850)), E ≤ CFSG.Sporadic.SmallOddCore.hsC r ∧
    (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧
    (r.outer = false → 2 ^ 4 ≤ Nat.card E) ∧ 2 ^ 3 ≤ Nat.card E := CertificateChecks.Batch22614.elem_all

end Certificates

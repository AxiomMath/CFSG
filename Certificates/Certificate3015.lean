module

public import CFSG.Monster.B.TwoA.Census.SignClsInputs
public import CFSG.Certificates.Kernel.MonsterB.U6OrbSound
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.Monster.Code CFSG.Monster.B.TwoA.Census CFSG.KC.U6Orb

namespace CertificateChecks.Batch3015

open CFSG.Monster.Code CFSG.Monster.B.TwoA.Census CFSG.KC.U6Orb

theorem kLen : Nat.beq (lenL validList) 2048 = true := by quickRfl

@[expose] def pivI : List ℕ := [1, 0, 4, 8, 12, 16, 2, 3, 6, 5, 10, 9]

@[expose] def decRow : List ℕ := [3935, 3902, 802, 3108, 40, 48, 3999, 4063, 256, 512, 1024, 2048]

@[expose] def decI (n : ℕ) : ℕ :=
  (List.range 12).foldl (fun acc r => if n.testBit (pivI.getD r 0) then acc ^^^ decRow.getD r 0
    else acc) 0

theorem kDec : (List.range 4096).all (fun m => decI (combI m) == m) = true := by decide +kernel

theorem combI_inj : Set.InjOn combI {m | m ∈ List.range 4096} := by
  intro a ha b hb e
  have h := List.all_eq_true.1 kDec
  have ha' := h a ha
  have hb' := h b hb
  simp only [beq_iff_eq] at ha' hb'
  rw [← ha', ← hb', e]

theorem nodup_valid : validList.Nodup :=
  ((List.nodup_range).map_on fun _ ha _ hb e => combI_inj ha hb e).filter _

theorem fold_mem (m : ℕ) : ∀ L : List ℕ, (∀ k ∈ L, k < 12) → ∀ acc, bvec 24 acc ∈ C →
    bvec 24 (L.foldl (fun acc k => if m.testBit k then acc ^^^ Bmask k else acc) acc) ∈ C
  | [], _, _, h => h
  | k :: L, hL, acc, h => by
    refine fold_mem m L (fun j hj => hL j (List.mem_cons_of_mem _ hj)) _ ?_
    dsimp only
    split
    · rw [bvec_xor]
      refine C.add_mem h ?_
      have hk := hL k List.mem_cons_self
      have := B_mem_C ⟨k, hk⟩
      rwa [B_eq_bvec] at this
    · exact h

theorem combI_mem (m : ℕ) : bvec 24 (combI m) ∈ C := by
  refine fold_mem m _ (fun k hk => List.mem_range.1 hk) 0 ?_
  rw [bvec_zero]
  exact C.zero_mem

end CertificateChecks.Batch3015

namespace Certificates

open CertificateChecks

open CFSG.Monster.Code in
open CFSG.Monster.B.TwoA.Census in
theorem certificate3015 : validList.length = 2048 ∧ validList.Nodup ∧ ∀ n ∈ validList, n < 2 ^ 23 ∧ bvec 24 n ∈ C := by
  refine ⟨?_, CertificateChecks.Batch3015.nodup_valid, fun n hn => ?_⟩
  · have := CertificateChecks.Batch3015.kLen
    rwa [Nat.beq_eq, lenL_eq] at this
  · rw [validList, List.mem_filter, List.mem_map] at hn
    obtain ⟨⟨m, -, rfl⟩, h⟩ := hn
    exact ⟨of_decide_eq_true h, CertificateChecks.Batch3015.combI_mem m⟩

end Certificates

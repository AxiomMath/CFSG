module

public import Certificates.Kernel.J4Loc.SubsAsm
public import Certificates.Kernel.J4Loc.RankAsm

public section

namespace Certificates

open CFSG.Quasithin.J4Loc CFSG.KS.J4Loc CertificateChecks.KernelJ4Loc

theorem srt_eq_of_perm4174 {l m : List ℕ} (hp : l.Perm m) (hm : m.Pairwise (· ≤ ·)) :
    srt l = m := by
  have hs : (srt l).Pairwise (fun a b => decide (a ≤ b) = true) :=
    List.pairwise_mergeSort (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  exact List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun a b _ _ h1 h2 => Nat.le_antisymm h1 h2)
    (hs.imp (fun h => by simpa using h)) hm ((List.mergeSort_perm l _).trans hp)

theorem small4174 : spanS [422, 553, 1131] = V0L ∧ V0L ∈ subs ∧
    ∀ B ∈ subs, B.length ≤ 2 → B = [0] ∨ B = z0L := by
  have hv : spanS [422, 553, 1131] = V0L := srt_eq_of_perm4174 (by decide) (by decide)
  refine ⟨hv, ?_, fun B hB h2 => ?_⟩
  · rw [← hv]
    exact List.mem_map_of_mem (by decide)
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hB
    rw [(spanS_spec b).2.1] at h2
    have h1 : b.length ≤ 1 := by
      by_contra hc
      have : 2 ^ 2 ≤ 2 ^ b.length := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hcases : ∀ b ∈ subBases, b.length ≤ 1 → b = [] ∨ b = [1131] := by decide
    rcases hcases b hb h1 with rfl | rfl
    · exact Or.inl (srt_eq_of_perm4174 (by decide) (by decide))
    · exact Or.inr (srt_eq_of_perm4174 (by decide) (by decide))

open CFSG.Quasithin.J4Loc CFSG.Sporadic.J4.QT in
theorem certificate4174 :
    (∀ B ∈ subs, (∀ c ∈ B, c < 2048) ∧ B.Pairwise (· < ·) ∧ 0 ∈ B ∧
      (∀ x ∈ B, ∀ y ∈ B, x ^^^ y ∈ B) ∧
      (∀ i < 4, ∀ c ∈ B, actT (kTab i) c ∈ B ∧ actT (kInvTab i) c ∈ B)) ∧
    [0] ∈ subs ∧
    (∀ B ∈ subs, ∀ v < 2048, v ∉ B → (∀ i < 4, (actT (kTab i) v ^^^ v) ∈ B) →
      ∃ B' ∈ subs, (∀ x ∈ B, x ∈ B') ∧ v ∈ B' ∧ ∀ y ∈ B', y ∈ B ∨ ∃ x ∈ B, y = x ^^^ v) ∧
    (∀ t ∈ tabL, t ≠ idT → 16 ≤ ((Finset.range 2048).image fun c => actT t c ^^^ c).card) ∧
    TrioOct.ncard = 3795 ∧
    (∀ W ∈ TrioOct, W.card = 8 ∧ 0 ∈ W ∧ (∀ x ∈ W, x < 2048) ∧ ∀ x ∈ W, ∀ y ∈ W, x ^^^ y ∈ W) ∧
    (∀ B ∈ subs, 16 ≤ B.length → 8 * xcnt B ≤ B.length ∧
      (8 * xcnt B = B.length → ∀ W ∈ TrioOct, (∀ w ∈ W, w ∈ B) → W = V0F)) ∧
    (spanS [422, 553, 1131] = V0L ∧ V0L ∈ subs ∧
      ∀ B ∈ subs, B.length ≤ 2 → B = [0] ∨ B = z0L) ∧
    (∀ B ∈ subs, 3 ≤ B.length → ∀ W ∈ TrioOct, (∀ c ∈ B, c ∈ W) → W = V0F) :=
  ⟨fun _ hB => k4174_subs_prop hB, k4174_subs_zero_mem,
    fun _ hB _ hv hvB hfix => k4174_subs_chain hB hv hvB hfix,
    fun _ ht hne => k4174_rank ht hne, k4174_trio_ncard, fun _ hW => k4174_trio_props hW,
    fun _ hB h16 => k4174_x_bound hB h16, small4174,
    fun _ hB h3 _ hW hsub => k4174_above hB h3 hW hsub⟩

end Certificates

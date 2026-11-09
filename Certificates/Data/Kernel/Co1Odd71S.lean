module

public import Certificates.Data.Kernel.Co1Odd71

public section

namespace CFSG.KD.Co1Odd

theorem distinctL_iff : ∀ L : List Nat, distinctL L = true ↔ L.Nodup
  | [] => by simp [distinctL]
  | a :: t => by
    simp [distinctL, List.nodup_cons, distinctL_iff t]

@[expose] noncomputable def bucketOK (m : Nat) (L : List Nat) : Bool :=
  (List.range m).all fun b => distinctL (L.filter fun x => Nat.beq (x % m) b)

theorem distinctL_of_buckets {m : Nat} {L : List Nat} (hm : 0 < m) (h : bucketOK m L = true) :
    distinctL L = true := by
  rw [distinctL_iff, List.nodup_iff_count]
  intro a
  have hb := List.all_eq_true.1 h (a % m) (List.mem_range.2 (Nat.mod_lt a hm))
  rw [distinctL_iff, List.nodup_iff_count] at hb
  have h2 := hb a
  rwa [List.count_filter (by simp)] at h2

end CFSG.KD.Co1Odd

end

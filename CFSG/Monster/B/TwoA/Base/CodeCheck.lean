module

public import CFSG.Monster.Code.Weights

public section

namespace CFSG.Monster.B.TwoA

open CFSG.Monster.Code

theorem treeSumN_mono {F G : ℕ → ℕ} (h : ∀ a, F a ≤ G a) (m : ℕ → ℕ) :
    ∀ k a, treeSumN F m k a ≤ treeSumN G m k a
  | 0, a => h a
  | k + 1, a => Nat.add_le_add (treeSumN_mono h m k a) (treeSumN_mono h m k (a ^^^ m k))

theorem forall_mem_C_of_count {P : (Fin 24 → ZMod 2) → Prop} (Pm : ℕ → Bool)
    (hP : ∀ a, Pm a = true → P (bvec 24 a))
    (h : treeSumN (fun a => if Pm a then 0 else 1) Bmask 12 0 = 0) {x : Fin 24 → ZMod 2}
    (hx : x ∈ C) : P x := by
  classical
  have hle : treeSumN (fun a => if P (bvec 24 a) then 0 else 1) Bmask 12 0 ≤
      treeSumN (fun a => if Pm a then 0 else 1) Bmask 12 0 :=
    treeSumN_mono (fun a => by
      by_cases ha : Pm a = true
      · rw [ite_eq_left (hP a ha)]; exact Nat.zero_le _
      · rw [ite_eq_right ha]; split_ifs <;> omega) Bmask 12 0
  rw [h, Nat.le_zero, ← sum_C_eq_treeSumN (fun x => if P x then 0 else 1),
    Finset.sum_eq_zero_iff] at hle
  have := hle x (Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩)
  simpa using this

end CFSG.Monster.B.TwoA

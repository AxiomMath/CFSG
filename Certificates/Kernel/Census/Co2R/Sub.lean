module

public import Certificates.Kernel.Census.Co2R.Data
import all Certificates.Kernel.Census.Co2R.Data
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.Packed
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 1000000

namespace CertificateChecks.KernelCensus.Co2R

open CFSG.KC.Census

theorem pinvRestQ_append (n w : Nat) (xs : List Nat) :
    ∀ (l1 l2 : List Nat) (m : Nat) (im : List Nat),
    pinvRest n w xs m im (l1 ++ l2) =
      (pinvRest n w xs m im l1).bind (fun im' => pinvRest n w xs (m + l1.length) im' l2)
  | [], l2, m, im => by simp [pinvRest]
  | x :: l1, l2, m, im => by
    have e : m + (l1.length + 1) = m + 1 + l1.length := by omega
    simp only [List.cons_append, pinvRest, List.length_cons, e]
    cases Nat.beq (im.headD (2 ^ xs.length)) m <;>
      cases (Nat.beq m 0 || (Nat.blt x n && !(Nat.beq (ppcAt w xs m (ppcAt w xs m x)) x))) <;>
      simp [pinvRestQ_append n w xs l1 l2]

theorem pinvRestQ_join (n w : Nat) (xs : List Nat) {l1 l2 : List Nat} {m : Nat} {a b c : List Nat}
    (h1 : (pinvRest n w xs m a l1 == some b) = true)
    (h2 : (pinvRest n w xs (m + l1.length) b l2 == some c) = true) :
    (pinvRest n w xs m a (l1 ++ l2) == some c) = true := by
  rw [beq_iff_eq] at h1 h2 ⊢
  rw [pinvRestQ_append, h1]
  exact h2

theorem imFromQ_congr (r : RootR) {S c S' c' : Nat} (h : c * S = c' * S') :
    imFrom r S c = imFrom r S' c' := by
  unfold imFrom; rw [h]

theorem invChunk_two {m : Nat} {r : RootR} {S c : Nat} (hlen : (2 * c + 1) * S ≤ r.d.wt.length)
    (h0 : invChunk m r S (2 * c) = true) (h1 : invChunk m r S (2 * c + 1) = true) :
    invChunk m r (2 * S) c = true := by
  unfold invChunk at *
  have ha : 2 * c * S = 2 * (c * S) := Nat.mul_assoc 2 c S
  have hb : c * (2 * S) = 2 * (c * S) := Nat.mul_left_comm c 2 S
  have hc : (2 * c + 1) * S = 2 * (c * S) + S := by rw [Nat.add_mul, Nat.one_mul, ha]
  have hd : (2 * c + 1 + 1) * S = 2 * (c * S) + S + S := by rw [Nat.add_mul, Nat.one_mul, hc]
  have he : (c + 1) * (2 * S) = 2 * (c * S) + 2 * S := by rw [Nat.add_mul, Nat.one_mul, hb]
  have e0 : c * (2 * S) = 2 * c * S := hb.trans ha.symm
  have e1 : 2 * c * S + S = (2 * c + 1) * S := by rw [ha, hc]
  have e2 : (c + 1) * (2 * S) = (2 * c + 1 + 1) * S := by rw [he, hd]; omega
  have hl : ((r.d.wt.drop (2 * c * S)).take S).length = S := by
    rw [List.length_take, List.length_drop]; omega
  have es : (r.d.wt.drop (2 * c * S)).take (2 * S) =
      (r.d.wt.drop (2 * c * S)).take S ++ (r.d.wt.drop ((2 * c + 1) * S)).take S := by
    rw [Nat.two_mul S, List.take_add, List.drop_drop, e1]
  rw [e0, es, imFromQ_congr r (S' := S) (c' := 2 * c) e0,
    imFromQ_congr r (S' := S) (c' := 2 * c + 1 + 1) e2]
  refine pinvRestQ_join _ _ _ h0 ?_
  rw [hl, e1]
  exact h1

theorem pinvRestQ_chunks {n w : Nat} (xs wt : List Nat) (S K : Nat) (I : Nat → List Nat)
    (hlen : wt.length = K * S)
    (hc : ∀ c < K, pinvRest n w xs (c * S) (I c) ((wt.drop (c * S)).take S) = some (I (c + 1))) :
    pinvRest n w xs 0 (I 0) wt = some (I K) := by
  have key : ∀ k ≤ K,
      pinvRest n w xs ((K - k) * S) (I (K - k)) (wt.drop ((K - k) * S)) = some (I K) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hlen])]
      rfl
    | succ k ih =>
      intro hk
      have hc1 : K - (k + 1) + 1 = K - k := by omega
      have hm : (K - (k + 1)) * S + S = (K - k) * S := by rw [← hc1, Nat.succ_mul]
      have hle : (K - k) * S ≤ K * S := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      have hS : min S (wt.length - (K - (k + 1)) * S) = S := by
        apply Nat.min_eq_left
        rw [hlen]
        have : (K - (k + 1)) * S + S ≤ K * S := by rw [hm]; exact hle
        omega
      rw [← List.take_append_drop S (wt.drop ((K - (k + 1)) * S)), pinvRestQ_append,
        hc _ (by omega), Option.bind_some, List.drop_drop, List.length_take, List.length_drop, hS,
        hm, hc1]
      exact ih (by omega)
  simpa using key K (Nat.le_refl K)

theorem pinvOKQ_of_chunks {m S K : Nat} {r : RootR} (hh : invHead m r = true)
    (hK : K * S = 2 ^ r.d.xs.length) (hc : ∀ c < K, invChunk m r S c = true) :
    pinvOK m 5 r.d.xs r.d.us r.d.im r.d.wt = true := by
  unfold invHead at hh
  unfold pinvOK
  simp only [Bool.and_eq_true] at hh ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hh
  refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
  have hlen : r.d.wt.length = K * S := by rw [hK]; exact Nat.eq_of_beq_eq_true h3
  have hw := pinvRestQ_chunks (n := m) (w := 5) r.d.xs r.d.wt S K (imFrom r S) hlen
    fun c hc' => by
      have := hc c hc'
      unfold invChunk at this
      exact beq_iff_eq.1 this
  have h0 : imFrom r S 0 = r.d.im := by
    unfold imFrom
    exact List.filter_eq_self.2 fun x _ => by simp [Nat.ble_eq]
  have hKe : imFrom r S K = [] := by
    unfold imFrom
    refine List.filter_eq_nil_iff.2 fun x hx => ?_
    have := List.all_eq_true.1 h4 x hx
    simp only [Nat.blt_eq] at this
    rw [← hK] at this
    simp only [Nat.ble_eq, Bool.not_eq_true, decide_eq_true_eq]
    omega
  rw [h0, hKe] at hw
  rw [hw]
  rfl

theorem invChunk_four {m : Nat} {r : RootR} (c : Nat) (hlen : (c + 1) * 16384 ≤ r.d.wt.length)
    (h0 : invChunk m r 4096 (2 * (2 * c)) = true) (h1 : invChunk m r 4096 (2 * (2 * c) + 1) = true)
    (h2 : invChunk m r 4096 (2 * (2 * c + 1)) = true)
    (h3 : invChunk m r 4096 (2 * (2 * c + 1) + 1) = true) :
    invChunk m r 16384 c = true := by
  have l0 : (2 * (2 * c) + 1) * 4096 ≤ r.d.wt.length := by omega
  have l1 : (2 * (2 * c + 1) + 1) * 4096 ≤ r.d.wt.length := by omega
  have l2 : (2 * c + 1) * 8192 ≤ r.d.wt.length := by omega
  exact invChunk_two (S := 8192) l2 (invChunk_two (S := 4096) l0 h0 h1)
    (invChunk_two (S := 4096) l1 h2 h3)

theorem all_range'_four' {f : Nat → Bool} {a : Nat} (h0 : f a = true) (h1 : f (a + 1) = true)
    (h2 : f (a + 2) = true) (h3 : f (a + 3) = true) : (List.range' a 4).all f = true := by
  rw [List.all_eq_true]
  intro k hk
  obtain ⟨hk1, hk2⟩ := List.mem_range'_1.1 hk
  obtain rfl | rfl | rfl | rfl : k = a ∨ k = a + 1 ∨ k = a + 2 ∨ k = a + 3 := by omega
  exacts [h0, h1, h2, h3]

theorem Z.wtLen : 262144 ≤ Z.r.d.wt.length := Nat.le_of_ble_eq_true (by quickRfl)

theorem T.wtLen : 131072 ≤ T.r.d.wt.length := Nat.le_of_ble_eq_true (by quickRfl)

end CertificateChecks.KernelCensus.Co2R

end

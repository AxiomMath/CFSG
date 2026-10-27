module

public import Certificates.Kernel.BabyMonster.CTIB.Hist

public section

namespace CertificateChecks.KernelBM.CTIB.Hist

open CFSG.Monster.B.CTIB CFSG.Monster.B.CTIB.Native CFSG.KC.Bfs CertificateChecks.KernelBM.CTIB
  CertificateChecks.KernelBM.CTIB.CosetQ CertificateChecks.KernelBM.CTIB.QK
  CertificateChecks.KernelBM.CTIB.Inner

open Classical

attribute [local irreducible] S cnt

@[expose] def pi (b c : ℕ) : ℕ := innerPairIdx (innerTyRank (b + 1)) (innerTyRank (c + 1))

@[expose] noncomputable def K (v : ℕ) : ℕ :=
  if bt v 1 = true then 0
  else innerPairIdx (innerTyRank innerTab[v]!) (innerTyRank innerTab[v ^^^ 1]!)

theorem sum_single {Q : ℕ → Prop} [DecidablePred Q] {x : ℕ} (hQ : ∀ b < 5, ∀ c < 5, Q b → Q c → b = c) :
    ∑ b ∈ Finset.range 5, (if Q b then x else 0) = if ∃ b < 5, Q b then x else 0 := by
  by_cases h : ∃ b < 5, Q b
  · obtain ⟨b, hb, hq⟩ := h
    rw [ite_eq_left ⟨b, hb, hq⟩, Finset.sum_eq_single b (fun c hc hne => ite_eq_right fun hc' =>
      hne (hQ c (Finset.mem_range.1 hc) b hb hc' hq)) (fun h => absurd (Finset.mem_range.2 hb) h),
      ite_eq_left hq]
  · rw [ite_eq_right h]
    exact Finset.sum_eq_zero fun b hb => ite_eq_right fun hq => h ⟨b, Finset.mem_range.1 hb, hq⟩

section Census

variable (hC : CensusLists)
include hC

theorem one_mem : (1 : ℕ) ∈ S 0 := (mem_S hC (by omega)).2 Reach.root

theorem Rc_disj {v : ℕ} : ∀ b < 5, ∀ c < 5, Rc b 1 v → Rc c 1 v → b = c :=
  fun _ hb _ hc h1 h2 => S_disj hC hb hc h1.2 h2.2

theorem K_of {b c v : ℕ} (hb : b < 5) (hc : c < 5) (hv : v ∈ S b) (h : Rc c 1 v) : K v = pi b c := by
  have hbt : bt v 1 = false := by rw [bt_comm]; exact h.1
  have h2 : v ^^^ 1 ∈ S c := by rw [Nat.xor_comm]; exact h.2
  rw [K, ite_eq_right (by rw [hbt]; decide), tab_S hC hb hv, tab_S hC hc h2]
  rfl

theorem one_split {b v : ℕ} (hb : b < 5) (hv : v ∈ S b) :
    (1 : ℕ) = (if bt 1 v = true then 1 else 0) + (if v = 1 then 1 else 0) +
      ∑ c ∈ Finset.range 5, (if Rc c 1 v then 1 else 0) := by
  rw [sum_single (Rc_disj hC)]
  have hvv := S_valid hC hb hv
  by_cases h1 : v = 1
  · subst h1
    have hbt : bt 1 1 = false := by simp [bt]
    rw [ite_eq_right (by rw [hbt]; decide), ite_eq_left rfl, ite_eq_right]
    rintro ⟨c, hc, -, hm⟩
    rw [Nat.xor_self] at hm
    exact absurd (S_valid hC hc hm).1 (Nat.lt_irrefl 0)
  · rw [ite_eq_right h1]
    by_cases hb1 : bt 1 v = true
    · rw [ite_eq_left hb1, ite_eq_right]
      rintro ⟨c, -, hc, -⟩
      rw [hc] at hb1
      exact absurd hb1 (by decide)
    · have hx : 0 < 1 ^^^ v := by
        rcases Nat.eq_zero_or_pos (1 ^^^ v) with h | h
        · exact absurd (Nat.eq_of_xor_eq_zero h).symm h1
        · exact h
      obtain ⟨c, hc, hm⟩ := S_cover hC hx (Nat.xor_lt_two_pow (by decide) hvv.2)
      rw [ite_eq_right hb1, ite_eq_left ⟨c, hc, Bool.eq_false_iff.2 hb1, hm⟩]

theorem key_split {b v j : ℕ} (hb : b < 5) (hv : v ∈ S b) :
    (if v ≠ 1 ∧ K v = j then 1 else 0) = (if bt 1 v = true then (if j = 0 then 1 else 0) else 0) +
      ∑ c ∈ Finset.range 5, (if Rc c 1 v then (if pi b c = j then 1 else 0) else 0) := by
  have hvv := S_valid hC hb hv
  by_cases h1 : v = 1
  · subst h1
    have hbt : bt 1 1 = false := by simp [bt]
    have hs : (∑ c ∈ Finset.range 5, (if Rc c 1 1 then (if pi b c = j then 1 else 0) else 0)) = 0 :=
      Finset.sum_eq_zero fun c hc => ite_eq_right_iff.2 fun h => by
        have hm := h.2
        rw [Nat.xor_self] at hm
        exact absurd (S_valid hC (Finset.mem_range.1 hc) hm).1 (Nat.lt_irrefl 0)
    rw [ite_eq_right (fun h => h.1 rfl), ite_eq_right (by rw [hbt]; decide), hs]
  · by_cases hb1 : bt 1 v = true
    · have hK : K v = 0 := by rw [K, ite_eq_left (by rw [bt_comm]; exact hb1)]
      have hs : (∑ c ∈ Finset.range 5, (if Rc c 1 v then (if pi b c = j then 1 else 0) else 0)) =
          0 := Finset.sum_eq_zero fun c _ => ite_eq_right_iff.2 fun h => by
        have hc := h.1
        rw [hc] at hb1
        exact absurd hb1 (by decide)
      rw [ite_eq_left hb1, hs, Nat.add_zero]
      by_cases hj : j = 0
      · rw [ite_eq_left ⟨h1, hK.trans hj.symm⟩, ite_eq_left hj]
      · rw [ite_eq_right (fun h => hj (h.2.symm.trans hK)), ite_eq_right hj]
    · have hx : 0 < 1 ^^^ v := by
        rcases Nat.eq_zero_or_pos (1 ^^^ v) with h | h
        · exact absurd (Nat.eq_of_xor_eq_zero h).symm h1
        · exact h
      obtain ⟨c, hc, hm⟩ := S_cover hC hx (Nat.xor_lt_two_pow (by decide) hvv.2)
      have hR : Rc c 1 v := ⟨Bool.eq_false_iff.2 hb1, hm⟩
      rw [ite_eq_right hb1, Nat.zero_add, Finset.sum_eq_single c (fun d hd hne => ite_eq_right fun hd' =>
        hne (Rc_disj hC d (Finset.mem_range.1 hd) c hc hd' hR))
        (fun h => absurd (Finset.mem_range.2 hc) h), ite_eq_left hR, K_of hC hb hc hv hR]
      by_cases hj : pi b c = j
      · rw [ite_eq_left ⟨h1, hj⟩, ite_eq_left hj]
      · rw [ite_eq_right (fun h => hj h.2), ite_eq_right hj]

noncomputable def T (b : ℕ) : ℕ := ((S b).filter fun v => bt 1 v = true).card

theorem size_split {b : ℕ} (hb : b < 5) :
    Inner.sizeOf b = T b + (if b = 0 then 1 else 0) + ∑ c ∈ Finset.range 5, cnt (Rc c) b 1 := by
  rw [← card_S hC hb, Finset.card_eq_sum_ones, Finset.sum_congr rfl fun v hv => one_split hC hb hv,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm, T, Finset.card_filter]
  congr 1
  · congr 1
    rw [← Finset.card_filter, Finset.filter_eq' (S b) 1]
    by_cases h : b = 0
    · subst h
      rw [ite_eq_left (one_mem hC), ite_eq_left rfl, Finset.card_singleton]
    · rw [ite_eq_right h, ite_eq_right fun h1 => h (S_disj hC hb (by omega) h1 (one_mem hC)),
        Finset.card_empty]
  · exact Finset.sum_congr rfl fun c _ => by rw [cnt, Finset.card_filter]

theorem countK {b j : ℕ} (hb : b < 5) :
    ((S b).filter fun v => v ≠ 1 ∧ K v = j).card =
      (if j = 0 then T b else 0) + ∑ c ∈ Finset.range 5, (if pi b c = j then cnt (Rc c) b 1 else 0) := by
  rw [Finset.card_filter, Finset.sum_congr rfl fun v hv => key_split hC hb hv,
    Finset.sum_add_distrib, Finset.sum_comm, T]
  congr 1
  · by_cases hj : j = 0
    · simp only [hj, if_true, Finset.card_filter]
    · simp only [hj, if_false, Finset.sum_const_zero, ite_self]
  · refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hj : pi b c = j
    · simp only [hj, if_true, cnt, Finset.card_filter]
    · simp only [hj, if_false, Finset.sum_const_zero, ite_self]

theorem range_split (Φ : ℕ → Prop) [DecidablePred Φ] :
    ((Finset.range (2 ^ 22)).filter Φ).card =
      (if Φ 0 then 1 else 0) + ∑ b ∈ Finset.range 5, ((S b).filter Φ).card := by
  have pt : ∀ v ∈ Finset.range (2 ^ 22), (if Φ v then 1 else 0) =
      (if v = 0 then (if Φ 0 then 1 else 0) else 0) +
        ∑ b ∈ Finset.range 5, (if v ∈ S b ∧ Φ v then 1 else 0) := by
    intro v hv
    rw [Finset.mem_range] at hv
    rw [sum_single (Q := fun b => v ∈ S b ∧ Φ v) fun b hb c hc h1 h2 => S_disj hC hb hc h1.1 h2.1]
    rcases Nat.eq_zero_or_pos v with rfl | h0
    · have hne : ¬ ∃ b < 5, 0 ∈ S b ∧ Φ 0 := fun ⟨b, hb, hm, _⟩ =>
        absurd (S_valid hC hb hm).1 (Nat.lt_irrefl 0)
      rw [ite_eq_left rfl, ite_eq_right hne, Nat.add_zero]
    · rw [ite_eq_right (Nat.ne_of_gt h0), Nat.zero_add]
      obtain ⟨b, hb, hm⟩ := S_cover hC h0 hv
      by_cases hΦ : Φ v
      · rw [ite_eq_left hΦ, ite_eq_left ⟨b, hb, hm, hΦ⟩]
      · rw [ite_eq_right hΦ, ite_eq_right fun ⟨_, _, _, h⟩ => hΦ h]
  have h0 : (0 : ℕ) ∈ Finset.range (2 ^ 22) := Finset.mem_range.2 (Nat.two_pow_pos 22)
  have e1 := Finset.card_filter Φ (Finset.range (2 ^ 22))
  have e2 := Finset.sum_congr rfl pt
  have e3 := Finset.sum_ite_eq' (Finset.range (2 ^ 22)) 0 (fun _ => if Φ 0 then 1 else 0)
  rw [ite_eq_left h0] at e3
  rw [e1, e2, Finset.sum_add_distrib, e3, Finset.sum_comm]
  refine congrArg (fun x => (if Φ 0 then 1 else 0) + x) (Finset.sum_congr rfl fun b hb => ?_)
  rw [Finset.card_filter, ← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext v
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨(S_valid hC (Finset.mem_range.1 hb) h.1).2, h⟩⟩

end Census

end CertificateChecks.KernelBM.CTIB.Hist

end

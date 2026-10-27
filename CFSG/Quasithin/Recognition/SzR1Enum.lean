module

public import CFSG.Quasithin.Recognition.SzR1GramPar

public section

namespace CFSG.Quasithin.SzR1

variable {P : Type*} [Group P] {Ω : Type*} {z : P} {w : Ω → P}

namespace GramRel

theorem exists_nodup [DecidableEq Ω] (h : GramRel z w) :
    ∀ (n a : ℕ) (l : List Ω), l.length = n →
      ∃ (b : ℕ) (l' : List Ω), l'.Nodup ∧ z ^ a * gprod w l = z ^ b * gprod w l' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a l hn
    by_cases hnd : l.Nodup
    · exact ⟨a, l, hnd, rfl⟩
    · rw [List.nodup_iff_count_le_one] at hnd
      push Not at hnd
      obtain ⟨i, hi⟩ := hnd
      have hmem : i ∈ l := List.count_pos_iff.mp (by omega)
      have p1 : l.Perm (i :: l.erase i) := List.perm_cons_erase hmem
      have hcnt' : 0 < (l.erase i).count i := by
        rw [List.count_erase_self]
        omega
      have hmem' : i ∈ l.erase i := List.count_pos_iff.mp hcnt'
      have p2 : (l.erase i).Perm (i :: (l.erase i).erase i) := List.perm_cons_erase hmem'
      have p3 : l.Perm (i :: i :: (l.erase i).erase i) := p1.trans (List.Perm.cons i p2)
      obtain ⟨k, hk⟩ := h.gprod_perm p3
      rw [h.gprod_cons_cons] at hk
      have hlen : ((l.erase i).erase i).length < n := by
        rw [List.length_erase_of_mem hmem', List.length_erase_of_mem hmem]
        have : 0 < l.length := List.length_pos_of_mem hmem
        omega
      obtain ⟨b, l', hnd', he⟩ := ih _ hlen (a + k) ((l.erase i).erase i) rfl
      refine ⟨b, l', hnd', ?_⟩
      rw [hk, ← mul_assoc, ← pow_add]
      exact he

theorem sq_mem [DecidableEq Ω] (h : GramRel z w) {x : P}
    (hx : x ∈ Subgroup.closure (insert z (Set.range w))) : ∃ c : ℕ, x * x = z ^ c := by
  obtain ⟨a, l, hxl⟩ := h.mem_closure_iff.mp hx
  obtain ⟨b, l', hnd, he⟩ := h.exists_nodup l.length a l rfl
  refine ⟨b + b + Nat.choose l'.length 2, ?_⟩
  rw [hxl, he, h.zg_mul, gprod_append, h.gprod_sq hnd, ← pow_add]

theorem even_countP_of_comm [DecidableEq Ω] (h : GramRel z w) (hz : z ≠ 1) {x : P} {a : ℕ}
    {l : List Ω} (hx : x = z ^ a * gprod w l) {j : Ω} (hc : x * w j = w j * x) :
    Even (l.countP (fun i => decide (i ≠ j))) := by
  have h1 := hc
  rw [hx] at h1
  have h2 := h.mul_gprod j l
  have h3 : z ^ a * (gprod w l * w j) =
      z ^ a * (z ^ (l.countP (fun i => decide (i ≠ j))) * (gprod w l * w j)) := by
    calc z ^ a * (gprod w l * w j) = z ^ a * gprod w l * w j := (mul_assoc _ _ _).symm
      _ = w j * (z ^ a * gprod w l) := h1
      _ = z ^ a * (w j * gprod w l) := by
          calc w j * (z ^ a * gprod w l) = (w j * z ^ a) * gprod w l := (mul_assoc _ _ _).symm
            _ = (z ^ a * w j) * gprod w l := by rw [h.mul_zpow_comm (w j) a]
            _ = z ^ a * (w j * gprod w l) := mul_assoc _ _ _
      _ = _ := by rw [h2]
  have h4 := mul_left_cancel h3
  have h5 : z ^ (l.countP (fun i => decide (i ≠ j))) = 1 := by
    have h6 : 1 * (gprod w l * w j) =
        z ^ (l.countP (fun i => decide (i ≠ j))) * (gprod w l * w j) := by
      rwa [one_mul]
    exact (mul_right_cancel h6).symm
  exact (h.z_pow_eq_one_iff hz _).mp h5

theorem sq_eq_one_comm_mem [DecidableEq Ω] [Fintype Ω] (h : GramRel z w) (hz : z ≠ 1)
    (hc5 : Fintype.card Ω = 5) (pt : Ω) (l₀ : List Ω) (hl₀ : l₀.Nodup) (hall : ∀ i, i ∈ l₀)
    {x : P} (hx : x ∈ Subgroup.closure (insert z (Set.range w))) (hsq : x * x = 1)
    (hcomm : x * w pt = w pt * x) :
    ∃ i j k : ℕ, x = z ^ i * w pt ^ j * (gprod w l₀) ^ k := by
  obtain ⟨a, l, hxl⟩ := h.mem_closure_iff.mp hx
  obtain ⟨b, l', hnd, hxb⟩ := h.exists_nodup l.length a l rfl
  rw [← hxl] at hxb
  have hsq' : z ^ (b + b + Nat.choose l'.length 2) = 1 := by
    have := hsq
    rw [hxb, h.zg_mul, gprod_append, h.gprod_sq hnd, ← pow_add] at this
    exact this
  have hev : Even (Nat.choose l'.length 2) := by
    obtain ⟨r, hr⟩ := (h.z_pow_eq_one_iff hz _).mp hsq'
    exact ⟨r - b, by omega⟩
  have hcev : Even (l'.countP (fun i => decide (i ≠ pt))) := h.even_countP_of_comm hz hxb hcomm
  have hlen : l'.length ≤ 5 := hc5 ▸ hnd.length_le_card
  have hcnt := countP_ne_add_count pt l'
  have hcle : l'.count pt ≤ 1 := List.nodup_iff_count_le_one.mp hnd pt
  have hcover : ∀ (m : List Ω), m.Nodup → m.length = 5 → m.Perm l₀ := by
    intro m hm hl
    refine List.perm_of_nodup_nodup_toFinset_eq hm hl₀ ?_
    have h1 : m.toFinset.card = Fintype.card Ω := by
      rw [List.toFinset_card_of_nodup hm, hl, hc5]
    have h2 : m.toFinset = Finset.univ := Finset.eq_univ_of_card _ h1
    ext i
    simp [h2, hall i]
  rcases (show l'.length = 0 ∨ l'.length = 1 ∨ l'.length = 2 ∨ l'.length = 3 ∨ l'.length = 4 ∨
      l'.length = 5 by omega) with hl | hl | hl | hl | hl | hl
  · have : l' = [] := List.length_eq_zero_iff.mp hl
    subst this
    exact ⟨b, 0, 0, by simpa using hxb⟩
  · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hl
    have hcpt : c = pt := by
      by_contra hne
      simp [hne] at hcev
    subst hcpt
    exact ⟨b, 1, 0, by simpa using hxb⟩
  · rw [hl] at hev
    exact absurd hev (by decide)
  · rw [hl] at hev
    exact absurd hev (by decide)
  · have hc0 : l'.count pt = 0 := by
      obtain ⟨r, hr⟩ := hcev
      omega
    have hptn : pt ∉ l' := List.count_eq_zero.mp hc0
    have hnd' : (pt :: l').Nodup := List.nodup_cons.mpr ⟨hptn, hnd⟩
    obtain ⟨e, he⟩ := h.gprod_perm (hcover _ hnd' (by simp [hl]))
    rw [gprod_cons] at he
    have hl' : gprod w l' = w pt * (z ^ e * gprod w l₀) := by
      calc gprod w l' = w pt * (w pt * gprod w l') := by
            rw [← mul_assoc, h.w_sq, one_mul]
        _ = _ := by rw [he]
    refine ⟨b + e, 1, 1, ?_⟩
    rw [hxb, hl', pow_one, pow_one, pow_add]
    calc z ^ b * (w pt * (z ^ e * gprod w l₀)) = z ^ b * (w pt * z ^ e * gprod w l₀) := by
          simp only [mul_assoc]
      _ = z ^ b * (z ^ e * w pt * gprod w l₀) := by rw [h.mul_zpow_comm (w pt) e]
      _ = z ^ b * z ^ e * w pt * gprod w l₀ := by simp only [mul_assoc]
  · obtain ⟨e, he⟩ := h.gprod_perm (hcover _ hnd hl)
    refine ⟨b + e, 0, 1, ?_⟩
    rw [hxb, he, pow_zero, pow_one, pow_add, mul_one, mul_assoc]

end GramRel

end CFSG.Quasithin.SzR1

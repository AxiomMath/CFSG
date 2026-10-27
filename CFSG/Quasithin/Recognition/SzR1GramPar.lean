module

public import CFSG.Quasithin.Recognition.SzR1Gram

public section

namespace CFSG.Quasithin.SzR1

variable {P : Type*} [Group P] {Ω : Type*} {z : P} {w : Ω → P}

namespace GramRel

theorem zg_mul (h : GramRel z w) (a b : ℕ) (l l' : List Ω) :
    z ^ a * gprod w l * (z ^ b * gprod w l') = z ^ (a + b) * gprod w (l ++ l') := by
  calc z ^ a * gprod w l * (z ^ b * gprod w l')
      = z ^ a * (gprod w l * z ^ b) * gprod w l' := by simp only [mul_assoc]
    _ = z ^ a * (z ^ b * gprod w l) * gprod w l' := by rw [h.mul_zpow_comm (gprod w l) b]
    _ = z ^ (a + b) * gprod w (l ++ l') := by
        rw [gprod_append, pow_add]
        simp only [mul_assoc]

theorem zg_inv (h : GramRel z w) (a : ℕ) (l : List Ω) :
    (z ^ a * gprod w l)⁻¹ = z ^ a * gprod w l.reverse := by
  rw [mul_inv_rev, h.gprod_inv, ← inv_pow, h.z_inv, h.mul_zpow_comm]

@[expose] def evenSub (h : GramRel z w) : Subgroup P where
  carrier := {x | ∃ (a : ℕ) (l : List Ω), Even l.length ∧ x = z ^ a * gprod w l}
  one_mem' := ⟨0, [], Even.zero, by simp⟩
  mul_mem' := by
    rintro x y ⟨a, l, hl, rfl⟩ ⟨b, l', hl', rfl⟩
    exact ⟨a + b, l ++ l', by simpa using hl.add hl', h.zg_mul a b l l'⟩
  inv_mem' := by
    rintro x ⟨a, l, hl, rfl⟩
    exact ⟨a, l.reverse, by simpa using hl, h.zg_inv a l⟩

theorem z_mem_evenSub (h : GramRel z w) : z ∈ h.evenSub :=
  ⟨1, [], Even.zero, by simp⟩

theorem central_mem_par [DecidableEq Ω] (h : GramRel z w) (hz : z ≠ 1) (l₀ : List Ω)
    (hl₀ : l₀.Nodup) (hall : ∀ i, i ∈ l₀) (hodd : Odd l₀.length) {x : P}
    (hc : ∀ i, x * w i = w i * x) :
    ∀ (n a : ℕ) (l : List Ω), l.length = n → x = z ^ a * gprod w l →
      (Even n ∧ ∃ b : ℕ, x = z ^ b) ∨ (Odd n ∧ ∃ b : ℕ, x = z ^ b * gprod w l₀) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a l hn hx
    by_cases hnd : l.Nodup
    · by_cases hl : l = []
      · left
        subst hl
        exact ⟨by simp [← hn], a, by simpa using hx⟩
      · obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil l hl
        have hev : ∀ j, Even (l.countP (fun i => decide (i ≠ j))) :=
          fun j => h.even_countP_of_central hz hx hc j
        have hall' : ∀ i, i ∈ l := by
          intro i
          by_contra hi
          have h1 := hev i
          have h2 := hev j
          have h3 : l.countP (fun k => decide (k ≠ i)) = l.length := by
            have := countP_ne_add_count i l
            rw [List.count_eq_zero_of_not_mem hi] at this
            omega
          have hcnt : l.countP (fun i => decide (i ≠ j)) + 1 = l.length := by
            have := countP_ne_add_count j l
            rwa [List.count_eq_one_of_mem hnd hj] at this
          rw [h3] at h1
          obtain ⟨r, hr⟩ := h1
          obtain ⟨s, hs⟩ := h2
          omega
        have hperm : l.Perm l₀ := List.perm_of_nodup_nodup_toFinset_eq hnd hl₀ (by
          ext i
          simp [hall i, hall' i])
        obtain ⟨k, hk⟩ := h.gprod_perm hperm
        right
        refine ⟨?_, a + k, ?_⟩
        · rw [← hn, hperm.length_eq]
          exact hodd
        · rw [hx, hk, pow_add, mul_assoc]
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
      have hlen1 : ((l.erase i).erase i).length + 2 = n := by
        rw [List.length_erase_of_mem hmem', List.length_erase_of_mem hmem]
        have h1 : 0 < l.length := List.length_pos_of_mem hmem
        have h2 : 0 < (l.erase i).length := List.length_pos_of_mem hmem'
        rw [List.length_erase_of_mem hmem] at h2
        omega
      have hlen : ((l.erase i).erase i).length < n := by omega
      rcases ih _ hlen (a + k) ((l.erase i).erase i) rfl
          (by rw [hx, hk, pow_add, mul_assoc]) with ⟨he, hb⟩ | ⟨ho, hb⟩
      · left
        refine ⟨?_, hb⟩
        rw [← hlen1]
        exact he.add even_two
      · right
        refine ⟨?_, hb⟩
        rw [← hlen1]
        exact ho.add_even even_two

theorem gprod_mem_zpowers_of_w_mem_evenSub [DecidableEq Ω] (h : GramRel z w) (hz : z ≠ 1)
    (l₀ : List Ω) (hl₀ : l₀.Nodup) (hall : ∀ i, i ∈ l₀) (hodd : Odd l₀.length) {i : Ω}
    (hi : w i ∈ h.evenSub) : ∃ b : ℕ, gprod w l₀ = z ^ b := by
  obtain ⟨a, l, hl, hwi⟩ := hi
  have hx : gprod w (i :: l.reverse) = z ^ a := by
    rw [gprod_cons, ← h.gprod_inv, hwi, mul_inv_cancel_right]
  have hc : ∀ j, gprod w (i :: l.reverse) * w j = w j * gprod w (i :: l.reverse) := by
    intro j
    rw [hx]
    exact (h.mul_zpow_comm (w j) a).symm
  have hodd' : Odd (i :: l.reverse).length := by simpa using hl.add_one
  rcases h.central_mem_par hz l₀ hl₀ hall hodd hc _ 0 (i :: l.reverse) rfl (by simp) with
    ⟨he, _⟩ | ⟨_, b, hb⟩
  · exact absurd he (Nat.not_even_iff_odd.mpr hodd')
  · rw [hx] at hb
    refine ⟨b + a, ?_⟩
    have : z ^ b * z ^ a = gprod w l₀ := by
      rw [hb, ← mul_assoc, ← pow_add, h.z_pow_add_self, one_mul]
    rw [pow_add]
    exact this.symm

theorem hom_gprod (h : GramRel z w) (φ : P →* P) (σ : Ω → Ω) (e : Ω → ℕ)
    (hφ : ∀ i, φ (w i) = w (σ i) * z ^ e i) (l : List Ω) :
    ∃ c : ℕ, φ (gprod w l) = z ^ c * gprod w (l.map σ) := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons i l ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨e i + c, ?_⟩
    rw [gprod_cons, map_mul, hφ, hc, List.map_cons, gprod_cons]
    calc w (σ i) * z ^ e i * (z ^ c * gprod w (l.map σ))
        = w (σ i) * z ^ (e i + c) * gprod w (l.map σ) := by rw [pow_add]; simp only [mul_assoc]
      _ = z ^ (e i + c) * w (σ i) * gprod w (l.map σ) := by
          rw [h.mul_zpow_comm (w (σ i))]
      _ = z ^ (e i + c) * (w (σ i) * gprod w (l.map σ)) := by rw [mul_assoc]

theorem hom_mul_inv_mem_evenSub (h : GramRel z w) (φ : P →* P) (hφz : φ z = z) (σ : Ω → Ω)
    (e : Ω → ℕ) (hφ : ∀ i, φ (w i) = w (σ i) * z ^ e i) {x : P}
    (hx : x ∈ Subgroup.closure (insert z (Set.range w))) : φ x * x⁻¹ ∈ h.evenSub := by
  obtain ⟨a, l, rfl⟩ := h.mem_closure_iff.mp hx
  obtain ⟨c, hc⟩ := h.hom_gprod φ σ e hφ l
  have e1 : φ (z ^ a * gprod w l) = z ^ (a + c) * gprod w (l.map σ) := by
    rw [map_mul, map_pow, hφz, hc, ← mul_assoc, ← pow_add]
  refine ⟨a + c + a, l.map σ ++ l.reverse, ⟨l.length, by simp⟩, ?_⟩
  rw [e1, h.zg_inv a l, h.zg_mul]

theorem mul_gprod_central [DecidableEq Ω] (h : GramRel z w) (j : Ω) (l : List Ω) {ε : P}
    (hε : ∀ g, ε * g = g * ε) :
    w j * (gprod w l * ε) =
      z ^ (l.countP (fun i => decide (i ≠ j))) * ((gprod w l * ε) * w j) := by
  rw [← mul_assoc, h.mul_gprod j l]
  calc z ^ (l.countP (fun i => decide (i ≠ j))) * (gprod w l * w j) * ε
      = z ^ (l.countP (fun i => decide (i ≠ j))) * (gprod w l * (w j * ε)) := by
        simp only [mul_assoc]
    _ = z ^ (l.countP (fun i => decide (i ≠ j))) * (gprod w l * (ε * w j)) := by
        rw [← hε (w j)]
    _ = z ^ (l.countP (fun i => decide (i ≠ j))) * ((gprod w l * ε) * w j) := by
        simp only [mul_assoc]

theorem even_countP_of_eq [DecidableEq Ω] (h : GramRel z w) (hz : z ≠ 1) {l l' : List Ω}
    {ε₁ ε₂ : P} (hε₁ : ∀ g, ε₁ * g = g * ε₁) (hε₂ : ∀ g, ε₂ * g = g * ε₂)
    (heq : gprod w l * ε₁ = gprod w l' * ε₂) (m : Ω) :
    Even (l.countP (fun i => decide (i ≠ m)) + l'.countP (fun i => decide (i ≠ m))) := by
  have h1 := h.mul_gprod_central m l hε₁
  have h2 := h.mul_gprod_central m l' hε₂
  rw [heq] at h1
  have h3 : z ^ (l.countP (fun i => decide (i ≠ m))) = z ^ (l'.countP (fun i => decide (i ≠ m))) :=
    mul_right_cancel (h1.symm.trans h2)
  have h4 : z ^ (l.countP (fun i => decide (i ≠ m)) + l'.countP (fun i => decide (i ≠ m))) = 1 := by
    rw [pow_add, h3, ← pow_add, h.z_pow_add_self]
  exact (h.z_pow_eq_one_iff hz _).mp h4

theorem pair_comm_ne (h : GramRel z w) {i j k : Ω} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (w i * w j) * (w i * w k) = z * ((w i * w k) * (w i * w j)) := by
  have zc : ∀ a b : P, a * (z * b) = z * (a * b) := fun a b => by
    rw [← mul_assoc, h.z_comm a, mul_assoc]
  have L : (w i * w j) * (w i * w k) = z * (w j * w k) := by
    calc (w i * w j) * (w i * w k) = w i * (w j * w i) * w k := by simp only [mul_assoc]
      _ = w i * (z * (w i * w j)) * w k := by rw [h.w_comm j i (Ne.symm hij)]
      _ = z * (w i * (w i * w j)) * w k := by rw [zc]
      _ = z * ((w i * w i) * w j) * w k := by simp only [mul_assoc]
      _ = z * (w j * w k) := by rw [h.w_sq]; simp only [one_mul, mul_assoc]
  have R : (w i * w k) * (w i * w j) = w j * w k := by
    calc (w i * w k) * (w i * w j) = w i * (w k * w i) * w j := by simp only [mul_assoc]
      _ = w i * (z * (w i * w k)) * w j := by rw [h.w_comm k i (Ne.symm hik)]
      _ = z * (w i * (w i * w k)) * w j := by rw [zc]
      _ = z * ((w i * w i) * w k) * w j := by simp only [mul_assoc]
      _ = z * (w k * w j) := by rw [h.w_sq]; simp only [one_mul, mul_assoc]
      _ = z * (z * (w j * w k)) := by rw [h.w_comm k j (Ne.symm hjk)]
      _ = w j * w k := by rw [← mul_assoc, h.z_sq, one_mul]
  rw [L, R]

end GramRel

theorem pair_perm [DecidableEq Ω] {a b i j : Ω} (hij : i ≠ j)
    (h : ∀ m, Even ([a, b].countP (fun x => decide (x ≠ m)) +
      [i, j].countP (fun x => decide (x ≠ m)))) :
    (a = i ∧ b = j) ∨ (a = j ∧ b = i) := by
  have hi := h i
  have hj := h j
  simp only [List.countP_cons, List.countP_nil, Nat.even_iff] at hi hj
  by_cases ha : a = i <;> by_cases hb : b = i <;> by_cases ha' : a = j <;> by_cases hb' : b = j <;>
    simp_all

namespace GramRel

theorem sigma_eq_of_fix [DecidableEq Ω] (h : GramRel z w) (hz : z ≠ 1) (φ : P →* P)
    (σ : Ω → Ω) (ε : Ω → P) (hε : ∀ i g, ε i * g = g * ε i)
    (hφ : ∀ i, φ (w i) = w (σ i) * ε i) {i j k : Ω} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hj : ∃ c : P, (∀ g, c * g = g * c) ∧ φ (w i * w j) = w i * w j * c)
    (hk : ∃ c : P, (∀ g, c * g = g * c) ∧ φ (w i * w k) = w i * w k * c) : σ i = i := by
  have key : ∀ {j : Ω}, i ≠ j →
      (∃ c : P, (∀ g, c * g = g * c) ∧ φ (w i * w j) = w i * w j * c) →
      (σ i = i ∧ σ j = j) ∨ (σ i = j ∧ σ j = i) := by
    intro j hij hc
    obtain ⟨c, hcc, hcφ⟩ := hc
    rw [map_mul, hφ, hφ] at hcφ
    have hcen : ∀ g, (ε i * ε j) * g = g * (ε i * ε j) := by
      intro g
      rw [mul_assoc, hε j g, ← mul_assoc, hε i g, mul_assoc]
    have heq : gprod w [σ i, σ j] * (ε i * ε j) = gprod w [i, j] * c := by
      simp only [gprod_cons, gprod_nil, mul_one]
      calc w (σ i) * w (σ j) * (ε i * ε j) = w (σ i) * ε i * (w (σ j) * ε j) := by
            rw [mul_assoc (w (σ i)), ← mul_assoc (w (σ j)), ← hε i (w (σ j))]
            simp only [mul_assoc]
        _ = w i * w j * c := hcφ
    exact pair_perm hij (fun m => h.even_countP_of_eq hz hcen hcc heq m)
  rcases key hij hj with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact h1
  · rcases key hik hk with ⟨h2, _⟩ | ⟨h2, _⟩
    · exact h2
    · exact absurd (h1.symm.trans h2) hjk

end GramRel

end CFSG.Quasithin.SzR1

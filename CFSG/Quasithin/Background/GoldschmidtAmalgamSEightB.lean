module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamSEight

public section

namespace CFSG.Quasithin.F6.GoldAmS

open Equiv

theorem perm3_order3 : ∀ s t : Perm (Fin 3), s ^ 3 = 1 → s ≠ 1 → t ^ 3 = 1 → t ≠ 1 →
    t = s ∨ t = s⁻¹ := by
  decide

structure Eight {X : Type*} [Group X] (Q : Subgroup X) (x : X) (π : X →* Perm (Fin 3)) : Prop where
  card : Nat.card Q = 8
  exp : ∀ q ∈ Q, q * q = 1
  x3 : x ^ 3 = 1
  nc : ∃ q ∈ Q, x * q * x⁻¹ ≠ q
  ker : ∀ g : X, π g = 1 ↔ g ∈ Q

namespace Eight

variable {X : Type*} [Group X] {Q : Subgroup X} {x : X} {π : X →* Perm (Fin 3)}

theorem comm (h : Eight Q x π) {q r : X} (hq : q ∈ Q) (hr : r ∈ Q) : q * r = r * q := by
  have h1 : (q * r)⁻¹ = q * r := inv_eq_of_mul_eq_one_right (h.exp _ (Subgroup.mul_mem _ hq hr))
  have h2 : q⁻¹ = q := inv_eq_of_mul_eq_one_right (h.exp q hq)
  have h3 : r⁻¹ = r := inv_eq_of_mul_eq_one_right (h.exp r hr)
  rw [← h1, mul_inv_rev, h2, h3]

theorem x_not_mem (h : Eight Q x π) : x ∉ Q := by
  intro hx
  obtain ⟨q, hq, hne⟩ := h.nc
  apply hne
  have := h.comm hx hq
  calc x * q * x⁻¹ = q * x * x⁻¹ := by rw [this]
    _ = q := by group

theorem π_x_ne (h : Eight Q x π) : π x ≠ 1 := fun h1 => h.x_not_mem ((h.ker x).1 h1)

theorem π_x_pow (h : Eight Q x π) : (π x) ^ 3 = 1 := by rw [← map_pow, h.x3, map_one]

theorem conj_x (h : Eight Q x π) (g : X) :
    ∃ u ∈ Q, g * x * g⁻¹ = x * u ∨ g * x * g⁻¹ = x⁻¹ * u := by
  have h1 : (π (g * x * g⁻¹)) ^ 3 = 1 := by
    rw [← map_pow]
    rw [conj_pow, h.x3]
    simp
  have h2 : π (g * x * g⁻¹) ≠ 1 := by
    intro h3
    apply h.π_x_ne
    have : π x = π g⁻¹ * π (g * x * g⁻¹) * π g := by
      simp only [map_mul, map_inv]
      group
    rw [this, h3]
    simp
  rcases perm3_order3 (π x) (π (g * x * g⁻¹)) h.π_x_pow h.π_x_ne h1 h2 with h3 | h3
  · refine ⟨x⁻¹ * (g * x * g⁻¹), (h.ker _).1 ?_, Or.inl (by group)⟩
    rw [map_mul, map_inv, h3]
    simp
  · refine ⟨x * (g * x * g⁻¹), (h.ker _).1 ?_, Or.inr (by group)⟩
    rw [map_mul, h3]
    simp

@[expose] def nor (x q : X) : X := q * (x * q * x⁻¹) * (x⁻¹ * q * x)

theorem nor_one (x : X) : nor x 1 = 1 := by simp [nor]

section WithNormal

variable [Q.Normal]

theorem conj_mem' {q : X} (hq : q ∈ Q) (g : X) : g * q * g⁻¹ ∈ Q :=
  (inferInstance : Q.Normal).conj_mem q hq g

theorem conj_mem'' {q : X} (hq : q ∈ Q) (g : X) : g⁻¹ * q * g ∈ Q := by
  have := conj_mem' (Q := Q) hq g⁻¹
  simpa using this

theorem nor_mem {q : X} (hq : q ∈ Q) : nor x q ∈ Q :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ hq (conj_mem' hq x)) (conj_mem'' hq x)

theorem nor_mul (h : Eight Q x π) {q r : X} (hq : q ∈ Q) (hr : r ∈ Q) :
    nor x (q * r) = nor x q * nor x r := by
  have ha : x * q * x⁻¹ ∈ Q := conj_mem' hq x
  have hb : x * r * x⁻¹ ∈ Q := conj_mem' hr x
  have ha' : x⁻¹ * q * x ∈ Q := conj_mem'' hq x
  have hra : r * (x * q * x⁻¹) = (x * q * x⁻¹) * r := h.comm hr ha
  have hra' : r * (x⁻¹ * q * x) = (x⁻¹ * q * x) * r := h.comm hr ha'
  have hba' : (x * r * x⁻¹) * (x⁻¹ * q * x) = (x⁻¹ * q * x) * (x * r * x⁻¹) := h.comm hb ha'
  have e1 : x * (q * r) * x⁻¹ = (x * q * x⁻¹) * (x * r * x⁻¹) := by group
  have e2 : x⁻¹ * (q * r) * x = (x⁻¹ * q * x) * (x⁻¹ * r * x) := by group
  unfold nor
  rw [e1, e2]
  generalize x * q * x⁻¹ = a at *
  generalize x * r * x⁻¹ = b at *
  generalize x⁻¹ * q * x = a' at *
  generalize x⁻¹ * r * x = b' at *
  calc q * r * (a * b) * (a' * b') = q * (r * a) * b * a' * b' := by group
    _ = q * (a * r) * b * a' * b' := by rw [hra]
    _ = q * a * (r * b * a') * b' := by group
    _ = q * a * (r * (b * a')) * b' := by group
    _ = q * a * (r * (a' * b)) * b' := by rw [hba']
    _ = q * a * ((r * a') * b) * b' := by group
    _ = q * a * ((a' * r) * b) * b' := by rw [hra']
    _ = q * a * a' * (r * b * b') := by group

theorem act_of_form (h : Eight Q x π) {x' u q : X} (hu : u ∈ Q) (hq : q ∈ Q)
    (hx' : x' = x * u ∨ x' = x⁻¹ * u) :
    (x' * q * x'⁻¹ = x * q * x⁻¹ ∧ x'⁻¹ * q * x' = x⁻¹ * q * x) ∨
      (x' * q * x'⁻¹ = x⁻¹ * q * x ∧ x'⁻¹ * q * x' = x * q * x⁻¹) := by
  have hq1 : x * q * x⁻¹ ∈ Q := conj_mem' hq x
  have hq2 : x⁻¹ * q * x ∈ Q := conj_mem'' hq x
  have c1 : u * q * u⁻¹ = q := by rw [h.comm hu hq]; group
  have c2 : u⁻¹ * (x⁻¹ * q * x) * u = x⁻¹ * q * x := by
    rw [h.comm (inv_mem hu) hq2]; group
  have c3 : u⁻¹ * (x * q * x⁻¹) * u = x * q * x⁻¹ := by
    rw [h.comm (inv_mem hu) hq1]; group
  rcases hx' with rfl | rfl
  · left
    constructor
    · calc x * u * q * (x * u)⁻¹ = x * (u * q * u⁻¹) * x⁻¹ := by group
        _ = x * q * x⁻¹ := by rw [c1]
    · calc (x * u)⁻¹ * q * (x * u) = u⁻¹ * (x⁻¹ * q * x) * u := by group
        _ = x⁻¹ * q * x := c2
  · right
    constructor
    · calc x⁻¹ * u * q * (x⁻¹ * u)⁻¹ = x⁻¹ * (u * q * u⁻¹) * x := by group
        _ = x⁻¹ * q * x := by rw [c1]
    · calc (x⁻¹ * u)⁻¹ * q * (x⁻¹ * u) = u⁻¹ * (x * q * x⁻¹) * u := by group
        _ = x * q * x⁻¹ := c3

omit [Q.Normal] in
theorem x_sq_eq (h : Eight Q x π) : x * x = x⁻¹ := by
  have h3 : x * (x * x) = 1 := by
    calc x * (x * x) = x ^ 3 := (pow_three x).symm
      _ = 1 := h.x3
  exact (inv_eq_of_mul_eq_one_right h3).symm

theorem nor_fixed (h : Eight Q x π) {q : X} (hq : q ∈ Q) : x * nor x q * x⁻¹ = nor x q := by
  have ha : x * q * x⁻¹ ∈ Q := conj_mem' hq x
  have ha' : x⁻¹ * q * x ∈ Q := conj_mem'' hq x
  have hqa : q * (x * q * x⁻¹) = (x * q * x⁻¹) * q := h.comm hq ha
  have hqa' : q * (x⁻¹ * q * x) = (x⁻¹ * q * x) * q := h.comm hq ha'
  have e1 : x * (x * q * x⁻¹) * x⁻¹ = x⁻¹ * q * x := by
    calc x * (x * q * x⁻¹) * x⁻¹ = (x * x) * q * (x * x)⁻¹ := by group
      _ = x⁻¹ * q * x⁻¹⁻¹ := by rw [h.x_sq_eq]
      _ = x⁻¹ * q * x := by rw [inv_inv]
  have e2 : x * (x⁻¹ * q * x) * x⁻¹ = q := by group
  have e3 : x * nor x q * x⁻¹ =
      (x * q * x⁻¹) * (x * (x * q * x⁻¹) * x⁻¹) * (x * (x⁻¹ * q * x) * x⁻¹) := by
    unfold nor; group
  rw [e3, e1, e2]
  unfold nor
  generalize x * q * x⁻¹ = a at *
  generalize x⁻¹ * q * x = a' at *
  calc a * a' * q = a * (a' * q) := by group
    _ = a * (q * a') := by rw [hqa']
    _ = (a * q) * a' := by group
    _ = (q * a) * a' := by rw [hqa]
    _ = q * a * a' := by group

end WithNormal

end Eight

structure HasC {X : Type*} [Group X] (Q : Subgroup X) (x c : X) : Prop where
  mem : c ∈ Q
  ne : c ≠ 1
  sq : c * c = 1
  fix : x * c * x⁻¹ = c
  uniq : ∀ q ∈ Q, x * q * x⁻¹ = q → q = 1 ∨ q = c

namespace HasC

variable {X : Type*} [Group X] {Q : Subgroup X} {x c : X}

theorem fix' (hc : HasC Q x c) : x⁻¹ * c * x = c := by
  calc x⁻¹ * c * x = x⁻¹ * (x * c * x⁻¹) * x := by rw [hc.fix]
    _ = c := by group

theorem nor_c (hc : HasC Q x c) : Eight.nor x c = c := by
  unfold Eight.nor
  rw [hc.fix, hc.fix', hc.sq, one_mul]

end HasC

namespace Eight

variable {X : Type*} [Group X] {Q : Subgroup X} {x : X} {π : X →* Perm (Fin 3)} [Q.Normal]
variable {c : X}

theorem exists_c (h : Eight Q x π) : ∃ c, HasC Q x c := by
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [h.card]; norm_num)
  obtain ⟨c, hcQ, hc1, hcc, hxc, hcu⟩ := exists_fixed_elem Q h.card x h.x3 h.nc
  exact ⟨c, hcQ, hc1, hcc, hxc, hcu⟩

theorem c_central (h : Eight Q x π) (hc : HasC Q x c) (g : X) : g * c * g⁻¹ = c := by
  obtain ⟨u, hu, hform⟩ := h.conj_x g⁻¹
  simp only [inv_inv] at hform
  have hx' : (g⁻¹ * x * g) * c * (g⁻¹ * x * g)⁻¹ = c := by
    rcases act_of_form h hu hc.mem hform with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1, hc.fix]
    · rw [h1, hc.fix']
  have hc' : x * (g * c * g⁻¹) * x⁻¹ = g * c * g⁻¹ := by
    calc x * (g * c * g⁻¹) * x⁻¹ = g * ((g⁻¹ * x * g) * c * (g⁻¹ * x * g)⁻¹) * g⁻¹ := by group
      _ = g * c * g⁻¹ := by rw [hx']
  rcases hc.uniq _ (conj_mem' hc.mem g) hc' with h1 | h1
  · exfalso
    apply hc.ne
    calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · exact h1

theorem nor_cases (h : Eight Q x π) (hc : HasC Q x c) {q : X} (hq : q ∈ Q) :
    nor x q = 1 ∨ nor x q = c :=
  hc.uniq _ (nor_mem hq) (nor_fixed h hq)

theorem nor_conj (h : Eight Q x π) (hc : HasC Q x c) (g : X) {q : X} (hq : q ∈ Q) :
    nor x (g * q * g⁻¹) = nor x q := by
  obtain ⟨u, hu, hform⟩ := h.conj_x g⁻¹
  simp only [inv_inv] at hform
  have ha : x * q * x⁻¹ ∈ Q := conj_mem' hq x
  have ha' : x⁻¹ * q * x ∈ Q := conj_mem'' hq x
  have haa : (x⁻¹ * q * x) * (x * q * x⁻¹) = (x * q * x⁻¹) * (x⁻¹ * q * x) := h.comm ha' ha
  have i1 : x * (g * q * g⁻¹) * x⁻¹ = g * ((g⁻¹ * x * g) * q * (g⁻¹ * x * g)⁻¹) * g⁻¹ := by
    group
  have i2 : x⁻¹ * (g * q * g⁻¹) * x = g * ((g⁻¹ * x * g)⁻¹ * q * (g⁻¹ * x * g)) * g⁻¹ := by
    group
  have key : nor x (g * q * g⁻¹) = g * nor x q * g⁻¹ := by
    unfold nor
    rw [i1, i2]
    rcases act_of_form h hu hq hform with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; group
    · rw [h1, h2]
      generalize x * q * x⁻¹ = a at *
      generalize x⁻¹ * q * x = a' at *
      calc g * q * g⁻¹ * (g * a' * g⁻¹) * (g * a * g⁻¹) = g * (q * (a' * a)) * g⁻¹ := by group
        _ = g * (q * (a * a')) * g⁻¹ := by rw [haa]
        _ = g * (q * a * a') * g⁻¹ := by group
  rw [key]
  rcases nor_cases h hc hq with h0 | h0
  · rw [h0]; group
  · rw [h0]; exact c_central h hc g

def normKer (h : Eight Q x π) : Subgroup X where
  carrier := {q | q ∈ Q ∧ nor x q = 1}
  one_mem' := ⟨Q.one_mem, nor_one x⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨Q.mul_mem ha.1 hb.1, by rw [nor_mul h ha.1 hb.1, ha.2, hb.2, one_mul]⟩
  inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, by
    have := nor_mul h ha.1 (Q.inv_mem ha.1)
    rw [mul_inv_cancel, nor_one, ha.2, one_mul] at this
    exact this.symm⟩

theorem normKer_le (h : Eight Q x π) : h.normKer ≤ Q := fun _ hq => hq.1

theorem c_not_mem_normKer (h : Eight Q x π) (hc : HasC Q x c) : c ∉ h.normKer := by
  intro hmem
  have := hmem.2
  rw [hc.nor_c] at this
  exact hc.ne this

theorem mem_normKer_or (h : Eight Q x π) (hc : HasC Q x c) {q : X} (hq : q ∈ Q) :
    q ∈ h.normKer ∨ c * q ∈ h.normKer := by
  rcases nor_cases h hc hq with h1 | h1
  · exact Or.inl ⟨hq, h1⟩
  · right
    refine ⟨Q.mul_mem hc.mem hq, ?_⟩
    rw [nor_mul h hc.mem hq, hc.nor_c, h1, hc.sq]

theorem normKer_conj (h : Eight Q x π) (hc : HasC Q x c) (g : X) {n : X}
    (hn : n ∈ h.normKer) : g * n * g⁻¹ ∈ h.normKer :=
  ⟨conj_mem' hn.1 g, by rw [nor_conj h hc g hn.1, hn.2]⟩

theorem normKer_kill (h : Eight Q x π) {M : Type*} [CommGroup M] (hM : ∀ y : M, y * y = 1)
    (V : X →* M) {n : X} (hn : n ∈ h.normKer) : V n = 1 := by
  have h1 : V (nor x n) = V n * (V x * V n * (V x)⁻¹) * ((V x)⁻¹ * V n * V x) := by
    simp [nor]
  have h2 : V (nor x n) = 1 := by rw [hn.2, map_one]
  have e1 : V x * V n * (V x)⁻¹ = V n := by rw [mul_comm (V x) (V n), mul_inv_cancel_right]
  have e2 : (V x)⁻¹ * V n * V x = V n := by rw [mul_comm (V x)⁻¹ (V n), inv_mul_cancel_right]
  rw [h1, e1, e2, hM (V n), one_mul] at h2
  exact h2

theorem comm_mem_normKer (h : Eight Q x π) (hc : HasC Q x c) {q : X} (hq : q ∈ Q) (g : X) :
    q * (g * q * g⁻¹)⁻¹ ∈ h.normKer := by
  have hq' : (g * q * g⁻¹)⁻¹ ∈ Q := Q.inv_mem (conj_mem' hq g)
  refine ⟨Q.mul_mem hq hq', ?_⟩
  have h1 := nor_mul h hq hq'
  have h2 : nor x ((g * q * g⁻¹)⁻¹) = (nor x (g * q * g⁻¹))⁻¹ := by
    have := nor_mul h (conj_mem' hq g) hq'
    rw [mul_inv_cancel, nor_one] at this
    exact (inv_eq_of_mul_eq_one_right this.symm).symm
  rw [h1, h2, nor_conj h hc g hq]
  exact mul_inv_cancel _

theorem card_normKer (h : Eight Q x π) (hc : HasC Q x c) : Nat.card h.normKer = 4 := by
  have hle := h.normKer_le
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [h.card]; norm_num)
  have hidx : (h.normKer.subgroupOf Q).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨c, hc.mem⟩, fun b => ?_⟩
    have hb := b.2
    rcases nor_cases h hc hb with h1 | h1
    ·
      have hbN : (b : X) ∈ h.normKer := ⟨hb, h1⟩
      have hbc : ((b * ⟨c, hc.mem⟩ : Q) : X) ∉ h.normKer := by
        intro hmem
        have := hmem.2
        have e : ((b * ⟨c, hc.mem⟩ : Q) : X) = (b : X) * c := rfl
        rw [e, nor_mul h hb hc.mem, h1, hc.nor_c, one_mul] at this
        exact hc.ne this
      exact Or.inr ⟨hbN, fun hh => hbc hh⟩
    · have hbN : (b : X) ∉ h.normKer := by
        intro hmem
        have := hmem.2
        rw [h1] at this
        exact hc.ne this
      have hbc : ((b * ⟨c, hc.mem⟩ : Q) : X) ∈ h.normKer := by
        have e : ((b * ⟨c, hc.mem⟩ : Q) : X) = (b : X) * c := rfl
        refine ⟨(b * ⟨c, hc.mem⟩ : Q).2, ?_⟩
        rw [e, nor_mul h hb hc.mem, h1, hc.nor_c, hc.sq]
      exact Or.inl ⟨hbc, hbN⟩
  have h2 := Subgroup.index_mul_card (h.normKer.subgroupOf Q)
  rw [hidx] at h2
  have h3 : Nat.card (h.normKer.subgroupOf Q) = Nat.card h.normKer :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h4 : Nat.card Q = 8 := h.card
  have h5 : Nat.card ↥Q = 8 := h4
  rw [h3] at h2
  rw [h5] at h2
  omega

end Eight

end CFSG.Quasithin.F6.GoldAmS

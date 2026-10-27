module

public import CFSG.Monster.GMS.Facts.Interfaces
public import CFSG.Monster.GMS.S341

public section

namespace CFSG.Monster.GMS.Fi23Local

open CFSG.Blueprint.NativeSporadic

section Basic

variable {G : Type} [Group G] {a z₀ b₀ z u : G}

theorem orderOf_eq_two_of_isConj_a (h : TwoClasses a z₀ b₀ z u) {y : G} (hy : IsConj a y) :
    orderOf y = 2 :=
  (orderOf_eq_of_isConj hy).symm.trans h.orderOf_a

theorem mul_self_eq_one_of_isConj_a (h : TwoClasses a z₀ b₀ z u) {y : G} (hy : IsConj a y) :
    y * y = 1 :=
  mul_self_eq_one_of_orderOf (orderOf_eq_two_of_isConj_a h hy)

theorem comm_of_mem_twoANbr (h : TwoClasses a z₀ b₀ z u) {y e : G} (hy : IsConj a y)
    (he : e ∈ twoANbr a y) : y * e = e * y :=
  mul_comm_of_mul_self_eq_one (mul_self_eq_one_of_isConj_a h hy)
    (mul_self_eq_one_of_isConj_a h he.1) (mul_self_eq_one_of_isConj_a h he.2)

theorem mem_twoANbr_symm (h : TwoClasses a z₀ b₀ z u) {y e : G} (hy : IsConj a y)
    (he : e ∈ twoANbr a y) : y ∈ twoANbr a e :=
  ⟨hy, by rw [← comm_of_mem_twoANbr h hy he]; exact he.2⟩

theorem not_comm_of_orderOf_eq_three {b x : G} (h3 : orderOf (b * x) = 3) (hb : b * b = 1)
    (hx : x * x = 1) : b * x ≠ x * b := by
  intro hc
  have h2 : (b * x) ^ 2 = 1 := by
    calc (b * x) ^ 2 = b * x * (b * x) := pow_two _
      _ = b * (x * b) * x := by group
      _ = b * (b * x) * x := by rw [hc]
      _ = (b * b) * (x * x) := by group
      _ = 1 := by rw [hb, hx, one_mul]
  have := orderOf_dvd_of_pow_eq_one h2
  rw [h3] at this
  omega

variable {b x : G}

theorem mem_inf_of_mem (h : TwoClasses a z₀ b₀ z u) (hb : IsConj a b) (hx : IsConj a x) {d : G}
    (hd : d ∈ twoANbr a b ∩ twoANbr a x) :
    d ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :=
  Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_twoANbr h hb hd.1).symm,
      Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_twoANbr h hx hd.2).symm⟩

theorem false_of_mem_inf (hbx : b * x ≠ x * b) {y : G} (hy : y = b ∨ y = x)
    (hyH : y ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) :
    False := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hyH
  rw [Subgroup.mem_centralizer_singleton_iff] at h1 h2
  rcases hy with rfl | rfl
  · exact hbx h2
  · exact hbx h1.symm

end Basic

section Leech

variable {G : Type} [Group G]

theorem false_of_mem_leechQ {w b x : G} (hb : b ∈ leechQ w) (hx : x ∈ leechQ w)
    (h3 : orderOf (b * x) = 3) : False := by
  obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow_of_mem_leechQ ((leechQ w).mul_mem hb hx)
  rw [h3] at hk
  rcases k with _ | k
  · norm_num at hk
  · have h2 : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (Nat.succ_ne_zero k)
    rw [← hk] at h2
    omega

end Leech

section Main

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem mem_leechQ_sq_of_four_A
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {y d₁ d₂ : G}
    (hy : IsConj a y) (h₁ : d₁ ∈ twoANbr a y) (h₂ : d₂ ∈ twoANbr a y)
    (h4 : orderOf (d₁ * d₂) = 4) (hw : IsConj z₀ ((d₁ * d₂) * (d₁ * d₂))) :
    y ∈ leechQ ((d₁ * d₂) * (d₁ * d₂)) := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  obtain ⟨φ, hφ⟩ := (isTwoBabyCentralizer_of_isConj I.sls hG hy).exists_cover
  have C : TableVICtx a z₀ b₀ z u d₁ y φ :=
    ⟨h, I.tableIII, I.tableIVBaby, h₁.1, mem_twoANbr_symm h hy h₁, hφ⟩
  have hd₁d₁ := mul_self_eq_one_of_isConj_a h h₁.1
  have hc : d₂ ∈ tableVISet a d₁ y := by
    refine ⟨h₂, ?_, ?_⟩
    · rintro rfl
      rw [hd₁d₁, orderOf_one] at h4
      omega
    · intro e
      have e' : d₁ * d₂ = y := by rw [e, ← mul_assoc, hd₁d₁, one_mul]
      rw [e', orderOf_eq_two_of_isConj_a h hy] at h4
      omega
  obtain ⟨K, hK⟩ := C.exists_cond hc
  have ho := C.orderOf_of_cond hc hK
  rw [h4] at ho
  cases K with
  | two_A => simp only [tableVIOrder] at ho; omega
  | two_B => simp only [tableVIOrder] at ho; omega
  | three_A => simp only [tableVIOrder] at ho; omega
  | six_A => simp only [tableVIOrder] at ho; omega
  | four_B =>
    exfalso
    have hK' : (d₁ * d₂) ^ 2 = y := hK
    rw [← pow_two, hK'] at hw
    exact h.not_isConj (hy.trans hw.symm)
  | four_A =>
    obtain ⟨-, -, -, -, -, hyQ⟩ := C.k3_data hc (C.cond_to_orbit hc hK)
    exact hyQ

omit [Finite G] in
theorem mem_leechQ_of_mul_mem_twoB {b₀ z u : G} (h : TwoClasses a z₀ b₀ z u) {y d f : G}
    (hy : IsConj a y)
    (hd : d ∈ twoANbr a y) (hf : f ∈ twoANbr a y) (hc : f * d = d * f)
    (hB : IsConj z₀ (f * d)) (hdQ : d ∈ leechQ (f * d)) : y ∈ leechQ (f * d) := by
  have hdd := mul_self_eq_one_of_isConj_a h hd.1
  have hyd := comm_of_mem_twoANbr h hy hd
  have hyf := comm_of_mem_twoANbr h hy hf
  have e1 : (y * d) * (f * d) = y * f := by
    calc (y * d) * (f * d) = y * (d * f) * d := by group
      _ = y * (f * d) * d := by rw [hc]
      _ = y * f * (d * d) := by group
      _ = y * f := by rw [hdd, mul_one]
  have e2 : (f * d) * (y * d) = y * f := by
    calc (f * d) * (y * d) = f * (d * y) * d := by group
      _ = f * (y * d) * d := by rw [hyd]
      _ = f * y * (d * d) := by group
      _ = y * f := by rw [hdd, mul_one, hyf]
  have hyd' : y * d ∈ leechQ (f * d) :=
    h.mem_leechQ_of_isConj_mul hd.2 hB (by rw [e1, e2]) (by rw [e1]; exact hf.2)
  have := (leechQ (f * d)).mul_mem hyd' ((leechQ (f * d)).inv_mem hdQ)
  rwa [mul_inv_cancel_right] at this

theorem threeTransposition
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {b x : G}
    (hb : IsConj a b) (hx : IsConj a x) (hbx : orderOf (b * x) = 3) {d₁ d₂ : G}
    (h₁ : d₁ ∈ twoANbr a b ∩ twoANbr a x) (h₂ : d₂ ∈ twoANbr a b ∩ twoANbr a x) :
    orderOf (d₁ * d₂) ∈ ({1, 2, 3} : Set ℕ) := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  have hncomm : b * x ≠ x * b := not_comm_of_orderOf_eq_three hbx
    (mul_self_eq_one_of_isConj_a h hb) (mul_self_eq_one_of_isConj_a h hx)
  have hd₁d₁ := mul_self_eq_one_of_isConj_a h h₁.1.1
  by_cases hd : d₂ = d₁
  · subst hd
    rw [hd₁d₁, orderOf_one]
    exact Set.mem_insert _ _
  obtain ⟨φ, hφ⟩ := (isTwoBabyCentralizer_of_isConj I.sls hG hb).exists_cover
  have C : TableVICtx a z₀ b₀ z u d₁ b φ :=
    ⟨h, I.tableIII, I.tableIVBaby, h₁.1.1, mem_twoANbr_symm h hb h₁.1, hφ⟩
  have hc : d₂ ∈ tableVISet a d₁ b := by
    refine ⟨h₂.1, hd, fun e => ?_⟩
    have e' : d₁ * d₂ = b := by rw [e, ← mul_assoc, hd₁d₁, one_mul]
    have hH := Subgroup.mul_mem _ (mem_inf_of_mem h hb hx h₁) (mem_inf_of_mem h hb hx h₂)
    rw [e'] at hH
    exact false_of_mem_inf hncomm (Or.inl rfl) hH
  have hxcomm : x * (d₁ * d₂) = (d₁ * d₂) * x := by
    rw [← mul_assoc, comm_of_mem_twoANbr h hx h₁.2, mul_assoc, comm_of_mem_twoANbr h hx h₂.2,
      ← mul_assoc]
  obtain ⟨K, hK⟩ := C.exists_cond hc
  have ho := C.orderOf_of_cond hc hK
  cases K with
  | two_A => simp only [tableVIOrder] at ho; simp [ho]
  | two_B => simp only [tableVIOrder] at ho; simp [ho]
  | three_A => simp only [tableVIOrder] at ho; simp [ho]
  | four_B =>
    exfalso
    have hK' : (d₁ * d₂) ^ 2 = b := hK
    have := (Commute.pow_right (show Commute x (d₁ * d₂) from hxcomm) 2).eq
    rw [hK'] at this
    exact hncomm this.symm
  | six_A =>
    exfalso
    have hK' : (d₁ * d₂) ^ 3 = b := hK
    have := (Commute.pow_right (show Commute x (d₁ * d₂) from hxcomm) 3).eq
    rw [hK'] at this
    exact hncomm this.symm
  | four_A =>
    exfalso
    have hK' : orderOf (d₁ * d₂) = 4 ∧ IsConj z₀ ((d₁ * d₂) ^ 2) := hK
    have hw : IsConj z₀ ((d₁ * d₂) * (d₁ * d₂)) := by rw [← pow_two]; exact hK'.2
    exact false_of_mem_leechQ (mem_leechQ_sq_of_four_A I hG hb h₁.1 h₂.1 hK'.1 hw)
      (mem_leechQ_sq_of_four_A I hG hx h₁.2 h₂.2 hK'.1 hw) hbx

theorem commute_mem_twoANbr
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {b x : G}
    (hb : IsConj a b) (hx : IsConj a x) (hbx : orderOf (b * x) = 3) {d f : G}
    (hd : d ∈ twoANbr a b ∩ twoANbr a x) (hf : f ∈ twoANbr a b ∩ twoANbr a x) (hfd : f ≠ d)
    (hc : f * d = d * f) : IsConj a (f * d) := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  have hdd := mul_self_eq_one_of_isConj_a h hd.1.1
  have hff := mul_self_eq_one_of_isConj_a h hf.1.1
  have hww : (f * d) * (f * d) = 1 := by
    calc (f * d) * (f * d) = f * (d * f) * d := by group
      _ = f * (f * d) * d := by rw [hc]
      _ = (f * f) * (d * d) := by group
      _ = 1 := by rw [hff, hdd, one_mul]
  have hw1 : f * d ≠ 1 := by
    intro h1
    apply hfd
    calc f = f * d * d := by rw [mul_assoc, hdd, mul_one]
      _ = d := by rw [h1, one_mul]
  have hdw : d * (f * d) = f := by
    calc d * (f * d) = (d * f) * d := by rw [mul_assoc]
      _ = (f * d) * d := by rw [hc]
      _ = f := by rw [mul_assoc, hdd, mul_one]
  have hwC : f * d ∈ Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hdw, mul_assoc, hdd, mul_one]
  rcases h.isConj_or_isConj_of_mem_centralizer hd.1.1 hwC (orderOf_eq_two_of_mul_self hww hw1) with
    hA | hB
  · exact hA
  exfalso
  have hdQ : d ∈ leechQ (f * d) :=
    h.mem_leechQ_of_isConj_mul hd.1.1 hB (by rw [hdw, mul_assoc, hdd, mul_one]) (by
      rw [hdw]; exact hf.1.1)
  exact false_of_mem_leechQ (mem_leechQ_of_mul_mem_twoB h hb hd.1 hf.1 hc hB hdQ)
    (mem_leechQ_of_mul_mem_twoB h hx hd.2 hf.2 hc hB hdQ) hbx

end Main

end CFSG.Monster.GMS.Fi23Local

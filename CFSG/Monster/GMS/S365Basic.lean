module

public import CFSG.Monster.GMS.Facts.Interfaces
public import CFSG.Monster.GMS.Facts.Section36
import CFSG.Monster.GMS.NotConj

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

section Klein

variable {G : Type*} [Group G]

@[expose] def InKlein (x y c : G) : Prop := c = 1 ∨ c = x ∨ c = y ∨ c = x * y

structure IsKlein (x y : G) : Prop where
  sq_x : x * x = 1
  sq_y : y * y = 1
  comm : x * y = y * x

@[expose] def cosetSet (x y t : G) : Set G := {t, t * x, t * y, t * x * y}

theorem mem_cosetSet_iff {x y t s : G} :
    s ∈ cosetSet x y t ↔ ∃ c, InKlein x y c ∧ s = t * c := by
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨1, Or.inl rfl, (mul_one _).symm⟩
    · exact ⟨x, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨y, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨x * y, Or.inr (Or.inr (Or.inr rfl)), mul_assoc _ _ _⟩
  · rintro ⟨c, hc | hc | hc | hc, rfl⟩
    · simp [hc, cosetSet]
    · simp [hc, cosetSet]
    · simp [hc, cosetSet]
    · simp [hc, cosetSet, mul_assoc]

theorem self_mem_cosetSet (x y t : G) : t ∈ cosetSet x y t := Or.inl rfl

theorem IsKlein.mul_mem {x y : G} (h : IsKlein x y) {a b : G} (ha : InKlein x y a)
    (hb : InKlein x y b) : InKlein x y (a * b) := by
  obtain ⟨hx, hy, hxy⟩ := h
  have h1 : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
  have h2 : y * (x * y) = x := by rw [← mul_assoc, ← hxy, mul_assoc, hy, mul_one]
  have h3 : x * y * x = y := by rw [hxy, mul_assoc, hx, mul_one]
  have h4 : x * y * y = x := by rw [mul_assoc, hy, mul_one]
  have h5 : x * y * (x * y) = 1 := by
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hxy]
      _ = 1 := by rw [← mul_assoc, hx, one_mul, hy]
  have h6 : y * x = x * y := hxy.symm
  rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;> rw [ha, hb] <;>
    simp only [InKlein, mul_one, one_mul, hx, hy, h1, h2, h3, h4, h5, h6, true_or, or_true]

theorem IsKlein.mul_self_of_mem {x y : G} (h : IsKlein x y) {c : G} (hc : InKlein x y c) :
    c * c = 1 := by
  obtain ⟨hx, hy, hxy⟩ := h
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · exact hx
  · exact hy
  · calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hxy]
      _ = 1 := by rw [← mul_assoc, hx, one_mul, hy]

theorem IsKlein.cosetSet_eq {x y t w : G} (h : IsKlein x y) (hw : w ∈ cosetSet x y t) :
    cosetSet x y w = cosetSet x y t := by
  obtain ⟨c₀, hc₀, rfl⟩ := mem_cosetSet_iff.1 hw
  have hinv : c₀ * c₀ = 1 := h.mul_self_of_mem hc₀
  ext s
  rw [mem_cosetSet_iff, mem_cosetSet_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c₀ * c, h.mul_mem hc₀ hc, by rw [mul_assoc]⟩
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c₀ * c, h.mul_mem hc₀ hc, ?_⟩
    calc t * c = t * (c₀ * c₀) * c := by rw [hinv, mul_one]
      _ = t * c₀ * (c₀ * c) := by group

theorem InKlein.conj (g : G) {x y c : G} (hc : InKlein x y c) :
    InKlein (g * x * g⁻¹) (g * y * g⁻¹) (g * c * g⁻¹) := by
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inl (by group)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (by group)))

theorem conj_mem_cosetSet (g : G) {x y t s : G} (hs : s ∈ cosetSet x y t) :
    g * s * g⁻¹ ∈ cosetSet (g * x * g⁻¹) (g * y * g⁻¹) (g * t * g⁻¹) := by
  obtain ⟨c, hc, rfl⟩ := mem_cosetSet_iff.1 hs
  refine mem_cosetSet_iff.2 ⟨g * c * g⁻¹, hc.conj g, by group⟩

theorem conj_mem_cosetSet_of_conj {x y t x' y' t' w w' g : G} (h : IsKlein x y)
    (h' : IsKlein x' y') (hw : w ∈ cosetSet x y t) (hw' : w' ∈ cosetSet x' y' t')
    (hgw : g * w * g⁻¹ = w') (hgx : g * x * g⁻¹ = x') (hgy : g * y * g⁻¹ = y') :
    g * t * g⁻¹ ∈ cosetSet x' y' t' := by
  have ht : t ∈ cosetSet x y w := by
    rw [h.cosetSet_eq hw]
    exact self_mem_cosetSet x y t
  have := conj_mem_cosetSet g ht
  rw [hgw, hgx, hgy, h'.cosetSet_eq hw'] at this
  exact this

theorem commute_of_mem_cosetSet {x y t s : G} (hxy : x * y = y * x) (htx : t * x = x * t)
    (hty : t * y = y * t) (hs : s ∈ cosetSet x y t) : s * x = x * s ∧ s * y = y * s := by
  have cxy : Commute x y := hxy
  have ctx : Commute t x := htx
  have cty : Commute t y := hty
  rcases hs with rfl | rfl | rfl | rfl
  · exact ⟨htx, hty⟩
  · exact ⟨(ctx.mul_left (Commute.refl x)).eq, (cty.mul_left cxy).eq⟩
  · exact ⟨(ctx.mul_left cxy.symm).eq, (cty.mul_left (Commute.refl y)).eq⟩
  · exact ⟨((ctx.mul_left (Commute.refl x)).mul_left cxy.symm).eq,
      ((cty.mul_left cxy).mul_left (Commute.refl y)).eq⟩

end Klein

section Count

variable {G : Type*} [Group G]

open Classical in
theorem twoBCount_eq_ite (z₀ x y t : G) :
    twoBCount z₀ x y t = (if IsConj z₀ t then 1 else 0) + (if IsConj z₀ (t * x) then 1 else 0) +
      (if IsConj z₀ (t * y) then 1 else 0) + (if IsConj z₀ (t * x * y) then 1 else 0) := by
  unfold twoBCount
  by_cases h0 : IsConj z₀ t <;> by_cases h1 : IsConj z₀ (t * x) <;>
    by_cases h2 : IsConj z₀ (t * y) <;> by_cases h3 : IsConj z₀ (t * x * y) <;>
    simp [h0, h1, h2, h3, -isConj_iff]

theorem twoBCount_eq_of_mem_cosetSet {z₀ x y t w : G} (h : IsKlein x y)
    (hw : w ∈ cosetSet x y t) : twoBCount z₀ x y w = twoBCount z₀ x y t := by
  obtain ⟨hx, hy, hxy⟩ := h
  rw [twoBCount_eq_ite, twoBCount_eq_ite]
  have e1 : t * x * x = t := by rw [mul_assoc, hx, mul_one]
  have e2 : t * y * y = t := by rw [mul_assoc, hy, mul_one]
  have e3 : t * y * x = t * x * y := by rw [mul_assoc, ← hxy, ← mul_assoc]
  have e4 : t * x * y * y = t * x := by rw [mul_assoc, hy, mul_one]
  have e5 : t * x * y * x = t * y := by
    calc t * x * y * x = t * x * (y * x) := by rw [mul_assoc (t * x) y x]
      _ = t * x * (x * y) := by rw [← hxy]
      _ = t * (x * x) * y := by group
      _ = t * y := by rw [hx, mul_one]
  rcases hw with rfl | rfl | rfl | rfl
  · rfl
  · rw [e1]
    ring
  · rw [e3, e2, e4]
    ring
  · rw [e5, e4, e2]
    ring

end Count

section Basic

variable {G : Type*} [Group G] {a x y : G}

theorem mul_mul_self_eq_one {u v : G} (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = v * u) :
    u * v * (u * v) = 1 := by
  calc u * v * (u * v) = u * (v * u) * v := by group
    _ = u * (u * v) * v := by rw [← huv]
    _ = 1 := by rw [← mul_assoc, hu, one_mul, hv]

theorem sq_of_isConj_a (ha : orderOf a = 2) {v : G} (hv : IsConj a v) : v * v = 1 :=
  mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hv).symm.trans ha)

theorem ne_one_of_isConj_a (ha : orderOf a = 2) {v : G} (hv : IsConj a v) : v ≠ 1 :=
  ne_one_of_orderOf ((orderOf_eq_of_isConj hv).symm.trans ha)

theorem isKlein_of_isLineTriple (ha : orderOf a = 2) (h : IsLineTriple a x y) : IsKlein x y :=
  ⟨sq_of_isConj_a ha h.1, sq_of_isConj_a ha h.2.1,
    mul_comm_of_mul_self_eq_one (sq_of_isConj_a ha h.1) (sq_of_isConj_a ha h.2.1)
      (sq_of_isConj_a ha h.2.2)⟩

theorem ne_of_isLineTriple (ha : orderOf a = 2) (h : IsLineTriple a x y) : x ≠ y := by
  intro hxy
  have h1 : x * y = 1 := by rw [← hxy]; exact sq_of_isConj_a ha h.1
  exact ne_one_of_isConj_a ha h.2.2 h1

end Basic

section Eight

variable {G : Type*} [Group G]

theorem exists_double [Finite G] (A : Subgroup G) {u : G} (hu : u * u = 1)
    (hcomm : ∀ a ∈ A, a * u = u * a) (huA : u ∉ A) :
    ∃ A' : Subgroup G, (∀ e ∈ A', e ∈ A ∨ ∃ a ∈ A, e = a * u) ∧
      Nat.card A' = 2 * Nat.card A := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  let A' : Subgroup G :=
    { carrier := {e | e ∈ A ∨ ∃ a ∈ A, e = a * u}
      mul_mem' := by
        rintro e₁ e₂ (h₁ | ⟨a₁, ha₁, rfl⟩) (h₂ | ⟨a₂, ha₂, rfl⟩)
        · exact Or.inl (A.mul_mem h₁ h₂)
        · exact Or.inr ⟨e₁ * a₂, A.mul_mem h₁ ha₂, by rw [mul_assoc]⟩
        · refine Or.inr ⟨a₁ * e₂, A.mul_mem ha₁ h₂, ?_⟩
          calc a₁ * u * e₂ = a₁ * (u * e₂) := mul_assoc _ _ _
            _ = a₁ * (e₂ * u) := by rw [hcomm e₂ h₂]
            _ = a₁ * e₂ * u := (mul_assoc _ _ _).symm
        · refine Or.inl ?_
          have e : a₁ * u * (a₂ * u) = a₁ * a₂ := by
            calc a₁ * u * (a₂ * u) = a₁ * (u * a₂) * u := by group
              _ = a₁ * (a₂ * u) * u := by rw [← hcomm a₂ ha₂]
              _ = a₁ * a₂ * (u * u) := by group
              _ = a₁ * a₂ := by rw [hu, mul_one]
          rw [e]
          exact A.mul_mem ha₁ ha₂
      one_mem' := Or.inl A.one_mem
      inv_mem' := by
        rintro e (h | ⟨a, ha, rfl⟩)
        · exact Or.inl (A.inv_mem h)
        · refine Or.inr ⟨a⁻¹, A.inv_mem ha, ?_⟩
          calc (a * u)⁻¹ = u⁻¹ * a⁻¹ := mul_inv_rev _ _
            _ = u * a⁻¹ := by rw [huinv]
            _ = a⁻¹ * u := (hcomm a⁻¹ (A.inv_mem ha)).symm }
  refine ⟨A', fun e he => he, ?_⟩
  have hset : (A' : Set G) = (A : Set G) ∪ (fun a => a * u) '' (A : Set G) := by
    ext e
    constructor
    · rintro (h | ⟨a, ha, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, ha, rfl⟩
    · rintro (h | ⟨a, ha, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, ha, rfl⟩
  have hdisj : Disjoint (A : Set G) ((fun a => a * u) '' (A : Set G)) := by
    rw [Set.disjoint_left]
    rintro e he ⟨a, ha, rfl⟩
    apply huA
    have e : u = a⁻¹ * (a * u) := by group
    rw [e]
    exact A.mul_mem (A.inv_mem ha) he
  rw [show Nat.card A' = (A' : Set G).ncard from Nat.card_coe_set_eq _, hset,
    Set.ncard_union_eq hdisj, Set.ncard_image_of_injective _ (mul_left_injective u),
    show Nat.card A = (A : Set G).ncard from Nat.card_coe_set_eq _]
  ring

theorem exists_subgroup_card_eight [Finite G] {x y u : G} (hxx : x * x = 1)
    (hyy : y * y = 1) (huu : u * u = 1) (hxy : x * y = y * x) (hxu : x * u = u * x)
    (hyu : y * u = u * y) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy' : x ≠ y) (hu1 : u ≠ 1)
    (hux : x ≠ u) (huy : y ≠ u) (hxyu : x * y ≠ u) :
    ∃ E : Subgroup G, Nat.card E = 8 ∧ ∀ e ∈ E,
      e = 1 ∨ e = x ∨ e = y ∨ e = x * y ∨ e = u ∨ e = x * u ∨ e = y * u ∨ e = x * y * u := by
  obtain ⟨A₁, hA₁, hc₁⟩ :=
    exists_double (⊥ : Subgroup G) hxx (by simp) fun h => hx1 (Subgroup.mem_bot.mp h)
  have hA₁' : ∀ e ∈ A₁, e = 1 ∨ e = x := by
    intro e he
    rcases hA₁ e he with h | ⟨a₀, ha₀, rfl⟩
    · exact Or.inl (Subgroup.mem_bot.mp h)
    · rw [Subgroup.mem_bot.mp ha₀, one_mul]
      exact Or.inr rfl
  obtain ⟨A₂, hA₂, hc₂⟩ := exists_double A₁ hyy
    (fun e he => by
      rcases hA₁' e he with rfl | rfl
      · simp
      · exact hxy)
    (fun h => by
      rcases hA₁' y h with h | h
      · exact hy1 h
      · exact hxy' h.symm)
  have hA₂' : ∀ e ∈ A₂, e = 1 ∨ e = x ∨ e = y ∨ e = x * y := by
    intro e he
    rcases hA₂ e he with h | ⟨a₁, ha₁, rfl⟩
    · rcases hA₁' e h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases hA₁' a₁ ha₁ with rfl | rfl
      · rw [one_mul]
        exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
  obtain ⟨A₃, hA₃, hc₃⟩ := exists_double A₂ huu
    (fun e he => by
      rcases hA₂' e he with rfl | rfl | rfl | rfl
      · simp
      · exact hxu
      · exact hyu
      · calc x * y * u = x * (y * u) := mul_assoc _ _ _
          _ = x * (u * y) := by rw [hyu]
          _ = x * u * y := (mul_assoc _ _ _).symm
          _ = u * x * y := by rw [hxu]
          _ = u * (x * y) := mul_assoc _ _ _)
    (fun h => by
      rcases hA₂' u h with h | h | h | h
      · exact hu1 h
      · exact hux h.symm
      · exact huy h.symm
      · exact hxyu h.symm)
  refine ⟨A₃, ?_, fun e he => ?_⟩
  · rw [hc₃, hc₂, hc₁, Subgroup.card_bot]
  · rcases hA₃ e he with h | ⟨a₂, ha₂, rfl⟩
    · rcases hA₂' e h with h | h | h | h <;> simp [h]
    · rcases hA₂' a₂ ha₂ with rfl | rfl | rfl | rfl <;> simp



end Eight

section Main

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ x y t : G}

theorem exists_twoB_mem_cosetSet
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hl : IsLineTriple a x y) (he : IsEightExt x y t) :
    ∃ w, IsConj z₀ w ∧ w ∈ cosetSet x y t := by
  have ha : orderOf a = 2 := hG.1.1
  obtain ⟨htt, htx, hty, ht1, htx', hty', htxy'⟩ := he
  have hK := isKlein_of_isLineTriple ha hl
  have hxx := hK.sq_x
  have hyy := hK.sq_y
  have hxy := hK.comm
  obtain ⟨hxA, hyA, hxyA⟩ := hl
  have hx1 := ne_one_of_isConj_a ha hxA
  have hy1 := ne_one_of_isConj_a ha hyA
  have hxy' : x ≠ y := fun h => ne_one_of_isConj_a ha hxyA (by rw [← h]; exact hxx)
  obtain ⟨E, hE8, hE⟩ := exists_subgroup_card_eight hxx hyy htt hxy htx.symm hty.symm hx1 hy1 hxy'
    ht1 htx'.symm hty'.symm htxy'.symm
  have hxt : x * t = t * x := htx.symm
  have hyt : y * t = t * y := hty.symm
  have hsq : ∀ e ∈ E, e * e = 1 := by
    intro e he
    rcases hE e he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · exact hxx
    · exact hyy
    · exact mul_mul_self_eq_one hxx hyy hxy
    · exact htt
    · exact mul_mul_self_eq_one hxx htt hxt
    · exact mul_mul_self_eq_one hyy htt hyt
    · exact mul_mul_self_eq_one (mul_mul_self_eq_one hxx hyy hxy) htt
        ((Commute.mul_left (show Commute x t from hxt) (show Commute y t from hyt)).eq)
  obtain ⟨e, heE, he1, heA⟩ := s33 I.sls I.tableV I.leech hG I.tableIV E hE8 hsq
  have hcos : e ∈ cosetSet x y t := by
    rcases hE e heE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl he1
    · exact absurd hxA heA
    · exact absurd hyA heA
    · exact absurd hxyA heA
    · exact self_mem_cosetSet x y e
    · exact Or.inr (Or.inl hxt)
    · exact Or.inr (Or.inr (Or.inl hyt))
    · refine Or.inr (Or.inr (Or.inr ?_))
      calc x * y * t = x * (y * t) := mul_assoc _ _ _
        _ = x * (t * y) := by rw [hyt]
        _ = x * t * y := (mul_assoc _ _ _).symm
        _ = t * x * y := by rw [hxt]
  refine ⟨e, ?_, hcos⟩
  rcases s31_five I.sls I.tableV I.leech hG I.leechInv
    (orderOf_eq_two_of_mul_self (hsq e heE) he1) with h | h
  · exact absurd h heA
  · exact h

theorem isConj_mul_iff
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {w c : G}
    (hw : IsConj z₀ w) (hc : IsConj a c) (hcomm : c * w = w * c) :
    IsConj z₀ (w * c) ↔ c ∉ leechQ w := by
  constructor
  · intro h
    exact (not_mem_leechQ_of_isConj_mul I.sls I.tableV I.leech hG hc hw hcomm
      (by rw [hcomm]; exact h)).1
  · intro hnot
    by_contra hB
    have hww : w * w = 1 :=
      mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hw).symm.trans hG.2.1)
    have hcc : c * c = 1 := sq_of_isConj_a hG.1.1 hc
    have hwc2 : w * c * (w * c) = 1 := mul_mul_self_eq_one hww hcc hcomm.symm
    have hwc1 : w * c ≠ 1 := by
      intro h1
      have h2 : w = c⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [inv_eq_of_mul_eq_one_right hcc] at h2
      rw [h2] at hw
      exact hG.not_isConj (hc.trans hw.symm)
    rcases s31_five I.sls I.tableV I.leech hG I.leechInv
      (orderOf_eq_two_of_mul_self hwc2 hwc1) with hA | hB'
    · exact hnot (mem_leechQ_of_isConj_mul I.sls I.tableV I.leech hG hc hw hcomm
        (by rw [hcomm]; exact hA))
    · exact hB hB'

open Classical in
theorem twoBCount_eq_of_twoB
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hl : IsLineTriple a x y) {w : G} (hw : IsConj z₀ w) (hxw : x * w = w * x)
    (hyw : y * w = w * y) :
    twoBCount z₀ x y w = 1 + (if x ∈ leechQ w then 0 else 1) + (if y ∈ leechQ w then 0 else 1) +
      (if x * y ∈ leechQ w then 0 else 1) := by
  classical
  have hxyw : x * y * w = w * (x * y) :=
    ((show Commute x w from hxw).mul_left (show Commute y w from hyw)).eq
  rw [twoBCount_eq_ite, mul_assoc w x y]
  have h1 := isConj_mul_iff I hG hw hl.1 hxw
  have h2 := isConj_mul_iff I hG hw hl.2.1 hyw
  have h3 := isConj_mul_iff I hG hw hl.2.2 hxyw
  by_cases hx : x ∈ leechQ w <;> by_cases hy : y ∈ leechQ w <;>
    by_cases hxy : x * y ∈ leechQ w <;> simp [hw, hx, hy, hxy, h1, h2, h3, -isConj_iff]

theorem twoBCount_cases
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    ∀ x y t : G, IsLineTriple a x y → IsEightExt x y t →
      twoBCount z₀ x y t = 1 ∨ twoBCount z₀ x y t = 3 ∨ twoBCount z₀ x y t = 4 := by
  intro x y t hl he
  obtain ⟨w, hw, hwc⟩ := exists_twoB_mem_cosetSet I hG hl he
  have hK := isKlein_of_isLineTriple hG.1.1 hl
  obtain ⟨hxw, hyw⟩ := commute_of_mem_cosetSet hK.comm he.2.1 he.2.2.1 hwc
  rw [← twoBCount_eq_of_mem_cosetSet hK hwc, twoBCount_eq_of_twoB I hG hl hw hxw.symm hyw.symm]
  have hxx := hK.sq_x
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hK.sq_y
  by_cases hx : x ∈ leechQ w <;> by_cases hy : y ∈ leechQ w
  · have : x * y ∈ leechQ w := (leechQ w).mul_mem hx hy
    simp [hx, hy, this]
  · have : x * y ∉ leechQ w := fun h => hy (by
      have := (leechQ w).mul_mem ((leechQ w).inv_mem hx) h
      rwa [hxi, ← mul_assoc, hxx, one_mul] at this)
    simp [hx, hy, this]
  · have : x * y ∉ leechQ w := fun h => hx (by
      have := (leechQ w).mul_mem h ((leechQ w).inv_mem hy)
      rwa [hyi, mul_assoc, hK.sq_y, mul_one] at this)
    simp [hx, hy, this]
  · by_cases hxy : x * y ∈ leechQ w <;> simp [hx, hy, hxy]

end Main

end S365

end CFSG.Monster.GMS

module

public import CFSG.Monster.GMS.S36LinesBasic
public import CFSG.Monster.GMS.Facts.Section36
public import CFSG.Monster.GMS.S36LinesA12

public section

namespace CFSG.Monster.GMS

open S36Lines

namespace S46

section Classes

variable {G : Type*} [Group G] {a z₀ : G}

@[expose] def cls (a z₀ : G) : Bool → G → Prop
  | false => IsConj a
  | true => IsConj z₀

theorem cls_mul_self (ha : orderOf a = 2) (hz : orderOf z₀ = 2) {p : Bool} {w : G}
    (h : cls a z₀ p w) : w * w = 1 := by
  cases p
  · exact sq_eq_one_of_isConj ha h
  · exact sq_eq_one_of_isConj hz h

theorem cls_ne_one (ha : orderOf a = 2) (hz : orderOf z₀ = 2) {p : Bool} {w : G}
    (h : cls a z₀ p w) : w ≠ 1 := by
  cases p
  · exact ne_one_of_isConj ha h
  · exact ne_one_of_isConj hz h

theorem cls_conj {p : Bool} {w : G} (g : G) (h : cls a z₀ p w) : cls a z₀ p (g * w * g⁻¹) := by
  cases p
  · exact IsConj.trans h (isConj_conj_self g w)
  · exact IsConj.trans h (isConj_conj_self g w)

theorem cls_unique (hnc : ¬ IsConj a z₀) {p q : Bool} {w : G} (hp : cls a z₀ p w)
    (hq : cls a z₀ q w) : p = q := by
  cases p <;> cases q
  · rfl
  · exact absurd (IsConj.trans hp (IsConj.symm hq)) hnc
  · exact absurd (IsConj.trans hq (IsConj.symm hp)) hnc
  · rfl

open Classical in
theorem ite_cls (hnc : ¬ IsConj a z₀) {p : Bool} {w : G} (h : cls a z₀ p w) :
    (if IsConj z₀ w then 1 else 0 : ℕ) = p.toNat := by
  cases p
  · have hz : ¬ IsConj z₀ w := fun hz => hnc (IsConj.trans h (IsConj.symm hz))
    rw [ite_eq_right hz]
    rfl
  · have hz : IsConj z₀ w := h
    rw [ite_eq_left hz]
    rfl

end Classes

section Algebra

variable {G : Type*} [Group G]

theorem coset_ids {b t t' : G} (hbb : b * b = 1) (hbt : b * t = t * b)
    (hbt' : b * t' = t' * b) (htt' : t * t' = t' * t) :
    t' * b = b * t' ∧ t' * t = t * t' ∧ t' * b * t = b * (t * t') ∧
      t * (t' * b) = b * (t * t') ∧ b * (t' * b * t) = t * t' := by
  have e3 : t' * b * t = b * (t * t') :=
    calc t' * b * t = b * t' * t := by rw [hbt']
      _ = b * (t' * t) := by rw [mul_assoc]
      _ = b * (t * t') := by rw [htt']
  refine ⟨hbt'.symm, htt'.symm, e3, ?_, ?_⟩
  · calc t * (t' * b) = t * (b * t') := by rw [hbt']
      _ = t * b * t' := by rw [mul_assoc]
      _ = b * t * t' := by rw [hbt]
      _ = b * (t * t') := by rw [mul_assoc]
  · rw [e3, ← mul_assoc, hbb, one_mul]

end Algebra

section Cfg

variable {G : Type*} [Group G] {a z₀ b t t' : G} {p₀ p₁ p₂ p₃ : Bool}

structure Cfg (a z₀ b t t' : G) (p₀ p₁ p₂ p₃ : Bool) : Prop where
  isConj_b : IsConj a b
  mem_t : t ∈ twoANbr a b
  cls₀ : cls a z₀ p₀ t'
  cls₁ : cls a z₀ p₁ (b * t')
  cls₂ : cls a z₀ p₂ (t * t')
  cls₃ : cls a z₀ p₃ (b * (t * t'))

namespace Cfg

theorem isLineTriple (h : Cfg a z₀ b t t' p₀ p₁ p₂ p₃) : IsLineTriple a b t :=
  ⟨h.isConj_b, h.mem_t.1, h.mem_t.2⟩

theorem comm (ha : orderOf a = 2) (hz : orderOf z₀ = 2) (h : Cfg a z₀ b t t' p₀ p₁ p₂ p₃) :
    b * t = t * b ∧ b * t' = t' * b ∧ t * t' = t' * t := by
  have hbb : b * b = 1 := sq_eq_one_of_isConj ha h.isConj_b
  have htt : t * t = 1 := sq_eq_one_of_isConj ha h.mem_t.1
  have ht't' : t' * t' = 1 := cls_mul_self ha hz h.cls₀
  exact ⟨mul_comm_of_isConj_mul ha h.isConj_b h.mem_t.1 h.mem_t.2,
    mul_comm_of_mul_self_eq_one hbb ht't' (cls_mul_self ha hz h.cls₁),
    mul_comm_of_mul_self_eq_one htt ht't' (cls_mul_self ha hz h.cls₂)⟩

theorem eightExt (ha : orderOf a = 2) (hz : orderOf z₀ = 2) (h : Cfg a z₀ b t t' p₀ p₁ p₂ p₃) :
    IsEightExt b t t' := by
  obtain ⟨hbt, hbt', htt'⟩ := h.comm ha hz
  have hbb : b * b = 1 := sq_eq_one_of_isConj ha h.isConj_b
  have htt : t * t = 1 := sq_eq_one_of_isConj ha h.mem_t.1
  refine ⟨cls_mul_self ha hz h.cls₀, hbt'.symm, htt'.symm, cls_ne_one ha hz h.cls₀, ?_, ?_, ?_⟩
  · intro e
    refine cls_ne_one ha hz h.cls₁ ?_
    rw [e, hbb]
  · intro e
    refine cls_ne_one ha hz h.cls₂ ?_
    rw [e, htt]
  · intro e
    refine cls_ne_one ha hz h.cls₃ ?_
    rw [e]
    calc b * (t * (b * t)) = b * (t * (t * b)) := by rw [hbt]
      _ = b * ((t * t) * b) := by rw [← mul_assoc t t b]
      _ = 1 := by rw [htt, one_mul, hbb]

theorem of_two (hb : IsConj a b) (ht : t ∈ twoANbr a b) (ht' : t' ∈ twoBNbr a z₀ b)
    (h : t * t' ∈ twoBBNbr z₀ b) : Cfg a z₀ b t t' false true true true :=
  ⟨hb, ht, ht'.1, ht'.2, h.1, h.2⟩

theorem conj (g : G) (h : Cfg a z₀ b t t' p₀ p₁ p₂ p₃) :
    Cfg a z₀ (g * b * g⁻¹) (g * t * g⁻¹) (g * t' * g⁻¹) p₀ p₁ p₂ p₃ := by
  have e1 : g * b * g⁻¹ * (g * t' * g⁻¹) = g * (b * t') * g⁻¹ := by group
  have e2 : g * t * g⁻¹ * (g * t' * g⁻¹) = g * (t * t') * g⁻¹ := by group
  have e3 : g * b * g⁻¹ * (g * t * g⁻¹ * (g * t' * g⁻¹)) = g * (b * (t * t')) * g⁻¹ := by group
  have e4 : g * b * g⁻¹ * (g * t * g⁻¹) = g * (b * t) * g⁻¹ := by group
  refine ⟨IsConj.trans h.isConj_b (isConj_conj_self g b), ⟨?_, ?_⟩, cls_conj g h.cls₀, ?_, ?_, ?_⟩
  · exact IsConj.trans h.mem_t.1 (isConj_conj_self g t)
  · rw [e4]
    exact IsConj.trans h.mem_t.2 (isConj_conj_self g _)
  · rw [e1]
    exact cls_conj g h.cls₁
  · rw [e2]
    exact cls_conj g h.cls₂
  · rw [e3]
    exact cls_conj g h.cls₃

end Cfg

open Classical in
theorem twoBCount_eq_ite (z₀ x y t : G) :
    twoBCount z₀ x y t = (if IsConj z₀ t then 1 else 0) + (if IsConj z₀ (t * x) then 1 else 0) +
      (if IsConj z₀ (t * y) then 1 else 0) + (if IsConj z₀ (t * x * y) then 1 else 0) := by
  unfold twoBCount
  by_cases h0 : IsConj z₀ t <;> by_cases h1 : IsConj z₀ (t * x) <;>
    by_cases h2 : IsConj z₀ (t * y) <;> by_cases h3 : IsConj z₀ (t * x * y) <;>
    simp [h0, h1, h2, h3, -isConj_iff]

theorem Cfg.twoBCount_eq (hnc : ¬ IsConj a z₀) (ha : orderOf a = 2) (hz : orderOf z₀ = 2)
    (h : Cfg a z₀ b t t' p₀ p₁ p₂ p₃) :
    twoBCount z₀ b t t' = p₀.toNat + p₁.toNat + p₂.toNat + p₃.toNat := by
  obtain ⟨hbt, hbt', htt'⟩ := h.comm ha hz
  have hbb : b * b = 1 := sq_eq_one_of_isConj ha h.isConj_b
  have htt : t * t = 1 := sq_eq_one_of_isConj ha h.mem_t.1
  obtain ⟨e1, e2, e3, -, -⟩ := coset_ids hbb hbt hbt' htt'
  rw [twoBCount_eq_ite, e3, e1, e2, ite_cls hnc h.cls₀, ite_cls hnc h.cls₁, ite_cls hnc h.cls₂,
    ite_cls hnc h.cls₃]

theorem eq_of_cfg (ha : orderOf a = 2) (hz : orderOf z₀ = 2) (hnc : ¬ IsConj a z₀)
    (hp : ¬ (p₀ = p₁ ∧ p₂ = p₃) ∧ ¬ (p₀ = p₂ ∧ p₁ = p₃) ∧ ¬ (p₀ = p₃ ∧ p₁ = p₂)) {s : G}
    (h : Cfg a z₀ b t t' p₀ p₁ p₂ p₃) (h' : Cfg a z₀ b t s p₀ p₁ p₂ p₃)
    (hs : s ∈ ({t', t' * b, t' * t, t' * b * t} : Set G)) : s = t' := by
  obtain ⟨hbt, hbt', htt'⟩ := h.comm ha hz
  have hbb : b * b = 1 := sq_eq_one_of_isConj ha h.isConj_b
  have htt : t * t = 1 := sq_eq_one_of_isConj ha h.mem_t.1
  obtain ⟨e1, e2, e3, e4, e5⟩ := coset_ids hbb hbt hbt' htt'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · rfl
  · exfalso
    have q1 : p₀ = p₁ := cls_unique hnc h'.cls₀ (by rw [e1]; exact h.cls₁)
    have q2 : p₂ = p₃ := cls_unique hnc h'.cls₂ (by rw [e4]; exact h.cls₃)
    exact hp.1 ⟨q1, q2⟩
  · exfalso
    have q1 : p₀ = p₂ := cls_unique hnc h'.cls₀ (by rw [e2]; exact h.cls₂)
    have q2 : p₁ = p₃ := cls_unique hnc h'.cls₁ (by rw [e2]; exact h.cls₃)
    exact hp.2.1 ⟨q1, q2⟩
  · exfalso
    have q1 : p₀ = p₃ := cls_unique hnc h'.cls₀ (by rw [e3]; exact h.cls₃)
    have q2 : p₁ = p₂ := cls_unique hnc h'.cls₁ (by rw [e5]; exact h.cls₂)
    exact hp.2.2 ⟨q1, q2⟩

theorem exists_conj_of_odd (hE8 : EightGroupLines a z₀) (ha : orderOf a = 2) (hz : orderOf z₀ = 2)
    (hnc : ¬ IsConj a z₀)
    (hp : ¬ (p₀ = p₁ ∧ p₂ = p₃) ∧ ¬ (p₀ = p₂ ∧ p₁ = p₃) ∧ ¬ (p₀ = p₃ ∧ p₁ = p₂))
    {b₀ t₀ t₀' : G} (h₀ : Cfg a z₀ b₀ t₀ t₀' p₀ p₁ p₂ p₃) (h : Cfg a z₀ b t t' p₀ p₁ p₂ p₃) :
    ∃ g : G, g * b₀ * g⁻¹ = b ∧ g * t₀ * g⁻¹ = t ∧ g * t₀' * g⁻¹ = t' := by
  obtain ⟨g, hgb, hgt, hgs⟩ := hE8.2 b₀ t₀ t₀' b t t' h₀.isLineTriple (h₀.eightExt ha hz)
    h.isLineTriple (h.eightExt ha hz)
    ((h₀.twoBCount_eq hnc ha hz).trans (h.twoBCount_eq hnc ha hz).symm)
  have hc := h₀.conj g
  rw [hgb, hgt] at hc
  exact ⟨g, hgb, hgt, eq_of_cfg ha hz hnc hp h hc hgs⟩

end Cfg

end S46

end CFSG.Monster.GMS

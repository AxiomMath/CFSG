module

public import CFSG.Monster.Tri.ASegShorten
public import CFSG.Monster.GMS.TwoAGraph

public section

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.Monster.B.Recog

theorem monsterGraph_triangulable_of {V I : Type*} {Γ : SimpleGraph V} (A : CommStruct Γ I)
    (H : ASegHyp A) : Triangulable Γ :=
  triangulable_of_short4 fun p hp => short4_of_hyp A H p hp

section Group

open CFSG.Monster.GMS

variable {G : Type*} [Group G]

private theorem mul_self_eq_one_of_isConj {a g : G} (ha : a * a = 1) (h : IsConj a g) :
    g * g = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  calc c * a * c⁻¹ * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
    _ = 1 := by rw [ha]; group

private theorem ne_one_of_isConj {a g : G} (ha1 : a ≠ 1) (h : IsConj a g) : g ≠ 1 := by
  rintro rfl
  exact ha1 (isConj_one_left.1 h)

private theorem commute_of_adj {a : G} (ha : a * a = 1) {x y : ConjVert a}
    (h : (twoAGraph a).Adj x y) : (x : G) * y = y * x := by
  have hx : (x : G) * x = 1 := mul_self_eq_one_of_isConj ha x.2
  have hy : (y : G) * y = 1 := mul_self_eq_one_of_isConj ha y.2
  have hxy : (x : G) * y * ((x : G) * y) = 1 := mul_self_eq_one_of_isConj ha h.2
  have h₁ : ((x : G) * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy] at h₁
  exact h₁.symm

open scoped Classical in
noncomputable def commStructOfGroup (a : G) (ha : a * a = 1) (ha1 : a ≠ 1) (Z : Set G)
    (Q : G → Set G) (hinv : ∀ g : G, g ≠ 1 → g * g = 1 → IsConj a g ∨ g ∈ Z) :
    CommStruct (twoAGraph a) {g : G // g * g = 1 ∧ g ≠ 1} where
  ι x := ⟨x, mul_self_eq_one_of_isConj ha x.2, ne_one_of_isConj ha1 x.2⟩
  cen i x := (i : G) * x = x * i
  Z := {i | (i : G) ∈ Z}
  Qs i := {x | (x : G) ∈ Q i}
  mid x y := if h : (twoAGraph a).Adj x y then ⟨(x : G) * y, h.2⟩ else x
  three x y := orderOf ((x : G) * y) = 3
  cen_symm _ _ h := h.symm
  cen_refl _ := rfl
  cen_of_adj _ _ h := commute_of_adj ha h
  adj_mid x y h := by
    have hx : (x : G) * x = 1 := mul_self_eq_one_of_isConj ha x.2
    have hy : (y : G) * y = 1 := mul_self_eq_one_of_isConj ha y.2
    have hc := commute_of_adj ha h
    simp only [h, ↓reduceDIte]
    refine ⟨⟨fun he => ?_, ?_⟩, ⟨fun he => ?_, ?_⟩⟩
    · exact ne_one_of_isConj ha1 y.2 (mul_left_cancel (a := (x : G)) (by
        simpa using congrArg Subtype.val he.symm))
    · show IsConj a ((x : G) * ((x : G) * y))
      rw [← mul_assoc, hx, one_mul]
      exact y.2
    · exact ne_one_of_isConj ha1 x.2 (mul_right_cancel (b := (y : G)) (by
        simpa using congrArg Subtype.val he.symm))
    · show IsConj a ((y : G) * ((x : G) * y))
      rw [hc, ← mul_assoc, hy, one_mul]
      exact x.2
  inv_cases i := by
    rcases hinv i.1 i.2.2 i.2.1 with hc | hz
    · exact Or.inl ⟨⟨i.1, hc⟩, Subtype.ext rfl⟩
    · exact Or.inr hz

theorem commStructOfGroup_mid (a : G) (ha : a * a = 1) (ha1 : a ≠ 1) (Z : Set G) (Q : G → Set G)
    (hinv : ∀ g : G, g ≠ 1 → g * g = 1 → IsConj a g ∨ g ∈ Z) {x y : ConjVert a}
    (h : (twoAGraph a).Adj x y) :
    (((commStructOfGroup a ha ha1 Z Q hinv).mid x y : ConjVert a) : G) = (x : G) * y := by
  simp only [commStructOfGroup, h, ↓reduceDIte]

theorem twoAGraph_triangulable_of (a : G) (ha : a * a = 1) (ha1 : a ≠ 1) (Z : Set G)
    (Q : G → Set G) (hinv : ∀ g : G, g ≠ 1 → g * g = 1 → IsConj a g ∨ g ∈ Z)
    (h88 : ∀ (u : ConjVert a) (c : (twoAGraph a).Walk u u), c.length ≤ 4 → Homotopic c .nil)
    (h85 : ∀ x u v : ConjVert a, (x : G) * u = u * x → (x : G) * v = v * x →
      (twoAGraph a).Adj u v → (u = x ∨ (twoAGraph a).Adj u x) ∨ (v = x ∨ (twoAGraph a).Adj v x) ∨
        ∃ c, (twoAGraph a).Adj c x ∧ (twoAGraph a).Adj c u ∧ (twoAGraph a).Adj c v)
    (h87_1 : ∀ z : G, z * z = 1 → z ≠ 1 → z ∈ Z → ∀ x y : ConjVert a, (x : G) ∈ Q z →
      (y : G) ∈ Q z → x = y ∨ (twoAGraph a).Adj x y ∨
        ∃ w : ConjVert a, (w : G) ∈ Q z ∧ (twoAGraph a).Adj x w ∧ (twoAGraph a).Adj w y)
    (h87_3 : ∀ z : G, z * z = 1 → z ≠ 1 → z ∈ Z → ∀ x y v : ConjVert a, (x : G) ∈ Q z →
      (y : G) ∈ Q z → (v : G) ∈ Q z → (twoAGraph a).Adj x y →
        (v : G) * x = x * v ∨ (v : G) * y = y * v ∨ (v : G) * (x * y) = x * y * v)
    (h89 : ∀ z : G, z * z = 1 → z ≠ 1 → z ∈ Z → ∀ u v : ConjVert a, z * u = u * z →
      z * v = v * z → (u : G) ∉ Q z → (v : G) ∉ Q z → (twoAGraph a).Adj u v →
        ∃ w : ConjVert a, (w : G) ∈ Q z ∧ (twoAGraph a).Adj w u ∧ (twoAGraph a).Adj w v)
    (h810 : ∀ i : G, i * i = 1 → i ≠ 1 → ∀ x y : ConjVert a, i * x = x * i → i * y = y * i →
      (twoAGraph a).dist x y = 2 → (x : G) * y ≠ y * x →
        ∃ v : ConjVert a, i * v = v * i ∧ (twoAGraph a).Adj v x ∧ (twoAGraph a).Adj v y)
    (h83_2 : ∀ x y v : ConjVert a, (twoAGraph a).dist x y = 2 → (twoAGraph a).Adj y v →
      ∃ i : G, i * i = 1 ∧ i ≠ 1 ∧ i * x = x * i ∧ i * y = y * i ∧ i * v = v * i)
    (h813_1 : ∀ z : G, z * z = 1 → z ≠ 1 → z ∈ Z → ∀ x y : ConjVert a, z * x = x * z →
      z * y = y * z →
        (∃ b : ConjVert a, z * b = b * z ∧ (x : G) * b = b * x ∧ (y : G) * b = b * y) ∨
          orderOf ((x : G) * y) = 3)
    (h814 : ∀ x u : ConjVert a, (∃ y : ConjVert a, (y = u ∨ (twoAGraph a).Adj y u) ∧
        (x : G) * y = y * x) → x = u ∨ (twoAGraph a).Adj x u ∨
          ∃ w : ConjVert a, (twoAGraph a).Adj x w ∧ (twoAGraph a).Adj w u)
    (h3C : (∀ i : G, i * i = 1 → i ≠ 1 →
        InducedNull (twoAGraph a) {v : ConjVert a | i * (v : G) = v * i}) →
      ∀ x y : ConjVert a, orderOf ((x : G) * y) = 3 →
        (¬∃ b : ConjVert a, (x : G) * b = b * x ∧ (y : G) * b = b * y) →
        ∀ p q : (twoAGraph a).Walk x y, p.length = 3 → q.length = 3 → Homotopic p q)
    (hS4 : ∀ x u v : ConjVert a, orderOf ((x : G) * u) = 3 → (twoAGraph a).Adj u v →
      ¬(x = v ∨ (twoAGraph a).Adj x v) →
      (¬∃ w : ConjVert a, (twoAGraph a).Adj x w ∧ (twoAGraph a).Adj w v) →
      (¬∃ b : ConjVert a, (x : G) * b = b * x ∧ (v : G) * b = b * v) →
      ∀ m : ConjVert a, (m : G) = (u : G) * v →
        ∃ c : ConjVert a, (twoAGraph a).Adj x c ∧ (twoAGraph a).Adj c m) :
    Triangulable (twoAGraph a) := by
  have hmid := fun {x y : ConjVert a} (h : (twoAGraph a).Adj x y) =>
    commStructOfGroup_mid a ha ha1 Z Q hinv h
  have H0 : ASegHyp0 (commStructOfGroup a ha ha1 Z Q hinv) := by
    refine
      { h88 := h88
        h85 := fun x u v hu hv huv => h85 x u v hu hv huv
        h87_1 := fun z hz x hx y hy => h87_1 z.1 z.2.1 z.2.2 hz x y hx hy
        h87_3 := fun z hz x hx y hy v hv hxy => ?_
        h89 := fun z hz u v hu hv hQu hQv huv =>
          h89 z.1 z.2.1 z.2.2 hz u v hu hv hQu hQv huv
        h810 := fun i x y hx hy hd hn => h810 i.1 i.2.1 i.2.2 x y hx hy hd hn
        h83_2 := fun x y v hd hyv => ?_
        h813_1 := fun z hz x y hx hy => h813_1 z.1 z.2.1 z.2.2 hz x y hx hy
        h814 := fun x u hy => h814 x u hy }
    · rcases h87_3 z.1 z.2.1 z.2.2 hz x y v hx hy hv hxy with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · refine Or.inr (Or.inr ?_)
        show (v : G) * ((commStructOfGroup a ha ha1 Z Q hinv).mid x y : ConjVert a) = _
        rw [hmid hxy]
        exact h
    · obtain ⟨i, hi, hi1, h₁, h₂, h₃⟩ := h83_2 x y v hd hyv
      exact ⟨⟨i, hi, hi1⟩, h₁, h₂, h₃⟩
  have hnull : ∀ i : G, i * i = 1 → i ≠ 1 →
      InducedNull (twoAGraph a) {v : ConjVert a | i * (v : G) = v * i} := fun i hi hi1 =>
    inducedNull_cen (commStructOfGroup a ha ha1 Z Q hinv) H0 ⟨i, hi, hi1⟩
  exact monsterGraph_triangulable_of (commStructOfGroup a ha ha1 Z Q hinv)
    { toASegHyp0 := H0
      h3C := fun x y hxy hno p q hp hq => h3C hnull x y hxy hno p q hp hq
      hS4 := fun x u v hxu huv hxv hcn hno => hS4 x u v hxu huv hxv hcn hno _ (hmid huv) }

end Group

end CFSG.Monster.Tri

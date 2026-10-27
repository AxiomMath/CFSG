module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.SetTheory.Cardinal.NatCard

public section

namespace CFSG.RankThree.PartOne.NF7J

section Count

variable {M : Type*} [Group M]

theorem pow_mod3 {z : M} (hz : z ^ 3 = 1) (n : ℕ) : z ^ n = z ^ (n % 3) := by
  conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hz, one_pow, mul_one]

theorem comm3 {x1 x2 x3 y1 y2 y3 : M} (h21 : Commute x2 y1) (h31 : Commute x3 y1)
    (h32 : Commute x3 y2) :
    x1 * x2 * x3 * (y1 * y2 * y3) = (x1 * y1) * (x2 * y2) * (x3 * y3) := by
  calc x1 * x2 * x3 * (y1 * y2 * y3) = x1 * x2 * (x3 * y1) * y2 * y3 := by simp only [mul_assoc]
    _ = x1 * x2 * (y1 * x3) * y2 * y3 := by rw [h31.eq]
    _ = x1 * (x2 * y1) * x3 * y2 * y3 := by simp only [mul_assoc]
    _ = x1 * (y1 * x2) * x3 * y2 * y3 := by rw [h21.eq]
    _ = x1 * y1 * x2 * (x3 * y2) * y3 := by simp only [mul_assoc]
    _ = x1 * y1 * x2 * (y2 * x3) * y3 := by rw [h32.eq]
    _ = (x1 * y1) * (x2 * y2) * (x3 * y3) := by simp only [mul_assoc]

theorem mem_range_of_closure (z₁ z₂ z₃ : M) (h12 : Commute z₁ z₂) (h13 : Commute z₁ z₃)
    (h23 : Commute z₂ z₃) (hz1 : z₁ ^ 3 = 1) (hz2 : z₂ ^ 3 = 1) (hz3 : z₃ ^ 3 = 1)
    {r : M} (hr : r ∈ Subgroup.closure ({z₁, z₂, z₃} : Set M)) :
    r ∈ Set.range (fun x : Fin 3 × Fin 3 × Fin 3 =>
      z₁ ^ (x.1 : ℕ) * z₂ ^ (x.2.1 : ℕ) * z₃ ^ (x.2.2 : ℕ)) := by
  have key : ∃ a b c : ℕ, r = z₁ ^ a * z₂ ^ b * z₃ ^ c := by
    induction hr using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨1, 0, 0, by simp⟩
      · exact ⟨0, 1, 0, by simp⟩
      · exact ⟨0, 0, 1, by simp⟩
    | one => exact ⟨0, 0, 0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, c, rfl⟩ := hx
      obtain ⟨a', b', c', rfl⟩ := hy
      refine ⟨a + a', b + b', c + c', ?_⟩
      rw [comm3 (h12.symm.pow_pow b a') (h13.symm.pow_pow c a') (h23.symm.pow_pow c b'),
        ← pow_add, ← pow_add, ← pow_add]
    | inv x _ hx =>
      obtain ⟨a, b, c, rfl⟩ := hx
      refine ⟨2 * a, 2 * b, 2 * c, ?_⟩
      apply inv_eq_of_mul_eq_one_right
      rw [comm3 (h12.symm.pow_pow b (2 * a)) (h13.symm.pow_pow c (2 * a))
        (h23.symm.pow_pow c (2 * b)), ← pow_add, ← pow_add, ← pow_add]
      have e1 : a + 2 * a = 3 * a := by omega
      have e2 : b + 2 * b = 3 * b := by omega
      have e3 : c + 2 * c = 3 * c := by omega
      rw [e1, e2, e3, pow_mul, pow_mul, pow_mul, hz1, hz2, hz3]
      simp
  obtain ⟨a, b, c, rfl⟩ := key
  refine ⟨(Fin.mk (a % 3) (Nat.mod_lt _ (by decide)), Fin.mk (b % 3) (Nat.mod_lt _ (by decide)),
    Fin.mk (c % 3) (Nat.mod_lt _ (by decide))), ?_⟩
  show z₁ ^ (a % 3) * z₂ ^ (b % 3) * z₃ ^ (c % 3) = _
  rw [← pow_mod3 hz1, ← pow_mod3 hz2, ← pow_mod3 hz3]

theorem sq_mem_aux {s u : M} (hu : u ^ 3 = 1) (h : u ^ 2 ∈ Subgroup.zpowers s) :
    u ∈ Subgroup.zpowers s := by
  have : u = (u ^ 2) ^ 2 := by
    rw [← pow_mul, (show 2 * 2 = 3 + 1 from rfl), pow_add, hu, one_mul, pow_one]
  rw [this]
  exact Subgroup.pow_mem _ h 2

theorem count_false (z₁ z₂ z₃ : M) (h12 : Commute z₁ z₂) (h13 : Commute z₁ z₃)
    (h23 : Commute z₂ z₃) (hz1 : z₁ ^ 3 = 1) (hz2 : z₂ ^ 3 = 1) (hz3 : z₃ ^ 3 = 1)
    (s : Fin 21 → M) (hs3 : ∀ i, s i ^ 3 = 1) (hs1 : ∀ i, s i ≠ 1)
    (hmem : ∀ i, s i ∈ Subgroup.closure ({z₁, z₂, z₃} : Set M))
    (hdist : ∀ i j, i ≠ j → s j ∉ Subgroup.zpowers (s i)) : False := by
  classical
  let g : Fin 3 × Fin 3 × Fin 3 → M := fun x =>
    z₁ ^ (x.1 : ℕ) * z₂ ^ (x.2.1 : ℕ) * z₃ ^ (x.2.2 : ℕ)
  have hT : ∀ r ∈ Subgroup.closure ({z₁, z₂, z₃} : Set M), r ∈ Set.range g :=
    fun r hr => mem_range_of_closure z₁ z₂ z₃ h12 h13 h23 hz1 hz2 hz3 hr
  let f : Fin 21 × Fin 2 → Set.range g := fun p =>
    ⟨s p.1 ^ ((p.2 : ℕ) + 1), hT _ (Subgroup.pow_mem _ (hmem p.1) _)⟩
  have hinj : Function.Injective f := by
    rintro ⟨i, k⟩ ⟨j, l⟩ h
    have h' : s i ^ ((k : ℕ) + 1) = s j ^ ((l : ℕ) + 1) := congrArg Subtype.val h
    have hk : (k : ℕ) = 0 ∨ (k : ℕ) = 1 := by have := k.isLt; omega
    have hl : (l : ℕ) = 0 ∨ (l : ℕ) = 1 := by have := l.isLt; omega
    by_cases hij : i = j
    · subst hij
      have hkl : (k : ℕ) = (l : ℕ) := by
        rcases hk with hk | hk <;> rcases hl with hl | hl
        · rw [hk, hl]
        · exfalso
          rw [hk, hl] at h'
          apply hs1 i
          have : s i * 1 = s i * s i := by simpa [pow_two] using h'
          exact (mul_left_cancel this).symm
        · exfalso
          rw [hk, hl] at h'
          apply hs1 i
          have : s i * s i = s i * 1 := by simpa [pow_two] using h'
          exact mul_left_cancel this
        · rw [hk, hl]
      rw [Prod.mk.injEq]
      exact ⟨rfl, Fin.ext hkl⟩
    · exfalso
      have hmemi : s j ^ ((l : ℕ) + 1) ∈ Subgroup.zpowers (s i) := by
        rw [← h']
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
      apply hdist i j hij
      rcases hl with hl | hl
      · rw [hl] at hmemi
        simpa using hmemi
      · rw [hl] at hmemi
        exact sq_mem_aux (hs3 j) hmemi
  have hcard : Nat.card (Set.range g) ≤ 27 := by
    have := Finite.card_range_le g
    simpa using this
  have h42 := Nat.card_le_card_of_injective f hinj
  have e42 : Nat.card (Fin 21 × Fin 2) = 42 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  omega

end Count

end CFSG.RankThree.PartOne.NF7J

module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsItem316Small

variable {W : Type*} [AddCommGroup W] {n : ℕ} (Q : W → ZMod 2) (c : Fin n → W)

theorem add_pairs_eq_zero (hW : ∀ v : W, v + v = 0) (x y z : W) :
    (x + y) + (x + z) + (y + z) = 0 := by
  have : (x + y) + (x + z) + (y + z) = (x + x) + ((y + y) + (z + z)) := by abel
  rw [this, hW, hW, hW, add_zero, add_zero]

theorem eq_of_c_eq (hW : ∀ v : W, v + v = 0) (hQ0 : Q 0 = 0)
    (hA : ∀ i j, i ≠ j → Q (c i + c j) = 1) {j k : Fin n} (h : c j = c k) : j = k := by
  by_contra hjk
  have h1 := hA j k hjk
  rw [h, hW, hQ0] at h1
  exact zero_ne_one h1

theorem adj_cases (hW : ∀ v : W, v + v = 0) (hQ0 : Q 0 = 0)
    (hS2 : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      Q (c i + c j + c k + c l) ≠ 1)
    {a b a' b' : Fin n} (hab : a ≠ b) (hab' : a' ≠ b')
    (h : Q ((c a + c b) + (c a' + c b')) = 1) :
    (a = a' ∧ b ≠ b') ∨ (a = b' ∧ b ≠ a') ∨ (b = a' ∧ a ≠ b') ∨ (b = b' ∧ a ≠ a') := by
  by_cases h1 : a = a'
  · subst h1
    by_cases h2 : b = b'
    · subst h2
      rw [hW, hQ0] at h
      exact absurd h zero_ne_one
    · exact Or.inl ⟨rfl, h2⟩
  by_cases h2 : a = b'
  · subst h2
    by_cases h3 : b = a'
    · subst h3
      rw [add_comm (c b) (c a), hW, hQ0] at h
      exact absurd h zero_ne_one
    · exact Or.inr (Or.inl ⟨rfl, h3⟩)
  by_cases h3 : b = a'
  · exact Or.inr (Or.inr (Or.inl ⟨h3, h2⟩))
  by_cases h4 : b = b'
  · exact Or.inr (Or.inr (Or.inr ⟨h4, h1⟩))
  rw [← add_assoc] at h
  exact absurd h (hS2 a b a' b' hab h1 h2 h3 h4 hab')

theorem pair_cases (hW : ∀ v : W, v + v = 0) (hQ0 : Q 0 = 0)
    (hA : ∀ i j, i ≠ j → Q (c i + c j) = 1)
    (hS3 : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      c i + c j + c k + c l ≠ 0)
    {a b a' b' : Fin n} (hab : a ≠ b) (hab' : a' ≠ b') (h : c a + c b = c a' + c b') :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  by_cases h1 : a = a'
  · subst h1
    exact Or.inl ⟨rfl, eq_of_c_eq Q c hW hQ0 hA (add_left_cancel h)⟩
  by_cases h2 : a = b'
  · subst h2
    rw [add_comm (c a') (c a)] at h
    exact Or.inr ⟨rfl, eq_of_c_eq Q c hW hQ0 hA (add_left_cancel h)⟩
  by_cases h3 : b = a'
  · subst h3
    rw [add_comm (c a) (c b)] at h
    exact Or.inr ⟨eq_of_c_eq Q c hW hQ0 hA (add_left_cancel h), rfl⟩
  by_cases h4 : b = b'
  · subst h4
    rw [add_comm (c a) (c b), add_comm (c a') (c b)] at h
    exact Or.inl ⟨eq_of_c_eq Q c hW hQ0 hA (add_left_cancel h), rfl⟩
  exfalso
  apply hS3 a b a' b' hab h1 h2 h3 h4 hab'
  rw [add_assoc (c a + c b), h]
  exact hW _

theorem exists_perm_of_isometry (hW : ∀ v : W, v + v = 0) (hQ0 : Q 0 = 0)
    (hA : ∀ i j, i ≠ j → Q (c i + c j) = 1)
    (hB : ∀ v, Q v = 1 → ∃ i j, i ≠ j ∧ v = c i + c j)
    (hS2 : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      Q (c i + c j + c k + c l) ≠ 1)
    (hS3 : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      c i + c j + c k + c l ≠ 0)
    {a b₁ b₂ : Fin n} (h1 : a ≠ b₁) (h2 : a ≠ b₂) (h12 : b₁ ≠ b₂)
    (g : W →+ W) (hg : Function.Injective g) (hgQ : ∀ v, Q (g v) = Q v) :
    ∃ σ : Equiv.Perm (Fin n), ∀ j, g (c a + c j) = c (σ a) + c (σ j) := by
  have hpair : ∀ j, j ≠ a → ∃ x y, x ≠ y ∧ g (c a + c j) = c x + c y := fun j hj =>
    hB _ (by rw [hgQ]; exact hA a j hj.symm)
  have hadj : ∀ j k, j ≠ k → Q (g (c a + c j) + g (c a + c k)) = 1 := by
    intro j k hjk
    rw [← map_add, hgQ]
    have : c a + c j + (c a + c k) = (c a + c a) + (c j + c k) := by abel
    rw [this, hW, zero_add]
    exact hA j k hjk
  obtain ⟨x1, y1, hxy1, e1⟩ := hpair b₁ h1.symm
  obtain ⟨x2, y2, hxy2, e2⟩ := hpair b₂ h2.symm
  have hadj12 := hadj b₁ b₂ h12
  rw [e1, e2] at hadj12
  obtain ⟨x, u1, u2, hxu1, hxu2, hu12, f1, f2⟩ : ∃ x u1 u2, x ≠ u1 ∧ x ≠ u2 ∧ u1 ≠ u2 ∧
      g (c a + c b₁) = c x + c u1 ∧ g (c a + c b₂) = c x + c u2 := by
    rcases adj_cases Q c hW hQ0 hS2 hxy1 hxy2 hadj12 with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩
    · subst h
      exact ⟨x1, y1, y2, hxy1, hxy2, h', e1, e2⟩
    · subst h
      exact ⟨x1, y1, x2, hxy1, hxy2.symm, h', e1, by rw [e2, add_comm]⟩
    · subst h
      exact ⟨y1, x1, y2, hxy1.symm, hxy2, h', by rw [e1, add_comm], e2⟩
    · subst h
      exact ⟨y1, x1, x2, hxy1.symm, hxy2.symm, h', by rw [e1, add_comm], by rw [e2, add_comm]⟩
  have hstar : ∀ j, j ≠ a → ∃ y, y ≠ x ∧ g (c a + c j) = c x + c y := by
    intro j hj
    by_cases hj1 : j = b₁
    · subst hj1
      exact ⟨u1, hxu1.symm, f1⟩
    by_cases hj2 : j = b₂
    · subst hj2
      exact ⟨u2, hxu2.symm, f2⟩
    obtain ⟨p, q, hpq, e⟩ := hpair j hj
    have k1 := hadj b₁ j (Ne.symm hj1)
    have k2 := hadj b₂ j (Ne.symm hj2)
    rw [f1, e] at k1
    rw [f2, e] at k2
    have hne : (c x + c u1) + (c x + c u2) + (c p + c q) ≠ 0 := by
      rw [← f1, ← f2, ← e, ← map_add, ← map_add]
      intro h0
      have h3 : c a + c b₁ + (c a + c b₂) + (c a + c j) = c a + c b₁ + c b₂ + c j := by
        have : c a + c b₁ + (c a + c b₂) + (c a + c j) =
            (c a + c a) + (c a + c b₁ + c b₂ + c j) := by abel
        rw [this, hW, zero_add]
      apply hS3 a b₁ b₂ j h1 h2 hj.symm h12 (Ne.symm hj1) (Ne.symm hj2)
      rw [← h3]
      exact hg (h0.trans (map_zero g).symm)
    have hx : x = p ∨ x = q := by
      by_contra hcon
      push Not at hcon
      rcases adj_cases Q c hW hQ0 hS2 hxu1 hpq k1 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact hcon.1 h
      · exact hcon.2 h
      · rcases adj_cases Q c hW hQ0 hS2 hxu2 hpq k2 with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩
        · exact hcon.1 h'
        · exact hcon.2 h'
        · exact hu12 (h.trans h'.symm)
        · apply hne
          rw [h, h']
          exact add_pairs_eq_zero hW _ _ _
      · rcases adj_cases Q c hW hQ0 hS2 hxu2 hpq k2 with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩
        · exact hcon.1 h'
        · exact hcon.2 h'
        · apply hne
          rw [h, h', add_comm (c p) (c q)]
          exact add_pairs_eq_zero hW _ _ _
        · exact hu12 (h.trans h'.symm)
    rcases hx with hx | hx
    · subst hx
      exact ⟨q, hpq.symm, e⟩
    · subst hx
      exact ⟨p, hpq, by rw [e, add_comm]⟩
  haveI : Nonempty (Fin n) := ⟨a⟩
  choose! τ' hτ'ne hτ' using hstar
  let τ : Fin n → Fin n := fun j => if j = a then x else τ' j
  have hτinj : Function.Injective τ := by
    intro j k hjk
    by_cases hj : j = a
    · by_cases hk : k = a
      · rw [hj, hk]
      · simp only [τ, hj, hk, if_true, if_false] at hjk
        exact absurd hjk.symm (hτ'ne k hk)
    · by_cases hk : k = a
      · simp only [τ, hj, hk, if_true, if_false] at hjk
        exact absurd hjk (hτ'ne j hj)
      · simp only [τ, hj, hk, if_false] at hjk
        have hgjk : g (c a + c j) = g (c a + c k) := by
          rw [hτ' j hj, hτ' k hk, hjk]
        exact eq_of_c_eq Q c hW hQ0 hA (add_left_cancel (hg hgjk))
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτinj)
  refine ⟨σ, fun j => ?_⟩
  have hσa : σ a = x := by simp [σ, τ]
  by_cases hj : j = a
  · subst hj
    rw [hW, map_zero, hW]
  · have hσj : σ j = τ' j := by simp [σ, τ, hj]
    rw [hσa, hσj]
    exact hτ' j hj

end CFSG.RankThree.PartTwo.Sec19.SimsItem316Small

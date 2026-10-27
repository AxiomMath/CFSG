module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSADefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAPairAux
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAPairAux2

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

lemma ggMUP1_swap_disjoint {n : ℕ} {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hcomm : Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b)
    (hne : Equiv.swap a b ≠ Equiv.swap c d) :
    Equiv.Perm.Disjoint (Equiv.swap a b) (Equiv.swap c d) := by
  rw [Equiv.Perm.disjoint_iff_eq_or_eq]
  intro x
  by_contra h
  push Not at h
  obtain ⟨hx1, hx2⟩ := h
  have hxt : x ∈ (Equiv.swap c d).support := by
    rw [Equiv.Perm.mem_support]; exact hx2
  have hxs : x ∈ (Equiv.swap a b).support := by
    rw [Equiv.Perm.mem_support]; exact hx1
  have hfx_t : Equiv.swap a b x ∈ (Equiv.swap c d).support :=
    (Equiv.Perm.mem_support_iff_of_commute hcomm x).mpr hxt
  have hb_or : x = a ∨ x = b := by
    have := hxs
    rwa [Equiv.Perm.support_swap hab, Finset.mem_insert, Finset.mem_singleton] at this
  have hsx : Equiv.swap a b x = a ∨ Equiv.swap a b x = b := by
    rcases hb_or with hx | hx
    · exact Or.inr (by rw [hx, Equiv.swap_apply_left])
    · exact Or.inl (by rw [hx, Equiv.swap_apply_right])
  have ha_t : a ∈ (Equiv.swap c d).support := by
    rcases hb_or with hx | hx
    · exact hx ▸ hxt
    · rcases hsx with h | h
      · rw [← h]; exact hfx_t
      · exact absurd (h.trans hx.symm) hx1
  have hb_t : b ∈ (Equiv.swap c d).support := by
    rcases hb_or with hx | hx
    · rcases hsx with h | h
      · exact absurd (h.trans hx.symm) hx1
      · rw [← h]; exact hfx_t
    · exact hx ▸ hxt
  have ha_cd : a = c ∨ a = d := by
    have := ha_t
    rwa [Equiv.Perm.support_swap hcd, Finset.mem_insert, Finset.mem_singleton] at this
  have hb_cd : b = c ∨ b = d := by
    have := hb_t
    rwa [Equiv.Perm.support_swap hcd, Finset.mem_insert, Finset.mem_singleton] at this
  rcases ha_cd with hac | had
  · rcases hb_cd with hbc | hbd
    · exact hab (by rw [hac, hbc])
    · exact hne (by rw [hac, hbd])
  · rcases hb_cd with hbc | hbd
    · exact hne (by rw [had, hbc, Equiv.swap_comm])
    · exact hab (by rw [had, hbd])

theorem ggMUP1_suPairBlock_comm
    {K : Type} [Field K] [Finite K] {p f n : ℕ} [Fact p.Prime] [CharP K p]
    {a b c d : Fin n} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ∀ A ∈ ggSuPairBlock K p f n a b, ∀ B ∈ ggSuPairBlock K p f n c d, A * B = B * A := by
  classical
  intro A hA B hB
  let P : Matrix (Fin n) (Fin n) K := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1
  let Q : Matrix (Fin n) (Fin n) K := ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1
  have hP : ∀ i j : Fin n, ¬ ((i = a ∨ i = b) ∧ (j = a ∨ j = b)) → P i j = 0 := by
    intro i j hij
    simp only [P, Matrix.sub_apply]
    rw [hA i j (by tauto), sub_self]
  have hQ : ∀ i j : Fin n, ¬ ((i = c ∨ i = d) ∧ (j = c ∨ j = d)) → Q i j = 0 := by
    intro i j hij
    simp only [Q, Matrix.sub_apply]
    rw [hB i j (by tauto), sub_self]
  have hPQ : P * Q = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = a ∨ k = b
    · have hkc : k ≠ c := by
        intro hkc
        rcases hk with h | h
        · exact hac (h.symm.trans hkc)
        · exact hbc (h.symm.trans hkc)
      have hkd : k ≠ d := by
        intro hkd
        rcases hk with h | h
        · exact had (h.symm.trans hkd)
        · exact hbd (h.symm.trans hkd)
      have hk' : ¬ ((k = c ∨ k = d) ∧ (j = c ∨ j = d)) := by
        rintro ⟨h1, -⟩
        exact h1.elim hkc hkd
      rw [hQ k j hk', mul_zero]
    · have hk' : ¬ ((i = a ∨ i = b) ∧ (k = a ∨ k = b)) := by
        rintro ⟨-, h2⟩
        exact hk h2
      rw [hP i k hk', zero_mul]
  have hQP : Q * P = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = c ∨ k = d
    · have hka : k ≠ a := by
        intro hka'
        rcases hk with h | h
        · exact hac (hka'.symm.trans h)
        · exact had (hka'.symm.trans h)
      have hkb : k ≠ b := by
        intro hkb'
        rcases hk with h | h
        · exact hbc (hkb'.symm.trans h)
        · exact hbd (hkb'.symm.trans h)
      have hk' : ¬ ((k = a ∨ k = b) ∧ (j = a ∨ j = b)) := by
        rintro ⟨h1, -⟩
        exact h1.elim hka hkb
      rw [hP k j hk', mul_zero]
    · have hk' : ¬ ((i = c ∨ i = d) ∧ (k = c ∨ k = d)) := by
        rintro ⟨-, h2⟩
        exact hk h2
      rw [hQ i k hk', zero_mul]
  have hAm : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + P := by
    dsimp only [P]; abel
  have hBm : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + Q := by
    dsimp only [Q]; abel
  have hkey : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [hAm, hBm]
    have hdiff : (1 + P) * (1 + Q) - (1 + Q) * (1 + P) = P * Q - Q * P := by
      noncomm_ring
    rw [hPQ, hQP, sub_zero] at hdiff
    exact sub_eq_zero.mp hdiff
  apply Subtype.ext
  apply Units.ext
  exact hkey

lemma ggMUP1_swap_overlap {n : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hcomm : Equiv.swap a b * Equiv.swap c d ≠ Equiv.swap c d * Equiv.swap a b) :
    a = c ∨ a = d ∨ b = c ∨ b = d := by
  by_contra h
  push Not at h
  obtain ⟨hac, had, hbc, hbd⟩ := h
  apply hcomm
  apply Equiv.Perm.Disjoint.commute
  rw [Equiv.Perm.disjoint_iff_eq_or_eq]
  intro x
  by_cases hxa : x = a
  · subst hxa
    exact Or.inr (Equiv.swap_apply_of_ne_of_ne hac had)
  by_cases hxb : x = b
  · subst hxb
    exact Or.inr (Equiv.swap_apply_of_ne_of_ne hbc hbd)
  by_cases hxc : x = c
  · subst hxc
    exact Or.inl (Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm)
  by_cases hxd : x = d
  · subst hxd
    exact Or.inl (Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm)
  exact Or.inl (Equiv.swap_apply_of_ne_of_ne hxa hxb)

lemma ggMUP1_share3 {n : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hcomm : Equiv.swap a b * Equiv.swap c d ≠ Equiv.swap c d * Equiv.swap a b) :
    ∃ x y z : Fin n, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      ({a, b} : Finset (Fin n)) = {x, y} ∧ ({c, d} : Finset (Fin n)) = {y, z} := by
  have hne : Equiv.swap a b ≠ Equiv.swap c d := fun h => hcomm (by rw [h])
  rcases ggMUP1_swap_overlap hab hcd hcomm with hac | had | hbc | hbd
  · refine ⟨b, a, d, hab.symm, ?_, ?_, Finset.pair_comm a b, ?_⟩
    · intro h; exact hcd (hac.symm.trans h)
    · intro h; exact hne (by rw [hac, h])
    · rw [hac]
  · refine ⟨b, a, c, hab.symm, ?_, ?_, Finset.pair_comm a b, ?_⟩
    · intro h; exact hcd (h.symm.trans had)
    · intro h; exact hne (by rw [had, h, Equiv.swap_comm])
    · rw [had, Finset.pair_comm]
  · refine ⟨a, b, d, hab, ?_, ?_, rfl, ?_⟩
    · intro h; exact hcd (hbc.symm.trans h)
    · intro h; exact hne (by rw [hbc, h, Equiv.swap_comm])
    · rw [hbc, Finset.pair_comm]
  · refine ⟨a, b, c, hab, ?_, ?_, rfl, ?_⟩
    · intro h; exact hcd (h.symm.trans hbd)
    · intro h; exact hne (by rw [hbd, h])
    · rw [hbd, Finset.pair_comm]

lemma ggMUP1_suPairBlock_congr {K : Type} [Field K] [Finite K] {p f n : ℕ}
    [Fact p.Prime] [CharP K p] {a b c d : Fin n}
    (h : ({a, b} : Finset (Fin n)) = {c, d}) :
    ggSuPairBlock K p f n a b = ggSuPairBlock K p f n c d := by
  have hiff : ∀ i : Fin n, (i ≠ a ∧ i ≠ b) ↔ (i ≠ c ∧ i ≠ d) := by
    intro i
    constructor
    · rintro ⟨hi1, hi2⟩
      have h1 : i ∉ ({a, b} : Finset (Fin n)) := by simp [hi1, hi2]
      rw [h] at h1
      simpa using h1
    · rintro ⟨hi1, hi2⟩
      have h1 : i ∉ ({c, d} : Finset (Fin n)) := by simp [hi1, hi2]
      rw [← h] at h1
      simpa using h1
  apply Subgroup.ext
  intro M
  simp only [ggSuPairBlock]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  exact imp_congr (or_congr (hiff i) (hiff j)) Iff.rfl

end CFSG.StandardType

end

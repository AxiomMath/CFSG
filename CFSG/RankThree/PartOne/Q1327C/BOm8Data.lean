module

public import CFSG.RankThree.PartOne.KFR4.B3Refl

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG.RankThree.PartOne.KFR4

theorem signed_perm_of_b3 {p : ℕ} (hp : p.Prime) {Γ : Type*} [Group Γ] {T : Subgroup Γ}
    (D : B3Data p T) :
    ∃ (e : Fin 3 → Γ) (w : Fin 3 → Γ) (u : Γ), (∀ j, e j ∈ T) ∧
      (∀ a b c : ℤ, e 0 ^ a * e 1 ^ b * e 2 ^ c = 1 →
        (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c) ∧
      (∀ i, w i ∈ Subgroup.normalizer (T : Set Γ)) ∧ u ∈ Subgroup.normalizer (T : Set Γ) ∧
      (∀ i j, w i * e j * (w i)⁻¹ = if i = j then (e j)⁻¹ else e j) ∧
      u * e 0 * u⁻¹ = e 1 ∧ u * e 1 * u⁻¹ = e 0 ∧ u * e 2 * u⁻¹ = e 2 := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  set c := D.c with hc
  let ε : Fin 3 → ↥T := fun j => c.symm (Multiplicative.ofAdd (Pi.single j 1))
  have hlin : ∀ j, lin c (ε j) = Pi.single j 1 := fun j => lin_symm c _
  let sroot : Fin 3 → Root := ![Root.s1, Root.s2, Root.s3]
  choose w hwN hw using fun i => D.realize (sroot i)
  obtain ⟨u, huN, hu⟩ := D.realize Root.m12
  have hrefl : ∀ (ρ : Root) (j : Fin 3), lin c (reflT c ρ (ε j)) =
      ((ρ.sgn j : ℤ) : ZMod p) • Pi.single (ρ.perm j) 1 := by
    intro ρ j
    rw [lin_reflT, hlin, reflLin_single_eq]
  have hsgn : ∀ i : Fin 3, (sroot i).sgn i = -1 ∧ (sroot i).perm i = i := by
    intro i
    fin_cases i <;> simp [sroot, Root.sgn, Root.perm]
  have hsgn' : ∀ i j : Fin 3, i ≠ j → (sroot i).sgn j = 1 ∧ (sroot i).perm j = j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [sroot, Root.sgn, Root.perm] at hij ⊢
  have hsw : ∀ i j, reflT c (sroot i) (ε j) = if i = j then (ε j)⁻¹ else ε j := by
    intro i j
    apply lin_injective c
    rw [hrefl]
    by_cases hij : i = j
    · subst hij
      have hite : (if i = i then (ε i)⁻¹ else ε i) = (ε i)⁻¹ := by simp
      rw [hite, lin_inv, hlin, (hsgn i).1, (hsgn i).2]
      funext k
      simp
    · have hite : (if i = j then (ε j)⁻¹ else ε j) = ε j := by simp [hij]
      rw [hite, hlin, (hsgn' i j hij).1, (hsgn' i j hij).2]
      funext k
      simp
  have hu0 : reflT c Root.m12 (ε 0) = ε 1 := by
    apply lin_injective c
    rw [hrefl, hlin]
    simp [Root.sgn, Root.perm]
  have hu1 : reflT c Root.m12 (ε 1) = ε 0 := by
    apply lin_injective c
    rw [hrefl, hlin]
    simp [Root.sgn, Root.perm]
  have hu2 : reflT c Root.m12 (ε 2) = ε 2 := by
    apply lin_injective c
    rw [hrefl, hlin]
    have h2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
    simp [Root.sgn, Root.perm, h2]
  have hlinzpow : ∀ (x : ↥T) (a : ℤ), lin c (x ^ a) = a • lin c x := by
    intro x a
    show Multiplicative.toAdd (c (x ^ a)) = a • Multiplicative.toAdd (c x)
    rw [map_zpow, toAdd_zpow]
    rfl
  refine ⟨fun j => (ε j : Γ), fun i => w i, u, fun j => (ε j).2, ?_, hwN, huN, ?_, ?_, ?_, ?_⟩
  · intro a b c' h
    have h1 : ε 0 ^ a * ε 1 ^ b * ε 2 ^ c' = 1 := by
      apply Subtype.ext
      simpa using h
    have h2 := congrArg (lin c) h1
    rw [lin_mul, lin_mul, hlinzpow, hlinzpow, hlinzpow, hlin, hlin, hlin, lin_one] at h2
    have h0 := congrFun h2 0
    have h1' := congrFun h2 1
    have h2' := congrFun h2 2
    simp at h0 h1' h2'
    refine ⟨?_, ?_, ?_⟩
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd a p).1 (by simpa using h0)
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd b p).1 (by simpa using h1')
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd c' p).1 (by simpa using h2')
  · intro i j
    have := hw i (ε j)
    rw [hsw] at this
    split_ifs at this ⊢
    · simpa using this
    · simpa using this
  · have := hu (ε 0)
    rw [hu0] at this
    exact this
  · have := hu (ε 1)
    rw [hu1] at this
    exact this
  · have := hu (ε 2)
    rw [hu2] at this
    exact this

end CFSG.RankThree.PartOne.Q1327C

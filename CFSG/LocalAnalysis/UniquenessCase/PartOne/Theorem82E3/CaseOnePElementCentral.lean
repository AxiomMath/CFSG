module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

private theorem not_modEq_twentySeven {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hp13 : p ≠ 13) (hd : d = 1 ∨ d = 3 ∨ d = 9) : ¬ 27 ≡ d [MOD p] := by
  intro h
  have hdvd : p ∣ 27 - d := (Nat.modEq_iff_dvd' (by omega)).1 h.symm
  have h2 : ¬ p ∣ 2 := fun h' => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  have h3 : ¬ p ∣ 3 := fun h' => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h')
  rcases hd with rfl | rfl | rfl
  · rw [show (27 : ℕ) - 1 = 2 * 13 by norm_num] at hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h' | h'
    · exact h2 h'
    · exact hp13 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h')
  · rw [show (27 : ℕ) - 3 = 2 ^ 3 * 3 by norm_num] at hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h' | h'
    · exact h2 (hp.dvd_of_dvd_pow h')
    · exact h3 h'
  · rw [show (27 : ℕ) - 9 = 2 * 3 ^ 2 by norm_num] at hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h' | h'
    · exact h2 h'
    · exact h3 (hp.dvd_of_dvd_pow h')

theorem centralizes_of_card_27_of_prime {X : Type*} [Group X] [Finite X] {U : Subgroup X}
    (hU : Nat.card U = 27) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp13 : p ≠ 13)
    {y : X} (hy : y ∈ Subgroup.normalizer (U : Set X)) {a : ℕ} (hya : y ^ p ^ a = 1) :
    ∀ u ∈ U, y * u = u * y := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype U := Fintype.ofFinite U
  let f : Function.End U := fun u => ⟨y * u * y⁻¹, (Subgroup.mem_normalizer_iff.1 hy u).1 u.2⟩
  have hfpow : ∀ k : ℕ, ∀ u : U, ((f ^ k) u : X) = y ^ k * u * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro u; simp; rfl
    | succ k ih =>
      intro u
      rw [pow_succ]
      change ((f ^ k) (f u) : X) = _
      rw [ih]
      change y ^ k * (y * u * y⁻¹) * (y ^ k)⁻¹ = _
      group
  have hf1 : f ^ p ^ a = 1 := by
    funext u
    apply Subtype.ext
    rw [hfpow, hya]
    simp; rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := U) hf1
  set C : Subgroup X := U ⊓ Subgroup.centralizer ({y} : Set X) with hC
  have hfix : Fintype.card f.fixedPoints = Nat.card C := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr ⟨fun u => ⟨(u.1 : X), u.1.2, ?_⟩, fun c => ⟨⟨c.1, c.2.1⟩, ?_⟩, ?_, ?_⟩
    · have hu : f u.1 = u.1 := u.2
      have h1 : y * (u.1 : X) * y⁻¹ = u.1 := congrArg Subtype.val hu
      show (u.1 : X) ∈ Subgroup.centralizer ({y} : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact (mul_inv_eq_iff_eq_mul.1 h1)
    · have h1 : y * (c.1 : X) = c.1 * y :=
        Subgroup.mem_centralizer_iff.1 c.2.2 y rfl
      show f ⟨c.1, c.2.1⟩ = ⟨c.1, c.2.1⟩
      apply Subtype.ext
      show y * (c.1 : X) * y⁻¹ = c.1
      rw [h1]; group
    · intro u; rfl
    · intro c; rfl
  have hCdvd : Nat.card C ∣ 27 := hU ▸ Subgroup.card_dvd_of_le inf_le_left
  have hC27 : Nat.card C = 27 := by
    have h27 : Fintype.card U = 27 := by rw [← Nat.card_eq_fintype_card]; exact hU
    rw [h27, hfix] at hmod
    have hdv : Nat.card C ∈ Nat.divisors 27 := Nat.mem_divisors.2 ⟨hCdvd, by norm_num⟩
    have : Nat.divisors 27 = {1, 3, 9, 27} := by decide
    rw [this] at hdv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdv
    rcases hdv with h | h | h | h
    · exact absurd hmod (not_modEq_twentySeven hp hp2 hp3 hp13 (Or.inl h))
    · exact absurd hmod (not_modEq_twentySeven hp hp2 hp3 hp13 (Or.inr (Or.inl h)))
    · exact absurd hmod (not_modEq_twentySeven hp hp2 hp3 hp13 (Or.inr (Or.inr h)))
    · exact h
  have hCU : C = U := Subgroup.eq_of_le_of_card_ge (inf_le_left : C ≤ U) (by rw [hU, hC27])
  intro u hu
  have : u ∈ C := hCU ▸ hu
  exact (Subgroup.mem_centralizer_iff.1 this.2 y rfl)

variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem Case811Sylow.mem_centralizer_of_isPGroup_of_prime {c : Ctx82E3 D} (h : Case811Sylow c)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp13 : p ≠ 13) :
    ∀ g ∈ D.M ⊓ Subgroup.normalizer (h.A : Set G),
      IsPGroup p (Subgroup.zpowers g) → g ∈ Subgroup.centralizer (h.A : Set G) := by
  intro g hg hgp
  obtain ⟨k, hk⟩ := hgp ⟨g, Subgroup.mem_zpowers g⟩
  have hgk : g ^ p ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (centralizes_of_card_27_of_prime h.card_A hp hp2 hp3 hp13 hg.2 hgk u hu).symm

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

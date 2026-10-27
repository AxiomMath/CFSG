module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.Quasithin.H13.F431.G2

section Fixed

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] def fixK : Set K := {t | σ t = t}

theorem mem_fixK {t : K} : t ∈ fixK σ ↔ σ t = t := Iff.rfl

@[expose] noncomputable def solK (c : K) : K :=
  open Classical in if h : ∃ t, σ t + t = c then h.choose else 0

theorem solK_spec {c t : K} (h : σ t + t = c) : σ (solK σ c) + solK σ c = c := by
  classical
  have h' : ∃ t, σ t + t = c := ⟨t, h⟩
  have := h'.choose_spec
  simpa [solK, h'] using this

end Fixed

section CharTwo

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)

theorem add_self_K (a : K) : a + a = 0 := CharTwo.add_self_eq_zero a

theorem add_comm_eq_zero_iff (t : K) : σ t + t = 0 ↔ σ t = t := by
  constructor
  · intro h
    have := add_eq_zero_iff_eq_neg.1 h
    rwa [CharTwo.neg_eq] at this
  · intro h
    rw [h, add_self_K]

theorem add_mem_fixK_of_eq {t t' c : K} (h : σ t + t = c) (h' : σ t' + t' = c) :
    t + t' ∈ fixK σ := by
  rw [mem_fixK, ← add_comm_eq_zero_iff, map_add]
  have : σ t + σ t' + (t + t') = (σ t + t) + (σ t' + t') := by ring
  rw [this, h, h', add_self_K]

theorem corr_mem_fixK {t c : K} (h : σ t + t = c) : t + solK σ c ∈ fixK σ :=
  add_mem_fixK_of_eq σ h (solK_spec σ h)

end CharTwo

section Frobenius

variable {K : Type} [Field K] [CharP K 2] [Finite K] (σ : K ≃+* K) {r : ℕ}

omit [CharP K 2] in
theorem sigma_sigma_of_frobenius (hr : Nat.card K = r ^ 2) (hσ : ∀ x, σ x = x ^ r) (x : K) :
    σ (σ x) = x := by
  classical
  have : Fintype K := Fintype.ofFinite K
  rw [hσ, hσ, ← pow_mul, ← sq, ← hr, Nat.card_eq_fintype_card, FiniteField.pow_card]

omit [CharP K 2] [Finite K] in
theorem card_fixK_le (hr2 : 2 ≤ r) (hσ : ∀ x, σ x = x ^ r) : Nat.card (fixK σ) ≤ r := by
  classical
  let p : Polynomial K := Polynomial.X ^ r - Polynomial.X
  have hdeg : p.natDegree = r := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt
      (by rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]; omega)]
    simp
  have hp : p ≠ 0 := by
    intro h
    have : p.natDegree = 0 := by rw [h]; simp
    omega
  have hsub : fixK σ ⊆ ↑p.roots.toFinset := by
    intro t ht
    have ht' : t ^ r = t := by rw [← hσ]; exact ht
    simp [p, Polynomial.mem_roots hp, ht']
  calc Nat.card (fixK σ) = (fixK σ).ncard := (Nat.card_coe_set_eq _)
    _ ≤ (↑p.roots.toFinset : Set K).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = p.roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ = r := hdeg

theorem le_card_fixK (hr : Nat.card K = r ^ 2) (hσ : ∀ x, σ x = x ^ r) :
    r ≤ Nat.card (fixK σ) := by
  classical
  let tr : K →+ K := (σ : K →+* K).toAddMonoidHom + AddMonoidHom.id K
  have htr : ∀ y, tr y = σ y + y := fun y => rfl
  have hker : (tr.ker : Set K) = fixK σ := by
    ext y
    simp [AddMonoidHom.mem_ker, htr, add_comm_eq_zero_iff, mem_fixK]
  have hrange : (tr.range : Set K) ⊆ fixK σ := by
    rintro _ ⟨y, rfl⟩
    rw [mem_fixK, htr, map_add, sigma_sigma_of_frobenius σ hr hσ, add_comm]
  have h1 := AddSubgroup.card_ker_mul_card_range tr
  have h2 : Nat.card tr.ker = Nat.card (fixK σ) := by rw [← hker]; rfl
  have h3 : Nat.card tr.range ≤ Nat.card (fixK σ) := by
    have := Set.ncard_le_ncard hrange (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at this
    exact this
  rw [h2, hr] at h1
  have h4 : r ^ 2 ≤ Nat.card (fixK σ) * Nat.card (fixK σ) := by
    rw [← h1]
    exact Nat.mul_le_mul_left _ h3
  by_contra hlt
  push Not at hlt
  have : Nat.card (fixK σ) * Nat.card (fixK σ) < r ^ 2 := by
    rw [sq]
    exact Nat.mul_lt_mul'' hlt hlt
  omega

theorem card_fixK_frobenius (hr2 : 2 ≤ r) (hr : Nat.card K = r ^ 2) (hσ : ∀ x, σ x = x ^ r) :
    Nat.card (fixK σ) = r :=
  le_antisymm (card_fixK_le σ hr2 hσ) (le_card_fixK σ hr hσ)

end Frobenius

end CFSG.Quasithin.H13.F431.G2

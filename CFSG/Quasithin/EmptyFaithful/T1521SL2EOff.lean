module

public import CFSG.Quasithin.EmptyFaithful.T1521SL2EField
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.L21521E

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

theorem twist_dichotomy {n : ℕ} (hK : Nat.card K = 2 ^ n) {V A : Subgroup G} (w : K → G)
    (hwinj : Function.Injective w) (hwV : ∀ x, w x ∈ V) (hVw : ∀ y ∈ V, ∃ x, w x = y)
    (hA : IsElemAbelian 2 A)
    (hact : ∀ a ∈ A, ∃ (t : K) (σ : K ≃+* K), t ≠ 0 ∧ ∀ x, a * w x * a⁻¹ = w (t * σ x)) :
    A ≤ Subgroup.centralizer (V : Set G) ∨
      ∃ a0 ∈ A, ∃ (t0 : K) (σ0 : K ≃+* K), t0 ≠ 0 ∧ σ0 ≠ 1 ∧
        (∀ x, a0 * w x * a0⁻¹ = w (t0 * σ0 x)) ∧
        Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hsq : ∀ s : K, s * s = 1 → s = 1 := by
    intro s hs
    have h : (s - 1) * (s - 1) = 0 := by linear_combination hs + (1 - s) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h)
  by_cases hnot : A ≤ Subgroup.centralizer (V : Set G)
  · exact Or.inl hnot
  right
  obtain ⟨a0, ha0A, ha0C⟩ : ∃ a0 ∈ A, a0 ∉ Subgroup.centralizer (V : Set G) := by
    by_contra h
    exact hnot fun a ha => by
      by_contra hc
      exact h ⟨a, ha, hc⟩
  choose! t σ ht hw using hact
  have hcomp : ∀ a ∈ A, ∀ b ∈ A, ∀ x, t (a * b) * σ (a * b) x = t a * σ a (t b * σ b x) := by
    intro a ha b hb x
    apply hwinj
    rw [← hw (a * b) (A.mul_mem ha hb) x, ← hw a ha (t b * σ b x), ← hw b hb x]
    group
  have hone : ∀ x, t 1 * σ 1 x = x := by
    intro x
    apply hwinj
    rw [← hw 1 A.one_mem x]
    group
  have hinv : ∀ a ∈ A, ∀ x, t a * σ a (t a * σ a x) = x := by
    intro a ha x
    have h2a : a * a = 1 := by
      have := hA.2 a ha
      rwa [sq] at this
    have := hcomp a ha a ha x
    rw [h2a, hone x] at this
    exact this.symm
  have e1 : ∀ a ∈ A, t a * σ a (t a) = 1 := by
    intro a ha
    have := hinv a ha 1
    simpa using this
  have e2 : ∀ a ∈ A, ∀ x, σ a (σ a x) = x := by
    intro a ha x
    have := hinv a ha x
    rw [map_mul, ← mul_assoc, e1 a ha, one_mul] at this
    exact this
  have hsqσ : ∀ a ∈ A, σ a * σ a = 1 := fun a ha => RingEquiv.ext fun x => e2 a ha x
  have hcent : ∀ a ∈ A, a ∈ Subgroup.centralizer (V : Set G) ↔ ∀ x, t a * σ a x = x := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h x
      have h1 := h (w x) (hwV x)
      apply hwinj
      rw [← hw a ha x, mul_inv_eq_iff_eq_mul]
      exact h1.symm
    · intro h y hy
      obtain ⟨x, rfl⟩ := hVw y hy
      have h1 := hw a ha x
      rw [h x, mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
  have hσne : ∀ a ∈ A, a ∉ Subgroup.centralizer (V : Set G) → σ a ≠ 1 := by
    intro a ha hac h1
    apply hac
    rw [hcent a ha]
    have h3 := e1 a ha
    rw [h1] at h3
    have h4 : t a = 1 := hsq _ (by simpa using h3)
    intro x
    rw [h1, h4]
    simp
  have hkey : ∀ a ∈ A, a ∈ Subgroup.centralizer (V : Set G) ∨
      a0 * a ∈ Subgroup.centralizer (V : Set G) := by
    intro a ha
    by_cases hac : a ∈ Subgroup.centralizer (V : Set G)
    · exact Or.inl hac
    · right
      have hσeq : σ a = σ a0 :=
        ringEquiv_eq_of_sq_eq_one hK (hσne a ha hac) (hσne a0 ha0A ha0C) (hsqσ a ha)
          (hsqσ a0 ha0A)
      have hb : a0 * a ∈ A := A.mul_mem ha0A ha
      obtain ⟨s, hstar⟩ : ∃ s : K, ∀ y, t (a0 * a) * σ (a0 * a) y = s * y := by
        refine ⟨t a0 * σ a0 (t a), fun y => ?_⟩
        rw [hcomp a0 ha0A a ha y, hσeq, map_mul, e2 a0 ha0A]
        ring
      have h1 := hinv (a0 * a) hb 1
      rw [hstar 1, hstar (s * 1)] at h1
      have hs1 : s = 1 := hsq s (by simpa using h1)
      rw [hcent _ hb]
      intro y
      rw [hstar y, hs1, one_mul]
  have hindex : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by
    have hinj : Function.Injective (fun a : ↥A =>
        if h : a.1 ∈ Subgroup.centralizer (V : Set G) then
          ((true, ⟨a.1, a.2, h⟩) : Bool × ↥(A ⊓ Subgroup.centralizer (V : Set G)))
        else (false, ⟨a0 * a.1, A.mul_mem ha0A a.2, (hkey a.1 a.2).resolve_left h⟩)) := by
      intro a b hab
      by_cases ha : a.1 ∈ Subgroup.centralizer (V : Set G) <;>
        by_cases hb : b.1 ∈ Subgroup.centralizer (V : Set G) <;>
        simp only [ha, hb, dite_true, dite_false] at hab
      · exact Subtype.ext (congrArg (fun p => (p.2 : G)) hab)
      · exact absurd (congrArg Prod.fst hab) (by simp)
      · exact absurd (congrArg Prod.fst hab) (by simp)
      · exact Subtype.ext (mul_left_cancel (congrArg (fun p => (p.2 : G)) hab))
    have := Nat.card_le_card_of_injective _ hinj
    simpa [Nat.card_prod, Nat.card_eq_fintype_card] using this
  exact ⟨a0, ha0A, t a0, σ a0, ht a0 ha0A, hσne a0 ha0A ha0C, hw a0 ha0A, hindex⟩

theorem card_le_two_mul_of_twist {n : ℕ} (hK : Nat.card K = 2 ^ n) {V A : Subgroup G} (w : K → G)
    (hwinj : Function.Injective w) (hwV : ∀ x, w x ∈ V) (hVw : ∀ y ∈ V, ∃ x, w x = y)
    (hA : IsElemAbelian 2 A)
    (hact : ∀ a ∈ A, ∃ (t : K) (σ : K ≃+* K), t ≠ 0 ∧ ∀ x, a * w x * a⁻¹ = w (t * σ x)) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by
  rcases twist_dichotomy hK w hwinj hwV hVw hA hact with h | ⟨-, -, -, -, -, -, -, h⟩
  · rw [inf_eq_left.mpr h]
    omega
  · exact h

theorem centralizes_of_offender_twist {n : ℕ} (hn : 3 ≤ n) (hK : Nat.card K = 2 ^ n)
    {V A : Subgroup G} (w : K → G) (hwinj : Function.Injective w) (hwV : ∀ x, w x ∈ V)
    (hVw : ∀ y ∈ V, ∃ x, w x = y) (hA : IsElemAbelian 2 A)
    (hact : ∀ a ∈ A, ∃ (t : K) (σ : K ≃+* K), t ≠ 0 ∧ ∀ x, a * w x * a⁻¹ = w (t * σ x))
    (hineq : Nat.card V * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) ≤
      Nat.card A * Nat.card ↥(A ⊓ V)) :
    A ≤ Subgroup.centralizer (V : Set G) := by
  classical
  rcases twist_dichotomy hK w hwinj hwV hVw hA hact with
    h | ⟨a0, ha0A, t0, σ0, ht0, hσ0, hw0, hindex⟩
  · exact h
  exfalso
  have hfix : Nat.card ↥(A ⊓ V) ≤ 2 ^ (n / 2) := by
    let f : ↥(A ⊓ V) → K := fun y => Classical.choose (hVw y.1 y.2.2)
    have hf : ∀ y : ↥(A ⊓ V), w (f y) = y.1 := fun y => Classical.choose_spec (hVw y.1 y.2.2)
    have hfixed : ∀ y : ↥(A ⊓ V), t0 * σ0 (f y) = f y := by
      intro y
      apply hwinj
      rw [← hw0 (f y), hf y]
      have hcomm : a0 * y.1 = y.1 * a0 :=
        congrArg Subtype.val (hA.1.is_comm.comm ⟨a0, ha0A⟩ ⟨y.1, y.2.1⟩)
      rw [hcomm]
      group
    have hle : Nat.card ↥(A ⊓ V) ≤ Nat.card {x : K // t0 * σ0 x = x} := by
      refine Nat.card_le_card_of_injective (fun y => ⟨f y, hfixed y⟩) ?_
      intro y y' hyy
      have h1 : f y = f y' := congrArg Subtype.val hyy
      apply Subtype.ext
      rw [← hf y, ← hf y', h1]
    exact hle.trans (card_twistedFixed_le (by omega) hK hσ0 ht0)
  have hVcard : 2 ^ n ≤ Nat.card V := by
    rw [← hK]
    exact Nat.card_le_card_of_injective (fun x : K => (⟨w x, hwV x⟩ : V))
      (fun x y h => hwinj (congrArg Subtype.val h))
  have hCpos : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
  have h1 : 2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) ≤
      (2 * 2 ^ (n / 2)) * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by
    calc 2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G))
        ≤ Nat.card V * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) :=
          Nat.mul_le_mul_right _ hVcard
      _ ≤ Nat.card A * Nat.card ↥(A ⊓ V) := hineq
      _ ≤ (2 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G))) * 2 ^ (n / 2) :=
          Nat.mul_le_mul hindex hfix
      _ = (2 * 2 ^ (n / 2)) * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by ring
  have h3 : 2 ^ n ≤ 2 ^ (n / 2 + 1) := by
    rw [pow_succ]
    have := Nat.le_of_mul_le_mul_right h1 hCpos
    linarith
  have h4 : n ≤ n / 2 + 1 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h3
  omega

end CFSG.Quasithin.L21521E

module

public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique

section Sylow

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_of_conjSub_eq {g : G} {X : Subgroup G} (h : B6.conjSub g X = X) :
    g ∈ Subgroup.normalizer (X : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

theorem exists_odd_pow_mem {T : Subgroup G} (hT : IsSylowTwoOf T ⊤) {s : G}
    (hs : s ∈ Subgroup.normalizer (T : Set G)) : ∃ k : ℕ, Odd k ∧ s ^ k ∈ T := by
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos s).ne'
  refine ⟨m, hm, ?_⟩
  have hSyl : IsSylowTwoOf T (Subgroup.normalizer (T : Set G)) :=
    B6.isSylowTwoOf_mono hT Subgroup.le_normalizer le_top
  have hdvd : m ∣ orderOf s := by rw [hord]; exact dvd_mul_left m (2 ^ a)
  have hord' : orderOf (s ^ m) = 2 ^ a := by
    rw [orderOf_pow_of_dvd hm.pos.ne' hdvd, hord, Nat.mul_div_cancel _ hm.pos]
  have hp : IsPGroup 2 (Subgroup.zpowers (s ^ m)) :=
    IsPGroup.of_card (n := a) (by rw [Nat.card_zpowers, hord'])
  have hle : Subgroup.zpowers (s ^ m) ≤ T :=
    B6.le_of_isPGroup_of_odd_relIndex (H := Subgroup.normalizer (T : Set G)) (N := T)
      (Subgroup.zpowers_le.2 (Subgroup.pow_mem _ hs m)) hp Subgroup.le_normalizer le_rfl hSyl.2.2
  exact hle (Subgroup.mem_zpowers _)

theorem no_swap {T A Q : Subgroup G} (hT : IsSylowTwoOf T ⊤)
    (hQT : T ≤ Subgroup.normalizer (Q : Set G)) (hne : A ≠ Q)
    (hpair : ∀ s ∈ Subgroup.normalizer (T : Set G), B6.conjSub s A = A ∨ B6.conjSub s A = Q)
    {s : G} (hs : s ∈ Subgroup.normalizer (T : Set G)) (hsQ : B6.conjSub s Q = A) : False := by
  have hsA : B6.conjSub s A = Q := by
    rcases hpair s hs with h | h
    · exfalso
      apply hne
      have : B6.conjSub s Q = B6.conjSub s A := by rw [hsQ, h]
      exact ((B6.conjSub s).injective this).symm
    · exact h
  have hs2 : B6.conjSub (s * s) A = A := by rw [B6.conjSub_mul, hsA, hsQ]
  have hs2N : s * s ∈ Subgroup.normalizer (A : Set G) := mem_normalizer_of_conjSub_eq hs2
  obtain ⟨k, ⟨j, hj⟩, hkT⟩ := exists_odd_pow_mem hT hs
  have hk : s ^ k = (s * s) ^ j * s := by rw [hj, pow_succ, pow_mul, sq]
  have h1 : B6.conjSub (s ^ k) Q = Q := B6.conjSub_eq_self (hQT hkT)
  have h2 : B6.conjSub (s ^ k) Q = A := by
    rw [hk, B6.conjSub_mul, hsQ]
    exact B6.conjSub_eq_self (Subgroup.pow_mem _ hs2N j)
  exact hne (h2.symm.trans h1)

end Sylow

section Union

variable {G : Type*} [Group G]

theorem le_or_le_of_forall_mem {K H₁ H₂ : Subgroup G} (h : ∀ a ∈ K, a ∈ H₁ ∨ a ∈ H₂) :
    K ≤ H₁ ∨ K ≤ H₂ := by
  by_cases h1 : K ≤ H₁
  · exact Or.inl h1
  · refine Or.inr fun b hbK => ?_
    by_contra hb2
    apply h1
    intro a haK
    by_contra ha1
    have ha2 : a ∈ H₂ := (h a haK).resolve_left ha1
    have hb1 : b ∈ H₁ := (h b hbK).resolve_right hb2
    rcases h (a * b) (K.mul_mem haK hbK) with hab | hab
    · exact ha1 (by simpa using H₁.mul_mem hab (H₁.inv_mem hb1))
    · exact hb2 (by simpa using H₂.mul_mem (H₂.inv_mem ha2) hab)

end Union

end CFSG.Quasithin.H13.F431.U42Aut

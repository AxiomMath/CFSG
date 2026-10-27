module

public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.EmptyFaithful.SBc17Ent0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

namespace SBc17

theorem perm_fix_of_invariant_small {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α)
    (hσ : σ ^ 5 = 1) (B : Finset α) (hB : ∀ x, σ x ∈ B ↔ x ∈ B) (hcard : B.card ≤ 4) :
    ∀ x ∈ B, σ x = x := by
  let τ : Equiv.Perm ↥B := σ.subtypePerm hB
  have hpow : ∀ (n : ℕ) (x : ↥B), (((τ ^ n) x : ↥B) : α) = (σ ^ n) x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]
      rfl
  have hτ5 : τ ^ 5 = 1 := by
    ext x
    rw [hpow, hσ]
    rfl
  have hdvd : orderOf τ ∣ (Nat.card ↥B).factorial := by
    have := orderOf_dvd_natCard τ
    rwa [Nat.card_perm] at this
  have h5 : orderOf τ ∣ 5 := orderOf_dvd_of_pow_eq_one hτ5
  have hcB : Nat.card ↥B ≤ 4 := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; exact hcard
  have h1 : orderOf τ = 1 := by
    have h24 : (Nat.card ↥B).factorial ∣ 24 := by
      interval_cases (Nat.card ↥B) <;> decide
    have h' : orderOf τ ∣ 24 := hdvd.trans h24
    have hg : orderOf τ ∣ Nat.gcd 24 5 := Nat.dvd_gcd h' h5
    simpa using hg
  have hτ1 : τ = 1 := orderOf_eq_one_iff.mp h1
  intro x hx
  have := congrArg (fun f : Equiv.Perm ↥B => (f ⟨x, hx⟩ : α)) hτ1
  simpa [τ] using this

theorem eq_one_of_stab_partition {n : ℕ} {P : Finset (Finset (Fin n))} {σ : Equiv.Perm (Fin n)}
    (hcov : P.biUnion id = Finset.univ) (hsmall : ∀ B ∈ P, B.card ≤ 4)
    (hcnt : ∀ k : ℕ, (P.filter (fun B => B.card = k)).card ≤ 4)
    (hσP : σ ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) P) (hσ5 : σ ^ 5 = 1) : σ = 1 := by
  have hσP' : σ • P = P := hσP
  have hmem : ∀ C : Finset (Fin n), σ • C ∈ P ↔ C ∈ P := by
    intro C
    conv_lhs => rw [← hσP']
    exact Finset.smul_mem_smul_finset_iff σ
  let τ : Equiv.Perm (Finset (Fin n)) := MulAction.toPermHom (Equiv.Perm (Fin n)) (Finset (Fin n)) σ
  have hτ5 : τ ^ 5 = 1 := by
    rw [← map_pow, hσ5, map_one]
  have hτapp : ∀ C, τ C = σ • C := fun C => rfl
  have hfixP : ∀ C ∈ P, σ • C = C := by
    intro C hC
    have h := perm_fix_of_invariant_small τ hτ5 (P.filter (fun B => B.card = C.card))
      (by
        intro D
        rw [Finset.mem_filter, Finset.mem_filter, hτapp, hmem, Finset.card_smul_finset])
      (hcnt C.card) C (by rw [Finset.mem_filter]; exact ⟨hC, rfl⟩)
    exact h
  have hfixpt : ∀ C ∈ P, ∀ x ∈ C, σ x = x := by
    intro C hC
    refine perm_fix_of_invariant_small σ hσ5 C (fun x => ?_) (hsmall C hC)
    have h2 : σ • x ∈ σ • C ↔ x ∈ C := Finset.smul_mem_smul_finset_iff σ
    rw [hfixP C hC] at h2
    exact h2
  refine Equiv.ext fun x => ?_
  have hx : x ∈ (P.biUnion id : Finset (Fin n)) := by rw [hcov]; exact Finset.mem_univ x
  obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
  simpa using hfixpt C hC x hxC

theorem card_filter_parts {n : ℕ} {P : Finset (Finset (Fin n))} {sizes : Multiset ℕ}
    (h : P.val.map Finset.card = sizes) (k : ℕ) :
    (P.filter (fun B => B.card = k)).card = Multiset.count k sizes := by
  have hf : Multiset.filter (fun B : Finset (Fin n) => B.card = k) P.val =
      Multiset.filter (fun B : Finset (Fin n) => k = B.card) P.val :=
    Multiset.filter_congr fun B _ => eq_comm
  rw [← h, Multiset.count_map, Finset.card_def, Finset.filter_val, hf]

theorem eq_one_of_stab_type_four_three {P : Finset (Finset (Fin 7))} {σ : Equiv.Perm (Fin 7)}
    (hP : IsPartitionOfType P {4, 3})
    (hσP : σ ∈ MulAction.stabilizer (Equiv.Perm (Fin 7)) P) (hσ5 : σ ^ 5 = 1) : σ = 1 := by
  refine eq_one_of_stab_partition hP.2.2.1 (fun B hB => ?_) (fun k => ?_) hσP hσ5
  · have h : B.card ∈ P.val.map Finset.card := Multiset.mem_map_of_mem _ hB
    rw [hP.2.2.2] at h
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h
    omega
  · rw [card_filter_parts hP.2.2.2 k]
    have : Multiset.count k ({4, 3} : Multiset ℕ) ≤ 1 := by
      by_cases h4 : k = 4
      · subst h4; decide
      · by_cases h3 : k = 3
        · subst h3; decide
        · rw [Multiset.count_eq_zero_of_notMem]
          · exact Nat.zero_le _
          · simp [h4, h3]
    omega

theorem eq_one_of_stab_type_two_two_two_one {P : Finset (Finset (Fin 7))} {σ : Equiv.Perm (Fin 7)}
    (hP : IsPartitionOfType P {2, 2, 2, 1})
    (hσP : σ ∈ MulAction.stabilizer (Equiv.Perm (Fin 7)) P) (hσ5 : σ ^ 5 = 1) : σ = 1 := by
  refine eq_one_of_stab_partition hP.2.2.1 (fun B hB => ?_) (fun k => ?_) hσP hσ5
  · have h : B.card ∈ P.val.map Finset.card := Multiset.mem_map_of_mem _ hB
    rw [hP.2.2.2] at h
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h
    omega
  · rw [card_filter_parts hP.2.2.2 k]
    have : Multiset.count k ({2, 2, 2, 1} : Multiset ℕ) ≤ 3 := by
      by_cases h2 : k = 2
      · subst h2; decide
      · by_cases h1 : k = 1
        · subst h1; decide
        · rw [Multiset.count_eq_zero_of_notMem]
          · exact Nat.zero_le _
          · simp [h2, h1]
    omega

theorem eq_one_of_commute_swap {n : ℕ} (hn : n ≤ 6) {c σ : Equiv.Perm (Fin n)} (hσ : σ.IsSwap)
    (hcomm : c * σ = σ * c) (hc5 : c ^ 5 = 1) : c = 1 := by
  obtain ⟨x, y, hxy, rfl⟩ := hσ
  have hsw : ∀ z, Equiv.swap x y z ≠ z ↔ z = x ∨ z = y := by
    intro z
    constructor
    · intro h
      by_contra hz
      push Not at hz
      exact h (Equiv.swap_apply_of_ne_of_ne hz.1 hz.2)
    · rintro (rfl | rfl)
      · rw [Equiv.swap_apply_left]
        exact hxy.symm
      · rw [Equiv.swap_apply_right]
        exact hxy
  have hc : ∀ z, Equiv.swap x y (c z) = c (Equiv.swap x y z) := fun z => by
    have := congrArg (fun f : Equiv.Perm (Fin n) => f z) hcomm
    simpa using this.symm
  set B : Finset (Fin n) := {x, y} with hB
  have hinv : ∀ z, c z ∈ B ↔ z ∈ B := by
    intro z
    simp only [hB, Finset.mem_insert, Finset.mem_singleton]
    rw [← hsw, ← hsw, hc]
    exact c.injective.ne_iff
  have hBc : B.card = 2 := Finset.card_pair hxy
  have hfixB := perm_fix_of_invariant_small c hc5 B hinv (by omega)
  have hinvC : ∀ z, c z ∈ Bᶜ ↔ z ∈ Bᶜ := by
    intro z
    rw [Finset.mem_compl, Finset.mem_compl, hinv]
  have hCc : (Bᶜ).card ≤ 4 := by
    rw [Finset.card_compl, Fintype.card_fin, hBc]
    omega
  have hfixC := perm_fix_of_invariant_small c hc5 Bᶜ hinvC hCc
  refine Equiv.ext fun z => ?_
  by_cases hz : z ∈ B
  · exact hfixB z hz
  · exact hfixC z (Finset.mem_compl.mpr hz)

variable {G : Type} [Group G]

theorem card_eq_quot_mul_pCore (J : Subgroup G) :
    Nat.card ↥J = Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) * Nat.card ↥(CFSG.pCore 2 ↥J) :=
  Subgroup.card_eq_card_quotient_mul_card_subgroup _

theorem not_five_dvd_card_pCore [Finite G] (J : Subgroup G) :
    ¬ 5 ∣ Nat.card ↥(CFSG.pCore 2 ↥J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (isPGroup_pCore J).exists_card_eq
  rw [hk]
  intro h
  have h5 : 5 ∣ 2 := Nat.prime_five.dvd_of_dvd_pow h
  omega

theorem not_twentyfive_dvd_card [Finite G] (J : Subgroup G)
    (h : ¬ 25 ∣ Nat.card (↥J ⧸ CFSG.pCore 2 ↥J)) : ¬ 25 ∣ Nat.card ↥J := by
  intro h25
  rw [card_eq_quot_mul_pCore] at h25
  have hcop : Nat.Coprime 25 (Nat.card ↥(CFSG.pCore 2 ↥J)) := by
    have h5 := not_five_dvd_card_pCore J
    have : Nat.Coprime 5 (Nat.card ↥(CFSG.pCore 2 ↥J)) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h5
    simpa using Nat.Coprime.pow_left 2 this
  exact h (hcop.dvd_of_dvd_mul_right h25)

theorem not_five_dvd_card [Finite G] (J : Subgroup G)
    (h : ¬ 5 ∣ Nat.card (↥J ⧸ CFSG.pCore 2 ↥J)) : ¬ 5 ∣ Nat.card ↥J := by
  intro h5
  rw [card_eq_quot_mul_pCore] at h5
  rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h5 with h1 | h1
  · exact h h1
  · exact not_five_dvd_card_pCore J h1

theorem no_five_of_relIndex [Finite G] {K M : Subgroup G} (hidx : 5 ∣ M.relIndex K)
    (h25 : ¬ 25 ∣ Nat.card ↥K) {a : G} (haM : a ∈ M ⊓ K) (ha5 : orderOf a = 5) : False := by
  have hdvd : 5 ∣ Nat.card ↥(M ⊓ K) := by
    have := orderOf_dvd_natCard (⟨a, haM⟩ : ↥(M ⊓ K))
    rwa [Subgroup.orderOf_mk, ha5] at this
  apply h25
  rw [← Subgroup.relIndex_mul_card (H := M) (K := K)]
  have : 5 * 5 ∣ M.relIndex K * Nat.card ↥(M ⊓ K) := Nat.mul_dvd_mul hidx hdvd
  simpa using this

end SBc17

end CFSG.Quasithin

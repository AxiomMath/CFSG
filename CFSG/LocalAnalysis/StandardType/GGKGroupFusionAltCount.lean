module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltOrbit

public section

namespace CFSG.StandardType

open Equiv Equiv.Perm

section Count

variable {V : Type} [DecidableEq V] [Fintype V] {E : Subgroup (Perm V)} {p : ℕ}

open Classical in
theorem ggCard_eq_filter (H : Subgroup (Perm V)) :
    Nat.card H = (Finset.univ.filter (· ∈ H)).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

omit [DecidableEq V] [Fintype V] in
theorem ggCard_stab_cases (hp : p.Prime) (hEcard : Nat.card E = p ^ 2) (ω : V) :
    Nat.card (ggStab E ω) = 1 ∨ Nat.card (ggStab E ω) = p ∨ Nat.card (ggStab E ω) = p ^ 2 := by
  have h := ggCard_stab_dvd (E := E) ω
  rw [hEcard, Nat.dvd_prime_pow hp] at h
  obtain ⟨k, hk, hk'⟩ := h
  interval_cases k <;> simp_all

omit [DecidableEq V] in
theorem ggFixed_of_card_stab (hEcard : Nat.card E = p ^ 2) {ω : V}
    (h : Nat.card (ggStab E ω) = p ^ 2) : ∀ x ∈ E, x ω = ω := by
  have heq : ggStab E ω = E :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hEcard])
  intro x hx
  rw [← heq] at hx
  exact (ggMem_stab.mp hx).2

theorem ggCard_orb_of_stab (hp : p.Prime) (hEcard : Nat.card E = p ^ 2) {ω : V}
    (h : Nat.card (ggStab E ω) = p) : (ggOrb E ω).card = p := by
  have := ggCard_orb_mul_stab (E := E) ω
  rw [h, hEcard, sq] at this
  exact Nat.eq_of_mul_eq_mul_right hp.pos this

theorem ggInvariant_sdiff {S : Finset V} (hS : ∀ ω ∈ S, ggOrb E ω ⊆ S) (ω : V) :
    ∀ v ∈ S \ ggOrb E ω, ggOrb E v ⊆ S \ ggOrb E ω := by
  intro v hv w hw
  rw [Finset.mem_sdiff] at hv ⊢
  exact ⟨hS v hv.1 hw, fun hwω => hv.2 (ggOrb_trans hwω (ggOrb_symm hw))⟩

theorem ggDvd_card_of_invariant (hp : p.Prime) (hEcard : Nat.card E = p ^ 2)
    (hstab : ∀ ω, Nat.card (ggStab E ω) = p) :
    ∀ X : Finset V, (∀ ω ∈ X, ggOrb E ω ⊆ X) → p ∣ X.card := by
  intro X
  induction hX : X.card using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    intro hinv
    rcases X.eq_empty_or_nonempty with h | ⟨ω, hω⟩
    · rw [← hX, h, Finset.card_empty]
      exact dvd_zero p
    · have hsub := hinv ω hω
      have hcard : (X \ ggOrb E ω).card = n - p := by
        rw [Finset.card_sdiff_of_subset hsub, ggCard_orb_of_stab hp hEcard (hstab ω), hX]
      have hpn : p ≤ n := by
        rw [← hX, ← ggCard_orb_of_stab hp hEcard (hstab ω)]
        exact Finset.card_le_card hsub
      have h1 := ih (n - p) (by have := hp.pos; omega) (X \ ggOrb E ω) hcard
        (ggInvariant_sdiff hinv ω)
      have h2 : n = (n - p) + p := by omega
      rw [h2]
      exact Nat.dvd_add h1 (dvd_refl p)

theorem ggCard_ne_of_stab (hp : p.Prime) (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hEcard : Nat.card E = p ^ 2) (hstab : ∀ ω, Nat.card (ggStab E ω) = p) :
    Fintype.card V ≠ p := by
  intro hn
  have hne : Nonempty V := by
    rw [← Fintype.card_pos_iff, hn]
    exact hp.pos
  obtain ⟨ω⟩ := hne
  have huniv : ggOrb E ω = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [ggCard_orb_of_stab hp hEcard (hstab ω), hn])
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ ggStab E ω, x ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : ggStab E ω = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    have h1 := hstab ω
    rw [hbot, Subgroup.card_bot] at h1
    exact hp.one_lt.ne h1
  apply hx1
  ext v
  rw [Perm.one_apply]
  exact ggFix_orb_of_mem_stab hEab hx (huniv ▸ Finset.mem_univ v)

theorem ggExists_distinct_orbits (hp : p.Prime) (hEcard : Nat.card E = p ^ 2)
    (hstab : ∀ ω, Nat.card (ggStab E ω) = p) (k : ℕ) :
    ∀ S : Finset V, (∀ ω ∈ S, ggOrb E ω ⊆ S) → k * p < S.card →
      ∃ β : Fin (k + 1) → V, (∀ i, β i ∈ S) ∧ ∀ i i', β i' ∈ ggOrb E (β i) → i = i' := by
  induction k with
  | zero =>
    intro S _ hcard
    obtain ⟨ω, hω⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    exact ⟨fun _ => ω, fun _ => hω, fun i i' _ => Fin.ext (by omega)⟩
  | succ k ih =>
    intro S hS hcard
    obtain ⟨ω, hω⟩ : S.Nonempty := Finset.card_pos.mp (by
      have : 0 ≤ (k + 1) * p := Nat.zero_le _
      omega)
    have hcard' : k * p < (S \ ggOrb E ω).card := by
      rw [Finset.card_sdiff_of_subset (hS ω hω), ggCard_orb_of_stab hp hEcard (hstab ω)]
      have : (k + 1) * p = k * p + p := by ring
      omega
    obtain ⟨β', hβ'S, hβ'⟩ := ih (S \ ggOrb E ω) (ggInvariant_sdiff hS ω) hcard'
    refine ⟨Fin.cons ω β', fun i => ?_, fun i i' h => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hω
      · simpa using (Finset.mem_sdiff.mp (hβ'S j)).1
    · induction i using Fin.cases with
      | zero =>
        induction i' using Fin.cases with
        | zero => rfl
        | succ j =>
          exfalso
          exact (Finset.mem_sdiff.mp (hβ'S j)).2 (by simpa using h)
      | succ j =>
        induction i' using Fin.cases with
        | zero =>
          exfalso
          exact (Finset.mem_sdiff.mp (hβ'S j)).2 (ggOrb_symm (by simpa using h))
        | succ j' =>
          simp only [Fin.cons_succ] at h
          rw [hβ' j j' h]

open Classical in
theorem ggExists_large_support (hp : p.Prime) (hEcard : Nat.card E = p ^ 2)
    (hstab : ∀ ω, Nat.card (ggStab E ω) = p) (hn : p ^ 2 ≤ Fintype.card V) :
    ∃ x ∈ E, x ≠ 1 ∧ (p - 1) * p < (Finset.univ.filter fun v => x v ≠ v).card := by
  by_contra hcon
  push Not at hcon
  set EF : Finset (Perm V) := Finset.univ.filter (· ∈ E) with hEF
  have hEFcard : EF.card = p ^ 2 := by rw [← ggCard_eq_filter, hEcard]
  have hpt : ∀ v : V, (EF.filter fun x => x v ≠ v).card = p ^ 2 - p := by
    intro v
    have h1 : (EF.filter fun x => x v = v).card = p := by
      rw [← hstab v, ggCard_eq_filter]
      congr 1
      ext x
      simp [hEF, ggMem_stab]
    have h2 := Finset.card_filter_add_card_filter_not (s := EF) (fun x : Perm V => x v = v)
    rw [hEFcard, h1] at h2
    simp only [ne_eq]
    omega
  have hsum : ∑ x ∈ EF, (Finset.univ.filter fun v => x v ≠ v).card =
      Fintype.card V * (p ^ 2 - p) := by
    have h : ∑ x ∈ EF, (Finset.univ.filter fun v => x v ≠ v).card =
        ∑ v : V, (EF.filter fun x => x v ≠ v).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    rw [h, Finset.sum_congr rfl (fun v _ => hpt v), Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  have h1mem : (1 : Perm V) ∈ EF := by simp [hEF]
  have hle : ∑ x ∈ EF, (Finset.univ.filter fun v => x v ≠ v).card ≤
      (p ^ 2 - 1) * ((p - 1) * p) := by
    rw [← Finset.sum_erase_add _ _ h1mem]
    have h0 : (Finset.univ.filter fun v => (1 : Perm V) v ≠ v).card = 0 := by simp
    rw [h0, add_zero]
    have h2 : (EF.erase 1).card = p ^ 2 - 1 := by
      rw [Finset.card_erase_of_mem h1mem, hEFcard]
    calc ∑ x ∈ EF.erase 1, (Finset.univ.filter fun v => x v ≠ v).card
        ≤ ∑ _x ∈ EF.erase 1, (p - 1) * p := by
          refine Finset.sum_le_sum fun x hx => hcon x ?_ (Finset.ne_of_mem_erase hx)
          have := Finset.mem_of_mem_erase hx
          simpa [hEF] using this
      _ = (p ^ 2 - 1) * ((p - 1) * p) := by rw [Finset.sum_const, h2, smul_eq_mul]
  rw [hsum] at hle
  have hpp : p ^ 2 - p = (p - 1) * p := by rw [Nat.sub_mul, one_mul, sq]
  rw [hpp] at hle
  have hp2 := hp.two_le
  have hpos : 0 < (p - 1) * p := Nat.mul_pos (by omega) (by omega)
  have h3 : Fintype.card V ≤ p ^ 2 - 1 := Nat.le_of_mul_le_mul_right hle hpos
  have h4 : 0 < p ^ 2 := by positivity
  omega

end Count

end CFSG.StandardType

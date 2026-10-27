module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.Quasithin.H13.LocDbl.M24Prof

private theorem card_filter_fix_modEq_abelNine {α : Type*} [DecidableEq α] (σ : Equiv.Perm α)
    (s : Finset α) (hs : ∀ a, a ∈ s ↔ σ a ∈ s) (p : ℕ) [hp : Fact p.Prime] (hσ : σ ^ p = 1) :
    s.card ≡ (s.filter fun a => σ a = a).card [MOD p] := by
  let τ : Equiv.Perm {a // a ∈ s} := σ.subtypePerm fun a => (hs a).symm
  have hτ : τ ^ p = 1 := by
    simp only [τ, Equiv.Perm.subtypePerm_pow, hσ]
    rfl
  have h1 := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) (σ := τ)
    (by rw [pow_one]; exact hτ)
  have h2 : τ.supportᶜ.card = (s.filter fun a => σ a = a).card := by
    refine Finset.card_bij (fun x _ => (x : α)) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hx
      rw [Finset.mem_filter]
      refine ⟨x.2, ?_⟩
      have := congrArg Subtype.val hx
      simpa [τ] using this
    · intro x _ y _ h
      exact Subtype.ext h
    · intro a ha
      rw [Finset.mem_filter] at ha
      refine ⟨⟨a, ha.1⟩, ?_, rfl⟩
      rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
      apply Subtype.ext
      simpa [τ] using ha.2
  rw [h2, Fintype.card_coe] at h1
  exact h1.symm

theorem exists_fixing_element_of_abelian_nine {A Ω : Type*} [Group A] [Finite A] [MulAction A Ω]
    [DecidableEq Ω] (hA : Nat.card A = 9) (hcomm : ∀ a b : A, a * b = b * a) (𝔅 : Finset Ω)
    (h6 : 𝔅.card = 6) (hinv : ∀ a : A, ∀ b ∈ 𝔅, a • b ∈ 𝔅)
    (hfaith : ∀ a : A, (∀ b ∈ 𝔅, a • b = b) → a = 1) :
    ∃ x : A, x ≠ 1 ∧ x ^ 3 = 1 ∧ ∃ S : Finset Ω, S ⊆ 𝔅 ∧ S.card = 3 ∧
      (∀ b ∈ 𝔅, (x • b = b ↔ b ∈ S)) ∧ ∀ b ∈ S, ∀ b' ∈ S, ∃ a : A, a • b = b' := by
  obtain ⟨b0, hb0, a1, ha1⟩ : ∃ b0 ∈ 𝔅, ∃ a1 : A, a1 • b0 ≠ b0 := by
    by_contra hcon
    have hall : ∀ a : A, a = 1 := fun a =>
      hfaith a fun b hb => by
        by_contra hne
        exact hcon ⟨b, hb, a, hne⟩
    have h1 : Nat.card A = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
    omega
  have hOsub : MulAction.orbit A b0 ⊆ (𝔅 : Set Ω) := by
    intro c hc
    obtain ⟨a, rfl⟩ := MulAction.mem_orbit_iff.mp hc
    exact Finset.mem_coe.mpr (hinv a b0 hb0)
  have hOfin : (MulAction.orbit A b0).Finite := (Finset.finite_toSet 𝔅).subset hOsub
  obtain ⟨S0, hS0⟩ : ∃ S0 : Finset Ω, ∀ c, c ∈ S0 ↔ c ∈ MulAction.orbit A b0 :=
    ⟨hOfin.toFinset, fun c => hOfin.mem_toFinset⟩
  have hOS0 : MulAction.orbit A b0 = (S0 : Set Ω) := by
    ext c
    simp only [Finset.mem_coe]
    exact (hS0 c).symm
  have hncard : (MulAction.orbit A b0).ncard = S0.card := by
    rw [hOS0, Set.ncard_coe_finset]
  have hS0sub : S0 ⊆ 𝔅 := by
    intro c hc
    obtain ⟨a, rfl⟩ := MulAction.mem_orbit_iff.mp ((hS0 c).mp hc)
    exact hinv a b0 hb0
  have hb0orb : b0 ∈ MulAction.orbit A b0 := MulAction.mem_orbit_iff.mpr ⟨1, one_smul A b0⟩
  have ha1orb : a1 • b0 ∈ MulAction.orbit A b0 := MulAction.mem_orbit_iff.mpr ⟨a1, rfl⟩
  have hS0two : 1 < S0.card :=
    Finset.one_lt_card.mpr ⟨b0, (hS0 b0).mpr hb0orb, a1 • b0, (hS0 _).mpr ha1orb, ha1.symm⟩
  have hS0le : S0.card ≤ 6 := by
    have := Finset.card_le_card hS0sub
    omega
  have hmul : Nat.card (MulAction.stabilizer A b0) * S0.card = 9 := by
    have h1 := Subgroup.card_mul_index (H := MulAction.stabilizer A b0)
    rw [MulAction.index_stabilizer, hncard, hA] at h1
    exact h1
  have key : ∀ n m : ℕ, 2 ≤ n → n ≤ 6 → m * n = 9 → n = 3 ∧ m = 3 := by
    intro n m h1 h2 h3
    interval_cases n <;> omega
  obtain ⟨hS0three, hstab3⟩ := key S0.card _ (by omega) hS0le hmul
  haveI : Nontrivial (MulAction.stabilizer A b0) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hstab3]; norm_num)
  obtain ⟨x, hxH, hx1, hx3⟩ : ∃ x : A, x ∈ MulAction.stabilizer A b0 ∧ x ≠ 1 ∧ x ^ 3 = 1 := by
    obtain ⟨y, hy⟩ := exists_ne (1 : MulAction.stabilizer A b0)
    refine ⟨(y : A), y.2, fun h' => hy (Subtype.ext h'), ?_⟩
    have h3 : y ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥(MulAction.stabilizer A b0)) (x := y)
      rwa [hstab3] at this
    simpa using congrArg Subtype.val h3
  have hxb0 : x • b0 = b0 := MulAction.mem_stabilizer_iff.mp hxH
  have hfixO : ∀ a : A, x • a • b0 = a • b0 := by
    intro a
    rw [← mul_smul, ← hcomm, mul_smul, hxb0]
  have hS0fix : ∀ c ∈ S0, x • c = c := by
    intro c hc
    obtain ⟨a, rfl⟩ := MulAction.mem_orbit_iff.mp ((hS0 c).mp hc)
    exact hfixO a
  obtain ⟨S, hSdef⟩ : ∃ S : Finset Ω, S = 𝔅.filter (fun c => x • c = c) := ⟨_, rfl⟩
  have hmemS : ∀ c, c ∈ S ↔ c ∈ 𝔅 ∧ x • c = c := by
    intro c
    rw [hSdef, Finset.mem_filter]
  have hSsub : S ⊆ 𝔅 := by
    intro c hc
    exact ((hmemS c).mp hc).1
  have hS0S : S0 ⊆ S := by
    intro c hc
    exact (hmemS c).mpr ⟨hS0sub hc, hS0fix c hc⟩
  obtain ⟨σ, hσdef⟩ : ∃ σ : Equiv.Perm Ω, σ = MulAction.toPermHom A Ω x := ⟨_, rfl⟩
  have hσapp : ∀ c, σ c = x • c := fun c => by
    subst hσdef
    rfl
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσdef, ← map_pow, hx3, map_one]
  have hsσ : ∀ c, c ∈ 𝔅 ↔ σ c ∈ 𝔅 := by
    intro c
    rw [hσapp c]
    constructor
    · intro hc
      exact hinv x c hc
    · intro hc
      have := hinv x⁻¹ _ hc
      rwa [inv_smul_smul] at this
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := card_filter_fix_modEq_abelNine σ 𝔅 hsσ 3 hσ3
  have hfilt : 𝔅.filter (fun c => σ c = c) = S := by
    rw [hSdef]
    exact Finset.filter_congr fun c _ => by rw [hσapp c]
  rw [hfilt, h6] at hmod
  unfold Nat.ModEq at hmod
  have hSle : S.card ≤ 6 := by
    have := Finset.card_le_card hSsub
    omega
  have hSge : 3 ≤ S.card := by
    have := Finset.card_le_card hS0S
    omega
  have hSc : S.card = 3 := by
    rcases (by omega : S.card = 3 ∨ S.card = 6) with h | h
    · exact h
    · exfalso
      have hSeq : S = 𝔅 := Finset.eq_of_subset_of_card_le hSsub (by omega)
      have hfixall : ∀ c ∈ 𝔅, x • c = c := fun c hc =>
        ((hmemS c).mp (by rw [hSeq]; exact hc)).2
      exact hx1 (hfaith x hfixall)
  have hSS0 : ∀ c ∈ S, c ∈ S0 := by
    have hEq : S0 = S := Finset.eq_of_subset_of_card_le hS0S (by omega)
    intro c hc
    rw [hEq]
    exact hc
  have htrans : ∀ b ∈ S, ∀ b' ∈ S, ∃ a : A, a • b = b' := by
    intro b hb b' hb'
    obtain ⟨a, rfl⟩ := MulAction.mem_orbit_iff.mp ((hS0 b).mp (hSS0 b hb))
    obtain ⟨a', rfl⟩ := MulAction.mem_orbit_iff.mp ((hS0 b').mp (hSS0 b' hb'))
    exact ⟨a' * a⁻¹, by rw [← mul_smul, inv_mul_cancel_right]⟩
  exact ⟨x, hx1, hx3, S, hSsub, hSc,
    fun b hb => ⟨fun hfix => (hmemS b).mpr ⟨hb, hfix⟩, fun hbS => ((hmemS b).mp hbS).2⟩, htrans⟩

end CFSG.Quasithin.H13.LocDbl.M24Prof

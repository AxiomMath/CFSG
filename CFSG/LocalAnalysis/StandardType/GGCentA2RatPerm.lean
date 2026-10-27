module

public import Mathlib.Order.Lattice.Nat
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.StandardType.NTPlane

private lemma ntpA2rat_iterate_image {X I : Type*} (ρ : Equiv.Perm X) (Ψ : I → Set X)
    (ρb : Equiv.Perm I) (hρb : ∀ i, ⇑ρ '' Ψ i = Ψ (ρb i)) (k : ℕ) (j : I) :
    (⇑ρ)^[k] '' Ψ j = Ψ ((⇑ρb)^[k] j) := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Set.image_comp, ih, hρb]
    congr 1
    rw [Function.iterate_succ_apply']

theorem ntpA2rat_orbitUnion_eq_iUnion {X I : Type*} (hI : Nat.card I = 3)
    (ρ : Equiv.Perm X) (Ψ : I → Set X) (hΨ : Function.Injective Ψ) (ρb : Equiv.Perm I)
    (hρb : ∀ i, ⇑ρ '' Ψ i = Ψ (ρb i))
    (horb : ∀ i, sInf {s : ℕ | 0 < s ∧ (⇑ρ)^[s] '' Ψ i = Ψ i} = 3) (i : I) :
    {γ | ∃ (k : ℕ) (δ : X), δ ∈ Ψ i ∧ γ = (⇑ρ)^[k] δ} = ⋃ j, Ψ j := by
  classical
  have hfin : Finite I := Nat.finite_of_card_ne_zero (by rw [hI]; exact Nat.succ_ne_zero 2)
  letI := Fintype.ofFinite I
  have hcard : Fintype.card I = 3 := by
    rw [← Nat.card_eq_fintype_card, hI]
  have hP1 : ¬ (1 ∈ {s : ℕ | 0 < s ∧ (⇑ρ)^[s] '' Ψ i = Ψ i}) := by
    intro hmem
    have hle := Nat.sInf_le hmem
    have h3 := horb i
    omega
  have hP2 : ¬ (2 ∈ {s : ℕ | 0 < s ∧ (⇑ρ)^[s] '' Ψ i = Ψ i}) := by
    intro hmem
    have hle := Nat.sInf_le hmem
    have h3 := horb i
    omega
  have hne1 : ρb i ≠ i := by
    intro h
    apply hP1
    refine ⟨by decide, ?_⟩
    simpa [h] using hρb i
  have hne2 : ρb (ρb i) ≠ i := by
    intro h
    apply hP2
    refine ⟨by decide, ?_⟩
    have h2 : (⇑ρb)^[2] i = i := by
      simpa [Function.iterate_succ_apply'] using h
    rw [ntpA2rat_iterate_image ρ Ψ ρb hρb 2 i, h2]
  let t : Finset I := {i, ρb i, ρb (ρb i)}
  have hcard3 : t.card = 3 := by
    rw [Finset.card_eq_three]
    refine ⟨i, ρb i, ρb (ρb i), ?_, ?_, ?_, rfl⟩
    · exact fun h => hne1 h.symm
    · exact fun h => hne2 h.symm
    · intro h
      exact hne1 (ρb.injective h).symm
  have htuniv : t = Finset.univ :=
    Finset.eq_univ_of_card t (hcard3.trans hcard.symm)
  have hL : {γ | ∃ (k : ℕ) (δ : X), δ ∈ Ψ i ∧ γ = (⇑ρ)^[k] δ}
      = ⋃ k : ℕ, (⇑ρ)^[k] '' Ψ i := by
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨k, δ, hδ, rfl⟩
      exact ⟨k, δ, hδ, rfl⟩
    · rintro ⟨k, δ, hδ, rfl⟩
      exact ⟨k, δ, hδ, rfl⟩
  calc
    {γ | ∃ (k : ℕ) (δ : X), δ ∈ Ψ i ∧ γ = (⇑ρ)^[k] δ}
        = ⋃ k : ℕ, (⇑ρ)^[k] '' Ψ i := hL
    _ = ⋃ k : ℕ, Ψ ((⇑ρb)^[k] i) := by
      simp_rw [ntpA2rat_iterate_image ρ Ψ ρb hρb]
    _ = ⋃ j, Ψ j := by
      ext γ
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨(⇑ρb)^[k] i, hk⟩
      · rintro ⟨j, hj⟩
        have hjmem : j ∈ t := htuniv ▸ Finset.mem_univ j
        simp only [t, Finset.mem_insert, Finset.mem_singleton] at hjmem
        rcases hjmem with rfl | rfl | rfl
        · exact ⟨0, by simpa using hj⟩
        · exact ⟨1, by simpa using hj⟩
        · exact ⟨2, by simpa using hj⟩

end CFSG.StandardType.NTPlane

end

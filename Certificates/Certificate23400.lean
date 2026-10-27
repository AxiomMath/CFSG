module

public import Certificates.Data.CatLeafProofQ81P2A7
import Mathlib.GroupTheory.Perm.Cycle.Type

public section

open CFSG.ComponentClassification.HarrisLit.L33.A7Data Equiv

namespace CertificateChecks.Batch23400

open CFSG.ComponentClassification.HarrisLit.L33.A7Data Equiv

def rep1 : Perm (Fin 7) := swap 0 1

def rep2 : Perm (Fin 7) := swap 0 1 * swap 2 3

def rep3 : Perm (Fin 7) := swap 0 1 * swap 2 3 * swap 4 5

def c3 (a b c : Fin 7) : Perm (Fin 7) := swap a c * swap a b

def cubes1 : List (Perm (Fin 7)) :=
  1 :: ([(2, 3, 4), (2, 3, 5), (2, 3, 6), (2, 4, 5), (2, 4, 6), (2, 5, 6), (3, 4, 5), (3, 4, 6),
    (3, 5, 6), (4, 5, 6)] : List (Fin 7 × Fin 7 × Fin 7)).flatMap fun t =>
      [c3 t.1 t.2.1 t.2.2, c3 t.1 t.2.2 t.2.1]

def cubes2 : List (Perm (Fin 7)) := [1, c3 4 5 6, c3 4 6 5]

def cubes3 : List (Perm (Fin 7)) :=
  [1, c3 0 2 4 * c3 1 3 5, c3 0 2 5 * c3 1 3 4, c3 0 3 4 * c3 1 2 5, c3 0 3 5 * c3 1 2 4,
    c3 0 4 2 * c3 1 5 3, c3 0 5 2 * c3 1 4 3, c3 0 4 3 * c3 1 5 2, c3 0 5 3 * c3 1 4 2]

def PairL (S : List (Perm (Fin 7))) : Prop :=
  ∀ g ∈ S, ∀ h ∈ S, g ≠ 1 → g * h = h * g → h = 1 ∨ h = g ∨ h = g * g

instance (S : List (Perm (Fin 7))) : Decidable (PairL S) :=
  inferInstanceAs (Decidable (∀ g ∈ S, ∀ h ∈ S, g ≠ 1 → g * h = h * g →
    h = 1 ∨ h = g ∨ h = g * g))

def SubOK (g : Perm (Fin 7)) : Prop :=
  (g * rep1 = rep1 * g → g * g * g = 1 → g ∈ cubes1) ∧
    (g * rep2 = rep2 * g → g * g * g = 1 → g ∈ cubes2) ∧
      (g * rep3 = rep3 * g → g * g * g = 1 → g ∈ cubes3)

instance (g : Perm (Fin 7)) : Decidable (SubOK g) :=
  inferInstanceAs (Decidable ((g * rep1 = rep1 * g → g * g * g = 1 → g ∈ cubes1) ∧
    (g * rep2 = rep2 * g → g * g * g = 1 → g ∈ cubes2) ∧
      (g * rep3 = rep3 * g → g * g * g = 1 → g ∈ cubes3)))

set_option maxRecDepth 100000 in
theorem cubes_sub : ∀ g : Perm (Fin 7), SubOK g := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pairOK_lists : PairL cubes1 ∧ PairL cubes2 ∧ PairL cubes3 := by
  decide +kernel

theorem mem_cubeCent {π g : Perm (Fin 7)} : g ∈ cubeCent π ↔ g ^ 3 = 1 ∧ g * π = π * g := by
  simp [cubeCent, cubes, Finset.mem_filter]

theorem pairOK_of_sub {r : Perm (Fin 7)} {S : List (Perm (Fin 7))}
    (hS : ∀ g : Perm (Fin 7), g ^ 3 = 1 → g * r = r * g → g ∈ S) (hP : PairL S) :
    pairOK (cubeCent r) := by
  intro g hg h hh
  rw [mem_cubeCent] at hg hh
  exact hP g (hS g hg.1 hg.2) h (hS h hh.1 hh.2)

private theorem a7_e9_reps_check :
    pairOK (cubeCent rep1) ∧ pairOK (cubeCent rep2) ∧ pairOK (cubeCent rep3) := by
  obtain ⟨p1, p2, p3⟩ := pairOK_lists
  have h3 : ∀ g : Perm (Fin 7), g ^ 3 = 1 → g * g * g = 1 := fun g h => by rwa [← pow_three']
  exact ⟨pairOK_of_sub (fun g hg hc => (cubes_sub g).1 hc (h3 g hg)) p1,
    pairOK_of_sub (fun g hg hc => (cubes_sub g).2.1 hc (h3 g hg)) p2,
    pairOK_of_sub (fun g hg hc => (cubes_sub g).2.2 hc (h3 g hg)) p3⟩

private theorem cycleType_swap' {a b : Fin 7} (h : a ≠ b) : (swap a b).cycleType = {2} := by
  rw [(Perm.isCycle_swap h).cycleType, Perm.card_support_swap h]

private theorem reps_cycleType :
    rep1.cycleType = Multiset.replicate 1 2 ∧ rep2.cycleType = Multiset.replicate 2 2 ∧
      rep3.cycleType = Multiset.replicate 3 2 := by
  have d12 : Perm.Disjoint (swap (0 : Fin 7) 1) (swap 2 3) := by
    unfold Perm.Disjoint
    decide +kernel
  have d3 : Perm.Disjoint (swap (0 : Fin 7) 1 * swap 2 3) (swap 4 5) := by
    unfold Perm.Disjoint
    decide +kernel
  have s01 := cycleType_swap' (a := (0 : Fin 7)) (b := 1) (by decide)
  have s23 := cycleType_swap' (a := (2 : Fin 7)) (b := 3) (by decide)
  have s45 := cycleType_swap' (a := (4 : Fin 7)) (b := 5) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [rep1, s01]
    rfl
  · rw [rep2, Perm.Disjoint.cycleType_mul d12, s01, s23]
    rfl
  · rw [rep3, Perm.Disjoint.cycleType_mul d3, Perm.Disjoint.cycleType_mul d12, s01, s23, s45]
    rfl

theorem pairOK_cubeCent_conj (σ π : Perm (Fin 7)) (h : pairOK (cubeCent π)) :
    pairOK (cubeCent (σ * π * σ⁻¹)) := by
  set c := MulAut.conj σ⁻¹ with hc
  have hπ : c (σ * π * σ⁻¹) = π := by
    rw [hc, MulAut.conj_apply]
    group
  have hmem : ∀ x, x ∈ cubeCent (σ * π * σ⁻¹) → c x ∈ cubeCent π := by
    intro x hx
    rw [mem_cubeCent] at hx ⊢
    refine ⟨by rw [← map_pow, hx.1, map_one], ?_⟩
    rw [← hπ, ← map_mul, ← map_mul, hx.2]
  intro g hg k hk hg1 hgk
  have hg1' : c g ≠ 1 := fun h1 => hg1 (c.injective (h1.trans (map_one c).symm))
  have hgk' : c g * c k = c k * c g := by rw [← map_mul, ← map_mul, hgk]
  rcases h (c g) (hmem g hg) (c k) (hmem k hk) hg1' hgk' with h1 | h1 | h1
  · exact Or.inl (c.injective (h1.trans (map_one c).symm))
  · exact Or.inr (Or.inl (c.injective h1))
  · exact Or.inr (Or.inr (c.injective (h1.trans (map_mul c g g).symm)))

theorem exists_conj_rep (π : Perm (Fin 7)) (h1 : π * π = 1) (h2 : π ≠ 1) :
    ∃ σ : Perm (Fin 7), ∃ r ∈ [rep1, rep2, rep3], π = σ * r * σ⁻¹ := by
  have ho : orderOf π = 2 := orderOf_eq_prime (by rw [sq]; exact h1) h2
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (σ := π) (by rw [ho]; exact Nat.prime_two)
  rw [ho] at hn
  have hle := Perm.sum_cycleType_le π
  rw [hn, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hle
  obtain ⟨c1, c2, c3⟩ := reps_cycleType
  have key : ∀ r : Perm (Fin 7), r ∈ [rep1, rep2, rep3] → r.cycleType = π.cycleType →
      ∃ σ : Perm (Fin 7), ∃ r ∈ [rep1, rep2, rep3], π = σ * r * σ⁻¹ := by
    intro r hr hcr
    obtain ⟨σ, hσ⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr hcr)
    exact ⟨σ, r, hr, hσ.symm⟩
  obtain rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  · exact key rep1 (by simp) (c1.trans hn.symm)
  · exact key rep2 (by simp) (c2.trans hn.symm)
  · exact key rep3 (by simp) (c3.trans hn.symm)

private theorem a7_e9_check_0 : a7E9 := by
  intro π h1 h2
  obtain ⟨σ, r, hr, rfl⟩ := exists_conj_rep π h1 h2
  obtain ⟨c1, c2, c3⟩ := a7_e9_reps_check
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact pairOK_cubeCent_conj σ _ c1
  · exact pairOK_cubeCent_conj σ _ c2
  · exact pairOK_cubeCent_conj σ _ c3

end CertificateChecks.Batch23400

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.HarrisLit.L33.A7Data in
theorem certificate23400 : a7E9 := by
  exact CertificateChecks.Batch23400.a7_e9_check_0

end Certificates

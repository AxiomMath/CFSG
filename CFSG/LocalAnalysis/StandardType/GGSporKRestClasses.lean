module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestCoverSpec

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

theorem sporKRest_cover_of_classes {K : Type} [Group K] {p : ℕ} (hp : p.Prime) (reps : List K)
    (hcomplete : ∀ s : K, orderOf s = p → ∃ r ∈ reps, IsConj r s)
    (hgen : ∀ r ∈ reps, ∀ x : K, IsConj r x → SporKRestGenerating p x) : SporKRestCover p K := by
  intro E hE hcard
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  have hlt : 1 < Nat.card E := by
    rw [hcard]
    nlinarith [hp.two_le]
  have hbot : E ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot E).mp hlt
  haveI : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).mpr hbot
  obtain ⟨x, hxE, hx1⟩ := Subgroup.exists_ne_one_of_nontrivial E
  have hpow : x ^ p = 1 := hE.2 x hxE
  have hord : orderOf x = p := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hpow) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact h1
  obtain ⟨r, hr, hrx⟩ := hcomplete x hord
  exact ⟨x, hxE, hx1, hgen r hr x hrx⟩

theorem sporKRest_generating_of_pgroup {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (a b : K) (hab : Subgroup.closure ({a, b} : Set K) = ⊤)
    (S₀ : Subgroup K) (hS₀ : IsPGroup p S₀) (sg : List K) (hS : S₀ = Subgroup.closure {g | g ∈ sg})
    (x₀ : K) (ent : List (K × K × List K))
    (hent : ∀ e ∈ ent, e.1 ∈ S₀ ∧ e.2.1⁻¹ * x₀ * e.2.1 = e.1 ∧ ∀ z ∈ e.2.2, z * e.1 = e.1 * z)
    (wa wb : List ℤ) (ha : sporKRestEval (sg ++ ent.flatMap fun e => e.2.2) wa = a)
    (hb : sporKRestEval (sg ++ ent.flatMap fun e => e.2.2) wb = b)
    {x : K} (hx : IsConj x₀ x) : SporKRestGenerating p x := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hSS⟩ := hS₀.exists_le_sylow
  refine ggSporKRest_generating_of_closure hp S hx
    {z : K | z ∈ ent.flatMap fun e => e.2.2} ?_ ?_
  · intro z hz
    rw [Set.mem_setOf_eq, List.mem_flatMap] at hz
    obtain ⟨e, he, hze⟩ := hz
    obtain ⟨he1S, he2, hzcent⟩ := hent e he
    exact ⟨e.2.1, e.1, hSS he1S, he2,
      (Subgroup.mem_centralizer_singleton_iff).mpr (hzcent z hze)⟩
  · set L : Subgroup K :=
      Subgroup.closure ((S : Set K) ∪ {z : K | z ∈ ent.flatMap fun e => e.2.2}) with hL
    have hSL : (S : Subgroup K) ≤ L := by
      rw [hL]
      intro y hy
      exact Subgroup.subset_closure (Set.mem_union_left _ hy)
    have hTL : ∀ z ∈ ent.flatMap (fun e => e.2.2), z ∈ L := by
      intro z hz
      rw [hL]
      exact Subgroup.subset_closure (Set.mem_union_right _ hz)
    rw [eq_top_iff, ← hab]
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    have hmem : ∀ g ∈ sg ++ ent.flatMap (fun e => e.2.2), g ∈ L := by
      intro g hg
      rw [List.mem_append] at hg
      rcases hg with hgsg | hgflat
      · apply hSL
        apply hSS
        rw [hS]
        exact Subgroup.subset_closure hgsg
      · exact hTL g hgflat
    rcases hz with rfl | rfl
    · have h := sporKRestEval_mem (sg ++ ent.flatMap fun e => e.2.2) wa L hmem
      simpa [ha] using h
    · have h := sporKRestEval_mem (sg ++ ent.flatMap fun e => e.2.2) wb L hmem
      simpa [hb] using h

end CFSG.StandardType.SporadicShape

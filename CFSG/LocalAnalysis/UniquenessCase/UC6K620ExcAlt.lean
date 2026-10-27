module

public import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

section Cycles

variable {m : ℕ}

theorem exists_isThreeCycle_commute {σ : Perm (Fin m)} (h1 : σ ≠ 1) (h3 : σ ^ 3 = 1) :
    ∃ c : Perm (Fin m), c.IsThreeCycle ∧ Commute c σ := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h
    push Not at h
    exact h1 (Equiv.ext fun a => by rw [Perm.one_apply]; exact h a)
  have hmem : σ.cycleOf a ∈ σ.cycleFactorsFinset :=
    cycleOf_mem_cycleFactorsFinset_iff.2 (mem_support.2 ha)
  have hcyc : (σ.cycleOf a).IsCycle := isCycle_cycleOf σ ha
  have hdvd : orderOf (σ.cycleOf a) ∣ 3 :=
    (orderOf_cycleOf_dvd_orderOf σ a).trans (orderOf_dvd_of_pow_eq_one h3)
  have hne : orderOf (σ.cycleOf a) ≠ 1 := by
    intro h
    rw [orderOf_eq_one_iff] at h
    exact hcyc.ne_one h
  have h3' : orderOf (σ.cycleOf a) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd h hne
    · exact h
  refine ⟨σ.cycleOf a, ?_, self_mem_cycle_factors_commute hmem⟩
  rw [← card_support_eq_three_iff, ← hcyc.orderOf]
  exact h3'

theorem exists_isThreeCycle_disjoint (hm : 9 ≤ m) {c c' : Perm (Fin m)} (hc : c.IsThreeCycle)
    (hc' : c'.IsThreeCycle) :
    ∃ d : Perm (Fin m), d.IsThreeCycle ∧ Disjoint d c ∧ Disjoint d c' := by
  classical
  have hscard : (c.support ∪ c'.support).card ≤ 6 := by
    calc (c.support ∪ c'.support).card ≤ c.support.card + c'.support.card :=
          Finset.card_union_le _ _
      _ = 6 := by rw [hc.card_support, hc'.card_support]
  have hcompl : 3 ≤ (c.support ∪ c'.support)ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hcompl
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 htcard
  have key : ∀ e : Perm (Fin m), (∀ u ∈ ({x, y, z} : Finset (Fin m)), e u = u) →
      Disjoint (swap x y * swap x z) e := by
    intro e he u
    by_cases hu : u = x ∨ u = y ∨ u = z
    · right
      apply he
      rcases hu with rfl | rfl | rfl <;> simp
    · left
      push Not at hu
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hu.1 hu.2.2, swap_apply_of_ne_of_ne hu.1 hu.2.1]
  have hfix : ∀ u ∈ ({x, y, z} : Finset (Fin m)), c u = u ∧ c' u = u := by
    intro u hu
    have h := hts hu
    rw [Finset.mem_compl, Finset.mem_union] at h
    push Not at h
    exact ⟨notMem_support.1 h.1, notMem_support.1 h.2⟩
  exact ⟨swap x y * swap x z, isThreeCycle_swap_mul_swap_same hxy hxz hyz,
    key c fun u hu => (hfix u hu).1, key c' fun u hu => (hfix u hu).2⟩

end Cycles

section Main

theorem eq_top_of_centralizer_le_alt {m : ℕ} (hm : 9 ≤ m) (N : Subgroup (alternatingGroup (Fin m)))
    (hC : ∀ y ∈ N, y ≠ 1 → y ^ 3 = 1 →
      Subgroup.centralizer ({y} : Set (alternatingGroup (Fin m))) ≤ N)
    (hN3 : 3 ∣ Nat.card N) : N = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' (G := N) 3 hN3
  have hy1 : (y₀ : alternatingGroup (Fin m)) ≠ 1 := by
    intro h
    have : y₀ = 1 := Subtype.ext h
    rw [this, orderOf_one] at hy₀
    exact absurd hy₀ (by norm_num)
  have hy3 : (y₀ : alternatingGroup (Fin m)) ^ 3 = 1 := by
    have := pow_orderOf_eq_one y₀
    rw [hy₀] at this
    exact congrArg Subtype.val this
  have hσ1 : (((y₀ : alternatingGroup (Fin m)) : Perm (Fin m))) ≠ 1 := fun h =>
    hy1 (Subtype.ext h)
  have hσ3 : (((y₀ : alternatingGroup (Fin m)) : Perm (Fin m))) ^ 3 = 1 := by
    have := congrArg Subtype.val hy3
    simpa using this
  obtain ⟨c₀, hc₀, hc₀comm⟩ := exists_isThreeCycle_commute hσ1 hσ3
  have hne : ∀ (c : Perm (Fin m)) (hc : c.IsThreeCycle),
      (⟨c, hc.mem_alternatingGroup⟩ : alternatingGroup (Fin m)) ≠ 1 := by
    intro c hc h
    have h1 : c = 1 := congrArg Subtype.val h
    have := hc.orderOf
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hpow : ∀ (c : Perm (Fin m)) (hc : c.IsThreeCycle),
      (⟨c, hc.mem_alternatingGroup⟩ : alternatingGroup (Fin m)) ^ 3 = 1 := by
    intro c hc
    apply Subtype.ext
    have := pow_orderOf_eq_one c
    rwa [hc.orderOf] at this
  have hc₀N : (⟨c₀, hc₀.mem_alternatingGroup⟩ : alternatingGroup (Fin m)) ∈ N := by
    refine hC _ y₀.2 hy1 hy3 ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    apply Subtype.ext
    exact hc₀comm.symm.eq
  have hall : ∀ c' : Perm (Fin m), ∀ hc' : c'.IsThreeCycle,
      (⟨c', hc'.mem_alternatingGroup⟩ : alternatingGroup (Fin m)) ∈ N := by
    intro c' hc'
    obtain ⟨d, hd, hdc₀, hdc'⟩ := exists_isThreeCycle_disjoint hm hc₀ hc'
    have hdN : (⟨d, hd.mem_alternatingGroup⟩ : alternatingGroup (Fin m)) ∈ N := by
      refine hC _ hc₀N (hne c₀ hc₀) (hpow c₀ hc₀) ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      apply Subtype.ext
      exact hdc₀.commute.symm.eq
    refine hC _ hdN (hne d hd) (hpow d hd) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    apply Subtype.ext
    exact hdc'.commute.eq
  have hclos : alternatingGroup (Fin m) ≤ N.map (alternatingGroup (Fin m)).subtype := by
    calc alternatingGroup (Fin m) = Subgroup.closure {σ : Perm (Fin m) | IsThreeCycle σ} :=
          closure_three_cycles_eq_alternating.symm
      _ ≤ N.map (alternatingGroup (Fin m)).subtype := by
          rw [Subgroup.closure_le]
          intro c hc
          exact ⟨_, hall c hc, rfl⟩
  rw [eq_top_iff]
  intro z _
  obtain ⟨w, hw, hwz⟩ := hclos z.2
  have : w = z := Subtype.ext hwz
  exact this ▸ hw

theorem not_isStronglyPEmbedded_three_of_alt {X : Type} [Group X] [Finite X] {m : ℕ} (hm : 9 ≤ m)
    (e : X ≃* alternatingGroup (Fin m)) (N : Subgroup X) : ¬ IsStronglyPEmbedded 3 N := by
  intro hN
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine hN.1 ?_
  have hmap : N.map e.toMonoidHom = ⊤ := by
    refine eq_top_of_centralizer_le_alt hm _ ?_ ?_
    · intro y hy hy1 hy3 z hz
      obtain ⟨y', hy', rfl⟩ := hy
      have hy'1 : y' ≠ 1 := by
        rintro rfl
        exact hy1 (map_one _)
      have hy'3 : y' ^ 3 = 1 := by
        apply e.injective
        rw [map_pow, map_one]
        exact hy3
      have hcent := hN.centralizer_le hy'1 hy'3 hy'
      have hz' : e.symm z ∈ Subgroup.centralizer ({y'} : Set X) := by
        rw [Subgroup.mem_centralizer_iff] at hz ⊢
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hz _ rfl
      refine ⟨e.symm z, hcent hz', ?_⟩
      simp
    · rw [Subgroup.card_map_of_injective e.injective]
      exact hN.2.1
  rw [eq_top_iff]
  intro x _
  have hx : e x ∈ N.map e.toMonoidHom := hmap ▸ Subgroup.mem_top _
  obtain ⟨x', hx', hxx⟩ := hx
  exact (e.injective hxx) ▸ hx'

end Main

end CFSG.LocalAnalysis.UniquenessCase.UCK

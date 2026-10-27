module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open TauCeti

section Generic

variable {P : GroupPresentation} {G : Type*} [Group G]

noncomputable def presGen (e : G ≃* P.Group) (i : Fin P.generatorCount) : G :=
  e.symm (PresentedGroup.of i)

theorem lift_presGen_eq_one (e : G ≃* P.Group) :
    ∀ t ∈ P.transcribed, FreeGroup.lift (presGen e) t.toFreeGroup = 1 := by
  intro t ht
  have hlift : FreeGroup.lift (presGen e) =
      e.symm.toMonoidHom.comp (PresentedGroup.mk P.relatorSet) := by
    ext i
    simp only [FreeGroup.lift_apply_of]
    rfl
  have hmem : t.toFreeGroup ∈ P.relatorSet := (P.mem_relatorSet_iff _).2 ⟨t, ht, rfl⟩
  rw [hlift, MonoidHom.comp_apply, PresentedGroup.mk_eq_one_iff.2
    (Subgroup.subset_normalClosure hmem), map_one]

theorem closure_range_presGen (e : G ≃* P.Group) :
    Subgroup.closure (Set.range (presGen e)) = ⊤ := by
  have h := PresentedGroup.closure_range_of P.relatorSet
  have hmap := congrArg (Subgroup.map e.symm.toMonoidHom) h
  rw [MonoidHom.map_closure, ← Set.range_comp, Subgroup.map_top_of_surjective _
    e.symm.surjective] at hmap
  exact hmap

end Generic

section Abelian

variable {G : Type*} [Group G]

theorem commute_of_closure_range_eq_top {ι : Type*} {x : ι → G}
    (hx : Subgroup.closure (Set.range x) = ⊤) (h : ∀ i j, Commute (x i) (x j)) (g k : G) :
    Commute g k := by
  have hS : Subgroup.closure (Set.range x) ≤ Subgroup.centralizer (Set.range x) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ ⟨j, rfl⟩
    exact (h j i).eq
  rw [hx] at hS
  have hg := Subgroup.mem_centralizer_iff.1 (hS (Subgroup.mem_top g))
  have hT : Subgroup.closure (Set.range x) ≤ Subgroup.centralizer {g} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact (hg _ ⟨i, rfl⟩).symm
  rw [hx] at hT
  exact (Subgroup.mem_centralizer_iff.1 (hT (Subgroup.mem_top k)) g rfl)

theorem eq_one_of_pow_three_eq_one [Finite G] (h3 : ¬ 3 ∣ Nat.card G) {g : G}
    (hg : g ^ 3 = 1) : g = 1 := by
  have hd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ orderOf_dvd_natCard g) h3

theorem pow_eq_one_of_pow_three_mul_eq_one [Finite G] (h3 : ¬ 3 ∣ Nat.card G) {g : G} {k : ℕ}
    (hg : g ^ (3 * k) = 1) : g ^ k = 1 :=
  eq_one_of_pow_three_eq_one h3 (by rw [← pow_mul, mul_comm, hg])

theorem eq_one_of_forall_commute [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {z : G}
    (hz : ∀ g, Commute z g) : z = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · have : z ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun g => (hz g).eq.symm
    rwa [h, Subgroup.mem_bot] at this
  · obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center G := h ▸ Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.1 ha b).symm hab

theorem commute_of_forall_commute_gen {ι : Type*} {x : ι → G}
    (hx : Subgroup.closure (Set.range x) = ⊤) {z : G} (hz : ∀ i, Commute z (x i)) (g : G) :
    Commute z g := by
  have hle : Subgroup.closure (Set.range x) ≤ Subgroup.centralizer {z} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact (hz i).eq
  rw [hx] at hle
  exact Subgroup.mem_centralizer_iff.1 (hle (Subgroup.mem_top g)) z rfl

end Abelian

@[expose] def SporThreeDvd (s : SporadicName) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Nonempty (G ≃* s.Group) → 3 ∣ Nat.card G

theorem sporThreeDvd_of_commute (s : SporadicName)
    (h : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      ¬ 3 ∣ Nat.card G → ∀ e : G ≃* s.presentation.Group, ∀ i j,
        Commute (presGen e i) (presGen e j)) :
    SporThreeDvd s := by
  intro G _ _ _ hnab ⟨e⟩
  by_contra h3
  obtain ⟨a, b, hab⟩ := hnab
  exact hab (commute_of_closure_range_eq_top (closure_range_presGen e)
    (h G ⟨a, b, hab⟩ h3 e) a b)

theorem commute_of_mem_zpowers {G : Type*} [Group G] {g x y : G} (hx : x ∈ Subgroup.zpowers g)
    (hy : y ∈ Subgroup.zpowers g) : Commute x y := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  exact Commute.zpow_zpow_self g m n

end CFSG.RankThree.PartTwo.KFacts.KS14

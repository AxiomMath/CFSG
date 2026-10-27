module

public import CFSG.LieType.Multipliers.CoverWords

public section

namespace CFSG.Sporadic.Recognition.CoverIndex

open CFSG.CosetTable CFSG.LieType.Multipliers

theorem exists_hom_genSub {m : ℕ} (ws : List (List (Fin m × Bool))) (S : List (Fin m)) :
    ∃ φ : PG S.length (restrictWords S ws) →*
      PresentedGroup {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk},
      φ.range = genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} S := by
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  have hrel : ∀ r ∈ {r : FreeGroup (Fin S.length) | r ∈ (restrictWords S ws).map FreeGroup.mk},
      FreeGroup.lift (fun j => (PresentedGroup.of (S.get j) : PresentedGroup rels)) r = 1 := by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map, restrictWords, List.mem_filterMap] at hr
    obtain ⟨w', ⟨w, hw, hren⟩, rfl⟩ := hr
    have hmap : FreeGroup.lift (fun j => (PresentedGroup.of (S.get j) : PresentedGroup rels))
        (FreeGroup.mk w') = PresentedGroup.mk rels (FreeGroup.mk w) := by
      rw [← map_renumber S w w' hren]
      clear hren hw
      induction w' with
      | nil => rfl
      | cons l w' ih =>
        rw [show FreeGroup.mk (l :: w') = FreeGroup.mk [l] * FreeGroup.mk w' from rfl, map_mul,
          ih, List.map_cons, show FreeGroup.mk ((S.get l.1, l.2) :: List.map
            (fun l => (S.get l.1, l.2)) w') = FreeGroup.mk [(S.get l.1, l.2)] *
            FreeGroup.mk (List.map (fun l => (S.get l.1, l.2)) w') from rfl, map_mul]
        congr 1
        obtain ⟨j, b⟩ := l
        cases b
        · rw [show FreeGroup.mk [(j, false)] = (FreeGroup.of j)⁻¹ from rfl, map_inv,
            FreeGroup.lift_apply_of]
          rfl
        · rw [show FreeGroup.mk [(j, true)] = FreeGroup.of j from rfl, FreeGroup.lift_apply_of]
          rfl
    rw [hmap]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)
  set φ := PresentedGroup.toGroup hrel
  refine ⟨φ, ?_⟩
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨S.get j, List.get_mem _ _, by simp [φ]⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := List.get_of_mem hx
    exact ⟨j, by rw [← hj]; simp [φ]⟩

theorem card_closure_range_le_PG {G : Type*} [Group G] {k : ℕ} {R : List (List (Fin k × Bool))}
    {y : Fin k → G} (hy : ∀ r ∈ wordSet R, FreeGroup.lift y r = 1) [Finite (PG k R)] :
    Nat.card (Subgroup.closure (Set.range y)) ≤ Nat.card (PG k R) := by
  have hrange : (PresentedGroup.toGroup hy).range = Subgroup.closure (Set.range y) := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      ← Set.range_comp]
    congr 2
    funext k
    exact PresentedGroup.toGroup.of hy
  rw [← hrange]
  exact Nat.card_le_card_of_surjective _ (PresentedGroup.toGroup hy).rangeRestrict_surjective

theorem dvd_of_counts {N m c n h j₀ h₀ k : ℕ} (hN : 0 < N) (hm : 0 < m) (hn : n ≤ N)
    (hn0 : 0 < n) (hdvd : j₀ ∣ n) (hj : j₀ * h₀ = N * m) (hh₀ : h₀ ≤ m)
    (hP : n * h = N * m * k) (hdiv : h ∣ m * c) : k ∣ c := by
  have hj₀ : j₀ ≤ n := Nat.le_of_dvd hn0 hdvd
  have h1 : N * m ≤ n * h₀ := by
    rw [← hj]
    exact Nat.mul_le_mul_right _ hj₀
  have h2 : n * h₀ ≤ N * h₀ := Nat.mul_le_mul_right _ hn
  have h3 : N * h₀ ≤ N * m := Nat.mul_le_mul_left _ hh₀
  have h4 : N * h₀ = N * m := le_antisymm h3 (h1.trans h2)
  have hh₀' : h₀ = m := Nat.eq_of_mul_eq_mul_left hN h4
  have h5 : n * h₀ = N * h₀ := le_antisymm h2 (by rw [h4]; exact h1)
  have h₀pos : 0 < h₀ := hh₀' ▸ hm
  have hn' : n = N := Nat.eq_of_mul_eq_mul_right h₀pos h5
  rw [hn'] at hP
  have hh : h = m * k := by
    refine Nat.eq_of_mul_eq_mul_left hN ?_
    rw [hP]
    ring
  rw [hh] at hdiv
  exact Nat.dvd_of_mul_dvd_mul_left hm hdiv

end CFSG.Sporadic.Recognition.CoverIndex

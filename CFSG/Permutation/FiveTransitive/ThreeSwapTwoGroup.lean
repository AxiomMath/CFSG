module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.SetTheory.Cardinal.Embedding

public section

namespace CFSG

namespace FiveTransitive.ThreeSwapTwoGroup

theorem closure_two_group
    {G : Type*} [Group G] (s : Set G) (hcomm : s.Pairwise Commute)
    (hsquare : ∀ g ∈ s, g ^ 2 = 1) :
    IsPGroup 2 (Subgroup.closure s) ∧
      ∀ g : Subgroup.closure s, g ^ 2 = 1 := by
  have habelian := Subgroup.isMulCommutative_closure hcomm
  have hp (g : G) (hg : g ∈ Subgroup.closure s) : g ^ 2 = 1 := by
    apply Subgroup.closure_induction (p := fun g _ => g ^ 2 = 1) ?_ ?_ ?_ ?_ hg
    · exact hsquare
    · simp
    · intro x y hx hy hx2 hy2
      have hc : Commute x y := congrArg Subtype.val
        ((isMulCommutative_iff.mp habelian) (⟨x, hx⟩ : Subgroup.closure s) ⟨y, hy⟩)
      rw [hc.mul_pow, hx2, hy2, one_mul]
    · intro x hx hx2
      rw [inv_pow, hx2, inv_one]
  have hsq (g : Subgroup.closure s) : g ^ 2 = 1 := Subtype.ext (hp g.val g.property)
  exact ⟨fun g => ⟨1, by simpa using hsq g⟩, hsq⟩

@[expose] def subgroup {F : Type*} [DecidableEq F] (e : Fin 6 ↪ F) : Subgroup (Equiv.Perm F) :=
  Subgroup.closure ({Equiv.swap (e 0) (e 1), Equiv.swap (e 2) (e 3),
    Equiv.swap (e 4) (e 5)} : Set (Equiv.Perm F))

theorem isTwoGroup {F : Type*} [DecidableEq F] (e : Fin 6 ↪ F) :
    IsPGroup 2 (subgroup e) ∧ ∀ g : subgroup e, g ^ 2 = 1 := by
  have hc (i j k l : Fin 6) (h : [i, j, k, l].Nodup) :
      Commute (Equiv.swap (e i) (e j)) (Equiv.swap (e k) (e l)) :=
    (Equiv.Perm.disjoint_swap_swap (by
      simpa only [List.map_cons, List.map_nil] using h.map e.injective)).commute
  have h01 := hc 0 1 2 3 (by decide)
  have h02 := hc 0 1 4 5 (by decide)
  have h12 := hc 2 3 4 5 (by decide)
  apply closure_two_group
  · intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first | exact Commute.refl _ | exact h01 | exact h01.symm | exact h02 | exact h02.symm | exact h12 | exact h12.symm
  · intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl <;> simp [pow_two]

theorem exists_embedding {F : Type*} [Finite F] [DecidableEq F]
    (hcard : 6 ≤ Nat.card F) (t : Equiv.Perm F) (ht : t.IsSwap) :
    ∃ e : Fin 6 ↪ F, t = Equiv.swap (e 0) (e 1) := by
  obtain ⟨a, b, hab, rfl⟩ := ht
  let c : Fin 2 ↪ F := ⟨![a, b], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  obtain ⟨e, he⟩ := Fin.Embedding.restrictSurjective_of_le_natCard
    (α := F) (m := 2) (n := 6) (by omega) hcard c
  have he0 : e 0 = a := DFunLike.congr_fun he 0
  have he1 : e 1 = b := DFunLike.congr_fun he 1
  exact ⟨e, by rw [he0, he1]⟩

end FiveTransitive.ThreeSwapTwoGroup

end CFSG

module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Cover3Sound

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

open CFSG.CosetTable CFSG.Sporadic.Recognition.CoverRecipe CFSG.Sporadic.Recognition.CoverTransfer
  Subgroup

theorem closure_range_codRestrict {G : Type*} [Group G] {m : ℕ} (g : Fin m → G) :
    Subgroup.closure (Set.range fun i : Fin m =>
      (⟨g i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : Subgroup.closure (Set.range g))) = ⊤ := by
  have e : (Set.range fun i : Fin m =>
      (⟨g i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : Subgroup.closure (Set.range g))) =
      Subtype.val ⁻¹' Set.range g := by
    ext ⟨x, hx⟩
    simp only [Set.mem_range, Set.mem_preimage]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, congrArg Subtype.val hy⟩,
      fun ⟨y, hy⟩ => ⟨y, Subtype.ext hy⟩⟩
  rw [e]
  exact closure_closure_coe_preimage

theorem coe_lift_codRestrict {G : Type*} [Group G] {m : ℕ} (g : Fin m → G) (w : FreeGroup (Fin m)) :
    ((FreeGroup.lift (fun i : Fin m =>
      (⟨g i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : Subgroup.closure (Set.range g))) w :
        Subgroup.closure (Set.range g)) : G) = FreeGroup.lift g w := by
  have : (Subgroup.closure (Set.range g)).subtype.comp (FreeGroup.lift fun i : Fin m =>
      (⟨g i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : Subgroup.closure (Set.range g))) =
        FreeGroup.lift g :=
    FreeGroup.ext_hom _ _ fun i => by simp
  exact congrArg (fun φ : FreeGroup (Fin m) →* G => φ w) this

theorem factorization_three_eq {a b n : ℕ} (hn : n = 3 ^ a * b) (hb : ¬ 3 ∣ b) :
    n.factorization 3 = a := by
  subst hn
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (dvd_zero 3)
  rw [Nat.factorization_mul (by positivity) hb0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hb, add_zero]

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

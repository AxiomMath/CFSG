module

public import CFSG.Quasithin.AppendixH.H9.H93.ExplicitDefs
public import CFSG.Quasithin.AppendixH.H9.H93.H93Defs
public import CFSG.Quasithin.AppendixH.H9.ModelBasic
import CFSG.Quasithin.AppendixH.H9.H93.A2Basic.A2Transvection

public section

namespace CFSG.ASVolI.ChH

open scoped Matrix
open CFSG.Quasithin CFSG.Open

theorem exists_param_A2g : ∃ ρ : Multiplicative (Fin 4 → ZMod 2) →* MulAut (PairN 4),
    Function.Injective ρ ∧ ρ.range = A2g ∧
    (∀ ε a b : Fin 4 → ZMod 2,
      ρ (Multiplicative.ofAdd ε) (pairVec a b) = pairVec (A2fst ε a b) (A2snd ε a b)) ∧
    (∀ ε : Fin 4 → ZMod 2, ρ (Multiplicative.ofAdd ε) ∈ Lg 4 ↔ ε 3 = 0) := by
  exact ⟨a2Hom, a2Hom_injective, a2Hom_range, a2Hom_apply, a2Hom_mem_Lg_iff⟩

theorem A2g_le_Mg : A2g ≤ Mg 4 := by
  rw [A2g, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact Lg_le_Mg (pairActN_mem_Lg _)
  · exact Lg_le_Mg (pairActN_mem_Lg _)
  · exact Lg_le_Mg (pairActN_mem_Lg _)
  · exact swapN_mem_Mg

private theorem multiplicative_sq_eq_one (x : Multiplicative (Fin 4 → ZMod 2)) : x ^ 2 = 1 := by
  rw [pow_two]
  exact Multiplicative.toAdd.injective
    ((toAdd_mul x x).trans ((A2eps_add_self x.toAdd).trans toAdd_one.symm))

theorem A2g_isElemAbelian2 : IsElemAbelian2 A2g := by
  rw [← a2Hom_range]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact (map_mul a2Hom x y).symm.trans
      ((congrArg a2Hom (mul_comm x y)).trans (map_mul a2Hom y x))
  · rintro _ ⟨x, rfl⟩
    exact (map_pow a2Hom x 2).symm.trans
      ((congrArg a2Hom (multiplicative_sq_eq_one x)).trans (map_one a2Hom))

theorem A2g_card : Nat.card A2g = 16 := by
  rw [← a2Hom_range]
  have h : Nat.card a2Hom.range = Nat.card (Multiplicative (Fin 4 → ZMod 2)) :=
    Nat.card_congr (MonoidHom.ofInjective a2Hom_injective).toEquiv.symm
  rw [h, Nat.card_eq_fintype_card, Fintype.card_multiplicative]
  simp

private theorem swapN_mem_A2g : swapN 4 ∈ A2g := by
  rw [A2g]
  exact Subgroup.subset_closure (by simp)

theorem A2g_not_le_Lg : ¬ A2g ≤ Lg 4 := by
  intro h
  exact swapN_not_mem_Lg (by norm_num) (h swapN_mem_A2g)

theorem ncard_tv_A2g : Set.ncard {g : MulAut (PairN 4) | g ∈ A2g ∧ IsTvElt g} = 3 := by
  have hset : {g : MulAut (PairN 4) | g ∈ A2g ∧ IsTvElt g} =
      {a2Hom (Multiplicative.ofAdd (Pi.single 0 1)), a2Hom (Multiplicative.ofAdd (Pi.single 1 1)),
        a2Hom (Multiplicative.ofAdd (Pi.single 2 1))} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hgA, hgT⟩
      rw [← a2Hom_range] at hgA
      obtain ⟨x, rfl⟩ := hgA
      obtain ⟨ε, rfl⟩ := Multiplicative.ofAdd.surjective x
      rcases (isTvElt_a2Hom_iff ε).mp hgT with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact ⟨a2Hom_mem_A2g _, (isTvElt_a2Hom_iff _).mpr (Or.inl rfl)⟩
      · exact ⟨a2Hom_mem_A2g _, (isTvElt_a2Hom_iff _).mpr (Or.inr (Or.inl rfl))⟩
      · exact ⟨a2Hom_mem_A2g _, (isTvElt_a2Hom_iff _).mpr (Or.inr (Or.inr rfl))⟩
  rw [hset, Set.ncard_eq_three]
  exact ⟨_, _, _, a2Hom_injective.ne (Multiplicative.ofAdd.injective.ne (by decide)),
    a2Hom_injective.ne (Multiplicative.ofAdd.injective.ne (by decide)),
    a2Hom_injective.ne (Multiplicative.ofAdd.injective.ne (by decide)), rfl⟩

end CFSG.ASVolI.ChH

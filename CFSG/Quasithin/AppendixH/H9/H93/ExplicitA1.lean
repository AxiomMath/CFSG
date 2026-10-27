module

public import CFSG.Quasithin.AppendixH.H9.H93.ExplicitDefs
public import CFSG.Quasithin.AppendixH.H9.H93.H93Defs
public import CFSG.Quasithin.AppendixH.H9.ModelBasic
import CFSG.Quasithin.AppendixH.H9.H93.TvMatrix
import CFSG.Quasithin.AppendixH.H9.H93.A1Basic.A1Structure

public section

namespace CFSG.ASVolI.ChH

open scoped Matrix
open CFSG.Quasithin CFSG.Open

theorem exists_param_A1g : ∃ ρ : Multiplicative (Fin 4 → ZMod 2) →* MulAut (PairN 4),
    Function.Injective ρ ∧ ρ.range = A1g ∧
    (∀ ε a b : Fin 4 → ZMod 2,
      ρ (Multiplicative.ofAdd ε) (pairVec a b) = pairVec (A1fst ε a b) (A1snd ε a b)) ∧
    (∀ ε : Fin 4 → ZMod 2, ρ (Multiplicative.ofAdd ε) ∈ Lg 4 ↔ ε 3 = 0) :=
  ⟨A1hom, A1hom_injective, A1hom_range, A1hom_apply_pairVec, A1hom_mem_Lg_iff⟩

theorem A1g_le_Mg : A1g ≤ Mg 4 := by
  rw [A1g, Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact Lg_le_Mg (pairActN_mem_Lg _)
  · exact Lg_le_Mg (pairActN_mem_Lg _)
  · exact Lg_le_Mg (pairActN_mem_Lg _)
  · exact swapN_mem_Mg

theorem A1g_isElemAbelian2 : IsElemAbelian2 A1g := by
  obtain ⟨ρ, -, hrange, -, -⟩ := exists_param_A1g
  rw [← hrange]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact ((map_mul ρ x y).symm.trans (congrArg ρ (mul_comm x y))).trans (map_mul ρ y x)
  · rintro _ ⟨x, rfl⟩
    have hx : ∀ x : Multiplicative (Fin 4 → ZMod 2), x ^ 2 = 1 := by decide
    exact (map_pow ρ x 2).symm.trans ((congrArg ρ (hx x)).trans (map_one ρ))

theorem A1g_card : Nat.card A1g = 16 := by
  obtain ⟨ρ, hinj, hrange, -, -⟩ := exists_param_A1g
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_eq_fintype_card]
  simp

theorem A1g_not_le_Lg : ¬ A1g ≤ Lg 4 := fun h =>
  swapN_not_mem_Lg (by norm_num) (h (Subgroup.subset_closure (Or.inr (Or.inr (Or.inr rfl)))))

theorem pairActN_gZJ_mem_A1g : pairActN 4 gZJ ∈ A1g :=
  Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))

theorem isTvElt_pairActN_gZJ : IsTvElt (pairActN 4 gZJ) := by
  refine (isTvElt_iff_vec (pairActN_mem_Lg gZJ)).mpr
    ⟨![1, 1, 1, 1], ![1, 1, 1, 1], by decide, by decide, fun a => ?_⟩
  rw [A1_pairActN_gZJ_pairVec, A1_vZJ_zero]
  exact congrArg (fun v => pairVec v 0) (A1_vZJ_eq_transvection a)

theorem ncard_tv_A1g : Set.ncard {g : MulAut (PairN 4) | g ∈ A1g ∧ IsTvElt g} = 1 := by
  have hset : {g : MulAut (PairN 4) | g ∈ A1g ∧ IsTvElt g} = {pairActN 4 gZJ} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hgA, hgT⟩
      obtain ⟨ρ, -, hrange, hact, hL⟩ := exists_param_A1g
      rw [← hrange] at hgA
      obtain ⟨e, rfl⟩ := hgA
      obtain ⟨ε, rfl⟩ := Multiplicative.ofAdd.surjective e
      have hLg : ρ (Multiplicative.ofAdd ε) ∈ Lg 4 := hgT.1
      have h3 : ε 3 = 0 := (hL ε).mp hLg
      obtain ⟨u, f, hu, hf, hvec⟩ := (isTvElt_iff_vec hLg).mp hgT
      have hA : ∀ a : Fin 4 → ZMod 2, A1vec ε a = a + (f ⬝ᵥ a) • u := by
        intro a
        have h1 := (hact ε a 0).symm.trans (hvec a)
        have h2 := (pairVec_inj.mp h1).1
        rw [A1fst, if_pos h3] at h2
        exact h2
      rcases A1vec_transvection_cases ε u f hA with h | h | ⟨h0, h1, h2⟩
      · exact absurd h hu
      · exact absurd h hf
      · apply MulEquiv.ext
        intro x
        obtain ⟨a, b, rfl⟩ := pairVec_surj x
        rw [hact ε a b, A1_pairActN_gZJ_pairVec]
        have hε : ε = Pi.single 2 1 := by
          funext i
          fin_cases i
          · simpa using h0
          · simpa using h1
          · simpa using h2
          · simpa using h3
        subst hε
        exact congrArg₂ pairVec (A1fst_snd_single_two a b).1 (A1fst_snd_single_two a b).2
    · rintro rfl
      exact ⟨pairActN_gZJ_mem_A1g, isTvElt_pairActN_gZJ⟩
  rw [hset, Set.ncard_singleton]

end CFSG.ASVolI.ChH

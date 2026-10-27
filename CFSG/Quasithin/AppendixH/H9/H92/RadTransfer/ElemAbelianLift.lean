module

public import CFSG.Quasithin.AppendixH.H9.ModelBasic

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem exists_map_pairActN_eq_of_le_Lg {n : ℕ} {E : Subgroup (MulAut (PairN n))} (hE : E ≤ Lg n) :
    ∃ E' : Subgroup (GL (Fin n) (ZMod 2)), E'.map (pairActN n) = E := by
  refine ⟨E.comap (pairActN n), le_antisymm ?_ ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ha
  · intro x hx
    obtain ⟨A, rfl⟩ := mem_Lg_iff.1 (hE hx)
    exact ⟨A, hx, rfl⟩

theorem card_map_pairActN {n : ℕ} (E' : Subgroup (GL (Fin n) (ZMod 2))) :
    Nat.card ↥(E'.map (pairActN n)) = Nat.card E' :=
  Subgroup.card_map_of_injective pairActN_injective

theorem comm_sq_of_isElemAbelian2_map {V : Type*} [CommGroup V] {G : Type*} [Group G]
    (φ : G →* MulAut V) (hφ : Function.Injective φ) (E : Subgroup G)
    (hab : IsElemAbelian2 (E.map φ)) :
    (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ ∀ a ∈ E, a * a = 1 := by
  refine ⟨fun a ha b hb => hφ ?_, fun a ha => hφ ?_⟩
  · rw [map_mul, map_mul]
    exact hab.1 _ (Subgroup.mem_map_of_mem φ ha) _ (Subgroup.mem_map_of_mem φ hb)
  · rw [map_mul, map_one]
    have h := hab.2 _ (Subgroup.mem_map_of_mem φ ha)
    rwa [pow_two] at h

end CFSG.ASVolI.ChH

module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTransvectionCore

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly CFSG.Open

variable {K : Type} [Field K]

theorem centralizer_inf_pCoreOf_centralizer_eq_zpowers (hK : Nat.card K = 4)
    {u : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    (hu : u ∈ Subgroup.normalizer
      (torU K : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))))
    (hu2 : orderOf u = 2) (hfix : Nat.card ↥(torU K ⊓ Subgroup.centralizer {u}) = 3 ^ 3) :
    Subgroup.centralizer ((torU K ⊓ Subgroup.centralizer {u} : Subgroup _) :
        Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) ⊓
      pCoreOf 2 (Subgroup.centralizer {u}) = Subgroup.zpowers u := by
  obtain ⟨g, hgN, hgu⟩ := exists_mem_normalizer_conj_eq_tZero' hK hu hu2 hfix
  obtain ⟨φ, hφ⟩ : ∃ φ : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)),
      φ = (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
  have hφinj : Function.Injective φ := by
    rw [hφ]
    exact (MulAut.conj g).injective
  have hφsurj : Function.Surjective φ := by
    rw [hφ]
    exact (MulAut.conj g).surjective
  have hφu : φ u = tZero hK := by
    rw [hφ]
    exact hgu
  have hmap_tor : Subgroup.map φ (torU K) = torU K := by
    rw [hφ]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).mp hgN
  have hmap_C : Subgroup.map φ (Subgroup.centralizer {u}) =
      Subgroup.centralizer {tZero hK} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      rw [← hφu, ← map_mul, ← map_mul]
      exact congrArg φ (hy u (by simp))
    · intro x hx
      obtain ⟨y, hy⟩ := hφsurj x
      refine Subgroup.mem_map.mpr ⟨y, ?_, hy⟩
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      apply hφinj
      rw [map_mul, map_mul, hy, hφu]
      exact hx (tZero hK) (by simp)
  have hmap_inf : Subgroup.map φ (torU K ⊓ Subgroup.centralizer {u}) =
      torU K ⊓ Subgroup.centralizer {tZero hK} := by
    rw [Subgroup.map_inf _ _ _ hφinj, hmap_tor, hmap_C]
  have hmap_pcore : Subgroup.map φ (pCoreOf 2 (Subgroup.centralizer {u})) =
      pCoreOf 2 (Subgroup.centralizer {tZero hK}) := by
    rw [hφ, ← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj g)
      (Subgroup.centralizer {u}), ← hφ, hmap_C]
  have hmap_zp : Subgroup.map φ (Subgroup.zpowers u) = Subgroup.zpowers (tZero hK) := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le, Subgroup.mem_comap, hφu]
      exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_map.mpr ⟨u, Subgroup.mem_zpowers u, hφu⟩
  have hcent : Subgroup.map φ
      (Subgroup.centralizer ((torU K ⊓ Subgroup.centralizer {u} : Subgroup _) :
          Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))) =
      Subgroup.centralizer ((torU K ⊓ Subgroup.centralizer {tZero hK} : Subgroup _) :
          Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro z hz
      rw [← hmap_inf] at hz
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
      rw [← map_mul, ← map_mul]
      exact congrArg φ (hy w hw)
    · intro x hx
      obtain ⟨y, hy⟩ := hφsurj x
      refine Subgroup.mem_map.mpr ⟨y, ?_, hy⟩
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro z hz
      apply hφinj
      rw [map_mul, map_mul, hy]
      exact hx (φ z) (by rw [← hmap_inf]; exact Subgroup.mem_map_of_mem φ hz)
  have hmap_lhs : Subgroup.map φ
      (Subgroup.centralizer ((torU K ⊓ Subgroup.centralizer {u} : Subgroup _) :
          Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) ⊓
        pCoreOf 2 (Subgroup.centralizer {u})) =
      Subgroup.centralizer ((torU K ⊓ Subgroup.centralizer {tZero hK} : Subgroup _) :
          Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) ⊓
        pCoreOf 2 (Subgroup.centralizer {tZero hK}) := by
    rw [Subgroup.map_inf _ _ _ hφinj, hcent, hmap_pcore]
  have hEq : Subgroup.map φ
      (Subgroup.centralizer ((torU K ⊓ Subgroup.centralizer {u} : Subgroup _) :
          Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) ⊓
        pCoreOf 2 (Subgroup.centralizer {u})) =
      Subgroup.map φ (Subgroup.zpowers u) := by
    rw [hmap_lhs, hmap_zp, centralizer_inf_pCoreOf_centralizer_tZero hK]
  exact Subgroup.map_injective hφinj hEq

end CFSG.StandardType.USixTwo

end

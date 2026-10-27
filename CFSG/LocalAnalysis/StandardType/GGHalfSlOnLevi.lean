module

public import CFSG.LocalAnalysis.StandardType.GGHalfSlOn

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

private theorem slLower2Hom_transvection {m : ℕ} {i j : Fin (m + 1)} (hij : i ≠ j) (c : F2) :
    slLower2Hom m (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection
        ((Fin.succ_injective _).ne ((Fin.succ_injective _).ne hij)) c := by
  rw [slLower2Hom, MonoidHom.comp_apply, slLowerBlockHom_transvection,
    slLowerBlockHom_transvection]

private theorem slUpper2Hom_transvection {m : ℕ} {i j : Fin (m + 1)} (hij : i ≠ j) (c : F2) :
    slUpper2Hom m (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection
        ((Fin.castSucc_injective _).ne ((Fin.castSucc_injective _).ne hij)) c := by
  rw [slUpper2Hom, MonoidHom.comp_apply, slUpperBlockHom_transvection,
    slUpperBlockHom_transvection]

private theorem slLower2Hom_map_slOn_aux (m : ℕ) (S : Set (Fin (m + 1))) :
    (slOn (m + 1) S).map (slLower2Hom m) =
      slOn (m + 1 + 1 + 1) ((fun i : Fin (m + 1) => i.succ.succ) '' S) := by
  rw [slOn, MonoidHom.map_closure, slOn]
  congr 1
  ext t
  constructor
  · rintro ⟨g, ⟨a, b, hab, c, ha, hb, rfl⟩, rfl⟩
    refine ⟨a.succ.succ, b.succ.succ,
      (Fin.succ_injective _).ne ((Fin.succ_injective _).ne hab),
      c, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, ?_⟩
    rw [slLower2Hom_transvection]
  · rintro ⟨a, b, hab, c, ⟨a₀, ha₀, rfl⟩, ⟨b₀, hb₀, rfl⟩, rfl⟩
    refine ⟨SpecialLinearGroup.transvection (fun hh => hab (by rw [hh])) c,
      ⟨a₀, b₀, _, c, ha₀, hb₀, rfl⟩, ?_⟩
    rw [slLower2Hom_transvection]

private theorem slUpper2Hom_map_slOn_aux (m : ℕ) (S : Set (Fin (m + 1))) :
    (slOn (m + 1) S).map (slUpper2Hom m) =
      slOn (m + 1 + 1 + 1) ((fun i : Fin (m + 1) => i.castSucc.castSucc) '' S) := by
  rw [slOn, MonoidHom.map_closure, slOn]
  congr 1
  ext t
  constructor
  · rintro ⟨g, ⟨a, b, hab, c, ha, hb, rfl⟩, rfl⟩
    refine ⟨a.castSucc.castSucc, b.castSucc.castSucc,
      (Fin.castSucc_injective _).ne ((Fin.castSucc_injective _).ne hab),
      c, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, ?_⟩
    rw [slUpper2Hom_transvection]
  · rintro ⟨a, b, hab, c, ⟨a₀, ha₀, rfl⟩, ⟨b₀, hb₀, rfl⟩, rfl⟩
    refine ⟨SpecialLinearGroup.transvection (fun hh => hab (by rw [hh])) c,
      ⟨a₀, b₀, _, c, ha₀, hb₀, rfl⟩, ?_⟩
    rw [slUpper2Hom_transvection]

theorem range_slLower2Hom (m : ℕ) :
    (slLower2Hom m).range = slOn (m + 1 + 1 + 1) {i | 2 ≤ i.val} := by
  rw [MonoidHom.range_eq_map, ← slOn_univ (m + 1), slLower2Hom_map_slOn_aux]
  congr 1
  ext i
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    simp only [Fin.val_succ]
    omega
  · intro hi
    refine ⟨⟨i.val - 2, by omega⟩, ?_⟩
    ext
    simp only [Fin.val_succ, Fin.val_mk]
    omega

theorem range_slUpper2Hom (m : ℕ) :
    (slUpper2Hom m).range = slOn (m + 1 + 1 + 1) {i | i.val ≤ m} := by
  rw [MonoidHom.range_eq_map, ← slOn_univ (m + 1), slUpper2Hom_map_slOn_aux]
  congr 1
  ext i
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    simp only [Fin.val_castSucc]
    omega
  · intro hi
    refine ⟨⟨i.val, by omega⟩, ?_⟩
    ext
    simp only [Fin.val_castSucc, Fin.val_mk]

theorem slLower2Hom_map_slOn (m : ℕ) (S : Set (Fin (m + 1))) :
    (slOn (m + 1) S).map (slLower2Hom m) =
      slOn (m + 1 + 1 + 1) ((fun i : Fin (m + 1) => i.succ.succ) '' S) :=
  slLower2Hom_map_slOn_aux m S

theorem slUpper2Hom_map_slOn (m : ℕ) (S : Set (Fin (m + 1))) :
    (slOn (m + 1) S).map (slUpper2Hom m) =
      slOn (m + 1 + 1 + 1) ((fun i : Fin (m + 1) => i.castSucc.castSucc) '' S) :=
  slUpper2Hom_map_slOn_aux m S

end CFSG.StandardType.GGHalf

end

module

public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

open Matrix MatrixGroups

theorem sl2_seven_pow : ∀ A : SL(2, ZMod 7), A ^ 3 = 1 ∨ A ^ 3 = -1 ∨ A ^ 4 = 1 ∨ A ^ 4 = -1 ∨
    A ^ 7 = 1 ∨ A ^ 7 = -1 := by
  decide +kernel

theorem alt6_pow : ∀ x : alternatingGroup (Fin 6), x ^ 3 = 1 ∨ x ^ 4 = 1 ∨ x ^ 5 = 1 := by
  decide +kernel

theorem neg_one_mem_center_sl2 (R : Type*) [CommRing R] :
    (-1 : SL(2, R)) ∈ Subgroup.center (SL(2, R)) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext i j
  simp

theorem psl2_zmod_seven_pow (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) :
    x ^ 3 = 1 ∨ x ^ 4 = 1 ∨ x ^ 7 = 1 := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : ∀ n : ℕ, A ^ n = 1 ∨ A ^ n = -1 → ((A : Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (ZMod 7))) ^ n = 1 := by
    intro n hn
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    rcases hn with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact neg_one_mem_center_sl2 _
  rcases sl2_seven_pow A with h | h | h | h | h | h
  · exact Or.inl (h1 3 (Or.inl h))
  · exact Or.inl (h1 3 (Or.inr h))
  · exact Or.inr (Or.inl (h1 4 (Or.inl h)))
  · exact Or.inr (Or.inl (h1 4 (Or.inr h)))
  · exact Or.inr (Or.inr (h1 7 (Or.inl h)))
  · exact Or.inr (Or.inr (h1 7 (Or.inr h)))

theorem psl2_pow_of_card_seven (F : Type) [Field F] [Fintype F] (hF : Fintype.card F = 7)
    (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) : x ^ 3 = 1 ∨ x ^ 4 = 1 ∨ x ^ 7 = 1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let e : ZMod 7 ≃+* F := ZMod.ringEquivOfPrime F (by norm_num) (by rw [hF])
  let f := CFSG.GorensteinWalter.psl2RingEquiv e
  obtain ⟨x', rfl⟩ := f.surjective x
  rcases psl2_zmod_seven_pow x' with h | h | h
  · exact Or.inl (by rw [← map_pow, h, map_one])
  · exact Or.inr (Or.inl (by rw [← map_pow, h, map_one]))
  · exact Or.inr (Or.inr (by rw [← map_pow, h, map_one]))

theorem psl2_pow_of_card_nine (F : Type) [Field F] [Fintype F] (hF : Fintype.card F = 9)
    (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) : x ^ 3 = 1 ∨ x ^ 4 = 1 ∨ x ^ 5 = 1 := by
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
    F hF
  rcases alt6_pow (e x) with h | h | h
  · exact Or.inl (e.injective (by rw [map_pow, h, map_one]))
  · exact Or.inr (Or.inl (e.injective (by rw [map_pow, h, map_one])))
  · exact Or.inr (Or.inr (e.injective (by rw [map_pow, h, map_one])))

end CFSG.Quasithin.Kleidman.ThreeLocal

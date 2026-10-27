module

public import CFSG.Quasithin.Background.SmithB42U33
public import CFSG.Quasithin.H13.L32A753b

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.B42U33
open CFSG.Quasithin.HatA6 (card_le_pow_of_le_closure)

namespace A6G2

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

omit [Finite V] in
theorem short_generation
    (hLG : L ≤ G) (hGN : G ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hCL : G ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L) (hP : B42TypeU33 ↥L)
    {A : Subgroup (MulAut V)} (hAG : A ≤ G) (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A) :
    ∃ r m : ℕ, Nat.card A = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 3 ∧ m * r ≤ 6 ∧
      ∃ l : Fin m → MulAut V, (∀ i, l i ∈ L) ∧
        L ≤ Subgroup.closure (⋃ i, ((A.map (MulAut.conj (l i)).toMonoidHom :
          Subgroup (MulAut V)) : Set (MulAut V))) :=
  CFSG.Quasithin.H13.L32A.M753.short_generation_of_le hLG hGN hCL hP hAG hA1 hAe

theorem offender_eq
    (hV : ∀ v : V, v ^ 2 = 1) (hLG : L ≤ G) (hGN : G ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hCL : G ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L) (hP : B42TypeU33 ↥L)
    (hfix : fixV L = ⊥) {A : Subgroup (MulAut V)} (hAG : A ≤ G) (hA1 : A ≠ ⊥)
    (hAe : IsElemAbelian2 A) (hff : (fixV A).index ≤ Nat.card A) :
    Nat.card A = 8 ∧ Nat.card (fixV A) = 8 ∧ Nat.card V = 2 ^ 6 := by
  obtain ⟨r, m, hr, -, -, hmr, l, -, hle⟩ := short_generation hLG hGN hCL hP hAG hA1 hAe
  have h1 := card_le_pow_of_le_closure hfix l hle
  have hup : Nat.card V ≤ 2 ^ 6 := by
    refine h1.trans ((Nat.pow_le_pow_left hff m).trans ?_)
    rw [hr, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by rw [mul_comm]; exact hmr)
  obtain ⟨k, hk⟩ : ∃ k, Nat.card V = 2 ^ k :=
    (IsPGroup.iff_card).1 (isPGroup_two_of_sq_eq_one hV)
  have hk6 : k ≤ 6 := by
    rw [hk] at hup
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hup
  have h6 := six_le_of_card_dvd hV hk L (card_of_b42TypeU33 hP)
  have h64 : Nat.card V = 2 ^ 6 := by rw [hk, show k = 6 by omega]
  obtain ⟨e, hLe⟩ := exists_equiv_of_g2NaturalDerived (u33SixNatural V hV h64 L hP)
  have hG : ∀ x ∈ G, MulAut.congr e x ∈ (g2QAct (ZMod 2)).range := by
    intro x hx
    refine normalizer_two_Q _ fun h => ?_
    obtain ⟨h', rfl⟩ := (MulAut.congr e).surjective h
    have hxN := Subgroup.mem_normalizer_iff.1 (hGN hx) h'
    rw [← hLe, ← map_inv, ← map_mul, ← map_mul]
    change (MulAut.congr e).toMonoidHom h' ∈ L.map (MulAut.congr e).toMonoidHom ↔
      (MulAut.congr e).toMonoidHom (x * h' * x⁻¹) ∈ L.map (MulAut.congr e).toMonoidHom
    rw [Subgroup.mem_map_iff_mem (MulAut.congr e).injective,
      Subgroup.mem_map_iff_mem (MulAut.congr e).injective]
    exact hxN
  have hφinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have hle' : A.map (MulAut.congr e).toMonoidHom ≤ (g2QAct (ZMod 2)).range := by
    rintro _ ⟨b, hb, rfl⟩
    exact hG b (hAG hb)
  have hne : A.map (MulAut.congr e).toMonoidHom ≠ ⊥ := fun h =>
    hA1 ((Subgroup.map_eq_bot_iff_of_injective _ hφinj).1 h)
  have hcardB : Nat.card (A.map (MulAut.congr e).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective hφinj
  have hfixB : Nat.card (fixV (A.map (MulAut.congr e).toMonoidHom)) = Nat.card (fixV A) := by
    rw [E3.fixV_map_congr, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  have hff' : Nat.card ModQ ≤ Nat.card (A.map (MulAut.congr e).toMonoidHom) *
      Nat.card (fixV (A.map (MulAut.congr e).toMonoidHom)) := by
    rw [hcardB, hfixB, ← Nat.card_congr e.toEquiv, ← (fixV A).card_mul_index, mul_comm]
    exact Nat.mul_le_mul_right _ hff
  have h := offender_exact hle' hne (H13.isElemAbelian2_map_congr e hAe) hff'
  rw [hcardB, hfixB] at h
  exact ⟨h.1, h.2, h64⟩

end A6G2

end CFSG.Quasithin.H13.A6

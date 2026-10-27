module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113BlockSteps
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.Seven

namespace A7Gen

theorem sup_eq_top_of_T7
    {R E : Subgroup ↥A7s} (hSN : T7 ≤ Subgroup.normalizer (R : Set ↥A7s)) (hR : ⁅R, R⁆ = R)
    (hE : ¬ E ≤ Subgroup.normalizer (R : Set ↥A7s)) : R ⊔ T7 ⊔ E = ⊤ := by
  by_contra hY
  have hMN : R ⊔ T7 ≤ Subgroup.normalizer (R : Set ↥A7s) := sup_le Subgroup.le_normalizer hSN
  have hMY : R ⊔ T7 ≤ R ⊔ T7 ⊔ E := le_sup_left
  have hYN : ¬ R ⊔ T7 ⊔ E ≤ Subgroup.normalizer (R : Set ↥A7s) := fun h =>
    hE (le_sup_right.trans h)
  obtain ⟨i, hi, hMi⟩ := overgroup_Z (le_sup_right : T7 ≤ R ⊔ T7)
  obtain ⟨j, hj, hYj⟩ := overgroup_Z (le_sup_right.trans hMY : T7 ≤ R ⊔ T7 ⊔ E)
  have hcM : Nat.card ↥(R ⊔ T7) =
      [8, 24, 24, 24, 24, 24, 72, 120, 168, 168, 360, 2520].getD i 0 := by
    rw [← card_map_subtype, hMi]
    exact card_Z hi
  have hcY : Nat.card ↥(R ⊔ T7 ⊔ E) =
      [8, 24, 24, 24, 24, 24, 72, 120, 168, 168, 360, 2520].getD j 0 := by
    rw [← card_map_subtype, hYj]
    exact card_Z hj
  have hYtop : Nat.card ↥(R ⊔ T7 ⊔ E) ≠ 2520 := fun h =>
    hY (Subgroup.eq_top_of_card_eq _ (h.trans card_A7s.symm))
  have hYM : Nat.card ↥(R ⊔ T7 ⊔ E) ≠ Nat.card ↥(R ⊔ T7) := fun h =>
    hYN ((Subgroup.eq_of_le_of_card_ge hMY h.le) ▸ hMN)
  have hdvd : Nat.card ↥(R ⊔ T7) ∣ Nat.card ↥(R ⊔ T7 ⊔ E) := Subgroup.card_dvd_of_le hMY
  rcases (show i ≤ 6 ∨ 7 ≤ i by omega) with h6 | h7
  ·
    have hMs : Group.IsSolvable ↥(R ⊔ T7) := by
      interval_cases i
      · exact isSolvable_of_card_two_three (a := 3) (b := 0) (by rw [hcM]; decide)
      all_goals first
        | exact isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcM]; decide)
        | exact isSolvable_of_card_two_three (a := 3) (b := 2) (by rw [hcM]; decide)
    have hRs : Group.IsSolvable ↥R := Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (le_sup_left : R ≤ R ⊔ T7)) (Subgroup.inclusion_injective _)
    have hRb : R = ⊥ := by
      by_contra hne
      have : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr hne
      have : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr hR
      exact Group.IsPerfect.not_isSolvable ↥R hRs
    rw [hRb, Subgroup.normalizer_eq_top_iff.mpr inferInstance] at hE
    exact hE le_top
  · rw [hcM] at hYM hdvd
    rw [hcY] at hYtop hYM hdvd
    interval_cases i <;> interval_cases j <;> first
      | (revert hYtop hYM hdvd; decide)
      | skip
    have hs : Equiv.Perm.sign (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 6) = 1 := by
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
        Equiv.Perm.sign_swap (by decide)]
      rfl
    have hxM : (⟨Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 6,
        Equiv.Perm.mem_alternatingGroup.mpr hs⟩ : ↥A7s) ∈ R ⊔ T7 :=
      (mem_of_map_eq hMi _).mpr ((mem_Z7 hs).mpr ⟨Or.inl (by decide), Or.inr (by decide)⟩)
    have h6 := (mem_Z10 hs).mp ((mem_of_map_eq hYj _).mp (hMY hxM))
    exact absurd h6 (by decide)

end A7Gen

theorem factA7Gen_holds :
    FactA7Gen := by
  intro X _ _ he R S E hS hSN hR hE
  obtain ⟨e⟩ := he
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf
    (isSylowTwoOf_top_map_of_surjective hS e.toMonoidHom e.surjective) isSylowTwoOf_T7
  set f : X ≃* ↥A7s := e.trans (MulAut.conj g) with hf
  have hfS : S.map f.toMonoidHom = T7 := by
    rw [← hg, Subgroup.map_map]
    rfl
  have hN : (Subgroup.normalizer (R : Set X)).map f.toMonoidHom =
      Subgroup.normalizer ((R.map f.toMonoidHom : Subgroup ↥A7s) : Set ↥A7s) :=
    Subgroup.map_equiv_normalizer_eq R f
  have hSN' : T7 ≤ Subgroup.normalizer ((R.map f.toMonoidHom : Subgroup ↥A7s) : Set ↥A7s) := by
    rw [← hfS, ← hN]
    exact Subgroup.map_mono hSN
  have hR' : ⁅R.map f.toMonoidHom, R.map f.toMonoidHom⁆ = R.map f.toMonoidHom := by
    rw [← Subgroup.map_commutator, hR]
  have hE' : ¬ E.map f.toMonoidHom ≤
      Subgroup.normalizer ((R.map f.toMonoidHom : Subgroup ↥A7s) : Set ↥A7s) := by
    rw [← hN]
    intro h
    exact hE ((Subgroup.map_le_map_iff_of_injective f.injective).mp h)
  have key := A7Gen.sup_eq_top_of_T7 hSN' hR' hE'
  rw [← hfS, ← Subgroup.map_sup, ← Subgroup.map_sup] at key
  rw [← Subgroup.comap_map_eq_self_of_injective (f := f.toMonoidHom) f.injective (R ⊔ S ⊔ E),
    key, Subgroup.comap_top]

end CFSG.Quasithin.H13

module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

private noncomputable def s15k_norm_klein_perm {W : Type} [CommGroup W] {R : Subgroup W} :
    ↥(stabSub R) →* Equiv.Perm {r : ↥R // r ≠ 1} where
  toFun y :=
    { toFun := fun s => ⟨⟨(y : MulAut W) (s.1 : W), (mem_stabSub.1 y.2 _).2 s.1.2⟩, by
        intro h
        apply s.2
        apply Subtype.ext
        have h1 : (y : MulAut W) (s.1 : W) = 1 := congrArg Subtype.val h
        have h2 : (y : MulAut W) (s.1 : W) = (y : MulAut W) 1 := by rw [h1, map_one]
        exact (y : MulAut W).injective h2⟩
      invFun := fun s => ⟨⟨(y⁻¹ : ↥(stabSub R)).1 (s.1 : W),
        (mem_stabSub.1 (y⁻¹ : ↥(stabSub R)).2 _).2 s.1.2⟩, by
        intro h
        apply s.2
        apply Subtype.ext
        have h1 : (y⁻¹ : ↥(stabSub R)).1 (s.1 : W) = 1 := congrArg Subtype.val h
        have h2 : (y⁻¹ : ↥(stabSub R)).1 (s.1 : W) = (y⁻¹ : ↥(stabSub R)).1 1 := by
          rw [h1, map_one]
        have := (y⁻¹ : ↥(stabSub R)).1.injective h2
        exact this⟩
      left_inv := fun s => by
        apply Subtype.ext
        apply Subtype.ext
        show (y⁻¹ : ↥(stabSub R)).1 ((y : MulAut W) _) = _
        exact MulAut.inv_apply_self W (y : MulAut W) _
      right_inv := fun s => by
        apply Subtype.ext
        apply Subtype.ext
        show (y : MulAut W) ((y⁻¹ : ↥(stabSub R)).1 _) = _
        exact MulAut.apply_inv_self W (y : MulAut W) _ }
  map_one' := by
    ext s
    rfl
  map_mul' a b := by
    ext s
    rfl

theorem s15k_norm_klein_six {W : Type} [CommGroup W]
    {J : Subgroup (MulAut W)} {R : Subgroup W} (hst : StableUnder J R) (hR : Nat.card R = 4)
    (hJ : Nat.card J = 6) (hfaith : ∀ j ∈ J, (∀ r ∈ R, j r = r) → j = 1) {x : MulAut W}
    (hx : x ∈ stabSub R) : ∃ j ∈ J, ∀ r ∈ R, x r = j r := by
  classical
  have hJs : J ≤ stabSub R := fun j hj => mem_stabSub.2 fun r =>
    ⟨fun h => by
      have := hst j⁻¹ (J.inv_mem hj) _ h
      rwa [MulAut.inv_apply_self] at this, hst j hj r⟩
  let Ψ : ↥J →* Equiv.Perm {r : ↥R // r ≠ 1} :=
    (s15k_norm_klein_perm (R := R)).comp (Subgroup.inclusion hJs)
  have hΨ : ∀ (j : ↥J) (s : {r : ↥R // r ≠ 1}),
      (((Ψ j s).1 : ↥R) : W) = (j : MulAut W) (s.1 : W) := fun j s => rfl
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro j hj
    apply Subtype.ext
    apply hfaith j j.2
    intro r hr
    by_cases h1 : r = 1
    · rw [h1, map_one]
    · have := hΨ j ⟨⟨r, hr⟩, fun h => h1 (congrArg Subtype.val h)⟩
      rw [hj] at this
      exact this.symm
  haveI : Finite R := Nat.finite_of_card_ne_zero (by rw [hR]; norm_num)
  haveI : Fintype R := Fintype.ofFinite R
  have hS : Nat.card {r : ↥R // r ≠ 1} = 3 := by
    haveI : Fintype {r : ↥R // r ≠ 1} := Fintype.ofFinite _
    haveI : Fintype {r : ↥R // r = 1} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hR]
  have hP : Nat.card (Equiv.Perm {r : ↥R // r ≠ 1}) = 6 := by
    rw [Nat.card_perm, hS]
    rfl
  haveI : Finite (Equiv.Perm {r : ↥R // r ≠ 1}) :=
    Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  have hbij : Function.Bijective Ψ :=
    ⟨hinj, (Function.Injective.bijective_of_nat_card_le hinj (by rw [hJ, hP])).2⟩
  obtain ⟨j, hj⟩ := hbij.2 (s15k_norm_klein_perm (R := R) ⟨x, hx⟩)
  refine ⟨(j : MulAut W), j.2, fun r hr => ?_⟩
  by_cases h1 : r = 1
  · rw [h1, map_one, map_one]
  · have h2 := congrArg (fun σ : Equiv.Perm {r : ↥R // r ≠ 1} =>
      (((σ ⟨⟨r, hr⟩, fun h => h1 (congrArg Subtype.val h)⟩).1 : ↥R) : W)) hj
    exact h2.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

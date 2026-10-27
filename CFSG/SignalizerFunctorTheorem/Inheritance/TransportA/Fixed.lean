module

public import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fitting

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.TransportA

variable {X Y : Type*} [Group X] [Group Y]

theorem congr_symm_apply (e : X ≃* Y) (f : MulAut Y) (x : X) :
    (MulAut.congr e.symm f) x = e.symm (f (e x)) := rfl

theorem mem_fixedSubgroup_congr (e : X ≃* Y) (f : MulAut Y) (x : X) :
    x ∈ signalizerFixedSubgroup (MulAut.congr e.symm f) ↔ e x ∈ signalizerFixedSubgroup f := by
  change (MulAut.congr e.symm f) x = x ↔ f (e x) = e x
  rw [congr_symm_apply, e.symm_apply_eq]

theorem map_fixedSubgroup_congr (e : X ≃* Y) (f : MulAut Y) :
    (signalizerFixedSubgroup (MulAut.congr e.symm f)).map (e : X →* Y) =
      signalizerFixedSubgroup f := by
  have : signalizerFixedSubgroup (MulAut.congr e.symm f) =
      (signalizerFixedSubgroup f).comap (e : X →* Y) :=
    Subgroup.ext fun x => mem_fixedSubgroup_congr e f x
  rw [this, Subgroup.map_comap_eq_self_of_surjective e.surjective]

theorem not_le_normalizer_of_congr (e : X ≃* Y) (f : MulAut Y)
    (h : ∀ T : Subgroup X, T ≠ ⊥ → Group.IsSolvable T →
      ¬ signalizerFixedSubgroup (MulAut.congr e.symm f) ≤ Subgroup.normalizer (T : Set X)) :
    ∀ T : Subgroup Y, T ≠ ⊥ → Group.IsSolvable T →
      ¬ signalizerFixedSubgroup f ≤ Subgroup.normalizer (T : Set Y) := by
  intro T hT hsolv hle
  refine h (T.comap (e : X →* Y)) ?_ ?_ fun x hx => ?_
  · intro hbot
    apply hT
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := (e : X →* Y)) e.surjective T, hbot,
      Subgroup.map_bot]
  · exact Group.isSolvable_of_isSolvable_injective (f := (e : X →* Y).subgroupComap T)
      fun a b hab => Subtype.ext (e.injective (congrArg Subtype.val hab))
  · have hx' := Subgroup.mem_normalizer_iff.mp (hle ((mem_fixedSubgroup_congr e f x).mp hx))
    refine Subgroup.mem_normalizer_iff.mpr fun z => ?_
    simpa using hx' (e z)

theorem fitting_clause_of_congr (e : X ≃* Y) (f : MulAut Y)
    (h : IsSimpleGroup (signalizerGeneralizedFitting
        (signalizerFixedSubgroup (MulAut.congr e.symm f))) ∧
      ∃ a b : signalizerGeneralizedFitting (signalizerFixedSubgroup (MulAut.congr e.symm f)),
        a * b ≠ b * a) :
    IsSimpleGroup (signalizerGeneralizedFitting (signalizerFixedSubgroup f)) ∧
      ∃ a b : signalizerGeneralizedFitting (signalizerFixedSubgroup f), a * b ≠ b * a := by
  obtain ⟨ε⟩ := nonempty_mulEquiv_generalizedFitting
    ((e.subgroupMap (signalizerFixedSubgroup (MulAut.congr e.symm f))).trans
      (MulEquiv.subgroupCongr (map_fixedSubgroup_congr e f)))
  obtain ⟨hsimple, a, b, hab⟩ := h
  exact ⟨ε.symm.isSimpleGroup, ε a, ε b, fun hba => hab (ε.injective (by simpa using hba))⟩

theorem eq_one_of_congr (e : X ≃* Y) (f : MulAut Y) {p : ℕ}
    (h : ∀ g : MulAut X, Nat.Coprime p (orderOf g) →
      (∀ x ∈ signalizerFixedSubgroup (MulAut.congr e.symm f), g x = x) → g = 1) :
    ∀ g : MulAut Y, Nat.Coprime p (orderOf g) →
      (∀ y ∈ signalizerFixedSubgroup f, g y = y) → g = 1 := by
  intro g hg hfix
  have h1 : MulAut.congr e.symm g = 1 := by
    refine h _ (by rwa [MulEquiv.orderOf_eq]) fun x hx => ?_
    rw [congr_symm_apply, hfix (e x) ((mem_fixedSubgroup_congr e f x).mp hx)]
    exact e.symm_apply_apply x
  exact (map_eq_one_iff _ (MulEquiv.injective _)).mp h1

end CFSG.SignalizerFunctorTheorem.TransportA

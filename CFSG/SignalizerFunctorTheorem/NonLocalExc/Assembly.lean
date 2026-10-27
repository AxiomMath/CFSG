module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Weights
public import CFSG.SignalizerFunctorTheorem.NonLocal.Faithful
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocal

public section

open Module CFSG.SignalizerFunctorTheorem.CatalogBridge CFSG.SignalizerFunctorTheorem.NonLocal

namespace CFSG.SignalizerFunctorTheorem.NonLocalExc

theorem nonLocalized_of_closing {X : Type*} [Group X] [Finite X] {J : Subgroup X}
    (hJ : IsSimpleGroup J) (hcent : ∀ x : X, (∀ j ∈ J, x * j = j * x) → x = 1)
    {r : ℕ}
    (hrsub : ∀ E : Subgroup X, IsPGroup r E → (∀ j ∈ J, ∀ e ∈ E, j * e * j⁻¹ ∈ E) → E = ⊥)
    (hclose : ∀ s : ℕ, s.Prime → s ≠ r → ∀ V : Subgroup X, V ≠ ⊥ →
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) → (∀ v ∈ V, v ^ s = 1) →
      (∀ j ∈ J, ∀ v ∈ V, j * v * j⁻¹ ∈ V) →
      (∀ j ∈ J, (∀ v ∈ V, j * v * j⁻¹ = v) → j = 1) → False) :
    NonLocalized J := by
  classical
  apply nonLocalized_of_elemAbelian
  intro s E hs hE0 hEcomm hEexp hle
  have hnormE : ∀ j ∈ J, ∀ e ∈ E, j * e * j⁻¹ ∈ E := fun j hj e he =>
    (Subgroup.mem_normalizer_iff.mp (hle hj) e).mp he
  have : Fact s.Prime := ⟨hs⟩
  have hEp : IsPGroup s E := by
    refine IsPGroup.iff_orderOf.mpr (fun g => ?_)
    have h1 : orderOf g ∣ s := orderOf_dvd_of_pow_eq_one (Subtype.ext (hEexp g g.2))
    rcases (Nat.dvd_prime hs).mp h1 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  by_cases hsr : s = r
  · subst hsr
    exact hE0 (hrsub E hEp hnormE)
  · have hnormJ : ∀ g : J, ∀ v ∈ E, J.subtype g * v * (J.subtype g)⁻¹ ∈ E := fun g v hv =>
      hnormE g g.2 v hv
    have hsimple : IsSimpleGroup (J.subtype.range) := by
      rw [Subgroup.range_subtype]
      exact hJ
    have hfaith' := faithful_of_simple J.subtype hsimple E hE0
      (fun c hc v hv => by
        obtain ⟨g, rfl⟩ := hc
        exact hnormJ g v hv)
      (fun x hx => hcent x fun j hj => hx ⟨j, hj⟩)
    exact hclose s hs hsr E hE0 hEcomm hEexp hnormE fun j hj hv => hfaith' ⟨j, hj⟩ hv

theorem cast_card_ne_zero_of_exponent {X : Type*} [Group X] {V : Subgroup X} [Finite V]
    {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hsr : s ≠ r) {F : Type*} [Field F] [CharP F r]
    (hexp : ∀ v ∈ V, v ^ s = 1) : (Nat.card V : F) ≠ 0 := by
  have : Fact s.Prime := ⟨hs⟩
  have hVp : IsPGroup s V := by
    refine IsPGroup.iff_orderOf.mpr (fun g => ?_)
    have h1 : orderOf g ∣ s := orderOf_dvd_of_pow_eq_one (Subtype.ext (hexp g g.2))
    rcases (Nat.dvd_prime hs).mp h1 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hVp
  have hrs : ¬ r ∣ s := fun h => hsr ((Nat.prime_dvd_prime_iff_eq hr hs).mp h).symm
  have hsF : (s : F) ≠ 0 := fun h => hrs ((CharP.cast_eq_zero_iff F r s).mp h)
  rw [hm]
  push_cast
  exact pow_ne_zero m hsF

theorem closing_of_perm {X : Type*} [Group X] [Finite X] {J : Subgroup X} {r : ℕ} (hr : r.Prime)
    {F W : Type*} [Field F] [IsAlgClosed F] [CharP F r] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (ρ : X →* End F W) (hρ : Function.Injective ρ)
    (R : Subgroup X) (hRJ : R ≤ J) (hR : ¬ Nat.card R ∣ (finrank F W).factorial) :
    ∀ s : ℕ, s.Prime → s ≠ r → ∀ V : Subgroup X, V ≠ ⊥ →
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) → (∀ v ∈ V, v ^ s = 1) →
      (∀ j ∈ J, ∀ v ∈ V, j * v * j⁻¹ ∈ V) →
      (∀ j ∈ J, (∀ v ∈ V, j * v * j⁻¹ = v) → j = 1) → False := by
  classical
  intro s hs hsr E hE0 hEcomm hEexp hnormE hfaith
  have : Fact s.Prime := ⟨hs⟩
  have hV : IsMulCommutative E := ⟨⟨fun a b => Subtype.ext (hEcomm _ a.2 _ b.2)⟩⟩
  have hEp : IsPGroup s E := by
    refine IsPGroup.iff_orderOf.mpr (fun g => ?_)
    have h1 : orderOf g ∣ s := orderOf_dvd_of_pow_eq_one (Subtype.ext (hEexp g g.2))
    rcases (Nat.dvd_prime hs).mp h1 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  have hinv : (Nat.card E : F) ≠ 0 := cast_card_ne_zero_of_exponent hr hs hsr hEexp
  have hnormJ : ∀ g : J, ∀ v ∈ E, J.subtype g * v * (J.subtype g)⁻¹ ∈ E := fun g v hv =>
    hnormE g g.2 v hv
  have hfaith2 : ∀ g : J, (∀ v ∈ E, J.subtype g * v * (J.subtype g)⁻¹ = v) → g = 1 :=
    fun g hg => Subtype.ext (hfaith g g.2 hg)
  have hdvd := card_dvd_factorial_of_faithful ρ hρ E hV hinv J.subtype hnormJ hfaith2
    (R.subgroupOf J)
  have hcard : Nat.card (R.subgroupOf J) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRJ).toEquiv
  rw [hcard] at hdvd
  exact hR hdvd

theorem nonLocalized_of_perm_data {X : Type*} [Group X] [Finite X] {J : Subgroup X}
    (hJ : IsSimpleGroup J) (hcent : ∀ x : X, (∀ j ∈ J, x * j = j * x) → x = 1)
    {r : ℕ} (hr : r.Prime)
    (hrsub : ∀ E : Subgroup X, IsPGroup r E → (∀ j ∈ J, ∀ e ∈ E, j * e * j⁻¹ ∈ E) → E = ⊥)
    {F W : Type*} [Field F] [IsAlgClosed F] [CharP F r] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (ρ : X →* End F W) (hρ : Function.Injective ρ)
    (R : Subgroup X) (hRJ : R ≤ J) (hR : ¬ Nat.card R ∣ (finrank F W).factorial) :
    NonLocalized J :=
  nonLocalized_of_closing hJ hcent hrsub (closing_of_perm hr ρ hρ R hRJ hR)

end CFSG.SignalizerFunctorTheorem.NonLocalExc

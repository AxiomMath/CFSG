module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.PermDegBasic

public section

open CFSG.SignalizerFunctorTheorem.Nonsolvable

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Deg

theorem eq_one_of_isPerfect_of_isSolvable {P S : Type*} [Group P] [Group S] [Group.IsPerfect P]
    [Group.IsSolvable S] (φ : P →* S) (x : P) : φ x = 1 := by
  have hP : ∀ n, derivedSeries P n = ⊤ := by
    intro n
    induction n with
    | zero => exact derivedSeries_zero P
    | succ n ih =>
      rw [derivedSeries_succ, ih]
      exact (Group.IsPerfect.commutator_eq_top (G := P))
  obtain ⟨n, hn⟩ := (inferInstance : Group.IsSolvable S).solvable
  have h := map_derivedSeries_le_derivedSeries φ n
  rw [hP n, hn, Subgroup.map_top, le_bot_iff] at h
  exact Subgroup.mem_bot.mp (h ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩)

variable {G : Type*} [Group G]

theorem isSolvable_subgroupOf (R H : Subgroup G) [Group.IsSolvable R] :
    Group.IsSolvable (R.subgroupOf H) :=
  Group.isSolvable_of_isSolvable_injective (f := H.subtype.subgroupComap R)
    (MonoidHom.subgroupComap_injective _ _ H.subtype_injective)

theorem le_of_isPerfect_of_le_sup {X R P : Subgroup G} [R.Normal] [Group.IsSolvable R]
    (hRX : R ≤ Subgroup.normalizer (X : Set G)) (hP : Group.IsPerfect P) (h : P ≤ X ⊔ R) :
    P ≤ X := by
  set Y : Subgroup G := X ⊔ R with hY
  have hXY : X ≤ Y := le_sup_left
  have hRY : R ≤ Y := le_sup_right
  have hnorm : (X.subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hXY]
    exact sup_le Subgroup.le_normalizer hRX
  let ψ : P →* Y ⧸ X.subgroupOf Y :=
    (QuotientGroup.mk' (X.subgroupOf Y)).comp (Subgroup.inclusion h)
  let ρ : R →* Y ⧸ X.subgroupOf Y :=
    (QuotientGroup.mk' (X.subgroupOf Y)).comp (Subgroup.inclusion hRY)
  have hρ : Function.Surjective ρ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, hx, r, hr, hxr⟩ := Subgroup.mem_sup_of_normal_right.mp y.2
    refine ⟨⟨r, hr⟩, ?_⟩
    show (QuotientGroup.mk ⟨r, hRY hr⟩ : Y ⧸ X.subgroupOf Y) = QuotientGroup.mk y
    have h1 : r⁻¹ * x * r ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (hRX (R.inv_mem hr)) x).mp hx
      simpa using this
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show r⁻¹ * (y : G) ∈ X
    rw [← hxr]
    simpa [mul_assoc] using h1
  have : Group.IsSolvable (Y ⧸ X.subgroupOf Y) := Group.isSolvable_of_surjective hρ
  have := hP
  intro x hx
  have h1 : ψ ⟨x, hx⟩ = 1 := eq_one_of_isPerfect_of_isSolvable ψ ⟨x, hx⟩
  have h2 : (QuotientGroup.mk ⟨x, h hx⟩ : Y ⧸ X.subgroupOf Y) = 1 := h1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem map_solvableRadical_le_of_surjective {X P : Type*} [Group X] [Finite X] [Group P]
    (φ : X →* P) (hφ : Function.Surjective φ) :
    (CFSG.solvableRadical X).map φ ≤ CFSG.solvableRadical P := by
  have : Group.IsSolvable (CFSG.solvableRadical X) := isSolvable_solvableRadical
  exact le_solvableRadical (Subgroup.Normal.map inferInstance φ hφ)
    (Group.isSolvable_of_surjective (φ.subgroupMap_surjective _))

theorem deg_eq_permDeg_of_surjective {X P : Type*} [Group X] [Finite X] [Group P]
    (φ : X →* P) (hφ : Function.Surjective φ) (hk : Group.IsSolvable φ.ker)
    (hP : CFSG.solvableRadical P = ⊥) : deg X = permDeg P := by
  have : Finite P := Finite.of_surjective φ hφ
  have hsol : CFSG.solvableRadical X = φ.ker := by
    refine le_antisymm ?_ (le_solvableRadical φ.normal_ker hk)
    have h := map_solvableRadical_le_of_surjective φ hφ
    rw [hP, le_bot_iff] at h
    exact (Subgroup.map_eq_bot_iff _).mp h
  let e : X ⧸ CFSG.solvableRadical X ≃* P :=
    (QuotientGroup.quotientMulEquivOfEq hsol).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  exact permDeg_congr e

end CFSG.SignalizerFunctorTheorem.McBride.Near.Deg

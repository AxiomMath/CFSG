module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Semisimple

public section

open CFSG.SignalizerFunctorTheorem.Nonsolvable

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm52Aux

variable {G : Type*} [Group G]

theorem le_oStar_of_mem_lcalOf {H : Type*} [Group H] [Finite H] {J : Subgroup H}
    (hJ : J ∈ lcalOf H) : J ≤ oStar H := by
  obtain ⟨hsub, hs, hnc⟩ := hJ
  refine le_oStar ?_
  rw [isSolComponent_iff_minimal]
  refine ⟨⟨hsub, fun hsolv => hnc (isMulCommutative_iff.mpr
    (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv))⟩, fun S hS hSJ => ?_⟩
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hs hS.1.subgroupOf with h | h
  · exfalso
    refine hS.2 ?_
    have hS1 : S = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall S).mpr fun x hx => ?_
      have hmem : (⟨x, hSJ hx⟩ : J) ∈ S.subgroupOf J := hx
      rw [h, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    rw [hS1]
    infer_instance
  · intro x hx
    have hmem : (⟨x, hx⟩ : J) ∈ S.subgroupOf J := by rw [h]; trivial
    exact hmem

theorem le_kOf_of_mem_lcal [Finite G] {X J : Subgroup G} (hJ : J ∈ lcal X) : J ≤ kOf X := by
  obtain ⟨hJX, hJ'⟩ := hJ
  have h1 := le_oStar_of_mem_lcalOf hJ'
  have h2 := Subgroup.map_mono (f := X.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hJX] at h2

theorem le_sol_of_isSubnormal [Finite G] {X U : Subgroup G} (hUX : U ≤ X)
    (hU : (U.subgroupOf X).IsSubnormal) (hs : Group.IsSolvable U) : U ≤ sol X := by
  have hs' : Group.IsSolvable (U.subgroupOf X) :=
    have := hs
    isSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hUX).symm
  have h := Subgroup.map_mono (f := X.subtype) (le_solvableRadical_of_isSubnormal hU hs')
  rwa [Subgroup.map_subgroupOf_eq_of_le hUX] at h

theorem le_kOf_of_isSubnormal_of_isSolvable [Finite G] {X U : Subgroup G} (hUX : U ≤ X)
    (hU : (U.subgroupOf X).IsSubnormal) (hs : Group.IsSolvable U) : U ≤ kOf X :=
  (le_sol_of_isSubnormal hUX hU hs).trans (sol_le_kOf X)

theorem isSubnormal_subgroupOf_of_normal_chain {D M X : Subgroup G} (hDM : D ≤ M)
    (hMX : M ≤ X) (hD : (D.subgroupOf M).Normal) (hM : (M.subgroupOf X).Normal) :
    (D.subgroupOf X).IsSubnormal := by
  have hDX : D.subgroupOf X ≤ M.subgroupOf X := fun x hx => hDM hx
  refine Subgroup.IsSubnormal.trans hDX ?_ hM.isSubnormal
  let e := Subgroup.subgroupOfEquivOfLe hMX
  have heq : (D.subgroupOf X).subgroupOf (M.subgroupOf X) =
      (D.subgroupOf M).comap e.toMonoidHom := by
    ext x
    rfl
  rw [heq]
  exact (hD.comap e.toMonoidHom).isSubnormal

theorem kOf_ne_bot [Finite G] {X : Subgroup G} (hX : X ≠ ⊥) : kOf X ≠ ⊥ := by
  by_cases hsol : sol X = ⊥
  · intro hk
    have h := centralizer_kOf_eq_bot hsol
    rw [hk, Subgroup.centralizer_eq_top_iff_subset.mpr (by simp), inf_top_eq] at h
    exact hX h
  · exact fun hk => hsol (eq_bot_iff.mpr (hk ▸ sol_le_kOf X))

theorem le_normalizer_iSup {ι : Sort*} {Q : Subgroup G} (K' : ι → Subgroup G)
    (hinv : ∀ i, Q ≤ Subgroup.normalizer (K' i : Set G)) :
    Q ≤ Subgroup.normalizer ((⨆ i, K' i : Subgroup G) : Set G) := by
  have key : ∀ a ∈ Q, ∀ m ∈ (⨆ i, K' i : Subgroup G), a * m * a⁻¹ ∈ (⨆ i, K' i : Subgroup G) := by
    intro a ha m hm
    refine Subgroup.iSup_induction K' (C := fun m => a * m * a⁻¹ ∈ (⨆ i, K' i : Subgroup G)) hm
      (fun i x hx => ?_) (by simp) (fun x y hx hy => ?_)
    · exact Subgroup.mem_iSup_of_mem i ((Subgroup.mem_normalizer_iff.mp (hinv i ha) x).mp hx)
    · rw [show a * (x * y) * a⁻¹ = a * x * a⁻¹ * (a * y * a⁻¹) by group]
      exact mul_mem hx hy
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro m
  refine ⟨key a ha m, fun h => ?_⟩
  simpa [mul_assoc] using key a⁻¹ (inv_mem ha) _ h

theorem normalizer_le_normalizer_kOf [Finite G] (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (kOf X : Set G) := by
  have key : ∀ {g : G}, g ∈ Subgroup.normalizer (X : Set G) → ∀ {x : G}, x ∈ kOf X →
      g * x * g⁻¹ ∈ kOf X := by
    intro g hg x hx
    let φ : MulAut ↥X := X.normalizerMonoidHom ⟨g, hg⟩
    have hφ : ∀ t : X, ((φ t : X) : G) = g * t * g⁻¹ := fun t =>
      Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨g, hg⟩ t
    have hchar : (oStar ↥X).map φ.toMonoidHom = oStar ↥X :=
      Subgroup.characteristic_iff_map_eq.mp inferInstance φ
    obtain ⟨t, ht, rfl⟩ := hx
    refine ⟨φ t, ?_, (hφ t).symm ▸ rfl⟩
    rw [← hchar]
    exact ⟨t, ht, rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key hg hx, fun hx => ?_⟩
  simpa [mul_assoc] using key (inv_mem hg) hx

theorem le_normalizer_kOf [Finite G] (X : Subgroup G) : X ≤ Subgroup.normalizer (kOf X : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_kOf X)

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm52Aux

module

public import CFSG.RankThree.GF2n.Tim79aSec23One

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem Dy_isClass : ∃ d₀ : Xbar V H, Dy V H = {g | IsConj d₀ g} := by
  obtain ⟨d₀, hd₀, hcl⟩ := hc.dbarOf_isClass
  have hd₀X : d₀ ∈ barOf V H (xOf V H) := hc.dbarOf_subset_barOf_xOf hd₀
  refine ⟨⟨d₀, hd₀X⟩, ?_⟩
  ext g
  simp only [Dy, Set.mem_setOf_eq]
  rw [hcl, isConj_iff]
  constructor
  · rintro ⟨x, hx, hgx⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hgx.symm⟩
  · rintro ⟨c, hc'⟩
    exact ⟨c.1, c.2, by rw [← hc']; rfl⟩

theorem noncentral_of_not_case_one
    (hnot : ¬ (Nat.card (barOf V H V) = 2 ∧
      barOf V H (xOf V H) = oddCoreX V H ⊔ barOf V H V)) :
    ∀ d ∈ Dy V H, d ∉ Subgroup.center (Xbar V H) := by
  intro d hd hcen
  apply hnot
  obtain ⟨d₀, hd₀, hcl⟩ := hc.dbarOf_isClass
  have hDd : ∀ y ∈ dbarOf V H, y = d.1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hcl y).1 hy
    obtain ⟨x', hx', hdx⟩ := (hcl d.1).1 hd
    have hc1 : d.1 * x' = x' * d.1 :=
      (Subtype.ext_iff.mp (Subgroup.mem_center_iff.mp hcen ⟨x', hx'⟩)).symm
    have : d₀ = d.1 := by
      have h2 : x'⁻¹ * d.1 * x' = d₀ := by rw [hdx]; group
      rw [← h2, mul_assoc, hc1]; group
    have hx2 : d.1 * x = x * d.1 :=
      (Subtype.ext_iff.mp (Subgroup.mem_center_iff.mp hcen ⟨x, hx⟩)).symm
    rw [this]
    calc x * d.1 * x⁻¹ = d.1 * x * x⁻¹ := by rw [← hx2]
      _ = d.1 := by group
  have hV1 : ∀ a ∈ barOf V H V, ∀ b ∈ barOf V H V, a ≠ 1 → b ≠ 1 → a = b := fun a ha b hb ha1 hb1 =>
    (hDd a (hc.barOf_V_subset_dbarOf ha ha1)).trans (hDd b (hc.barOf_V_subset_dbarOf hb hb1)).symm
  refine ⟨hc.card_barOf_V_eq_two hV1, ?_⟩
  obtain ⟨e, hdV, hdW⟩ := SetLike.not_le_iff_exists.mp hc.not_V_le_wOf
  have hdH : e ∈ H := hc.V_le_H hdV
  have he1 : piBar V H ⟨e, hdH⟩ ≠ 1 := fun h => hdW ((piBar_eq_one_iff _).1 h)
  have hem : piBar V H ⟨e, hdH⟩ ∈ barOf V H V := mem_barOf_iff.mpr ⟨_, hdV, rfl⟩
  have hed : piBar V H ⟨e, hdH⟩ = d.1 := hDd _ (hc.barOf_V_subset_dbarOf hem he1)
  have hdV' : d.1 ∈ barOf V H V := hed ▸ hem
  have hXV : barOf V H (xOf V H) ≤ barOf V H V := by
    rw [← hc.closure_dbarOf]
    refine (Subgroup.closure_le _).2 fun y hy => ?_
    rw [hDd y hy]
    exact hdV'
  refine le_antisymm ?_ (sup_le (oddCoreX_le V H) (barOf_V_le V H))
  exact hXV.trans le_sup_right

theorem Dy_root : CFSG.Timmesfeld.IsRootInvolutionSet (Dy V H) :=
  CFSG.Timmesfeld.isRootInvolutionSet_subtype (S := barOf V H (xOf V H))
    hc.dbarOf_isRootInvolutionSet

theorem Dy_gen : Subgroup.closure (Dy V H) = ⊤ := by
  apply Subgroup.map_injective (barOf V H (xOf V H)).subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have : (barOf V H (xOf V H)).subtype '' Dy V H = dbarOf V H := by
    have h := Subtype.image_preimage_coe (barOf V H (xOf V H) : Set (Hbar V H)) (dbarOf V H)
    rw [Set.inter_eq_right.mpr hc.dbarOf_subset_barOf_xOf] at h
    exact h
  rw [this, hc.closure_dbarOf]

theorem sec23_dichotomy :
    (Nat.card (barOf V H V) = 2 ∧ barOf V H (xOf V H) = oddCoreX V H ⊔ barOf V H V) ∨
      Sec23Data V H := by
  by_cases h1 : CFSG.oddCore (Xbar V H) ≤ Subgroup.center (Xbar V H)
  · by_cases h2 : Nat.card (barOf V H V) = 2 ∧
        barOf V H (xOf V H) = oddCoreX V H ⊔ barOf V H V
    · exact Or.inl h2
    · right
      refine ⟨hc.Dy_isClass, hc.Dy_root, hc.Dy_gen, ?_, hc.noncentral_of_not_case_one h2⟩
      intro N hN hsol
      haveI := hN
      refine solvable_normal_le_center ?_ hsol
      exact CFSG.WholeGroup.fittingSubgroup_le_pCore_two_sup_oddCore.trans
        (sup_le hc.pCore_two_le_center h1)
  · exact Or.inl (hc.case_one h1)

end MinCex

end CFSG.RankThree.GF2n.Tim79a

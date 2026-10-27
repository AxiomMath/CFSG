module

public import Mathlib.GroupTheory.Frattini

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

private theorem ker_le_frattini_of_forall_map_eq {T Q : Type*} [Group T] [Group Q] (ψ : T →* Q)
    (hmin : ∀ H : Subgroup T, H.map ψ = ψ.range → H = ⊤) : ψ.ker ≤ frattini T := by
  refine le_iInf₂ fun H hH => ?_
  have hH' : IsCoatom H := hH
  by_contra hKH
  have hsup : H ⊔ ψ.ker = ⊤ := hH'.2 _ (left_lt_sup.mpr hKH)
  refine hH'.1 (hmin H (le_antisymm (Subgroup.map_le_range ψ H) ?_))
  rintro _ ⟨t, rfl⟩
  have ht : t ∈ H ⊔ ψ.ker := hsup ▸ Subgroup.mem_top t
  rw [← Subgroup.comap_map_eq] at ht
  exact ht

theorem exists_perfect_cover {P Q : Type*} [Group P] [Finite P] [Group Q] (ρ : P →* Q)
    (Λ : Subgroup P) (S : Subgroup Q) (hS : ⁅S, S⁆ = S) (h : S ≤ Λ.map ρ) :
    ∃ Pi : Subgroup P, Pi ≤ Λ ∧ Pi.map ρ = S ∧ ⁅Pi, Pi⁆ = Pi ∧
      ∀ x : ↥Pi, ρ (x : P) = 1 → x ∈ frattini ↥Pi := by
  have h0 : (Λ ⊓ S.comap ρ).map ρ = S := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr inf_le_right) fun s hs => ?_
    obtain ⟨x, hxΛ, rfl⟩ := h hs
    exact ⟨x, ⟨hxΛ, hs⟩, rfl⟩
  obtain ⟨Pi, hmin⟩ := (Set.toFinite {H : Subgroup P | H ≤ Λ ∧ H.map ρ = S}).exists_minimal
    ⟨Λ ⊓ S.comap ρ, inf_le_left, h0⟩
  obtain ⟨hPiΛ, hPiS⟩ := hmin.prop
  have hperf : ⁅Pi, Pi⁆ = Pi := by
    refine hmin.eq_of_le ⟨(Subgroup.commutator_le_self Pi).trans hPiΛ, ?_⟩
      (Subgroup.commutator_le_self Pi)
    rw [Subgroup.map_commutator, hPiS, hS]
  refine ⟨Pi, hPiΛ, hPiS, hperf, ?_⟩
  have hker : (ρ.comp Pi.subtype).ker ≤ frattini ↥Pi := by
    refine ker_le_frattini_of_forall_map_eq _ fun H hH => ?_
    have hHS : (H.map Pi.subtype).map ρ = S := by
      rw [Subgroup.map_map, hH, MonoidHom.range_comp, Subgroup.range_subtype, hPiS]
    have hHPi : H.map Pi.subtype = Pi :=
      hmin.eq_of_le ⟨(Subgroup.map_subtype_le H).trans hPiΛ, hHS⟩ (Subgroup.map_subtype_le H)
    refine Subgroup.map_injective Pi.subtype_injective ?_
    rw [hHPi, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact fun x hx => hker hx

theorem exists_perfect_cover_nilpotent {P Q : Type*} [Group P] [Finite P] [Group Q] (ρ : P →* Q)
    (Λ : Subgroup P) (S : Subgroup Q) (hS : ⁅S, S⁆ = S) (h : S ≤ Λ.map ρ) :
    ∃ Pi : Subgroup P, Pi ≤ Λ ∧ Pi.map ρ = S ∧ ⁅Pi, Pi⁆ = Pi ∧
      Group.IsNilpotent ↥(ρ.comp Pi.subtype).ker := by
  obtain ⟨Pi, hPiΛ, hPiS, hperf, hfr⟩ := exists_perfect_cover ρ Λ S hS h
  refine ⟨Pi, hPiΛ, hPiS, hperf, ?_⟩
  have hle : (ρ.comp Pi.subtype).ker ≤ frattini ↥Pi := fun x hx => hfr x hx
  have : Group.IsNilpotent ↥(frattini ↥Pi) := frattini_nilpotent
  exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1

module

public import CFSG.LocalAnalysis.StandardType.FS81.D6PlaneData

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.D6M

open CFSG.SeitzReduction.OmegaPilot
open scoped MatrixGroups

private theorem d6node_two_eq :
    node 2 = Subgroup.map lin (siegelParam (ZMod 2) {2,3} ∅).range := by
  rw [node, rootL, ← range_siegelParam]
  rfl

private theorem d6flip_two_eq :
    flip2 = Subgroup.map lin (siegelParam (ZMod 2) {2,3} {3}).range := by
  rw [flip2, rootL, ← range_siegelParam]

private theorem d6mem_node2 {z : V12 ≃ₗ[ZMod 2] V12} :
    z ∈ node 2 ↔ ∃ B : d6PlaneSL, z = lin (siegelParam (ZMod 2) {2,3} ∅ B) := by
  rw [d6node_two_eq, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨B, rfl⟩ := hg
    exact ⟨B, rfl⟩
  · rintro ⟨B, rfl⟩
    exact ⟨_, ⟨B, rfl⟩, rfl⟩

private theorem d6mem_flip2 {z : V12 ≃ₗ[ZMod 2] V12} :
    z ∈ flip2 ↔ ∃ A : d6PlaneSL, z = lin (siegelParam (ZMod 2) {2,3} {3} A) := by
  rw [d6flip_two_eq, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨A, rfl⟩ := hg
    exact ⟨A, rfl⟩
  · rintro ⟨A, rfl⟩
    exact ⟨_, ⟨A, rfl⟩, rfl⟩

private theorem d6lin_injective : Function.Injective lin :=
  fun _ _ h => (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 6 ⊕ Fin 6) (ZMod 2)).injective h

private theorem d6ne_one_of_flip_ne_one {A : d6PlaneSL}
    (h : lin (siegelParam (ZMod 2) {2,3} {3} A) ≠ 1) : A ≠ 1 := by
  intro hA
  apply h
  rw [hA]
  simp

private theorem d6pres_of_preserves {u v : Fin 4 → ZMod 2} {A B : d6PlaneSL}
    (h : ∀ x ∈ Submodule.span (ZMod 2) ({d6PlaneEmb u, d6PlaneEmb v} : Set V12),
      (lin (siegelParam (ZMod 2) {2,3} ∅ B) * lin (siegelParam (ZMod 2) {2,3} {3} A)) x ∈
        Submodule.span (ZMod 2) ({d6PlaneEmb u, d6PlaneEmb v} : Set V12)) :
    d6Pres u v (d6PlaneNle B * d6PlaneFle A) := by
  constructor
  · have hu := h (d6PlaneEmb u) (Submodule.subset_span (by simp))
    rw [d6PlaneMap_apply_emb] at hu
    exact d6InPair_emb_iff.mp (d6mem_span_pair.mp hu)
  · have hv := h (d6PlaneEmb v) (Submodule.subset_span (by simp))
    rw [d6PlaneMap_apply_emb] at hv
    exact d6InPair_emb_iff.mp (d6mem_span_pair.mp hv)

private theorem d6planeSpan_mono {P Q : Finset (Fin 6)} (h : P ⊆ Q) : planeSpan P ≤ planeSpan Q := by
  intro x hx
  rw [mem_planeSpan] at hx ⊢
  intro i hi
  exact hx i (fun hp => hi (h hp))

private theorem d6planeSpan_two_eq :
    planeSpan ({2} : Finset (Fin 6)) = Submodule.span (ZMod 2)
      ({d6PlaneEmb (d6PlaneV 14), d6PlaneEmb (d6PlaneU 14)} : Set V12) := by
  have hU : d6PlaneU 14 = d6PlaneV4 0 0 1 0 := rfl
  have hV : d6PlaneV 14 = d6PlaneV4 1 0 0 0 := rfl
  apply le_antisymm
  · intro v hv
    have hv' := mem_planeSpan.mp hv
    have hdecomp : v = v (Sum.inl 2) • d6PlaneEmb (d6PlaneV 14) +
        v (Sum.inr 2) • d6PlaneEmb (d6PlaneU 14) := by
      funext j
      rcases j with i | i <;> fin_cases i <;>
        simp [hU, hV, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          d6PlaneEmb_v4_inl_zero, d6PlaneEmb_v4_inl_one, d6PlaneEmb_v4_inl_two,
          d6PlaneEmb_v4_inl_three, d6PlaneEmb_v4_inl_four, d6PlaneEmb_v4_inl_five,
          d6PlaneEmb_v4_inr_zero, d6PlaneEmb_v4_inr_one, d6PlaneEmb_v4_inr_two,
          d6PlaneEmb_v4_inr_three, d6PlaneEmb_v4_inr_four, d6PlaneEmb_v4_inr_five,
          (hv' 0 (by decide)).1, (hv' 0 (by decide)).2,
          (hv' 1 (by decide)).1, (hv' 1 (by decide)).2,
          (hv' 3 (by decide)).1, (hv' 3 (by decide)).2,
          (hv' 4 (by decide)).1, (hv' 4 (by decide)).2,
          (hv' 5 (by decide)).1, (hv' 5 (by decide)).2]
    rw [hdecomp]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · change d6PlaneEmb (d6PlaneV 14) ∈ planeSpan ({2} : Finset (Fin 6))
      rw [mem_planeSpan]
      intro i _
      fin_cases i <;> simp_all [hV, d6PlaneEmb_v4_inl_zero, d6PlaneEmb_v4_inl_one,
        d6PlaneEmb_v4_inl_two, d6PlaneEmb_v4_inl_three, d6PlaneEmb_v4_inl_four,
        d6PlaneEmb_v4_inl_five, d6PlaneEmb_v4_inr_zero, d6PlaneEmb_v4_inr_one,
        d6PlaneEmb_v4_inr_two, d6PlaneEmb_v4_inr_three, d6PlaneEmb_v4_inr_four,
        d6PlaneEmb_v4_inr_five]
    · change d6PlaneEmb (d6PlaneU 14) ∈ planeSpan ({2} : Finset (Fin 6))
      rw [mem_planeSpan]
      intro i _
      fin_cases i <;> simp_all [hU, d6PlaneEmb_v4_inl_zero, d6PlaneEmb_v4_inl_one,
        d6PlaneEmb_v4_inl_two, d6PlaneEmb_v4_inl_three, d6PlaneEmb_v4_inl_four,
        d6PlaneEmb_v4_inl_five, d6PlaneEmb_v4_inr_zero, d6PlaneEmb_v4_inr_one,
        d6PlaneEmb_v4_inr_two, d6PlaneEmb_v4_inr_three, d6PlaneEmb_v4_inr_four,
        d6PlaneEmb_v4_inr_five]

theorem isHypPlane_planeSpan_two : IsHypPlane (planeSpan {2}) := by
  refine ⟨?_, d6PlaneEmb (d6PlaneV 14), d6PlaneEmb (d6PlaneU 14), d6planeSpan_two_eq,
    ?_, ?_, ?_⟩
  · show planeSpan ({2} : Finset (Fin 6)) ≤ planeSpan ({2,3} : Finset (Fin 6))
    exact d6planeSpan_mono (by decide)
  · rw [d6PlaneQ_emb]; decide +kernel
  · rw [d6PlaneQ_emb]; decide +kernel
  · rw [d6PlaneB_emb]; decide +kernel

theorem isHypPlane_perpY2 {P : Submodule (ZMod 2) V12} (hP : IsHypPlane P) :
    IsHypPlane (perpY2 P) := by
  obtain ⟨i, rfl⟩ := (d6IsHypPlane_iff P).mp hP
  rw [d6perpY2_span_pair_emb, d6Perp4_span_pair_data, d6span_pair_map_emb]
  obtain ⟨j, h1, h2, h3, h4⟩ := d6perp_index_data i
  refine (d6IsHypPlane_iff _).mpr ⟨j, ?_⟩
  exact d6span_pair_eq_of (d6InPair_emb_iff.mpr h1) (d6InPair_emb_iff.mpr h2)
    (d6InPair_emb_iff.mpr h3) (d6InPair_emb_iff.mpr h4)

theorem sigOf_unique {P : Submodule (ZMod 2) V12} {c c' : V12 ≃ₗ[ZMod 2] V12}
    (hP : IsHypPlane P) (h : SigOf P c) (h' : SigOf P c') : c = c' := by
  obtain ⟨i, rfl⟩ := (d6IsHypPlane_iff P).mp hP
  obtain ⟨hcF, hcne, m, hm, hpres⟩ := h
  obtain ⟨hcF', hcne', m', hm', hpres'⟩ := h'
  obtain ⟨A, rfl⟩ := d6mem_flip2.mp hcF
  obtain ⟨A', rfl⟩ := d6mem_flip2.mp hcF'
  obtain ⟨B, rfl⟩ := d6mem_node2.mp hm
  obtain ⟨B', rfl⟩ := d6mem_node2.mp hm'
  have hA : A ≠ 1 := d6ne_one_of_flip_ne_one hcne
  have hA' : A' ≠ 1 := d6ne_one_of_flip_ne_one hcne'
  have hd : d6Pres (d6PlaneU i) (d6PlaneV i) (d6PlaneNle B * d6PlaneFle A) :=
    d6pres_of_preserves hpres
  have hd' : d6Pres (d6PlaneU i) (d6PlaneV i) (d6PlaneNle B' * d6PlaneFle A') :=
    d6pres_of_preserves hpres'
  rw [d6sigOf_unique_data i A A' B B' hA hA' hd hd']

theorem sigOf_perpY2 {P : Submodule (ZMod 2) V12} {c : V12 ≃ₗ[ZMod 2] V12}
    (hP : IsHypPlane P) (h : SigOf P c) : SigOf (perpY2 P) c := by
  obtain ⟨i, rfl⟩ := (d6IsHypPlane_iff P).mp hP
  obtain ⟨hcF, hcne, m, hm, hpres⟩ := h
  obtain ⟨A, rfl⟩ := d6mem_flip2.mp hcF
  obtain ⟨B, rfl⟩ := d6mem_node2.mp hm
  have hA : A ≠ 1 := d6ne_one_of_flip_ne_one hcne
  have hd : d6Pres (d6PlaneU i) (d6PlaneV i) (d6PlaneNle B * d6PlaneFle A) :=
    d6pres_of_preserves hpres
  obtain ⟨B', hd'⟩ := d6sigOf_perp_data i A hA ⟨B, hd⟩
  refine ⟨d6mem_flip2.mpr ⟨A, rfl⟩, hcne,
    lin (siegelParam (ZMod 2) {2,3} ∅ B'), d6mem_node2.mpr ⟨B', rfl⟩, ?_⟩
  intro v hv
  rw [d6perpY2_span_pair_emb, d6Perp4_span_pair_data, d6span_pair_map_emb] at hv ⊢
  exact d6maps_span_emb (f := lin (siegelParam (ZMod 2) {2,3} ∅ B') *
    lin (siegelParam (ZMod 2) {2,3} {3} A)) (d6PlaneMap_apply_emb A B') hd' v hv

theorem exists_node2_map_eq_perpY2 {P P' : Submodule (ZMod 2) V12}
    {c : V12 ≃ₗ[ZMod 2] V12} (hP : IsHypPlane P) (hP' : IsHypPlane P')
    (h : SigOf P c) (h' : SigOf P' c) :
    ∃ k ∈ node 2, P.map (k : V12 →ₗ[ZMod 2] V12) = perpY2 P' := by
  obtain ⟨i, rfl⟩ := (d6IsHypPlane_iff P).mp hP
  obtain ⟨j, rfl⟩ := (d6IsHypPlane_iff P').mp hP'
  obtain ⟨hcF, hcne, m, hm, hpres⟩ := h
  obtain ⟨hcF', hcne', m', hm', hpres'⟩ := h'
  obtain ⟨A, hAeq⟩ := d6mem_flip2.mp hcF
  obtain ⟨A', hA'eq⟩ := d6mem_flip2.mp hcF'
  have hAA : A = A' := by
    apply siegelParam_injective (B := ({2,3} : Finset (Fin 6))) (P := ({3} : Finset (Fin 6)))
    apply d6lin_injective
    rw [← hAeq, ← hA'eq]
  subst hAA
  rw [hAeq] at hpres hcne
  rw [hA'eq] at hpres' hcne'
  obtain ⟨B, rfl⟩ := d6mem_node2.mp hm
  obtain ⟨B', rfl⟩ := d6mem_node2.mp hm'
  have hA : A ≠ 1 := d6ne_one_of_flip_ne_one hcne
  have hd : d6Pres (d6PlaneU i) (d6PlaneV i) (d6PlaneNle B * d6PlaneFle A) :=
    d6pres_of_preserves hpres
  have hd' : d6Pres (d6PlaneU j) (d6PlaneV j) (d6PlaneNle B' * d6PlaneFle A) :=
    d6pres_of_preserves hpres'
  obtain ⟨D, h1, h2, h3, h4⟩ := d6node_perp_data i j A hA ⟨B, hd⟩ ⟨B', hd'⟩
  refine ⟨lin (siegelParam (ZMod 2) {2,3} ∅ D), d6mem_node2.mpr ⟨D, rfl⟩, ?_⟩
  rw [d6perpY2_span_pair_emb, d6Perp4_span_pair_data, d6span_pair_map_emb]
  refine d6span_map_eq_of_preimage (u := d6PlaneEmb (d6PlaneU i))
    (v := d6PlaneEmb (d6PlaneV i)) (u' := d6PlaneEmb (d6PlanePU j))
    (v' := d6PlaneEmb (d6PlanePV j))
    (w := d6PlaneEmb (d6PlaneNle D⁻¹ (d6PlanePU j)))
    (w' := d6PlaneEmb (d6PlaneNle D⁻¹ (d6PlanePV j)))
    (f := ((lin (siegelParam (ZMod 2) {2,3} ∅ D) : V12 ≃ₗ[ZMod 2] V12) :
      V12 →ₗ[ZMod 2] V12)) ?_ ?_ ?_ ?_ ?_ ?_
  · change (lin (siegelParam (ZMod 2) {2,3} ∅ D)) (d6PlaneEmb (d6PlaneU i)) ∈
      Submodule.span (ZMod 2) ({d6PlaneEmb (d6PlanePU j), d6PlaneEmb (d6PlanePV j)} : Set V12)
    rw [d6PlaneNode_apply_emb]
    exact d6mem_span_pair.mpr (d6InPair_emb_iff.mpr h1)
  · change (lin (siegelParam (ZMod 2) {2,3} ∅ D)) (d6PlaneEmb (d6PlaneV i)) ∈
      Submodule.span (ZMod 2) ({d6PlaneEmb (d6PlanePU j), d6PlaneEmb (d6PlanePV j)} : Set V12)
    rw [d6PlaneNode_apply_emb]
    exact d6mem_span_pair.mpr (d6InPair_emb_iff.mpr h2)
  · exact d6mem_span_pair.mpr (d6InPair_emb_iff.mpr h3)
  · exact d6mem_span_pair.mpr (d6InPair_emb_iff.mpr h4)
  · change (lin (siegelParam (ZMod 2) {2,3} ∅ D))
      (d6PlaneEmb (d6PlaneNle D⁻¹ (d6PlanePU j))) = d6PlaneEmb (d6PlanePU j)
    exact d6PlaneNode_inv_apply D (d6PlanePU j)
  · change (lin (siegelParam (ZMod 2) {2,3} ∅ D))
      (d6PlaneEmb (d6PlaneNle D⁻¹ (d6PlanePV j))) = d6PlaneEmb (d6PlanePV j)
    exact d6PlaneNode_inv_apply D (d6PlanePV j)

theorem exists_map_eq_of_isHypPlane {P P' : Submodule (ZMod 2) V12}
    (hP : IsHypPlane P) (hP' : IsHypPlane P') :
    ∃ m ∈ node 2, ∃ c ∈ flip2,
      P.map ((m * c : V12 ≃ₗ[ZMod 2] V12) : V12 →ₗ[ZMod 2] V12) = P' := by
  obtain ⟨i, rfl⟩ := (d6IsHypPlane_iff P).mp hP
  obtain ⟨j, rfl⟩ := (d6IsHypPlane_iff P').mp hP'
  obtain ⟨A, B, h1, h2, h3, h4⟩ := d6transitive_data i j
  refine ⟨lin (siegelParam (ZMod 2) {2,3} ∅ B), d6mem_node2.mpr ⟨B, rfl⟩,
    lin (siegelParam (ZMod 2) {2,3} {3} A), d6mem_flip2.mpr ⟨A, rfl⟩, ?_⟩
  refine d6span_map_eq_of_preimage (u := d6PlaneEmb (d6PlaneU i))
    (v := d6PlaneEmb (d6PlaneV i)) (u' := d6PlaneEmb (d6PlaneU j))
    (v' := d6PlaneEmb (d6PlaneV j))
    (w := d6PlaneEmb ((d6PlaneFle A⁻¹ * d6PlaneNle B⁻¹) (d6PlaneU j)))
    (w' := d6PlaneEmb ((d6PlaneFle A⁻¹ * d6PlaneNle B⁻¹) (d6PlaneV j)))
    (f := (((lin (siegelParam (ZMod 2) {2,3} ∅ B) *
      lin (siegelParam (ZMod 2) {2,3} {3} A)) : V12 ≃ₗ[ZMod 2] V12) :
      V12 →ₗ[ZMod 2] V12)) ?_ ?_ ?_ ?_ ?_ ?_
  · change (lin (siegelParam (ZMod 2) {2,3} ∅ B) *
      lin (siegelParam (ZMod 2) {2,3} {3} A)) (d6PlaneEmb (d6PlaneU i)) ∈
      Submodule.span (ZMod 2) ({d6PlaneEmb (d6PlaneU j), d6PlaneEmb (d6PlaneV j)} : Set V12)
    rw [d6PlaneMap_apply_emb]
    exact d6mem_span_pair.mpr (d6InPair_emb_iff.mpr h1)
  · change (lin (siegelParam (ZMod 2) {2,3} ∅ B) *
      lin (siegelParam (ZMod 2) {2,3} {3} A)) (d6PlaneEmb (d6PlaneV i)) ∈
      Submodule.span (ZMod 2) ({d6PlaneEmb (d6PlaneU j), d6PlaneEmb (d6PlaneV j)} : Set V12)
    rw [d6PlaneMap_apply_emb]
    exact d6mem_span_pair.mpr (d6InPair_emb_iff.mpr h2)
  · exact d6mem_span_pair.mpr (d6InPair_emb_iff.mpr h3)
  · exact d6mem_span_pair.mpr (d6InPair_emb_iff.mpr h4)
  · change (lin (siegelParam (ZMod 2) {2,3} ∅ B) *
      lin (siegelParam (ZMod 2) {2,3} {3} A))
      (d6PlaneEmb ((d6PlaneFle A⁻¹ * d6PlaneNle B⁻¹) (d6PlaneU j))) = d6PlaneEmb (d6PlaneU j)
    exact d6PlaneMap_inv_apply A B (d6PlaneU j)
  · change (lin (siegelParam (ZMod 2) {2,3} ∅ B) *
      lin (siegelParam (ZMod 2) {2,3} {3} A))
      (d6PlaneEmb ((d6PlaneFle A⁻¹ * d6PlaneNle B⁻¹) (d6PlaneV j))) = d6PlaneEmb (d6PlaneV j)
    exact d6PlaneMap_inv_apply A B (d6PlaneV j)

end CFSG.StandardType.FrameRoute.FS81.D6M

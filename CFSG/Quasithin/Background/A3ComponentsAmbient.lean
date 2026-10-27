module

public import CFSG.Quasithin.Background.A3ComponentsQuotient

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem map_subtype_mem_cComp [Finite G] {X : Subgroup G} {L' : Subgroup ↥X}
    (hL' : L' ∈ cComp (⊤ : Subgroup ↥X)) : L'.map X.subtype ∈ cComp X := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact ne_bot_of_mem_cComp hL'
      ((Subgroup.map_eq_bot_iff_of_injective L' X.subtype_injective).mp h)
  · rw [← Subgroup.map_commutator, perfect_of_mem_cComp hL']
  · have := A3.subnormal_map X.subtype (subnormal_of_mem_cComp hL')
    rwa [Subgroup.map_top, Subgroup.range_subtype] at this
  · intro K hKlt hKne hKperf hKsub
    have hKX : K ≤ X := A3.subnormal_le hKsub
    have hKK' : (K.subgroupOf X).map X.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKX
    have hlt : K.subgroupOf X < L' := by
      refine lt_of_le_of_ne ?_ ?_
      · calc K.subgroupOf X ≤ (L'.map X.subtype).subgroupOf X := Subgroup.comap_mono hKlt.le
          _ = L' := Subgroup.comap_map_eq_self_of_injective X.subtype_injective L'
      · intro h
        rw [← h, hKK'] at hKlt
        exact lt_irrefl _ hKlt
    have hne : K.subgroupOf X ≠ ⊥ := by
      intro h
      apply hKne
      rw [← hKK', h, Subgroup.map_bot]
    have hperf : ⁅K.subgroupOf X, K.subgroupOf X⁆ = K.subgroupOf X := by
      apply Subgroup.map_injective X.subtype_injective
      rw [Subgroup.map_commutator, hKK', hKperf]
    have hsub : IsSubnormal (K.subgroupOf X) ⊤ := by
      have := A3.subnormal_comap X.subtype hKsub
      rwa [show X.comap X.subtype = ⊤ from Subgroup.subgroupOf_self X] at this
    exact not_subnormal_of_mem_cComp hL' hlt hne hperf hsub

theorem subgroupOf_mem_cComp [Finite G] {X L : Subgroup G} (hL : L ∈ cComp X) :
    L.subgroupOf X ∈ cComp (⊤ : Subgroup ↥X) := by
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hLL' : (L.subgroupOf X).map X.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLX
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    apply ne_bot_of_mem_cComp hL
    rw [← hLL', h, Subgroup.map_bot]
  · apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, hLL', perfect_of_mem_cComp hL]
  · have := A3.subnormal_comap X.subtype (subnormal_of_mem_cComp hL)
    rwa [show X.comap X.subtype = ⊤ from Subgroup.subgroupOf_self X] at this
  · intro K' hK'lt hK'ne hK'perf hK'sub
    have hKlt : K'.map X.subtype < L := by
      rw [← hLL']
      exact lt_of_le_of_ne (Subgroup.map_mono hK'lt.le) fun h =>
        hK'lt.ne (Subgroup.map_injective X.subtype_injective h)
    have hKne : K'.map X.subtype ≠ ⊥ := fun h =>
      hK'ne ((Subgroup.map_eq_bot_iff_of_injective K' X.subtype_injective).mp h)
    have hKperf : ⁅K'.map X.subtype, K'.map X.subtype⁆ = K'.map X.subtype := by
      rw [← Subgroup.map_commutator, hK'perf]
    have hKsub : IsSubnormal (K'.map X.subtype) X := by
      have := A3.subnormal_map X.subtype hK'sub
      rwa [Subgroup.map_top, Subgroup.range_subtype] at this
    exact not_subnormal_of_mem_cComp hL hKlt hKne hKperf hKsub

theorem cComp_map_subtype_bijOn [Finite G] (X : Subgroup G) :
    Set.BijOn (Subgroup.map X.subtype) (cComp (⊤ : Subgroup ↥X)) (cComp X) := by
  refine ⟨fun _ hL' => map_subtype_mem_cComp hL', (Subgroup.map_injective
    X.subtype_injective).injOn, fun L hL => ⟨L.subgroupOf X, subgroupOf_mem_cComp hL, ?_⟩⟩
  exact Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp hL)

theorem cComp_subgroupOf_bijOn [Finite G] (X : Subgroup G) :
    Set.BijOn (fun L : Subgroup G => L.subgroupOf X) (cComp X) (cComp (⊤ : Subgroup ↥X)) := by
  refine ⟨fun _ hL => subgroupOf_mem_cComp hL, fun L₁ h₁ L₂ h₂ h => ?_,
    fun K' hK' => ⟨K'.map X.subtype, map_subtype_mem_cComp hK', ?_⟩⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp h₁),
      ← Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp h₂)]
    exact congrArg (Subgroup.map X.subtype) h
  · exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective K'

theorem cCompSpan_eq_map_subtype [Finite G] (X : Subgroup G) :
    cCompSpan X = (cCompSpan (⊤ : Subgroup ↥X)).map X.subtype := by
  unfold cCompSpan
  rw [(Subgroup.gc_map_comap X.subtype).l_sSup, ← sSup_image, (cComp_map_subtype_bijOn X).image_eq]

theorem perfectCore_eq_map_perfectResidual (H : Subgroup G) :
    perfectCore H = (CFSG.perfectResidual ↥H).map H.subtype := by
  unfold perfectCore CFSG.perfectResidual
  rw [Subgroup.map_iInf H.subtype H.subtype_injective]
  exact iInf_congr fun n => derivedSeriesOf_eq_map_derivedSeries H n

theorem solvRad_eq_map_solvableRadical [Finite G] (X : Subgroup G) :
    solvRad X = (CFSG.solvableRadical ↥X).map X.subtype := by
  apply le_antisymm
  · have h1 : (solvRad X).subgroupOf X ≤ CFSG.solvableRadical ↥X := by
      refine A3.le_solvableRadical (solvRad_normal X) ?_
      have := solvRad_isSolvable X
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe (solvRad_le X)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (solvRad_le X)).injective
    calc solvRad X = ((solvRad X).subgroupOf X).map X.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (solvRad_le X)).symm
      _ ≤ (CFSG.solvableRadical ↥X).map X.subtype := Subgroup.map_mono h1
  · have hle : (CFSG.solvableRadical ↥X).map X.subtype ≤ X := fun _ ⟨y, _, hy⟩ => hy ▸ y.2
    have hsub : ((CFSG.solvableRadical ↥X).map X.subtype).subgroupOf X =
        CFSG.solvableRadical ↥X :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
    refine le_solvRad hle (by rw [hsub]; infer_instance) ?_
    have : Group.IsSolvable ↥(CFSG.solvableRadical ↥X) := A3.solvableRadical_isSolvable
    exact Group.isSolvable_of_surjective
      (f := ((CFSG.solvableRadical ↥X).equivMapOfInjective X.subtype
        X.subtype_injective).toMonoidHom)
      ((CFSG.solvableRadical ↥X).equivMapOfInjective X.subtype X.subtype_injective).surjective

theorem cComp_quotient_bijOn_of_le [Finite G] {X N : Subgroup G} (hNX : N ≤ X)
    (hNn : (N.subgroupOf X).Normal) (hN : Group.IsSolvable N) :
    Set.BijOn (fun L : Subgroup G => (L.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X)))
      (cComp X) (cComp (⊤ : Subgroup (↥X ⧸ N.subgroupOf X))) := by
  have hs : Group.IsSolvable ↥(N.subgroupOf X) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNX).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNX).injective
  exact (cComp_quotient_bijOn (N.subgroupOf X) hs).comp (cComp_subgroupOf_bijOn X)

theorem cComp_part_five_of_le [Finite G] (X : Subgroup G) :
    cComp (⊤ : Subgroup (↥X ⧸ CFSG.solvableRadical ↥X)) = {K | CFSG.IsComponent K} ∧
      cCompSpan X = perfectCore ((oInftyE ↥X).map X.subtype) := by
  obtain ⟨h1, h2⟩ := cComp_part_five (G := ↥X)
  refine ⟨h1, ?_⟩
  rw [cCompSpan_eq_map_subtype, h2, map_perfectCore]

theorem cComp_normal_span_of_le [Finite G] {X L : Subgroup G} (hL : L ∈ cComp X) :
    L ≤ cCompSpan X ∧ (L.subgroupOf (cCompSpan X)).Normal := by
  obtain ⟨hle, hn⟩ := cComp_normal_span (subgroupOf_mem_cComp hL)
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hLL' : (L.subgroupOf X).map X.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLX
  have hS : cCompSpan X = (cCompSpan (⊤ : Subgroup ↥X)).map X.subtype :=
    cCompSpan_eq_map_subtype X
  have hLS : L ≤ cCompSpan X := by
    rw [hS, ← hLL']
    exact Subgroup.map_mono hle
  refine ⟨hLS, (Subgroup.normal_subgroupOf_iff hLS).mpr fun l s hl hs => ?_⟩
  rw [hS] at hs
  obtain ⟨s', hs', rfl⟩ := hs
  rw [← hLL'] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  have h := (Subgroup.normal_subgroupOf_iff hle).mp hn l' s' hl' hs'
  rw [← hLL']
  exact ⟨s' * l' * s'⁻¹, h, by simp⟩

theorem cComp_commutator_dichotomy_of_le [Finite G] {Y L X : Subgroup G} (hL : L ∈ cComp Y)
    (hXY : X ≤ Y) :
    (⁅L, X⁆ ≤ solvRad Y ∧ Group.IsSolvable ↥⁅L, X⁆) ∨ ⁅L, X⁆ = conjClosure L X := by
  have hLY : L ≤ Y := le_of_mem_cComp hL
  have hLL' : (L.subgroupOf Y).map Y.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLY
  have hXX' : (X.subgroupOf Y).map Y.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXY
  have hcomm : (⁅L.subgroupOf Y, X.subgroupOf Y⁆).map Y.subtype = ⁅L, X⁆ := by
    rw [Subgroup.map_commutator, hLL', hXX']
  have hconj : (conjClosure (L.subgroupOf Y) (X.subgroupOf Y)).map Y.subtype =
      conjClosure L X := by
    rw [A3.map_conjClosure, hLL', hXX']
  rcases cComp_commutator_dichotomy (subgroupOf_mem_cComp hL) (X.subgroupOf Y) with
    ⟨h1, -⟩ | h2
  · left
    have hle : ⁅L, X⁆ ≤ solvRad Y := by
      rw [solvRad_eq_map_solvableRadical, ← hcomm]
      exact Subgroup.map_mono h1
    have := solvRad_isSolvable Y
    exact ⟨hle, Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)⟩
  · right
    rw [← hcomm, ← hconj, h2]

end CFSG.Quasithin

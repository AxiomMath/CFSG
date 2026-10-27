module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFourDefs

public section

namespace CFSG.StandardType.SpFour

open CFSG.Assembly TableB

section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem map_centralizer_singleton (e : G ≃* G') (y : G) :
    (Subgroup.centralizer ({y} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e y} : Set G') := by
  ext g'
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 := congrArg e h
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
    exact h1
  · intro h
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h

theorem layerC_map (e : G ≃* G') (y : G) :
    (layerC y).map e.toMonoidHom = layerC (e y) := by
  unfold layerC
  rw [← largeEvenLayer_map_of_injective e.toMonoidHom e.injective, map_centralizer_singleton]

theorem isComponentOf_map_iff (e : G ≃* G') {K C : Subgroup G} :
    IsComponentOf (K.map e.toMonoidHom) (C.map e.toMonoidHom) ↔ IsComponentOf K C := by
  refine ⟨fun h => ?_, isComponentOf_map_of_injective e.toMonoidHom e.injective⟩
  have h1 := (isComponentOf_comap_of_injective e.toMonoidHom e.injective h).1
  rwa [Subgroup.comap_map_eq_self_of_injective e.injective] at h1

theorem mem_zpowers_map_iff (e : G ≃* G') (y s : G) :
    e s ∈ Subgroup.zpowers (e y) ↔ s ∈ Subgroup.zpowers y := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, e.injective (by rw [map_zpow]; exact hk)⟩
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [map_zpow]⟩

theorem endNodeAt_map_iff (e : G ≃* G') (Ã : Subgroup G) (y : G) :
    EndNodeAt (Ã.map e.toMonoidHom) (e y) ↔ EndNodeAt Ã y := by
  unfold EndNodeAt
  rw [← layerC_map e y, ← map_centralizer_singleton e y, isComponentOf_map_iff]
  refine and_congr_right fun _ => ?_
  have h2 : ∀ s : G, (∀ j ∈ (layerC y).map e.toMonoidHom, e s * j = j * e s) ↔
      ∀ j ∈ layerC y, s * j = j * s := by
    intro s
    constructor
    · intro hj j hjl
      have := hj (e j) (Subgroup.mem_map_of_mem _ hjl)
      rw [← map_mul, ← map_mul] at this
      exact e.injective this
    · rintro hj _ ⟨j, hjl, rfl⟩
      change e s * e j = e j * e s
      rw [← map_mul, ← map_mul, hj j hjl]
  constructor
  · intro h s hs
    have h1 := h (e s) (Subgroup.mem_map_of_mem _ hs)
    rw [h2 s, mem_zpowers_map_iff] at h1
    exact h1
  · rintro h _ ⟨s, hs, rfl⟩
    change (∀ j ∈ (layerC y).map e.toMonoidHom, e s * j = j * e s) ↔ e s ∈ _
    rw [h2 s, mem_zpowers_map_iff]
    exact h s hs

theorem largeEvenSmall_map_iff (e : G ≃* G') (K : Subgroup G) :
    LargeEvenSmall (K.map e.toMonoidHom) ↔ LargeEvenSmall K :=
  (largeEvenSmall_congr (K.equivMapOfInjective e.toMonoidHom e.injective)).symm

theorem ruleAt_map_iff (e : G ≃* G') (Ã : Subgroup G) (y : G) :
    RuleAt (Ã.map e.toMonoidHom) (e y) ↔ RuleAt Ã y := by
  unfold RuleAt
  rw [← layerC_map e y, largeEvenSmall_map_iff]
  constructor
  · rintro h ⟨z, hz, hz1, hEN, hns⟩
    apply h
    refine ⟨e z, Subgroup.mem_map_of_mem _ hz, ?_, (endNodeAt_map_iff e Ã z).mpr hEN, ?_⟩
    · intro h1
      exact hz1 (e.injective (by rw [h1, map_one]))
    · rw [← layerC_map e z, largeEvenSmall_map_iff]
      exact hns
  · rintro h ⟨z', hz', hz1, hEN, hns⟩
    obtain ⟨z, hz, rfl⟩ := hz'
    have hEN' : EndNodeAt (Ã.map e.toMonoidHom) (e z) := hEN
    have hns' : ¬ LargeEvenSmall (layerC (e z)) := hns
    apply h
    refine ⟨z, hz, ?_, (endNodeAt_map_iff e Ã z).mp hEN', ?_⟩
    · intro h1
      exact hz1 (by change e z = 1; rw [h1, map_one])
    · rw [← layerC_map e z, largeEvenSmall_map_iff] at hns'
      exact hns'

theorem mem_layerC_iff (e : G ≃* G') (y g : G) : e g ∈ layerC (e y) ↔ g ∈ layerC y := by
  rw [← layerC_map e y]
  exact Subgroup.mem_map_iff_mem e.injective

theorem conclAt_of_map (e : G ≃* G') (Ã : Subgroup G) (y : G)
    (h : ConclAt (Ã.map e.toMonoidHom) (e y)) : ConclAt Ã y := by
  obtain ⟨U', hU1, hU2, hUl, hUA, t', htl, ht3, htA, htN, j', hjl, htj⟩ := h
  obtain ⟨t, rfl⟩ := e.surjective t'
  obtain ⟨j, rfl⟩ := e.surjective j'
  refine ⟨U'.comap e.toMonoidHom, ?_, hU2.comap_of_injective _ e.injective, ?_, ?_, t,
    (mem_layerC_iff e y t).mp htl, ?_, ?_, ?_, j, (mem_layerC_iff e y j).mp hjl, ?_⟩
  · intro hbot
    apply hU1
    rw [eq_bot_iff]
    intro g' hg'
    obtain ⟨g, rfl⟩ := e.surjective g'
    have h1 : g ∈ U'.comap e.toMonoidHom := hg'
    rw [hbot, Subgroup.mem_bot] at h1
    rw [h1, map_one]
    exact Subgroup.one_mem _
  · intro g hg
    exact (mem_layerC_iff e y g).mp (hUl hg)
  · intro s hs u hu
    have h1 := hUA (e s) (Subgroup.mem_map_of_mem _ hs) (e u) hu
    change e (s * u * s⁻¹) ∈ U'
    rw [map_mul, map_mul, map_inv]
    exact h1
  · apply e.injective
    rw [map_pow, ht3, map_one]
  · intro s hs
    have h1 := htA (e s) (Subgroup.mem_map_of_mem _ hs)
    apply e.injective
    rw [map_mul, map_mul]
    exact h1
  · rw [Subgroup.mem_normalizer_iff] at htN ⊢
    intro u
    have h1 := htN (e u)
    change e u ∈ U' ↔ e (t * u * t⁻¹) ∈ U'
    rw [map_mul, map_mul, map_inv]
    exact h1
  · intro hcomm
    apply htj
    have h1 := congrArg e hcomm
    rwa [map_mul, map_mul] at h1

end Transport

section Conj

variable {L : Type} [Group L]

theorem ggFix_conj (y : L) : ggFix (MulAut.conj y) = Subgroup.centralizer ({y} : Set L) := by
  ext g
  rw [mem_ggFix, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * y = (y * g * y⁻¹) * y := by rw [h]
      _ = y * g := by group
  · intro h
    calc y * g * y⁻¹ = (g * y) * y⁻¹ := by rw [h]
      _ = g := by group

theorem ggIsEndNode_conj_iff {A : Subgroup (MulAut L)}
    (hinn : ∀ a ∈ A, ∃ l : L, a = MulAut.conj l)
    (hinj : Function.Injective (MulAut.conj : L →* MulAut L)) (y : L) :
    GGIsEndNode A (MulAut.conj y) ↔
      y ∈ A.comap (MulAut.conj : L →* MulAut L) ∧ y ≠ 1 ∧
        EndNodeAt (A.comap (MulAut.conj : L →* MulAut L)) y := by
  have hlay : LargeEvenLayer (ggFix (MulAut.conj y)) = layerC y := by
    rw [ggFix_conj]
    rfl
  have hcent : ∀ s : L, (∀ j ∈ layerC y, MulAut.conj s j = j) ↔
      ∀ j ∈ layerC y, s * j = j * s := by
    intro s
    refine forall₂_congr fun j _ => ?_
    rw [MulAut.conj_apply]
    constructor
    · intro h
      calc s * j = (s * j * s⁻¹) * s := by group
        _ = j * s := by rw [h]
    · intro h
      calc s * j * s⁻¹ = (j * s) * s⁻¹ := by rw [h]
        _ = j := by group
  have hzp : ∀ s : L, MulAut.conj s ∈ Subgroup.zpowers (MulAut.conj y) ↔
      s ∈ Subgroup.zpowers y := by
    intro s
    constructor
    · intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, hinj (by rw [map_zpow]; exact hk)⟩
    · intro h
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [map_zpow]⟩
  unfold GGIsEndNode GGCentEnd EndNodeAt
  rw [hlay, ggFix_conj]
  constructor
  · rintro ⟨hyA, hy1, hcomp, hcentEnd⟩
    refine ⟨hyA, ?_, hcomp, ?_⟩
    · intro h
      apply hy1
      rw [h, map_one]
    · intro s hs
      have h1 := hcentEnd (MulAut.conj s) hs
      rw [hcent s, hzp s] at h1
      exact h1
  · rintro ⟨hyA, hy1, hcomp, hcentEnd⟩
    refine ⟨hyA, ?_, hcomp, ?_⟩
    · intro h
      apply hy1
      exact hinj (by rw [h, map_one])
    · intro a' ha'
      obtain ⟨s, rfl⟩ := hinn a' ha'
      rw [hcent s, hzp s]
      exact hcentEnd s ha'

theorem conclAt_to_ggConcl {A : Subgroup (MulAut L)}
    (hinn : ∀ a ∈ A, ∃ l : L, a = MulAut.conj l) (y : L)
    (h : ConclAt (A.comap (MulAut.conj : L →* MulAut L)) y) :
    GGStdSubTwoTorusConcl 3 A (MulAut.conj y) := by
  have hlay : LargeEvenLayer (ggFix (MulAut.conj y)) = layerC y := by
    rw [ggFix_conj]
    rfl
  obtain ⟨U, hU1, hU2, hUl, hUA, t, htl, ht3, htA, htN, j, hjl, htj⟩ := h
  rw [GGStdSubTwoTorusConcl, hlay]
  refine ⟨U, hU1, hU2, hUl, ?_, t, htl, ht3, ?_, htN, j, hjl, htj⟩
  · intro a' ha' u hu
    obtain ⟨s, rfl⟩ := hinn a' ha'
    have h1 := hUA s ha' u hu
    rwa [MulAut.conj_apply]
  · intro a' ha'
    obtain ⟨s, rfl⟩ := hinn a' ha'
    have h1 := htA s ha'
    rw [MulAut.conj_apply]
    calc s * t * s⁻¹ = (t * s) * s⁻¹ := by rw [h1]
      _ = t := by group

end Conj

end CFSG.StandardType.SpFour

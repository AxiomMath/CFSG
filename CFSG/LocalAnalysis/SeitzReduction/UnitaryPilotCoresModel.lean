module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignCores

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti
  le_centralizerPerfectCore normalizer_le_normalizer_centralizerPerfectCore
  map_centralizerPerfectCore)

section Transport

variable {G P : Type*} [Group G] [Group P] {L : Subgroup G} (e : L ≃* P)

@[expose] def modelToG (A : Subgroup P) : Subgroup G :=
  (A.map e.symm.toMonoidHom).map L.subtype

theorem modelToG_def (A : Subgroup P) :
    modelToG e A = (A.map e.symm.toMonoidHom).map L.subtype :=
  rfl

theorem mem_modelToG {A : Subgroup P} {g : G} :
    g ∈ modelToG e A ↔ ∃ x ∈ A, ((e.symm x : L) : G) = g := by
  simp only [modelToG, mem_map, MulEquiv.coe_toMonoidHom, coe_subtype]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

theorem symm_mem_modelToG {A : Subgroup P} {x : P} (hx : x ∈ A) :
    ((e.symm x : L) : G) ∈ modelToG e A :=
  (mem_modelToG e).2 ⟨x, hx, rfl⟩

theorem symm_mem_modelToG_iff {A : Subgroup P} {x : P} :
    ((e.symm x : L) : G) ∈ modelToG e A ↔ x ∈ A := by
  refine ⟨fun hx => ?_, symm_mem_modelToG e⟩
  obtain ⟨y, hy, hyx⟩ := (mem_modelToG e).1 hx
  rwa [← e.symm.injective (Subtype.ext hyx)]

theorem coe_mem_modelToG_iff {A : Subgroup P} {y : L} : (y : G) ∈ modelToG e A ↔ e y ∈ A := by
  rw [← symm_mem_modelToG_iff e, MulEquiv.symm_apply_apply]

theorem modelToG_mono {A B : Subgroup P} (h : A ≤ B) : modelToG e A ≤ modelToG e B :=
  map_mono (map_mono h)

theorem modelToG_le (A : Subgroup P) : modelToG e A ≤ L :=
  map_subtype_le _

theorem modelToG_top : modelToG e (⊤ : Subgroup P) = L := by
  rw [modelToG, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 e.symm.surjective,
    ← MonoidHom.range_eq_map, range_subtype]

@[simp]
theorem modelToG_bot : modelToG e (⊥ : Subgroup P) = ⊥ := by
  rw [modelToG, Subgroup.map_bot, Subgroup.map_bot]

theorem modelToG_injective : Function.Injective (modelToG (G := G) e) := by
  intro A B hAB
  ext x
  rw [← symm_mem_modelToG_iff e, hAB, symm_mem_modelToG_iff e]

theorem modelToG_le_modelToG_iff {A B : Subgroup P} : modelToG e A ≤ modelToG e B ↔ A ≤ B := by
  refine ⟨fun h x hx => ?_, modelToG_mono e⟩
  exact (symm_mem_modelToG_iff e).1 (h (symm_mem_modelToG e hx))

theorem modelToG_sup (A B : Subgroup P) :
    modelToG e (A ⊔ B) = modelToG e A ⊔ modelToG e B := by
  rw [modelToG, Subgroup.map_sup, Subgroup.map_sup]
  rfl

theorem modelToG_iSup {ι : Sort*} (A : ι → Subgroup P) :
    modelToG e (⨆ i, A i) = ⨆ i, modelToG e (A i) := by
  rw [modelToG, Subgroup.map_iSup, Subgroup.map_iSup]
  rfl

@[expose] noncomputable def modelToGEquiv (A : Subgroup P) : A ≃* modelToG e A :=
  (A.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
    ((A.map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective)

theorem coe_modelToGEquiv_apply (A : Subgroup P) (x : A) :
    ((modelToGEquiv e A x : modelToG e A) : G) = ((e.symm x : L) : G) :=
  rfl

theorem card_modelToG (A : Subgroup P) : Nat.card (modelToG e A) = Nat.card A :=
  (Nat.card_congr (modelToGEquiv e A).toEquiv).symm

theorem modelToG_le_centralizer {A B : Subgroup P} (h : A ≤ centralizer (B : Set P)) :
    modelToG e A ≤ centralizer (modelToG e B : Set G) := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hg
  rw [mem_centralizer_iff]
  intro g' hg'
  obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hg'
  rw [← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul, mem_centralizer_iff.1 (h hx) y hy]

theorem inf_centralizer_modelToG (A : Subgroup P) :
    L ⊓ centralizer (modelToG e A : Set G) = modelToG e (centralizer (A : Set P)) := by
  ext g
  constructor
  · rintro ⟨hgL, hgc⟩
    refine (mem_modelToG e).2 ⟨e ⟨g, hgL⟩, mem_centralizer_iff.2 fun a ha => ?_, by simp⟩
    have h := mem_centralizer_iff.1 hgc ((e.symm a : L) : G) (symm_mem_modelToG e ha)
    have h' : e.symm a * ⟨g, hgL⟩ = ⟨g, hgL⟩ * e.symm a := Subtype.ext h
    have := congrArg e h'
    simpa using this
  · intro hg
    obtain ⟨c, hc, rfl⟩ := (mem_modelToG e).1 hg
    refine ⟨(e.symm c).2, mem_centralizer_iff.2 fun g' hg' => ?_⟩
    obtain ⟨a, ha, rfl⟩ := (mem_modelToG e).1 hg'
    rw [← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul, mem_centralizer_iff.1 hc a ha]

theorem modelToG_commutator (A B : Subgroup P) :
    modelToG e ⁅A, B⁆ = ⁅modelToG e A, modelToG e B⁆ := by
  rw [modelToG, modelToG, modelToG, map_commutator, map_commutator]

theorem modelToG_perfect {A : Subgroup P} (hA : ⁅A, A⁆ = A) :
    ⁅modelToG e A, modelToG e A⁆ = modelToG e A := by
  rw [← modelToG_commutator, hA]

theorem mem_normalizer_modelToG_of_mem_centralizer {t : G} (ht : t ∈ centralizer (L : Set G))
    (A : Subgroup P) : t ∈ normalizer (modelToG e A : Set G) :=
  centralizer_le_normalizer _ (centralizer_le (SetLike.coe_subset_coe.2 (modelToG_le e A)) ht)

theorem modelToG_map_conj (A : Subgroup P) (x : P) :
    modelToG e (A.map (MulAut.conj x).toMonoidHom) =
      (modelToG e A).map (MulAut.conj ((e.symm x : L) : G)).toMonoidHom := by
  ext g
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [mem_modelToG]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨((e.symm y : L) : G), symm_mem_modelToG e hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv]
  · rintro ⟨_, hg, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hg
    refine ⟨x * y * x⁻¹, ⟨y, hy, rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv]

theorem symm_mem_normalizer_modelToG {A : Subgroup P} {x : P}
    (hx : x ∈ normalizer (A : Set P)) :
    ((e.symm x : L) : G) ∈ normalizer (modelToG e A : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hg
    refine (mem_modelToG e).2 ⟨x * y * x⁻¹, (mem_normalizer_iff.1 hx y).1 hy, ?_⟩
    rw [map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv]
  · intro hg
    obtain ⟨y, hy, hyg⟩ := (mem_modelToG e).1 hg
    have hy' : x⁻¹ * y * x ∈ A := by
      have := (mem_normalizer_iff.1 (inv_mem hx) y).1 hy
      simpa only [inv_inv] using this
    refine (mem_modelToG e).2 ⟨x⁻¹ * y * x, hy', ?_⟩
    rw [map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv, hyg]
    group

end Transport

section Cores

variable {G P : Type*} [Group G] [Group P] {L : Subgroup G} (e : L ≃* P)

theorem modelToG_le_centralizerPerfectCore {T A : Subgroup P}
    (hA : A ≤ centralizer (T : Set P)) (hperf : ⁅A, A⁆ = A) :
    modelToG e A ≤ centralizerPerfectCore (modelToG e T) :=
  le_centralizerPerfectCore (modelToG_perfect e hperf) (modelToG_le_centralizer e hA)

theorem mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer {t : G}
    (ht : t ∈ centralizer (L : Set G)) (T : Subgroup P) :
    t ∈ normalizer (centralizerPerfectCore (modelToG e T) : Set G) :=
  normalizer_le_normalizer_centralizerPerfectCore _
    (mem_normalizer_modelToG_of_mem_centralizer e ht T)

theorem symm_mem_normalizer_centralizerPerfectCore_modelToG {T : Subgroup P} {x : P}
    (hx : x ∈ normalizer (T : Set P)) :
    ((e.symm x : L) : G) ∈ normalizer (centralizerPerfectCore (modelToG e T) : Set G) :=
  normalizer_le_normalizer_centralizerPerfectCore _ (symm_mem_normalizer_modelToG e hx)

variable [Finite G]

theorem centralizerPerfectCore_modelToG_map_conj (T : Subgroup P) (x : P) :
    centralizerPerfectCore (modelToG e (T.map (MulAut.conj x).toMonoidHom)) =
      (centralizerPerfectCore (modelToG e T)).map
        (MulAut.conj ((e.symm x : L) : G)).toMonoidHom := by
  rw [modelToG_map_conj, map_centralizerPerfectCore]

theorem centralizerPerfectCore_modelToG_eq_perfectCore_inf {X : Subgroup G} {T : Subgroup P}
    (hX : X ≤ modelToG e T) :
    centralizerPerfectCore (modelToG e T) =
      perfectCore (centralizerPerfectCore X ⊓ centralizer (modelToG e T : Set G)) :=
  F4Pilot.centralizerPerfectCore_eq_of_le hX

theorem centralizerPerfectCore_modelToG_of_le {Y T : Subgroup P} (hYT : Y ≤ T) :
    centralizerPerfectCore (modelToG e T) =
      perfectCore (centralizerPerfectCore (modelToG e Y) ⊓ centralizer (modelToG e T : Set G)) :=
  centralizerPerfectCore_modelToG_eq_perfectCore_inf e (modelToG_mono e hYT)

theorem perfectCore_inf_centralizer_modelToG_eq {X X' : Subgroup G} {T : Subgroup P}
    (hX : X ≤ modelToG e T) (hX' : X' ≤ modelToG e T) :
    perfectCore (centralizerPerfectCore X ⊓ centralizer (modelToG e T : Set G)) =
      perfectCore (centralizerPerfectCore X' ⊓ centralizer (modelToG e T : Set G)) :=
  F4Pilot.perfectCore_neighbour_eq_of_le_of_le hX hX'

end Cores

end CFSG.SeitzReduction.UnitaryPilot

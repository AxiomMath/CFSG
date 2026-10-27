module

public import CFSG.Sporadic.SmallOddCore.J2Local
public import CFSG.Sporadic.SuzOddCore.CompQuot

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.LocalAnalysis.ComponentInitial

variable {M : Type*} [Group M]

theorem map_conj_centralizer (g : M) (S : Set M) :
    (centralizer S).map (MulAut.conj g).toMonoidHom =
      centralizer ((MulAut.conj g).toMonoidHom '' S) := by
  rw [map_centralizer_eq_inf (MulAut.conj g).injective,
    MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective, top_inf_eq]

theorem map_conj_self {H : Subgroup M} {g : M} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)
  · intro x hx
    refine ⟨g⁻¹ * x * g, H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem map_conj_inf_inf_centralizer {P : Subgroup M} {g : M} (hg : g ∈ P) (τ : M)
    (B : Subgroup M) :
    (P ⊓ centralizer ({τ} : Set M) ⊓ centralizer (B : Set M)).map (MulAut.conj g).toMonoidHom =
      P ⊓ centralizer ({g * τ * g⁻¹} : Set M) ⊓
        centralizer ((B.map (MulAut.conj g).toMonoidHom : Subgroup M) : Set M) := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective, map_conj_self hg, map_conj_centralizer,
    map_conj_centralizer, Set.image_singleton, Subgroup.coe_map]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem map_inf_centralizer_of_injective {T : Type*} [Group T] {f : T →* M}
    (hf : Function.Injective f) (t : T) (B : Subgroup T) :
    (centralizer ({t} : Set T) ⊓ centralizer (B : Set T)).map f =
      f.range ⊓ centralizer ({f t} : Set M) ⊓ centralizer ((B.map f : Subgroup M) : Set M) := by
  rw [Subgroup.map_inf _ _ _ hf, map_centralizer_eq_inf hf, map_centralizer_eq_inf hf,
    Set.image_singleton, Subgroup.coe_map]
  ext x
  simp only [mem_inf]
  tauto

theorem map_subtype_center (H : Subgroup M) :
    (center H).map H.subtype = H ⊓ centralizer (H : Set M) := by
  ext x
  simp only [mem_map, mem_inf, mem_center_iff, mem_centralizer_iff, coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun h hh => ?_⟩
    exact congrArg Subtype.val (hy ⟨h, hh⟩)
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, fun g => Subtype.ext (hc g g.2), rfl⟩

theorem card_inf_centralizer_self (H : Subgroup M) :
    Nat.card ↥(H ⊓ centralizer (H : Set M)) = Nat.card (center H) := by
  rw [← map_subtype_center, Subgroup.card_map_of_injective H.subtype_injective]

theorem isComponentOf_eq_of_isQuasisimple [Finite M] {B H : Subgroup M}
    (hB : CFSG.Assembly.IsComponentOf B H) (hH : CFSG.IsQuasisimple H) {p : ℕ} [Fact p.Prime]
    (hZ : IsPGroup p (center H)) : B = H := by
  have hc := (isComponentOf_iff_isComponent_subgroupOf hB.1).1 hB
  rcases quasisimple_subnormal_subgroups hH hc.2 with htop | hcen
  · apply le_antisymm hB.1
    intro x hx
    have : (⟨x, hx⟩ : ↥H) ∈ B.subgroupOf H := by rw [htop]; trivial
    exact mem_subgroupOf.mp this
  · exfalso
    exact CFSG.Sporadic.SuzOddCore.not_isComponent_of_le_pgroup hZ hcen hc

theorem card_local_of_reps {P : Subgroup M} (reps : Set M) {k : ℕ}
    (hcover : ∀ τ ∈ P, orderOf τ = 2 → ∃ r ∈ reps, ∃ g ∈ P, τ = g * r * g⁻¹)
    (hreps : ∀ r ∈ reps, ∀ B : Subgroup M,
      CFSG.Assembly.IsComponentOf B (P ⊓ centralizer ({r} : Set M)) →
        Nat.card ↥(P ⊓ centralizer ({r} : Set M) ⊓ centralizer (B : Set M)) = k)
    {τ : M} (hτP : τ ∈ P) (hτ : orderOf τ = 2) {B : Subgroup M}
    (hB : CFSG.Assembly.IsComponentOf B (P ⊓ centralizer ({τ} : Set M))) :
    Nat.card ↥(P ⊓ centralizer ({τ} : Set M) ⊓ centralizer (B : Set M)) = k := by
  obtain ⟨r, hr, g, hg, rfl⟩ := hcover τ hτP hτ
  have hfinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have hgr : g⁻¹ * (g * r * g⁻¹) * g⁻¹⁻¹ = r := by group
  have hBr : CFSG.Assembly.IsComponentOf (B.map (MulAut.conj g⁻¹).toMonoidHom)
      (P ⊓ centralizer ({r} : Set M)) := by
    have h := (isComponentOf_map_iff hfinj).2 hB
    rwa [Subgroup.map_inf _ _ _ hfinj, map_conj_self (P.inv_mem hg), map_conj_centralizer,
      Set.image_singleton, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hgr] at h
  have hmap := map_conj_inf_inf_centralizer (P.inv_mem hg) (g * r * g⁻¹) B
  rw [hgr] at hmap
  rw [← Subgroup.card_map_of_injective hfinj, hmap]
  exact hreps r hr _ hBr

theorem card_local_of_model {T : Type*} [Group T] {P : Subgroup M} (e : T ≃* P) {k : ℕ}
    (hP : ∀ τ ∈ P, orderOf τ = 2 → ∀ B : Subgroup M,
      CFSG.Assembly.IsComponentOf B (P ⊓ centralizer ({τ} : Set M)) →
        Nat.card ↥(P ⊓ centralizer ({τ} : Set M) ⊓ centralizer (B : Set M)) = k)
    {t : T} (ht : orderOf t = 2) {B : Subgroup T}
    (hB : CFSG.Assembly.IsComponentOf B (centralizer ({t} : Set T))) :
    Nat.card ↥(centralizer ({t} : Set T) ⊓ centralizer (B : Set T)) = k := by
  set ι : T →* M := P.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hrange : ι.range = P := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, ← MonoidHom.range_eq_map,
      range_subtype]
  have hτP : ι t ∈ P := hrange ▸ ⟨t, rfl⟩
  have hτ : orderOf (ι t) = 2 := by rw [orderOf_injective ι hι, ht]
  have hB' : CFSG.Assembly.IsComponentOf (B.map ι) (P ⊓ centralizer ({ι t} : Set M)) := by
    have := (isComponentOf_map_iff hι).2 hB
    rwa [map_centralizer_eq_inf hι, hrange, Set.image_singleton] at this
  rw [← Subgroup.card_map_of_injective hι, map_inf_centralizer_of_injective hι, hrange]
  exact hP _ hτP hτ _ hB'

theorem card_inf_centralizer_subgroupOf {C B : Subgroup M} (hBC : B ≤ C) :
    Nat.card ↥(C ⊓ centralizer (B : Set M)) =
      Nat.card ↥(centralizer ((B.subgroupOf C : Subgroup C) : Set C)) := by
  have h := map_centralizer_eq_inf C.subtype_injective ((B.subgroupOf C : Subgroup C) : Set C)
  rw [range_subtype, ← Subgroup.coe_map, map_subgroupOf_eq_of_le hBC] at h
  rw [← h, Subgroup.card_map_of_injective C.subtype_injective]

end CFSG.Sporadic.SmallOddCore

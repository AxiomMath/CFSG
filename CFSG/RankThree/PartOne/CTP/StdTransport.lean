module

public import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG

variable {G H : Type} [Group G] [Group H] (I : Subgroup G) (Ψ : ↥I →* H)

@[expose] def tr (X : Subgroup G) : Subgroup H := (X.subgroupOf I).map Ψ

variable {I Ψ}

theorem mem_tr_iff (hΨ : Function.Injective Ψ) {X : Subgroup G} (x : ↥I) :
    Ψ x ∈ tr I Ψ X ↔ (x : G) ∈ X := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := hΨ hyx
    subst this
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem tr_le_iff (hΨ : Function.Injective Ψ) {X Y : Subgroup G} (hX : X ≤ I) :
    tr I Ψ X ≤ tr I Ψ Y ↔ X ≤ Y := by
  constructor
  · intro h x hx
    have hxI := hX hx
    have := h (Subgroup.mem_map_of_mem Ψ (show (⟨x, hxI⟩ : ↥I) ∈ X.subgroupOf I from hx))
    exact (mem_tr_iff hΨ ⟨x, hxI⟩).mp this
  · intro h
    exact Subgroup.map_mono (fun x hx => h hx)

theorem tr_injective (hΨ : Function.Injective Ψ) {X Y : Subgroup G} (hX : X ≤ I) (hY : Y ≤ I)
    (h : tr I Ψ X = tr I Ψ Y) : X = Y :=
  le_antisymm ((tr_le_iff hΨ hX).mp h.le) ((tr_le_iff hΨ hY).mp h.ge)

theorem tr_mono {X Y : Subgroup G} (h : X ≤ Y) : tr I Ψ X ≤ tr I Ψ Y :=
  Subgroup.map_mono (fun _ hx => h hx)

theorem tr_inf (hΨ : Function.Injective Ψ) (X Y : Subgroup G) :
    tr I Ψ (X ⊓ Y) = tr I Ψ X ⊓ tr I Ψ Y := by
  unfold tr
  rw [← Subgroup.map_inf _ _ _ hΨ]
  rfl

theorem tr_sup {X Y : Subgroup G} (hX : X ≤ I) (hY : Y ≤ I) :
    tr I Ψ (X ⊔ Y) = tr I Ψ X ⊔ tr I Ψ Y := by
  unfold tr
  rw [← Subgroup.map_sup]
  congr 1
  exact (Subgroup.comap_sup_eq_of_le_range I.subtype (H := X) (K := Y)
    (by rw [Subgroup.range_subtype]; exact hX) (by rw [Subgroup.range_subtype]; exact hY)).symm

theorem tr_self : tr I Ψ I = Ψ.range := by
  unfold tr
  rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]

theorem tr_le_range {X : Subgroup G} (hX : X ≤ I) : tr I Ψ X ≤ Ψ.range := by
  rw [← tr_self]
  exact tr_mono hX

theorem tr_centralizer (hΨ : Function.Injective Ψ) {Y : Subgroup G} (hY : Y ≤ I) :
    tr I Ψ (I ⊓ Subgroup.centralizer (Y : Set G)) =
      Ψ.range ⊓ Subgroup.centralizer (tr I Ψ Y : Set H) := by
  ext h
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have hxc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp
      (show (x : G) ∈ I ⊓ Subgroup.centralizer (Y : Set G) from hx)).2 (y : G) hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using hxc)
  · rintro ⟨⟨x, rfl⟩, hc⟩
    refine ⟨x, ?_, rfl⟩
    refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp hc (Ψ ⟨y, hY hy⟩)
      ⟨⟨y, hY hy⟩, hy, rfl⟩
    rw [← map_mul, ← map_mul] at this
    have := hΨ this
    exact congrArg Subtype.val this

variable [Finite G] [Finite H]

theorem tr_residual (hΨ : Function.Injective Ψ) {X : Subgroup G} (hX : X ≤ I) :
    tr I Ψ (inSubgroup perfectResidual X) = inSubgroup perfectResidual (tr I Ψ X) := by
  have hI : Function.Injective I.subtype := Subtype.val_injective
  have hXI : (X.subgroupOf I).map I.subtype = X := Subgroup.map_subgroupOf_eq_of_le hX
  have h1 : (inSubgroup perfectResidual (X.subgroupOf I)).map I.subtype =
      inSubgroup perfectResidual X := by
    rw [CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _ hI,
      hXI]
  have h2 : (inSubgroup perfectResidual X).subgroupOf I =
      inSubgroup perfectResidual (X.subgroupOf I) := by
    rw [← h1]
    exact Subgroup.comap_map_eq_self_of_injective hI _
  unfold tr
  rw [h2, CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _ hΨ]

noncomputable def mulEquivTr (hΨ : Function.Injective Ψ) {X : Subgroup G} (hX : X ≤ I) :
    ↥X ≃* ↥(tr I Ψ X) :=
  (Subgroup.subgroupOfEquivOfLe hX).symm.trans (Subgroup.equivMapOfInjective _ Ψ hΨ)

end CFSG.RankThree.PartOne.CTP

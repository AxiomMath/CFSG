module

public import CFSG.Quasithin.Background.F918P1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

section QuotApi

variable {Y : Type} [CommGroup Y]

@[expose] noncomputable def v3qb_quotHomOn (Z : Subgroup Y) {H : Subgroup (MulAut Y)}
    (hH : H ≤ stabSub Z) : ↥H →* MulAut (Y ⧸ Z) :=
  (quotHom Z).comp (Subgroup.inclusion hH)

theorem v3qb_autQuot_eq_map {K H : Subgroup (MulAut Y)} {Z : Subgroup Y} (hKH : K ≤ H)
    (hH : H ≤ stabSub Z) : autQuot K Z = (K.subgroupOf H).map (v3qb_quotHomOn Z hH) := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, hg, rfl⟩ := mem_autQuot.mp hφ
    exact ⟨⟨(g : MulAut Y), hKH hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact mem_autQuot.mpr ⟨⟨(g : MulAut Y), hH g.2⟩, Subgroup.mem_subgroupOf.mp hg, rfl⟩

theorem v3qb_autQuot_sup {A B : Subgroup (MulAut Y)} {Z : Subgroup Y} (hA : A ≤ stabSub Z)
    (hB : B ≤ stabSub Z) : autQuot (A ⊔ B) Z = autQuot A Z ⊔ autQuot B Z := by
  have hAB : A ⊔ B ≤ stabSub Z := sup_le hA hB
  rw [v3qb_autQuot_eq_map le_rfl hAB, v3qb_autQuot_eq_map (le_sup_left : A ≤ A ⊔ B) hAB,
    v3qb_autQuot_eq_map (le_sup_right : B ≤ A ⊔ B) hAB, ← Subgroup.map_sup,
    ← Subgroup.subgroupOf_sup (le_sup_left : A ≤ A ⊔ B) (le_sup_right : B ≤ A ⊔ B)]

theorem v3qb_mk_mem_map_iff {Z U : Subgroup Y} {y : Y} :
    (QuotientGroup.mk y : Y ⧸ Z) ∈ U.map (QuotientGroup.mk' Z) ↔ ∃ u ∈ U, u * y⁻¹ ∈ Z := by
  rw [Subgroup.mem_map]
  refine exists_congr fun u => and_congr_right fun _ => ?_
  exact mk_eq_mk_iff u y

theorem v3qb_mem_stabSub_map {Z U : Subgroup Y} {g : MulAut Y} (hgZ : g ∈ stabSub Z)
    (hgU : g ∈ stabSub U) :
    quotHom Z ⟨g, hgZ⟩ ∈ stabSub (U.map (QuotientGroup.mk' Z)) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [quotHom_mk]
    simp only [v3qb_mk_mem_map_iff]
    constructor
    · rintro ⟨u, hu, h⟩
      refine ⟨g⁻¹ u, ((stabSub U).inv_mem hgU u).mpr hu, ?_⟩
      have e : g⁻¹ u * y⁻¹ = g⁻¹ (u * (g y)⁻¹) := by simp [map_mul, map_inv]
      rw [e]
      exact ((stabSub Z).inv_mem hgZ _).mpr h
    · rintro ⟨u, hu, h⟩
      refine ⟨g u, (hgU u).mpr hu, ?_⟩
      have e : g u * (g y)⁻¹ = g (u * y⁻¹) := by simp [map_mul, map_inv]
      rw [e]
      exact (hgZ _).mpr h

@[expose] noncomputable def v3qb_resQuot (Z U : Subgroup Y) :
    ↥(stabSub Z ⊓ stabSub U) →* MulAut ↥(U.map (QuotientGroup.mk' Z)) :=
  (resHom (U.map (QuotientGroup.mk' Z))).comp
    (((quotHom Z).comp (Subgroup.inclusion inf_le_left)).codRestrict
      (stabSub (U.map (QuotientGroup.mk' Z))) (fun g => v3qb_mem_stabSub_map g.2.1 g.2.2))

theorem v3qb_resQuot_apply {Z U : Subgroup Y} (g : ↥(stabSub Z ⊓ stabSub U)) {u : Y}
    (hu : u ∈ U) :
    ((v3qb_resQuot Z U g ⟨QuotientGroup.mk' Z u, Subgroup.mem_map_of_mem _ hu⟩ :
      ↥(U.map (QuotientGroup.mk' Z))) : Y ⧸ Z) = QuotientGroup.mk ((g : MulAut Y) u) := rfl

theorem v3qb_exists_mk {Z U : Subgroup Y} (x : ↥(U.map (QuotientGroup.mk' Z))) :
    ∃ (u : Y) (hu : u ∈ U), x = ⟨QuotientGroup.mk' Z u, Subgroup.mem_map_of_mem _ hu⟩ := by
  obtain ⟨u, hu, hx⟩ := x.2
  exact ⟨u, hu, Subtype.ext hx.symm⟩

theorem v3qb_resQuot_eq_one_iff {Z U : Subgroup Y} (g : ↥(stabSub Z ⊓ stabSub U)) :
    v3qb_resQuot Z U g = 1 ↔ ∀ u ∈ U, (g : MulAut Y) u * u⁻¹ ∈ Z := by
  constructor
  · intro h u hu
    have h1 := congrArg (fun φ : MulAut ↥(U.map (QuotientGroup.mk' Z)) =>
      ((φ ⟨QuotientGroup.mk' Z u, Subgroup.mem_map_of_mem _ hu⟩ :
        ↥(U.map (QuotientGroup.mk' Z))) : Y ⧸ Z)) h
    simp only [v3qb_resQuot_apply g hu, MulAut.one_apply] at h1
    exact (mk_eq_mk_iff _ _).1 h1
  · intro h
    refine MulEquiv.ext fun x => ?_
    obtain ⟨u, hu, rfl⟩ := v3qb_exists_mk x
    refine Subtype.ext ?_
    rw [v3qb_resQuot_apply g hu, MulAut.one_apply]
    exact (mk_eq_mk_iff _ _).2 (h u hu)

theorem v3qb_autSub_autQuot {Z U : Subgroup Y} {H : Subgroup (MulAut Y)} (hHZ : H ≤ stabSub Z)
    (hHU : H ≤ stabSub U) :
    autSub (autQuot H Z) (U.map (QuotientGroup.mk' Z)) =
      ((v3qb_resQuot Z U).comp (Subgroup.inclusion (le_inf hHZ hHU))).range := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, hgmem, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨x, hxH, hx⟩ := mem_autQuot.mp hgmem
    exact ⟨⟨(x : MulAut Y), hxH⟩, congrArg (resHom (U.map (QuotientGroup.mk' Z)))
      (Subtype.ext hx)⟩
  · rintro ⟨x, rfl⟩
    exact mem_autSub.mpr ⟨⟨quotHom Z ⟨x, hHZ x.2⟩, v3qb_mem_stabSub_map (hHZ x.2) (hHU x.2)⟩,
      mem_autQuot.mpr ⟨⟨x, hHZ x.2⟩, x.2, rfl⟩, rfl⟩

end QuotApi

section Orbits

variable {Y : Type} [CommGroup Y]

theorem v3qb_orbSup_map {Z V : Subgroup Y} {S : Subgroup (MulAut Y)} (hSZ : S ≤ stabSub Z) :
    orbSup (autQuot S Z) (V.map (QuotientGroup.mk' Z)) =
      (orbSup S V).map (QuotientGroup.mk' Z) := by
  apply le_antisymm
  · refine orbSup_le fun t ht => ?_
    obtain ⟨s, hsS, rfl⟩ := mem_autQuot.mp ht
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨(s : MulAut Y) v, map_le_orbSup hsS ⟨v, hv, rfl⟩, rfl⟩
  · rw [orbSup, Subgroup.map_iSup]
    refine iSup_le fun s => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hs => ?_
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact map_le_orbSup (mem_autQuot.mpr ⟨⟨s, hSZ hs⟩, hs, rfl⟩)
      ⟨QuotientGroup.mk' Z v, ⟨v, hv, rfl⟩, rfl⟩

theorem v3qb_invariant_orbSup {V : Subgroup Y} {Λ S : Subgroup (MulAut Y)}
    (hSN : S ≤ Subgroup.normalizer (Λ : Set (MulAut Y))) (hV : ∀ x ∈ Λ, ∀ w ∈ V, x w ∈ V) :
    ∀ x ∈ Λ, ∀ w ∈ orbSup S V, x w ∈ orbSup S V := by
  intro x hx w hw
  have key : orbSup S V ≤ (orbSup S V).comap x.toMonoidHom := by
    refine orbSup_le fun s hs => ?_
    rintro _ ⟨v, hv, rfl⟩
    have hx' : s⁻¹ * x * s ∈ Λ := (Subgroup.mem_normalizer_iff''.mp (hSN hs) x).mp hx
    have h1 : x (s v) = s ((s⁻¹ * x * s) v) := by simp [MulAut.mul_apply]
    show x (s v) ∈ orbSup S V
    rw [h1]
    exact map_le_orbSup hs ⟨_, hV _ hx' v hv, rfl⟩
  exact key hw

end Orbits

end CFSG.Quasithin

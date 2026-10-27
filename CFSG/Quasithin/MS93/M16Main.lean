module

public import CFSG.Quasithin.MS93.M16Pt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin Matrix

variable {F : Type} [Field F] {V : Type*} [CommGroup V]

namespace M16

section Quot

variable {ρ : SL3 F →* MulAut V} {Z : Subgroup V} (hZ : ∀ g : SL3 F, ∀ z ∈ Z, ρ g z ∈ Z)
include hZ

theorem map_mk_map_rho (A : Subgroup V) (g : SL3 F) :
    (A.map (ρ g).toMonoidHom).map (QuotientGroup.mk' Z) =
      (A.map (QuotientGroup.mk' Z)).map (quotAct ρ Z hZ g).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem map_mk_wOff (W₀ : Subgroup V) :
    (wOff ρ W₀).map (QuotientGroup.mk' Z) =
      wOff (quotAct ρ Z hZ) (W₀.map (QuotientGroup.mk' Z)) := by
  unfold wOff
  rw [Subgroup.map_iSup]
  refine iSup_congr fun g => ?_
  rw [Subgroup.map_iSup]
  refine iSup_congr fun _ => ?_
  exact map_mk_map_rho hZ W₀ g

theorem map_mk_submoduleClosure (A : Subgroup V) :
    (G6.submoduleClosure ρ.range A).map (QuotientGroup.mk' Z) =
      G6.submoduleClosure (quotAct ρ Z hZ).range (A.map (QuotientGroup.mk' Z)) := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap, submoduleClosure_le_iff]
    intro g
    rw [← Subgroup.map_le_iff_le_comap, map_mk_map_rho hZ]
    exact map_le_submoduleClosure _ g
  · rw [submoduleClosure_le_iff]
    intro g
    rw [← map_mk_map_rho hZ]
    exact Subgroup.map_mono (map_le_submoduleClosure _ g)

theorem map_mk_commOn (X : Subgroup (SL3 F)) (A : Subgroup V) :
    (G6.commOn (X.map ρ) A).map (QuotientGroup.mk' Z) =
      G6.commOn (X.map (quotAct ρ Z hZ)) (A.map (QuotientGroup.mk' Z)) := by
  unfold G6.commOn
  rw [MonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, a, ha, rfl⟩, rfl⟩
    exact ⟨quotAct ρ Z hZ x, ⟨x, hx, rfl⟩, QuotientGroup.mk' Z a, ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨ρ x a * a⁻¹, ⟨ρ x, ⟨x, hx, rfl⟩, a, ha, rfl⟩, rfl⟩

theorem map_mk_commV :
    (commV ρ.range).map (QuotientGroup.mk' Z) = commV (quotAct ρ Z hZ).range := by
  unfold commV
  rw [MonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨_, ⟨_, ⟨g, rfl⟩, v, rfl⟩, rfl⟩
    exact ⟨quotAct ρ Z hZ g, ⟨g, rfl⟩, QuotientGroup.mk' Z v, rfl⟩
  · rintro ⟨_, ⟨g, rfl⟩, v, rfl⟩
    induction v using QuotientGroup.induction_on with
    | H v => exact ⟨ρ g v * v⁻¹, ⟨ρ g, ⟨g, rfl⟩, v, rfl⟩, rfl⟩

omit hZ in
theorem fixV_quotAct_eq_bot :
    fixV (quotAct ρ (fixV ρ.range) (fun g _ hz => rho_mem_fixV ρ g hz)).range = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H v =>
    rw [mem_fixV_range] at hx
    have hcomm : ∀ g : SL3 F, ρ g v * v⁻¹ ∈ fixV ρ.range := by
      intro g
      have h := hx g
      change (QuotientGroup.mk (ρ g v) : V ⧸ fixV ρ.range) = QuotientGroup.mk v at h
      rw [QuotientGroup.eq] at h
      have := Subgroup.inv_mem _ h
      rwa [_root_.mul_inv_rev, inv_inv, mul_comm] at this
    have hv : v ∈ fixV ρ.range := by
      rw [mem_fixV_range]
      exact fix_of_comm_fix ρ v fun g k => (mem_fixV_range.mp (hcomm k)) g
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
    exact hv

end Quot

theorem card_map_le' {G H : Type*} [Group G] [Group H] [Finite G] (K : Subgroup G)
    (f : G →* H) : Nat.card ↥(K.map f) ≤ Nat.card K :=
  Nat.card_le_card_of_surjective _ (f.subgroupMap_surjective K)

theorem commOn_le_of_sup_fixV {ρ : SL3 F →* MulAut V} {X : Subgroup (SL3 F)} {A B : Subgroup V}
    (hAB : A ≤ B ⊔ fixV ρ.range) : G6.commOn (X.map ρ) A ≤ G6.commOn (X.map ρ) B := by
  rw [G6.commOn_le_iff]
  rintro _ ⟨x, hx, rfl⟩ a ha
  obtain ⟨b, hb, z, hz, rfl⟩ := Subgroup.mem_sup.mp (hAB ha)
  have hzfix : ρ x z = z := (mem_fixV_range.mp hz) x
  have he : ρ x (b * z) * (b * z)⁻¹ = ρ x b * b⁻¹ := by
    rw [map_mul, hzfix]
    group
  change ρ x (b * z) * (b * z)⁻¹ ∈ _
  rw [he]
  exact G6.mem_commOn_of_mem (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩) hb

theorem sup_eq_top_of_map_mk {Z A : Subgroup V} (h : A.map (QuotientGroup.mk' Z) = ⊤) :
    A ⊔ Z = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨a, ha, hav⟩ := (h ▸ Subgroup.mem_top (QuotientGroup.mk' Z v) :
    QuotientGroup.mk' Z v ∈ A.map (QuotientGroup.mk' Z))
  have hz : a⁻¹ * v ∈ Z := QuotientGroup.eq.mp hav
  rw [show v = a * (a⁻¹ * v) by group]
  exact Subgroup.mul_mem_sup ha hz

end M16

end CFSG.Quasithin.MS93

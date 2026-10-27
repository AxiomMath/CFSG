module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G]

theorem s16h_centSub_sup_eq {W : Type*} [CommGroup W] (U U' : Subgroup W) :
    centSub (U ⊔ U') = centSub U ⊓ centSub U' := by
  ext g
  rw [mem_centSub, Subgroup.mem_inf, mem_centSub, mem_centSub]
  exact ⟨fun h => ⟨fun u hu => h u (Subgroup.mem_sup_left hu),
      fun u hu => h u (Subgroup.mem_sup_right hu)⟩,
    fun h u hu => by
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu
      rw [map_mul, h.1 a ha, h.2 b hb]⟩

theorem s16h_imgTil_preTil_inf (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (S T : Subgroup (Vtil V₀ V hV)) :
    imgTil V₀ V hV (preTil V₀ V hV S ⊓ preTil V₀ V hV T) = S ⊓ T := by
  ext q
  rw [Subgroup.mem_inf, mem_imgTil]
  constructor
  · rintro ⟨x, ⟨hxS, hxT⟩, rfl⟩
    constructor
    · obtain ⟨y, hy, hyS⟩ := (mem_preTil V₀ V hV S).1 hxS
      rwa [IntMod.val_injective hy] at hyS
    · obtain ⟨y, hy, hyT⟩ := (mem_preTil V₀ V hV T).1 hxT
      rwa [IntMod.val_injective hy] at hyT
  · rintro ⟨hS, hT⟩
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV q
    exact ⟨x, ⟨(mem_preTil V₀ V hV S).2 ⟨x, rfl, hS⟩,
      (mem_preTil V₀ V hV T).2 ⟨x, rfl, hT⟩⟩, rfl⟩

theorem s16h_imgTil_bot (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    imgTil V₀ V hV ⊥ = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨x, hx, rfl⟩ := (mem_imgTil V₀ V hV ⊥ q).1 hq
  rw [Subgroup.mem_bot]
  have hx' : x = 1 := by
    apply IntMod.val_injective
    rw [IntMod.val_one]
    exact Subgroup.mem_bot.1 hx
  rw [hx', map_one]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.Quasithin.EmptyFaithful.S1417Setup

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S1417

open scoped commutatorElement

section Glue

variable {G : Type} [Group G] {V : Subgroup G}

theorem inclMod_injective (hV : IsElemAbelian 2 V) : Function.Injective (inclMod hV) :=
  fun _ _ h => IntMod.val_injective h

theorem map_inclMod_top (hV : IsElemAbelian 2 V) : (⊤ : Subgroup (IntMod V hV)).map (inclMod hV) = V := by
  ext x
  constructor
  · rintro ⟨u, -, rfl⟩
    exact IntMod.val_mem u
  · intro hx
    exact ⟨IntMod.mk hV ⟨x, hx⟩, Subgroup.mem_top _, rfl⟩

theorem inclMod_apply (hV : IsElemAbelian 2 V) (u : IntMod V hV) : inclMod hV u = u.val := rfl

theorem commutator_eq_map_commV (hV : IsElemAbelian 2 V) {Y : Subgroup G}
    (hYN : Y ≤ Subgroup.normalizer (V : Set G)) :
    ⁅V, Y⁆ = (commV (autI hV Y)).map (inclMod hV) := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv y hy
    have hyN : y ∈ Subgroup.normalizer (V : Set G) := hYN hy
    set w₀ : IntMod V hV := IntMod.mk hV ⟨v, hv⟩ with hw₀
    have hx : convI hV ⟨y, hyN⟩ ∈ autI hV Y := convI_mem_autI hV hy hyN
    refine ⟨convI hV ⟨y, hyN⟩ w₀⁻¹ * w₀, Subgroup.subset_closure ⟨_, hx, w₀⁻¹, by simp⟩, ?_⟩
    have h1 : (convI hV ⟨y, hyN⟩ w₀⁻¹).val = y * v⁻¹ * y⁻¹ :=
      convI_apply_val hV ⟨y, hyN⟩ w₀⁻¹
    have h2 : w₀.val = v := rfl
    have hcomm : (convI hV ⟨y, hyN⟩ w₀⁻¹).val * v = v * (convI hV ⟨y, hyN⟩ w₀⁻¹).val :=
      IntMod.val_comm _ w₀
    show (convI hV ⟨y, hyN⟩ w₀⁻¹ * w₀).val = ⁅v, y⁆
    rw [IntMod.val_mul, h2, hcomm, h1, commutatorElement_def]
    group
  · rw [Subgroup.map_le_iff_le_comap, commV, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, rfl⟩
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hx
    have h1 : (convI hV g w).val = (g : G) * w.val * (g : G)⁻¹ := convI_apply_val hV g w
    show inclMod hV (convI hV g w * w⁻¹) ∈ ⁅V, Y⁆
    rw [inclMod_apply, IntMod.val_mul, h1, IntMod.val_inv]
    have : (g : G) * w.val * (g : G)⁻¹ * w.val⁻¹ = ⁅(g : G), w.val⁆ := by
      rw [commutatorElement_def]
    rw [this, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hg w.val_mem

end Glue

end S1417

end CFSG.Quasithin

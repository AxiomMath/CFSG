module

public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSL2
public import CFSG.Quasithin.Background.B2FactorizationBridge

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

@[expose] noncomputable def valHom : IntMod V hV →* G where
  toFun := IntMod.val
  map_one' := IntMod.val_one
  map_mul' := IntMod.val_mul

theorem valHom_injective : Function.Injective (valHom hV) := IntMod.val_injective

@[expose] noncomputable def toG (W : Subgroup (IntMod V hV)) : Subgroup G := W.map (valHom hV)

theorem mem_toG {W : Subgroup (IntMod V hV)} {g : G} : g ∈ toG hV W ↔ ∃ w ∈ W, w.val = g := by
  unfold toG
  simp only [Subgroup.mem_map]
  exact Iff.rfl

theorem toG_le (W : Subgroup (IntMod V hV)) : toG hV W ≤ V := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := (mem_toG hV).1 hg
  exact w.val_mem

theorem toG_le_iff {W W' : Subgroup (IntMod V hV)} : toG hV W ≤ toG hV W' ↔ W ≤ W' :=
  Subgroup.map_le_map_iff_of_injective (valHom_injective hV)

theorem toG_inj {W W' : Subgroup (IntMod V hV)} : toG hV W = toG hV W' ↔ W = W' :=
  (Subgroup.map_injective (valHom_injective hV)).eq_iff

theorem mem_toG_iff_of_mem {W : Subgroup (IntMod V hV)} (w : IntMod V hV) :
    w.val ∈ toG hV W ↔ w ∈ W := by
  rw [mem_toG]
  constructor
  · rintro ⟨w', hw', h⟩
    rwa [← IntMod.val_injective h]
  · exact fun h => ⟨w, h, rfl⟩

variable {K : Subgroup G} (hK : K ≤ Subgroup.normalizer (V : Set G))

include hK

theorem isInv_iff {W : Subgroup (IntMod V hV)} :
    XMod.IsInv ↥(autI hV K) W ↔ ∀ g ∈ K, ∀ w ∈ toG hV W, g * w * g⁻¹ ∈ toG hV W := by
  constructor
  · intro h g hg w hw
    obtain ⟨u, hu, rfl⟩ := (mem_toG hV).1 hw
    have this := h ⟨convI hV ⟨g, hK hg⟩, convI_mem_autI hV hg (hK hg)⟩ u hu
    have this' : ((convI hV ⟨g, hK hg⟩ u : IntMod V hV)).val ∈ toG hV W :=
      (mem_toG_iff_of_mem hV _).2 this
    have e : ((convI hV ⟨g, hK hg⟩ u : IntMod V hV)).val = g * u.val * g⁻¹ :=
      convI_apply_val hV ⟨g, hK hg⟩ u
    rwa [e] at this'
  · intro h a u hu
    obtain ⟨g, hgK, hga⟩ := (mem_autI hV).1 a.2
    have e : (a • u : IntMod V hV).val = g * u.val * (g : G)⁻¹ := by
      show ((a : MulAut (IntMod V hV)) u).val = _
      rw [← hga]
      exact convI_apply_val hV g u
    rw [← mem_toG_iff_of_mem hV, e]
    exact h g hgK u.val ((mem_toG_iff_of_mem hV u).2 hu)

theorem mem_fixed_iff {W : Subgroup (IntMod V hV)} {w : IntMod V hV} :
    w ∈ XMod.fixed ↥(autI hV K) W ↔ w ∈ W ∧ ∀ g ∈ K, g * w.val * g⁻¹ = w.val := by
  constructor
  · rintro ⟨hw, h⟩
    refine ⟨hw, fun g hg => ?_⟩
    have := h ⟨convI hV ⟨g, hK hg⟩, convI_mem_autI hV hg (hK hg)⟩
    have e := congrArg IntMod.val this
    rwa [show (⟨convI hV ⟨g, hK hg⟩, _⟩ : ↥(autI hV K)) • w =
      convI hV ⟨g, hK hg⟩ w from rfl, convI_apply_val hV] at e
  · rintro ⟨hw, h⟩
    refine ⟨hw, fun a => ?_⟩
    obtain ⟨g, hgK, hga⟩ := (mem_autI hV).1 a.2
    apply IntMod.val_injective
    show ((a : MulAut (IntMod V hV)) w).val = w.val
    rw [← hga, convI_apply_val hV]
    exact h g hgK

theorem toG_fixed {W : Subgroup (IntMod V hV)} :
    toG hV (XMod.fixed ↥(autI hV K) W) = toG hV W ⊓ Subgroup.centralizer (K : Set G) := by
  ext g
  constructor
  · intro hg
    obtain ⟨w, hw, rfl⟩ := (mem_toG hV).1 hg
    obtain ⟨hwW, hwf⟩ := (mem_fixed_iff hV hK).1 hw
    refine ⟨(mem_toG hV).2 ⟨w, hwW, rfl⟩, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
    have := hwf k hk
    calc k * w.val = (k * w.val * k⁻¹) * k := by group
      _ = w.val * k := by rw [this]
  · rintro ⟨hg1, hg2⟩
    obtain ⟨w, hwW, rfl⟩ := (mem_toG hV).1 hg1
    refine (mem_toG hV).2 ⟨w, (mem_fixed_iff hV hK).2 ⟨hwW, fun k hk => ?_⟩, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hg2 k hk
    rw [this]
    group

theorem toG_commV : toG hV (commV (autI hV K)) = ⁅K, V⁆ := by
  unfold commV toG
  rw [MonoidHom.map_closure, Subgroup.commutator_def]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨x, hx, v, rfl⟩, rfl⟩
    obtain ⟨k, hkK, hkx⟩ := (mem_autI hV).1 hx
    refine ⟨k, hkK, v.val, v.val_mem, ?_⟩
    simp only [valHom, MonoidHom.coe_mk, OneHom.coe_mk, IntMod.val_mul]
    rw [← hkx, convI_apply_val hV]
    simp [commutatorElement_def]
  · rintro ⟨k, hkK, v, hv, rfl⟩
    refine ⟨_, ⟨convI hV ⟨k, hK hkK⟩, convI_mem_autI hV hkK (hK hkK), IntMod.mk hV ⟨v, hv⟩,
      rfl⟩, ?_⟩
    simp only [valHom, MonoidHom.coe_mk, OneHom.coe_mk, IntMod.val_mul, IntMod.val_inv]
    rw [convI_apply_val hV]
    simp [commutatorElement_def, IntMod.mk]
    rfl

end CFSG.Quasithin.C124

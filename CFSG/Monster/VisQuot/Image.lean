module

public import CFSG.Monster.VisQuot.Stabilizer
public import CFSG.Monster.VisCert.FrameOrbit
public import CFSG.Monster.Visible.Kernel

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisQuot

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Lifts CFSG.Monster.Visible CFSG.Monster.VisCert CFSG.Monster.Spin

@[expose] def OLvis : Subgroup GLV := modTwoHom.range.unop

theorem mem_OLvis {u : GLV} : u ∈ OLvis ↔ ∃ g : latticeO, modTwoUnit g = u := by
  rw [OLvis, Subgroup.mem_unop, MonoidHom.mem_range]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, MulOpposite.op_injective hg⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, rfl⟩

theorem range_actQ : actQ.range = modTwoHom.range := by
  ext x
  rw [MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    induction y using QuotientGroup.induction_on with
    | H g => exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨QuotientGroup.mk g, rfl⟩

theorem Hvis_le_OLvis : Hvis ≤ OLvis := fun _ hu => by
  obtain ⟨g, -, rfl⟩ := mem_Hvis.1 hu
  exact mem_OLvis.2 ⟨g, rfl⟩

theorem modTwoUnit_mem_Kvis
    (g : latticeO) : modTwoUnit g ∈ Kvis := by
  have hf : modTwoEnd g twoΩCls ∈ frameDelta :=
    (modTwoEnd_mem_frameDelta_iff g).2 twoΩCls_mem_frameDelta
  obtain ⟨k, hk, hkf⟩ := exists_Kvis_smul_twoΩCls hf
  obtain ⟨g', -, rfl⟩ := mem_Hvis.1 (Kvis_le_Hvis hk)
  have hkf' : modTwoEnd g' twoΩCls = modTwoEnd g twoΩCls := hkf
  have hfix : modTwoEnd (g * g'⁻¹) twoΩCls = twoΩCls := by
    rw [modTwoEnd_mul, Module.End.mul_apply, ← hkf', modTwoEnd_inv_apply]
  have hN : modTwoUnit (g * g'⁻¹) ∈ Nvis :=
    Nvis_eq_range_monoHom ▸ (modTwoEnd_twoΩCls_eq_iff _).1 hfix
  have e : modTwoUnit g = modTwoUnit g' * modTwoUnit (g * g'⁻¹) := by
    rw [← modTwoUnit_mul, inv_mul_cancel_right]
  rw [e]
  exact Kvis.mul_mem hk (Nvis_le_Kvis hN)

theorem Kvis_eq_OLvis :
    Kvis = OLvis :=
  le_antisymm (Kvis_le_Hvis.trans Hvis_le_OLvis) fun _ hu => by
    obtain ⟨g, rfl⟩ := mem_OLvis.1 hu
    exact modTwoUnit_mem_Kvis g

theorem Hvis_eq_Kvis : Hvis = Kvis :=
  le_antisymm (Hvis_le_OLvis.trans Kvis_eq_OLvis.ge) Kvis_le_Hvis

theorem Hvis_eq_OLvis :
    Hvis = OLvis := Hvis_eq_Kvis.trans Kvis_eq_OLvis

theorem modTwoUnit_mem_Hvis'
    (g : latticeO) : modTwoUnit g ∈ Hvis :=
  Hvis_eq_Kvis ▸ modTwoUnit_mem_Kvis g

theorem exists_mem_Pvis
    (g : latticeO) : ∃ s, (s, g) ∈ Pvis := by
  obtain ⟨g', hg', hgg'⟩ := mem_Hvis.1 (modTwoUnit_mem_Hvis' g)
  obtain ⟨s, hs⟩ := mem_PvisLat.1 hg'
  rcases (modTwoUnit_eq_modTwoUnit_iff g' g).1 hgg' with rfl | rfl
  · exact ⟨s, hs⟩
  · refine ⟨zU * s, ?_⟩
    have h := Pvis.mul_mem negPair.2 hs
    have e : negOneO * (negOneO * g) = g := by rw [← mul_assoc, negOneO_mul_self, one_mul]
    rw [coe_negPair, Prod.mk_mul_mk, e] at h
    exact h

theorem PvisLat_eq_top :
    PvisLat = ⊤ :=
  eq_top_iff.2 fun g _ => mem_PvisLat.2 (exists_mem_Pvis g)

theorem range_piVis_unop :
    piVis.range.unop = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  induction x using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨s, hs⟩ := exists_mem_Pvis g
    exact mem_unop_range_piVis.2 ⟨⟨(s, g), hs⟩, rfl⟩

theorem closure_frameGen_eq_top :
    Subgroup.closure (Set.range fun j : Fin 15 => (QuotientGroup.mk (frameGen j) : OLq)) = ⊤ := by
  apply Subgroup.map_injective actQ_injective
  rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map, range_actQ]
  have e : Set.range (⇑actQ ∘ fun j : Fin 15 => (QuotientGroup.mk (frameGen j) : OLq)) =
      MulOpposite.unop ⁻¹' Set.range kGen := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, by
        show MulOpposite.op (kGen j) = x
        rw [hj, MulOpposite.op_unop]⟩
  rw [e, ← Subgroup.op_closure]
  show Kvis.op = modTwoHom.range
  rw [Kvis_eq_OLvis, OLvis, Subgroup.op_unop]

theorem eq_one_of_forall_frameDelta {u : GLV} (hu : ∀ x ∈ frameDelta, u • x = x) : u = 1 := by
  let W : Submodule (ZMod 2) L2 := LinearMap.ker ((u : Module.End (ZMod 2) L2) - 1)
  have hspan : Submodule.span (ZMod 2) {x : L2 | ∃ p : Pvis, modTwoEnd p.1.2 twoΩCls = x} ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    have hx : modTwoEnd p.1.2 twoΩCls ∈ frameDelta :=
      (modTwoEnd_mem_frameDelta_iff _).2 twoΩCls_mem_frameDelta
    show ((u : Module.End (ZMod 2) L2) - 1) (modTwoEnd p.1.2 twoΩCls) = 0
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    exact hu _ hx
  rw [span_orbit_twoΩCls, top_le_iff] at hspan
  refine Units.ext (LinearMap.ext fun x => ?_)
  have hx : x ∈ W := hspan ▸ Submodule.mem_top
  have := LinearMap.mem_ker.1 hx
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
  exact this

theorem eq_one_of_forall_frameDelta_actQ {x : OLq}
    (hx : ∀ v ∈ frameDelta, (actQ x).unop • v = v) : x = 1 := by
  have h := eq_one_of_forall_frameDelta hx
  apply actQ_injective
  rw [map_one, ← MulOpposite.op_unop (actQ x), h, MulOpposite.op_one]

theorem visible_full_lattice_image_and_generation :
    Hvis = Kvis ∧ Kvis = OLvis ∧ (∀ u : GLV, u ∈ OLvis ↔ ∃ g : latticeO, modTwoUnit g = u) ∧
    Function.Injective actQ ∧ piVis.range.unop = ⊤ ∧
    PvisLat = ⊤ ∧ (∀ g : latticeO, ∃ s, (s, g) ∈ Pvis) ∧
    Subgroup.closure (Set.range fun j : Fin 15 => (QuotientGroup.mk (frameGen j) : OLq)) = ⊤ ∧
    (∀ (g : latticeO) (x : L2), modTwoEnd g x ∈ frameDelta ↔ x ∈ frameDelta) ∧
    (∀ x ∈ frameDelta, ∀ y ∈ frameDelta, ∃ k ∈ Kvis, k • x = y) ∧
    (∀ u ∈ Kvis, (∀ x ∈ frameDelta, u • x = x) → u = 1) ∧
    (∀ x : OLq, (∀ v ∈ frameDelta, (actQ x).unop • v = v) → x = 1) :=
  ⟨Hvis_eq_Kvis, Kvis_eq_OLvis, fun _ => mem_OLvis, actQ_injective, range_piVis_unop,
    PvisLat_eq_top, exists_mem_Pvis, closure_frameGen_eq_top,
    fun g _ => modTwoEnd_mem_frameDelta_iff g, fun _ hx _ hy => exists_Kvis_smul_eq hx hy,
    fun _ _ h => eq_one_of_forall_frameDelta h, fun _ h => eq_one_of_forall_frameDelta_actQ h⟩

end CFSG.Monster.VisQuot

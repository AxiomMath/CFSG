module

public import CFSG.Monster.B.TwoA.Fischer.AmbientRootHyp
public import CFSG.Monster.B.TwoA.Amalgam.GlobalTypeCore
public import CFSG.Monster.B.TwoA.Amalgam.FischerSliceNative

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.Monster.B.E6 CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension

section Local

variable {v w : CVert} {ρv : vStab v →* GStar} {iv : cgraph.neighborSet v ≃ rootClass}
  (hlab : ∀ (z : cgraph.neighborSet v) (y : vStab v), ((y : Shat) : Dfull) = clabel z →
    ρv y = SemidirectProduct.inl (iv z : stdGroup))
  (hex : ∀ z : cgraph.neighborSet v, ∃ y : vStab v, ((y : Shat) : Dfull) = clabel z)

include hex in
theorem labelS_mem_vStab (z : cgraph.neighborSet v) : clabelS z ∈ vStab v := by
  obtain ⟨y, hy⟩ := hex z
  have e : (y : Shat) = clabelS z := Subtype.ext (by rw [hy, coe_clabelS])
  rw [← e]
  exact y.2

include hlab hex in
theorem rho_labelS_eq (z : cgraph.neighborSet v) :
    ρv ⟨clabelS z, labelS_mem_vStab hex z⟩ = SemidirectProduct.inl (iv z : stdGroup) :=
  hlab z _ (coe_clabelS z)

include hlab hex in
theorem exists_cnGroup_restrict (hle : cnGroup v w ≤ vStab v) :
    ∃ ρH : cnGroup v w →* stdGroup, ∀ h : cnGroup v w,
      SemidirectProduct.inl (ρH h) = ρv ⟨h, hle h.2⟩ := by
  obtain ⟨ρ0, hρ0⟩ : ∃ ρ0 : cnGroup v w →* GStar, ∀ h : cnGroup v w, ρ0 h = ρv ⟨h, hle h.2⟩ :=
    ⟨ρv.comp (Subgroup.inclusion hle), fun _ => rfl⟩
  have hT : cnGroup v w ≤
      (((SemidirectProduct.inl : stdGroup →* GStar).range).comap ρv).map (vStab v).subtype := by
    rw [cnGroup, Subgroup.closure_le]
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨clabelS z, labelS_mem_vStab hex ⟨z, hz.1⟩⟩,
      ⟨_, (rho_labelS_eq hlab hex ⟨z, hz.1⟩).symm⟩, rfl⟩
  have hrange : ∀ h, ρ0 h ∈ (SemidirectProduct.inl : stdGroup →* GStar).range := by
    intro h
    obtain ⟨y, hy, e⟩ := hT h.2
    have e' : y = ⟨h, hle h.2⟩ := Subtype.ext e
    rw [hρ0, ← e']
    exact hy
  let e : stdGroup ≃* (SemidirectProduct.inl : stdGroup →* GStar).range :=
    MonoidHom.ofInjective SemidirectProduct.inl_injective
  refine ⟨e.symm.toMonoidHom.comp (ρ0.codRestrict _ hrange), fun h => ?_⟩
  have h1 := congrArg Subtype.val (e.apply_symm_apply ⟨ρ0 h, hrange h⟩)
  rw [MonoidHom.ofInjective_apply] at h1
  exact h1.trans (hρ0 h)

end Local

theorem ambientRootOrbitsHyp :
    AmbientRootOrbitsHyp := by
  intro v w hw
  obtain ⟨ρv, iv, -, hker, hker', -, hcompat, hadj, hex, hlab⟩ := native_local_label_root v
  refine ⟨ρv, iv, ⟨hcompat, hadj, hlab⟩, ?_⟩
  have hS := native_isFischerSlice hw
  have hHQ : cnGroup v w ≤ vStab v ⊓ vStab w :=
    (native_order_three_common_neighbor_three_transposition_group.choose_spec.2 v w hw).1
  have hle : cnGroup v w ≤ vStab v := fun h hh => (hHQ hh).1
  obtain ⟨ρH, hρH⟩ := exists_cnGroup_restrict hlab hex hle
  have hρ : Function.Injective ρH := by
    intro a b hab
    have e : ρv ⟨a, hle a.2⟩ = ρv ⟨b, hle b.2⟩ := by rw [← hρH, ← hρH, hab]
    have hc : ρv (⟨a, hle a.2⟩⁻¹ * ⟨b, hle b.2⟩) = 1 := by rw [map_mul, map_inv, e, inv_mul_cancel]
    have hfix := ((hker' _).2 ((hker _).1 hc)).2
    have hone : ((a : Shat)⁻¹ * b) = 1 := by
      refine hS.faithful _ (mul_mem (inv_mem a.2) b.2) fun y hy => ?_
      rw [cvPerm_apply]
      have hy' : cvMul y ((a : Shat)⁻¹ * b) = y := hfix y hy.1
      conv_lhs => rw [← hy']
      exact cvMul_inv_cancel y _
    exact Subtype.ext (inv_mul_eq_one.1 hone)
  have hρlab : ∀ (y : cgraph.commonNeighbors v w),
      ρH ⟨clabelS y, Fischer.lab_mem_sliceGroup y.2⟩ = (iv ⟨y, y.2.1⟩ : stdGroup) := by
    intro y
    apply inl_injective
    rw [hρH]
    exact rho_labelS_eq hlab hex ⟨y, y.2.1⟩
  have hroot : ∀ y : cgraph.commonNeighbors v w,
      ρH ⟨clabelS y, Fischer.lab_mem_sliceGroup y.2⟩ ∈ rootClass := fun y => by
    rw [hρlab y]
    exact (iv ⟨y, y.2.1⟩).2
  have hQY : ∀ q ∈ vStab v ⊓ vStab w, ∀ y ∈ cgraph.commonNeighbors v w,
      cvPerm q y ∈ cgraph.commonNeighbors v w := by
    intro q hq y hy
    have hq' := inv_mem hq
    rw [cvPerm_apply]
    exact cvMul_mem_commonNeighbors (mem_vStab.1 hq'.1) (mem_vStab.1 hq'.2) hy
  obtain ⟨ρQ, hρQdef⟩ : ∃ ρQ : (vStab v ⊓ vStab w : Subgroup Shat) →* GStar,
      ∀ q : (vStab v ⊓ vStab w : Subgroup Shat), ρQ q = ρv ⟨q, q.2.1⟩ :=
    ⟨ρv.comp (Subgroup.inclusion inf_le_left), fun _ => rfl⟩
  have hρQ : ∀ (h : Shat) (hh : h ∈ Fischer.sliceGroup clabelS (cgraph.commonNeighbors v w)),
      ρQ ⟨h, hHQ hh⟩ = SemidirectProduct.inl (ρH ⟨h, hh⟩) := by
    intro h hh
    rw [hρH, hρQdef]
  obtain ⟨r, hpart, h0, hsize, hcount⟩ :=
    hS.ambient_root_orbits_hyp hρ hroot (vStab v ⊓ vStab w) hHQ hQY ρQ hρQ
  have horbit : ∀ x : rootClass, rootPairOrbit ρv w x = Fischer.qRootOrbit _ ρQ x := by
    intro x
    ext x'
    constructor
    · rintro ⟨q, hqw, e⟩
      refine ⟨⟨q, q.2, hqw⟩, ?_⟩
      rw [hρQdef]
      exact e
    · rintro ⟨q, e⟩
      refine ⟨⟨q, q.2.1⟩, q.2.2, ?_⟩
      rw [hρQdef] at e
      exact e
  have hnat : nativeRoots ρv w = {x : rootClass | ∃ y : cgraph.commonNeighbors v w,
      ρH ⟨clabelS y, Fischer.lab_mem_sliceGroup y.2⟩ = (x : stdGroup)} := by
    ext x
    constructor
    · rintro ⟨z, hz, y, hy, e⟩
      refine ⟨⟨z, hz⟩, inl_injective ?_⟩
      rw [hρlab ⟨z, hz⟩, ← e, hlab ⟨z, hz.1⟩ y hy]
    · rintro ⟨y, e⟩
      refine ⟨y, y.2, ⟨clabelS y, labelS_mem_vStab hex ⟨y, y.2.1⟩⟩, coe_clabelS y, ?_⟩
      rw [rho_labelS_eq hlab hex ⟨y, y.2.1⟩, ← hρlab y, e]
  refine ⟨r, fun x => ?_, ?_, fun k => ?_, fun k x hx => ?_⟩
  · simp only [horbit]
    exact hpart x
  · rw [horbit, hnat]
    exact h0
  · rw [horbit]
    exact hsize k
  · rw [horbit] at hx
    rw [hnat]
    exact hcount k x hx

end CFSG.Monster.B.TwoA.Amalgam

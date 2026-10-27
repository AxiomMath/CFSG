module

public import CFSG.Quasithin.Background.HL3WrShat

public section

namespace CFSG.Quasithin.RonanH49

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr

abbrev yW : WMod := eW 0 1 * eW 1 0

abbrev dWd : WMod := eW 0 0 * eW 1 1 * eW 2 2

noncomputable abbrev GW : Subgroup (MulAut WMod) := img ⊔ Subgroup.zpowers tau

theorem GW_eq_norm : GW = norm := by
  refine le_antisymm ?_ ?_
  · exact sup_le img_le_norm (Subgroup.zpowers_le.mpr tau_mem_norm)
  · intro x hx
    obtain ⟨g, rfl | rfl⟩ := mem_norm_iff.1 hx
    · exact Subgroup.mem_sup_left ⟨g, rfl⟩
    · exact mul_mem (Subgroup.mem_sup_left ⟨g, rfl⟩)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers tau))

noncomputable abbrev G2 : Subgroup (MulAut WMod) := (P2.prod P2).map rho ⊔ Subgroup.zpowers tau

noncomputable abbrev Cy : Subgroup (MulAut WMod) := GW ⊓ centSub (Subgroup.zpowers yW)

noncomputable abbrev Cd : Subgroup (MulAut WMod) := GW ⊓ centSub (Subgroup.zpowers dWd)

@[expose] def commOnR (W : Subgroup WMod) (A : Subgroup (MulAut WMod)) : Subgroup WMod :=
  Subgroup.closure {u | ∃ a ∈ A, ∃ w ∈ W, u = a w * w⁻¹}

@[expose] def trZ : Subgroup WMod :=
  AddSubgroup.toSubgroup (AddMonoidHom.ker (Matrix.traceAddMonoidHom (Fin 3) (ZMod 2)))

theorem mem_centSub_zpowers_iff {V : Type*} [CommGroup V] {g : MulAut V} {z : V} :
    g ∈ centSub (Subgroup.zpowers z) ↔ g z = z := by
  refine ⟨fun h => h z (Subgroup.mem_zpowers z), fun h u hu => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  rw [map_zpow, h]

theorem mem_Cy {x : MulAut WMod} : x ∈ Cy ↔ x ∈ norm ∧ x yW = yW := by
  constructor
  · intro h
    exact ⟨GW_eq_norm ▸ (Subgroup.mem_inf.1 h).1, mem_centSub_zpowers_iff.1 (Subgroup.mem_inf.1 h).2⟩
  · rintro ⟨h1, h2⟩
    exact Subgroup.mem_inf.2 ⟨GW_eq_norm.symm ▸ h1, mem_centSub_zpowers_iff.2 h2⟩

theorem mem_Cd {x : MulAut WMod} : x ∈ Cd ↔ x ∈ norm ∧ x dWd = dWd := by
  constructor
  · intro h
    exact ⟨GW_eq_norm ▸ (Subgroup.mem_inf.1 h).1, mem_centSub_zpowers_iff.1 (Subgroup.mem_inf.1 h).2⟩
  · rintro ⟨h1, h2⟩
    exact Subgroup.mem_inf.2 ⟨GW_eq_norm.symm ▸ h1, mem_centSub_zpowers_iff.2 h2⟩

end CFSG.Quasithin.RonanH49

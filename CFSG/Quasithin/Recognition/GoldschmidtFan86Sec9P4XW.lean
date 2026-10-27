module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P4X

variable {L : ZLab Γ G} {α : V}

@[expose] def Compat (D₀ D : D10Set L α) (g : G) : Prop :=
  (∀ m, m ≤ 4 → g • (D₀.P 0).vert m = (D.P 0).vert m) ∧
    ∀ m, m ≤ 4 → g • (D₀.P 2).vert m = (D.P 2).vert m

theorem Compat.symm {D₀ D : D10Set L α} {g : G} (h : Compat D₀ D g) : Compat D D₀ g⁻¹ :=
  ⟨fun m hm => inv_smul_eq_iff.2 (h.1 m hm).symm, fun m hm => inv_smul_eq_iff.2 (h.2 m hm).symm⟩

theorem Compat.x_eq (F : FanTree Γ G) {D₀ D : D10Set L α} {g : G} (h : Compat D₀ D g) :
    D.x = g * D₀.x * g⁻¹ := by
  have e0 : D.delta 0 = g • D₀.delta 0 := (h.1 4 le_rfl).symm
  have e2 : D.delta 2 = g • D₀.delta 2 := (h.2 4 le_rfl).symm
  show L.z (D.delta 2) * L.z (D.delta 0) = g * (L.z (D₀.delta 2) * L.z (D₀.delta 0)) * g⁻¹
  rw [e0, e2, L.equivariant g _ (D₀.valence_delta F 2), L.equivariant g _ (D₀.valence_delta F 0)]
  group

theorem z_smul_eq_conj {L : ZLab Γ G} {g : G} {v : V} (hv : valence Γ v = 5)
    (hgv : g • v = v) : L.z v = g * L.z v * g⁻¹ := by
  have := L.equivariant g v hv
  rwa [hgv] at this

theorem isW1_conj (F : FanTree Γ G) {D₀ D : D10Set L α} {g w : G} (hg : g • α = α)
    (h : Compat D₀ D g) (hw : IsW1 D₀ w) : IsW1 D (g * w * g⁻¹) := by
  have hx := h.x_eq F
  refine ⟨?_, ?_, ?_⟩
  · rw [Arc.mem_stab]
    intro i hi
    rw [← h.2 i hi, mul_smul, mul_smul, inv_smul_smul, (Arc.mem_stab G).1 hw.fixes i hi]
  · rw [hx]
    calc (g * w * g⁻¹)⁻¹ * (g * D₀.x * g⁻¹) * (g * w * g⁻¹) = g * (w⁻¹ * D₀.x * w) * g⁻¹ := by
          group
      _ = g * D₀.x ^ 2 * g⁻¹ := by rw [hw.conj]
      _ = (g * D₀.x * g⁻¹) ^ 2 := by rw [conj_pow]
  · have e : (g * w * g⁻¹) * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
    have hδ2 : D.delta 2 = g • D₀.delta 2 := (h.2 4 le_rfl).symm
    have hz2 : L.z (D.delta 2) = g * L.z (D₀.delta 2) * g⁻¹ := by
      rw [hδ2, L.equivariant g _ (D₀.valence_delta F 2)]
    have hzα : L.z α = g * L.z α * g⁻¹ := z_smul_eq_conj D₀.val hg
    rw [e]
    rcases hw.sq with hs | hs
    · left
      rw [hs, hz2]
      calc g * (L.z (D₀.delta 2) * L.z α) * g⁻¹
          = (g * L.z (D₀.delta 2) * g⁻¹) * (g * L.z α * g⁻¹) := by group
        _ = (g * L.z (D₀.delta 2) * g⁻¹) * L.z α := by rw [← hzα]
    · right
      rw [hs, hz2]

theorem isW1Star_conj (F : FanTree Γ G) {D₀ D : D10Set L α} {g w : G} (hg : g • α = α)
    (h : Compat D₀ D g) (hw : IsW1Star D₀ w) : IsW1Star D (g * w * g⁻¹) := by
  refine ⟨isW1_conj F hg h hw.1, fun hsq ⟨w', hw', hsq'⟩ => ?_⟩
  have hg' : g⁻¹ • α = α := inv_smul_eq_iff.2 hg.symm
  have h1 := isW1_conj F hg' h.symm hw'
  rw [inv_inv] at h1
  have hδ2 : D₀.delta 2 = g⁻¹ • D.delta 2 := eq_inv_smul_iff.2 (h.2 4 le_rfl)
  have hz2 : L.z (D₀.delta 2) = g⁻¹ * L.z (D.delta 2) * g := by
    rw [hδ2]
    exact L.z_inv_smul g (D.valence_delta F 2)
  have hzα : L.z α = g⁻¹ * L.z α * g := by
    have := L.z_inv_smul g D₀.val
    rwa [hg'] at this
  refine hw.2 ?_ ⟨g⁻¹ * w' * g, h1, ?_⟩
  · have e : g * (w * w) * g⁻¹ = L.z (D.delta 2) := by
      rw [← hsq]; group
    rw [hz2, ← e]
    group
  · have e : g⁻¹ * w' * g * (g⁻¹ * w' * g) = g⁻¹ * (w' * w') * g := by group
    rw [e, hsq', hz2]
    calc g⁻¹ * (L.z (D.delta 2) * L.z α) * g
        = (g⁻¹ * L.z (D.delta 2) * g) * (g⁻¹ * L.z α * g) := by group
      _ = (g⁻¹ * L.z (D.delta 2) * g) * L.z α := by rw [← hzα]

end P4X

end CFSG.Quasithin.Fan86

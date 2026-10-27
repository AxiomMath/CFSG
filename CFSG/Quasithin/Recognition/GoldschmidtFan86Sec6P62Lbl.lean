module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62A

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P62

theorem cinv_iff {v : V} {w : G} : w ∈ Cinv G v ↔ IsCentralInvolIn G v w :=
  ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h3, h1, h2, h4⟩, fun ⟨h3, h1, h2, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

open scoped Classical in
variable (G) in
noncomputable def pick (α v : V) : G := if h : ∃ g : G, g • α = v then h.choose else 1

theorem pick_smul {α v : V} (h : ∃ g : G, g • α = v) : pick G α v • α = v := by
  simp only [pick, h, dite_true]
  exact h.choose_spec

@[expose] noncomputable def labOf (α : V) (z : G) (v : V) : G :=
  pick G α v * z * (pick G α v)⁻¹

theorem labOf_eq {α v : V} {z g : G} (hz : ∀ h ∈ MulAction.stabilizer G α, h * z = z * h)
    (hg : g • α = v) : labOf α z v = g * z * g⁻¹ := by
  have hp : pick G α v • α = v := pick_smul ⟨g, hg⟩
  have hmem : g⁻¹ * pick G α v ∈ MulAction.stabilizer G α := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hp, ← hg, inv_smul_smul]
  have hc := hz _ hmem
  unfold labOf
  calc pick G α v * z * (pick G α v)⁻¹ = g * (g⁻¹ * pick G α v * z) * (pick G α v)⁻¹ := by group
    _ = g * (z * (g⁻¹ * pick G α v)) * (pick G α v)⁻¹ := by rw [hc]
    _ = g * z * g⁻¹ := by group

@[expose] noncomputable def labZ (F : FanTree Γ G) {α : V} (hα : valence Γ α = 5) {z : G}
    (hz : IsCentralInvolIn G α z) : ZLab Γ G where
  z := labOf α z
  isCentral v hv := by
    obtain ⟨g, hg⟩ := exists_smul_of_valence_eq F (u := α) (w := v) (by rw [hv, hα])
    rw [labOf_eq hz.2.2.2 hg]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff, ← hg]
      simp [mul_smul, MulAction.mem_stabilizer_iff.1 hz.1]
    · intro h
      apply hz.2.1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
        _ = 1 := by rw [hz.2.2.1]; group
    · intro h hh
      have hmem : g⁻¹ * h * g ∈ MulAction.stabilizer G α := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hg, MulAction.mem_stabilizer_iff.1 hh,
          ← hg, inv_smul_smul]
      have hc := hz.2.2.2 _ hmem
      calc h * (g * z * g⁻¹) = g * (g⁻¹ * h * g * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * h * g)) * g⁻¹ := by rw [hc]
        _ = g * z * g⁻¹ * h := by group
  equivariant g v hv := by
    obtain ⟨h, hh⟩ := exists_smul_of_valence_eq F (u := α) (w := v) (by rw [hv, hα])
    rw [labOf_eq hz.2.2.2 hh, labOf_eq hz.2.2.2 (show (g * h) • α = g • v by rw [mul_smul, hh])]
    group

theorem labZ_z (F : FanTree Γ G) {α : V} (hα : valence Γ α = 5) {z : G}
    (hz : IsCentralInvolIn G α z) : (labZ F hα hz).z = labOf α z := rfl

end P62

end CFSG.Quasithin.Fan86

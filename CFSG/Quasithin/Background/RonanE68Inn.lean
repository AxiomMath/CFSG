module

public import CFSG.Quasithin.Background.RonanE68Defs

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanE68

section Inn

variable {G : Type} [Group G] {L V W : Subgroup G}

theorem coe_conj_apply (l x : ↥L) : ((MulAut.conj l x : ↥L) : G) = (l : G) * (x : G) * (l : G)⁻¹ :=
  rfl

theorem autSubInduced_eq_map_conj (hVN : V ≤ Subgroup.normalizer (L : Set G)) (hWV : W ≤ V)
    (hWL : W ≤ L)
    (hdec : ∀ v ∈ V, ∃ w ∈ W, ∀ x ∈ L, v * x * v⁻¹ = w * x * w⁻¹) :
    autSubInduced L V = (W.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L) := by
  ext α
  constructor
  · rintro ⟨g, hg, hα⟩
    obtain ⟨w, hw, hwx⟩ := hdec g hg.1
    refine ⟨⟨w, hWL hw⟩, Subgroup.mem_subgroupOf.2 hw, ?_⟩
    ext x
    rw [hα x, coe_conj_apply]
    exact (hwx x x.2).symm
  · rintro ⟨l, hl, rfl⟩
    have hlW : (l : G) ∈ W := Subgroup.mem_subgroupOf.1 hl
    exact ⟨l, ⟨hWV hlW, hVN (hWV hlW)⟩, fun x => rfl⟩

theorem autSubInduced_sup_eq_range (hVN : V ≤ Subgroup.normalizer (L : Set G)) (hWV : W ≤ V)
    (hWL : W ≤ L)
    (hdec : ∀ v ∈ V, ∃ w ∈ W, ∀ x ∈ L, v * x * v⁻¹ = w * x * w⁻¹) :
    autSubInduced L (L ⊔ V) = (MulAut.conj : ↥L →* MulAut ↥L).range := by
  ext α
  constructor
  · rintro ⟨g, hg, hα⟩
    have hgLV : g ∈ (L : Set G) * (V : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left L V hVN]
      exact hg.1
    obtain ⟨l, hl, v, hv, rfl⟩ := hgLV
    obtain ⟨w, hw, hwx⟩ := hdec v hv
    refine ⟨⟨l * w, L.mul_mem hl (hWL hw)⟩, ?_⟩
    ext x
    rw [hα x, coe_conj_apply]
    have h1 := hwx x x.2
    symm
    calc ((l : G) * v) * (x : G) * ((l : G) * v)⁻¹ = l * (v * (x : G) * v⁻¹) * l⁻¹ := by group
      _ = l * (w * (x : G) * w⁻¹) * l⁻¹ := by rw [h1]
      _ = ((⟨l * w, L.mul_mem hl (hWL hw)⟩ : ↥L) : G) * (x : G) *
          ((⟨l * w, L.mul_mem hl (hWL hw)⟩ : ↥L) : G)⁻¹ := by
        show _ = ((l : G) * w) * (x : G) * ((l : G) * w)⁻¹
        group
  · rintro ⟨l, rfl⟩
    exact ⟨l, ⟨Subgroup.mem_sup_left l.2, Subgroup.le_normalizer l.2⟩, fun x => rfl⟩

@[expose] def inducedAut (L : Subgroup G) (v : G) (hv : v ∈ Subgroup.normalizer (L : Set G)) :
    MulAut ↥L where
  toFun x := ⟨v * x * v⁻¹, (Subgroup.mem_normalizer_iff.1 hv x).1 x.2⟩
  invFun x := ⟨v⁻¹ * x * v, by
    have := (Subgroup.mem_normalizer_iff.1 hv (v⁻¹ * (x : G) * v)).2
    rw [show v * (v⁻¹ * (x : G) * v) * v⁻¹ = x by group] at this
    exact this x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem inducedAut_mem_autSubInduced {X : Subgroup G} {v : G}
    (hvX : v ∈ X) (hv : v ∈ Subgroup.normalizer (L : Set G)) :
    inducedAut L v hv ∈ autSubInduced L X :=
  ⟨v, ⟨hvX, hv⟩, fun _ => rfl⟩

end Inn

end CFSG.Quasithin.RonanE68

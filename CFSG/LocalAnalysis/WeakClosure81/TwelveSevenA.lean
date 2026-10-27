module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveLift
public import CFSG.LocalAnalysis.WeakClosure81.TwelveOddPart
public import CFSG.LocalAnalysis.WeakClosure81.TwelvePartTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

section PartTwo

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G} {n : ℕ}

theorem Setting12Two.exists_odd_fix (h : Setting12Two A M n)
    (hA : IsElemAbelian 2 A) (ρ : G →* LGL 2 V) (hq : RepQuad ρ A)
    {u v : G ⧸ CFSG.Quasithin.kerIn M ⊤} (hu : u * u = 1) (hv : v * v = 1)
    (huv : Odd (orderOf (u * v))) (huv1 : u * v ≠ 1) :
    ∃ y : G, Odd (orderOf y) ∧ QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤) y = u * v ∧
      fixMod (cE ρ.range) (ρ y) ⊓ commSub ρ.range ≤ cE ρ.range := by
  obtain ⟨a, g, x, w, y, ha, haK, hg, hc, hw, hy, hw2, hyodd, _hyM, _hinv, hxy⟩ :=
    h.exists_odd_part_lift hA hu hv huv huv1
  have h5 : fixMod (cE ρ.range) (ρ a * (MulAut.conj (ρ g)) (ρ a)) ⊓ commSub ρ.range
      ≤ cE ρ.range :=
    (twelveFive_partTwo h ρ hq hg).2.2.2 (ρ a) (Subgroup.mem_map_of_mem ρ ha)
      ⟨a, ha, haK, rfl⟩
  have hcc : ρ a * (MulAut.conj (ρ g)) (ρ a) = ρ (a * (g * a * g⁻¹)) := by
    simp [MulAut.conj_apply]
  rw [hcc] at h5
  have hzp : ∀ z ∈ Subgroup.zpowers (a * (g * a * g⁻¹)),
      ρ z ∈ Subgroup.zpowers (ρ (a * (g * a * g⁻¹))) := by
    intro z hz
    rw [← MonoidHom.map_zpowers]
    exact Subgroup.mem_map_of_mem ρ hz
  have hcρ : ρ (a * (g * a * g⁻¹)) = ρ w * ρ y := by
    rw [hc, map_mul]
  have hw2ρ : ∃ k : ℕ, (ρ w) ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hw2
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hyfix : fixMod (cE ρ.range) (ρ y) ⊓ commSub ρ.range ≤ cE ρ.range :=
    fixMod_inf_commSub_le_of_two_part (G := ρ.range) ⟨a * (g * a * g⁻¹), rfl⟩ hcρ
      (hzp w hw) (hzp y hy) hw2ρ h5
  have hconj : fixMod (cE ρ.range) ((ρ x)⁻¹ * ρ y * ρ x) ⊓ commSub ρ.range
      ≤ cE ρ.range :=
    fixMod_inf_commSub_le_conj (G := ρ.range) (x := ρ x) ⟨x, rfl⟩ hyfix
  have hxyfix : fixMod (cE ρ.range) (ρ (x⁻¹ * y * x)) ⊓ commSub ρ.range
      ≤ cE ρ.range := by
    simpa [map_mul, map_inv] using hconj
  refine ⟨x⁻¹ * y * x, ?_, hxy, hxyfix⟩
  have hsem : SemiconjBy x⁻¹ y (x⁻¹ * y * x) := by
    unfold SemiconjBy
    group
  rw [← SemiconjBy.orderOf_eq x⁻¹ hsem]
  exact hyodd

end PartTwo

end CFSG.LocalAnalysis.WeakClosure81

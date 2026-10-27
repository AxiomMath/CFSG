module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecG.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {V : Type} [CommGroup V]

theorem apply_mem_fixV_of_normalizes {N : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ k ∈ N, g⁻¹ * k * g ∈ N) {c : V} (hc : c ∈ fixV N) : g c ∈ fixV N := by
  intro k hk
  have h1 : (g⁻¹ * k * g) c = c := hc _ (hg k hk)
  have h2 : k (g c) = g ((g⁻¹ * k * g) c) := by
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply]
  rw [h2, h1]

@[expose] def cosetStab (G : Subgroup (MulAut V)) (C : Subgroup V)
    (hC : ∀ g ∈ G, ∀ c ∈ C, g c ∈ C) (u : V) : Subgroup (MulAut V) where
  carrier := {g | g ∈ G ∧ g u * u⁻¹ ∈ C}
  one_mem' := ⟨G.one_mem, by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, hgu⟩ ⟨hh, hhu⟩
    refine ⟨G.mul_mem hg hh, ?_⟩
    have e : (g * h) u * u⁻¹ = g (h u * u⁻¹) * (g u * u⁻¹) := by
      rw [MulAut.mul_apply, map_mul, map_inv]
      group
    rw [e]
    exact C.mul_mem (hC g hg _ hhu) hgu
  inv_mem' := by
    rintro g ⟨hg, hgu⟩
    refine ⟨G.inv_mem hg, ?_⟩
    have e : g⁻¹ u * u⁻¹ = (g⁻¹ (g u * u⁻¹))⁻¹ := by
      rw [map_mul, map_inv]
      simp only [MulAut.inv_apply, MulEquiv.symm_apply_apply]
      group
    rw [e]
    exact C.inv_mem (hC _ (G.inv_mem hg) _ hgu)

theorem zpow_eq_one_or_eq' {M : Type*} [Group M] {a : M} (ha : a ^ 2 = 1) (k : ℤ) :
    a ^ k = 1 ∨ a ^ k = a := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, zpow_ofNat, ha, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_ofNat, ha, one_zpow, one_mul]

theorem apply_eq_or_of_commV {a : MulAut V} {v₁ : V}
    (hc : commV (Subgroup.zpowers a) = Subgroup.zpowers v₁) (hv₁ : v₁ ^ 2 = 1) (w : V) :
    a w = w ∨ a w = v₁ * w := by
  have hmem : a w * w⁻¹ ∈ Subgroup.zpowers v₁ := by
    rw [← hc]
    exact Subgroup.subset_closure ⟨a, Subgroup.mem_zpowers a, w, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rcases zpow_eq_one_or_eq' hv₁ k with h | h
  · left
    rw [h] at hk
    exact (mul_inv_eq_one.mp hk.symm)
  · right
    rw [h] at hk
    rw [hk]
    group

end CFSG.Quasithin.Vol2.Ch10.SecG.C10E4

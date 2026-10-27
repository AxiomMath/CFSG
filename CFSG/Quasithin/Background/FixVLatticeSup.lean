module

public import CFSG.Quasithin.Background.Module
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.FixVLat

variable {V : Type*} [CommGroup V]

theorem commV_biSup_le (I : Finset (Subgroup (MulAut V))) :
    commV (⨆ L ∈ I, L) ≤ ⨆ L ∈ I, commV L := by
  set S : Subgroup V := ⨆ L ∈ I, commV L with hS
  let N : Subgroup (MulAut V) :=
    { carrier := {g | ∀ v : V, g v * v⁻¹ ∈ S}
      one_mem' := fun v => by simp
      mul_mem' := by
        intro a b ha hb v
        have h1 : (a * b) v * v⁻¹ = (a (b v) * (b v)⁻¹) * (b v * v⁻¹) := by
          show a (b v) * v⁻¹ = _
          group
        rw [h1]
        exact S.mul_mem (ha (b v)) (hb v)
      inv_mem' := by
        intro a ha v
        have h1 : a⁻¹ v * v⁻¹ = (a (a⁻¹ v) * (a⁻¹ v)⁻¹)⁻¹ := by
          have : a (a⁻¹ v) = v := by simp
          rw [this]
          group
        rw [h1]
        exact S.inv_mem (ha (a⁻¹ v)) }
  have hle : (⨆ L ∈ I, L) ≤ N := by
    refine iSup₂_le fun L hL g hg v => ?_
    have : g v * v⁻¹ ∈ commV L := Subgroup.subset_closure ⟨g, hg, v, rfl⟩
    exact le_iSup₂ (f := fun L (_ : L ∈ I) => commV L) L hL this
  refine (Subgroup.closure_le S).mpr ?_
  rintro _ ⟨x, hx, v, rfl⟩
  exact hle hx v

theorem isElemAbelian2_map_iff {Γ : Type*} [Group Γ] {W : Type*} [CommGroup W]
    {φ : Γ →* MulAut W} (hφ : Function.Injective φ) {B : Subgroup Γ} :
    IsElemAbelian2 (B.map φ) ↔
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ ∀ a ∈ B, a * a = 1 := by
  constructor
  · rintro ⟨hc, hs⟩
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · have h1 := hc (φ a) (Subgroup.mem_map_of_mem φ ha) (φ b) (Subgroup.mem_map_of_mem φ hb)
      rw [← map_mul, ← map_mul] at h1
      exact hφ h1
    · have h1 := hs (φ a) (Subgroup.mem_map_of_mem φ ha)
      rw [← map_pow] at h1
      have h2 : a ^ 2 = 1 := hφ (by rw [h1, map_one])
      simpa [pow_two] using h2
  · rintro ⟨hc, hs⟩
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hy
      rw [← map_mul, ← map_mul, hc a ha b hb]
    · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
      rw [← map_pow, pow_two, hs a ha, map_one]

end CFSG.Quasithin.FixVLat

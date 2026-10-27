module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.Quasithin

theorem center_eq_ker_of_central_cover {Y S : Type*} [Group Y] [Group S] (p : Y →* S)
    (hp : Function.Surjective p) (hS : IsSimpleGroup S) (hSnc : ∃ a b : S, a * b ≠ b * a)
    (hker : p.ker ≤ Subgroup.center Y) : Subgroup.center Y = p.ker := by
  haveI : IsSimpleGroup S := hS
  refine le_antisymm ?_ hker
  intro x hx
  rw [MonoidHom.mem_ker]
  have hfx : p x ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨y, rfl⟩ := hp s
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
  have hcenter : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hSnc
      have ha : a ∈ Subgroup.center S := by rw [h]; trivial
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  rw [hcenter, Subgroup.mem_bot] at hfx
  exact hfx

theorem isPerfect_of_central_cover {Y S : Type*} [Group Y] [Group S] (p : Y →* S)
    (hp : Function.Surjective p) (hS : Group.IsPerfect S) (ω : Y)
    (hker : p.ker = Subgroup.zpowers ω) (hω : ω ∈ commutator Y) : Group.IsPerfect Y := by
  rw [Group.isPerfect_def]
  have hmap : (commutator Y).map p = commutator S := by
    rw [commutator_def Y, commutator_def S, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective p hp]
  have hmapTop : (commutator Y).map p = ⊤ := by
    rw [hmap, hS.commutator_eq_top]
  have hkerC : p.ker ≤ commutator Y := by
    rw [hker]; exact Subgroup.zpowers_le.mpr hω
  rw [Subgroup.eq_top_iff']
  intro y
  have hy : p y ∈ (commutator Y).map p := by rw [hmapTop]; trivial
  obtain ⟨c, hc, hcy⟩ := hy
  have hmem : c⁻¹ * y ∈ p.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcy, inv_mul_cancel]
  have hy' : y = c * (c⁻¹ * y) := by group
  rw [hy']
  exact Subgroup.mul_mem _ hc (hkerC hmem)

theorem isHat_of_central_cover {Y S : Type} [Group Y] [Group S] (p : Y →* S)
    (hp : Function.Surjective p) (hS : IsSimpleGroup S) (hSnc : ∃ a b : S, a * b ≠ b * a)
    (ω : Y) (hω : orderOf ω = 3) (hωc : ω ∈ Subgroup.center Y)
    (hker : p.ker = Subgroup.zpowers ω) (hperf : Group.IsPerfect Y) : IsHat Y S := by
  haveI : IsSimpleGroup S := hS
  have hcenter : Subgroup.center Y = p.ker :=
    center_eq_ker_of_central_cover p hp hS hSnc (by rw [hker]; exact Subgroup.zpowers_le.mpr hωc)
  let e : Y ⧸ Subgroup.center Y ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientKerEquivOfSurjective p hp)
  have hnab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hSnc
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  refine ⟨⟨hperf, e.isSimpleGroup, hnab⟩, ?_, ⟨e⟩⟩
  rw [hcenter, hker, Nat.card_zpowers, hω]

end CFSG.Quasithin.AppendixH.H12

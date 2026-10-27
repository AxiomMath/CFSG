module

public import CFSG.Quasithin.Background.D2Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin
open scoped commutatorElement

variable {W : Type} [CommGroup W]

theorem s16c167_cfg2_perf_fixed [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hperf : ⁅L, L⁆ = L) {U : Subgroup W} (hU : ∀ x ∈ L, ∀ u ∈ U, x u ∈ U)
    (hr : rk ↥U ≤ 2) : U ≤ fixV L := by
  classical
  have hA : L ≤ stabSub U := by
    intro x hx
    rw [mem_stabSub]
    intro u
    constructor
    · intro hxu
      have h := hU x⁻¹ (L.inv_mem hx) (x u) hxu
      rwa [MulAut.inv_apply_self] at h
    · intro hu
      exact hU x hx u hu
  have hcard : Nat.card ↥U ≤ 4 := by
    calc Nat.card ↥U = 2 ^ rk ↥U := card_eq_two_pow hW U
      _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (n := 2) (by norm_num) hr
      _ = 4 := by norm_num
  haveI : Group.IsSolvable (MulAut ↥U) :=
    haveI : Group.IsSolvable (Equiv.Perm ↥U) := Equiv.Perm.isSolvable hcard
    Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm ↥U)
      MulEquiv.toEquiv_injective
  let ρ : ↥L →* MulAut ↥U := (resHom U).comp (Subgroup.inclusion hA)
  haveI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  have hbot : ρ.range = ⊥ := by
    by_contra hne
    have hlt := Group.IsSolvable.commutator_lt_of_ne_bot hne
    haveI : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
    rw [Subgroup.commutator_eq_self] at hlt
    exact (lt_irrefl ρ.range) hlt
  intro u hu
  rw [mem_fixV]
  intro x hx
  have hmem : ρ ⟨x, hx⟩ ∈ ρ.range :=
    MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩
  rw [hbot] at hmem
  have hρ : ρ ⟨x, hx⟩ = 1 := by simpa using hmem
  have h1 : ((ρ ⟨x, hx⟩ ⟨u, hu⟩ : ↥U) : W) = u := by
    have h2 : ((ρ ⟨x, hx⟩ ⟨u, hu⟩ : ↥U) : W) =
        (((1 : MulAut ↥U) ⟨u, hu⟩ : ↥U) : W) :=
      congrArg (fun (φ : MulAut ↥U) => ((φ ⟨u, hu⟩ : ↥U) : W)) hρ
    simpa using h2
  have h4 : ((ρ ⟨x, hx⟩ ⟨u, hu⟩ : ↥U) : W) = x u := by
    change ((resHom U (Subgroup.inclusion hA ⟨x, hx⟩) ⟨u, hu⟩ : ↥U) : W) = x u
    have h := resHom_apply U (Subgroup.inclusion hA ⟨x, hx⟩) ⟨u, hu⟩
    simpa using h
  rw [← h4]
  exact h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

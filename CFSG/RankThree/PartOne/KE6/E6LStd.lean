module

public import CFSG.RankThree.PartOne.KE6.E6LAct
public import CFSG.RankThree.PartOne.KE.A1Main

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)
open CFSG.LieType.Steinberg.TwistedE6 (sigma fixedGroup mem_fixedGroup sigma_xm_single
  sigma_xm_neg_single rhoPerm)
open scoped Matrix MatrixGroups

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6 in
open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule in
theorem certificate123_of_kernel : (checkPerm = true)
    ∧ (checkRho = true)
    ∧ (checkTranspose = true)
    ∧ (checkSimple = true) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem rhoPerm_eq_rho6 (k : Fin Tag.E6.rank) : rhoPerm k = rho6 k := by
  revert k
  decide +kernel

section Std

variable {τ : Tag} {L : Type} [Field L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

structure StdTwist6 [E6Sub τ] (n₁ : ModGL τ L) (π : Equiv.Perm (Fin τ.rank)) : Prop where
  hπ : π = 1 ∨ π = rhoτ τ
  hgen : ∀ j ∈ e6Set τ, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
    n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c

@[expose] def stdLayer (τ : Tag) {L : Type} [Field L] (ℓ f : ℕ) [Fact ℓ.Prime]
    [CharP L ℓ] (n₁ : ModGL τ L) : Subgroup (ModGL τ L) :=
  subsystemGroup τ L (e6Set τ) ⊓
    twistedFixedPoints n₁ (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))

theorem mem_stdLayer {n₁ : ModGL τ L} {g : ModGL τ L} :
    g ∈ stdLayer τ ℓ f n₁ ↔ g ∈ subsystemGroup τ L (e6Set τ) ∧
      n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n₁⁻¹ = g :=
  Iff.rfl

theorem stdLayer_le (n₁ : ModGL τ L) :
    stdLayer τ ℓ f n₁ ≤ subsystemGroup τ L (e6Set τ) :=
  inf_le_left

theorem StdTwist6.theta_xUnit [E6Sub τ] {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    (h : StdTwist6 n₁ π) {j : Fin τ.rank} (hj : j ∈ e6Set τ) (c : L) :
    frobTwistGL τ L ℓ f n₁ (xUnit τ L j c) = xUnit τ L (π j) (c ^ ℓ ^ f) := by
  rw [frobTwistGL_apply]
  change n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (xUnit τ L j c) * n₁⁻¹ = _
  rw [units_map_entrywiseHom_xUnit, iterateFrobenius_def, (h.hgen j hj _).1]

theorem StdTwist6.theta_yUnit [E6Sub τ] {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    (h : StdTwist6 n₁ π) {j : Fin τ.rank} (hj : j ∈ e6Set τ) (c : L) :
    frobTwistGL τ L ℓ f n₁ (yUnit τ L j c) = yUnit τ L (π j) (c ^ ℓ ^ f) := by
  rw [frobTwistGL_apply]
  change n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (yUnit τ L j c) * n₁⁻¹ = _
  rw [units_map_entrywiseHom_yUnit, iterateFrobenius_def, (h.hgen j hj _).2]

theorem StdTwist6.commute_of_one [E6Sub τ] {n₁ : ModGL τ L}
    {π : Equiv.Perm (Fin τ.rank)} (h : StdTwist6 n₁ π) (hπ : π = 1) {g : ModGL τ L}
    (hg : g ∈ subsystemGroup τ L (e6Set τ)) : n₁ * g * n₁⁻¹ = g := by
  subst hπ
  rw [subsystemGroup] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · exact (h.hgen i hi c).1
    · exact (h.hgen i hi c).2
  | one => simp
  | mul x y _ _ hx hy =>
    calc n₁ * (x * y) * n₁⁻¹ = (n₁ * x * n₁⁻¹) * (n₁ * y * n₁⁻¹) := by group
      _ = x * y := by rw [hx, hy]
  | inv x _ hx =>
    calc n₁ * x⁻¹ * n₁⁻¹ = (n₁ * x * n₁⁻¹)⁻¹ := by group
      _ = x⁻¹ := by rw [hx]

theorem entrywiseFrob_mem {g : ModGL τ L} (hg : g ∈ subsystemGroup τ L (e6Set τ))
    (e : ℕ) :
    Units.map (entrywiseHom (iterateFrobenius L ℓ e)) g ∈ subsystemGroup τ L (e6Set τ) := by
  rw [subsystemGroup] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rw [units_map_entrywiseHom_xUnit]
      exact xUnit_mem_subsystemGroup hi _
    · rw [units_map_entrywiseHom_yUnit]
      exact yUnit_mem_subsystemGroup hi _
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

theorem baseChangeGL_mem_subsystemGroup' {K : Type} [Field K] (ι : K →+* L)
    {g : ModGL τ K} (hg : g ∈ subsystemGroup τ K (e6Set τ)) :
    baseChangeGL ι g ∈ subsystemGroup τ L (e6Set τ) := by
  rw [subsystemGroup] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rw [baseChangeGL_xUnit]
      exact xUnit_mem_subsystemGroup hi _
    · rw [baseChangeGL_yUnit]
      exact yUnit_mem_subsystemGroup hi _
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

end Std

end CFSG.RankThree.PartOne.KE6

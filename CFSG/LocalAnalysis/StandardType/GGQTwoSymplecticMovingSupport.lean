module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticFrameDimensions
public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticComponentBounds

public section

namespace CFSG.StandardType.QTwoSymplecticCav

open Matrix Polynomial CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.SymplecticPilot
open CFSG.StandardType.WitSpNs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.RankThree.PartOne.KCSpFull (spEnd_mul spEnd_one)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem mem_movingFactor_of_fix_fixed (hK : Nat.card K = 2)
    {t g : StatedSp n K} (ht3 : t ^ 3 = 1) (hc : g * t = t * g)
    (hfix : ∀ w ∈ LinearMap.ker (spEnd t - 1), spEnd g w = w) :
    g ∈ spSupported t {X ^ 2 + X + 1} := by
  apply mem_spSupported.mpr
  refine ⟨hc, ?_⟩
  intro f hf hnot w hw
  rcases SpFour.primaryFactor_cases_sp hK ht3 hf with hX | h3
  · subst f
    apply hfix
    have h := mem_primaryComponent.mp hw
    rw [map_sub, aeval_X, map_one] at h
    exact LinearMap.mem_ker.mpr h
  · exact (hnot (Set.mem_singleton_iff.mpr h3)).elim

theorem fix_fixed_of_supported_moving (hK : Nat.card K = 2)
    {t g : StatedSp n K}
    {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1) (hM : M * M + M + 1 = 0)
    {c : Fin n → Multiplicative (ZMod 3)}
    (ht : mat n K t = planeMat (fun j => M ^ (Multiplicative.toAdd (c j)).val))
    {I : Finset (Fin n)} (hI : ∀ i ∈ I, c i ≠ 1)
    (hg : g ∈ spBlock K I) :
    ∀ w ∈ LinearMap.ker (spEnd t - 1), spEnd g w = w := by
  intro w hw
  change mat n K g *ᵥ w = w
  apply mulVec_eq_self_of_isSupp hg
  intro a ha
  have hi : plane a ∈ I := ha
  have hcoord : coord (side a) (plane a) = a := by rcases a with a | a <;> simp [coord, side, plane]
  simpa only [hcoord] using plane_zero_of_mem_fixed hK hdet hM ht hw (hI _ hi) (side a)

theorem conj_mem_movingFactor_of_fix_fixed (hK : Nat.card K = 2) (a : StatedSp n K)
    {t g : StatedSp n K} (ht3 : t ^ 3 = 1) (hc : g * t = t * g)
    (hfix : ∀ w ∈ LinearMap.ker (spEnd t - 1), spEnd g w = w) :
    a * g * a⁻¹ ∈ spSupported (a * t * a⁻¹) {X ^ 2 + X + 1} := by
  have h3 : (a * t * a⁻¹) ^ 3 = 1 := by
    change ((MulAut.conj a) t) ^ 3 = 1
    rw [← map_pow, ht3, map_one]
  apply mem_movingFactor_of_fix_fixed hK h3
  · calc (a * g * a⁻¹) * (a * t * a⁻¹) = a * (g * t) * a⁻¹ := by group
      _ = a * (t * g) * a⁻¹ := by rw [hc]
      _ = (a * t * a⁻¹) * (a * g * a⁻¹) := by group
  · intro w hw
    have hwfix : spEnd (a * t * a⁻¹) w = w := sub_eq_zero.mp (LinearMap.mem_ker.mp hw)
    have hw₀ : spEnd a⁻¹ w ∈ LinearMap.ker (spEnd t - 1) := by
      apply LinearMap.mem_ker.mpr
      change spEnd t (spEnd a⁻¹ w) - spEnd a⁻¹ w = 0
      rw [← Module.End.mul_apply, ← spEnd_mul,
        show t * a⁻¹ = a⁻¹ * (a * t * a⁻¹) by group, spEnd_mul, Module.End.mul_apply, hwfix, sub_self]
    apply spEnd_injective' a⁻¹
    rw [← Module.End.mul_apply, ← spEnd_mul,
      show a⁻¹ * (a * g * a⁻¹) = g * a⁻¹ by group, spEnd_mul, Module.End.mul_apply]
    exact hfix _ hw₀

theorem permSp_mem_spBlock_of_fix_outside {I : Finset (Fin n)}
    (π : Equiv.Perm (Fin n)) (hfix : ∀ j ∉ I, π j = j) : permSp K π ∈ spBlock K I := by
  rw [spBlock, mem_suppGroup_iff (parClosed_planeCoords I)]
  intro a ha b
  rw [mat_permSp, spIncl_apply, Matrix.one_apply]
  have hpa : Sum.map π π a = a := by
    rcases a with a | a
    · have hai : a ∉ I := ha
      simp [hfix a hai]
    · have hai : a ∉ I := ha
      simp [hfix a hai]
  rw [hpa]

theorem permSp_commute_of_constant_planes
    {t : StatedSp n K} {P : Fin n → Matrix (Fin 2) (Fin 2) K}
    (ht : mat n K t = planeMat P) {I : Finset (Fin n)} {T : Matrix (Fin 2) (Fin 2) K}
    (hP : ∀ j ∈ I, P j = T) (π : Equiv.Perm (Fin n)) (hfix : ∀ j ∉ I, π j = j) :
    permSp K π * t = t * permSp K π := by
  have hc : permSp K π * t * (permSp K π)⁻¹ = t := by
    apply mat_injective
    rw [SymplecticPlaneActions.mat_permSp_conj_planeMat ht, ht]
    congr 1
    funext j
    by_cases hj : j ∈ I
    · have hπj : π.symm j ∈ I := by
        by_contra hn
        have h := hfix (π.symm j) hn
        rw [π.apply_symm_apply] at h
        exact hn (h ▸ hj)
      rw [hP _ hπj, hP _ hj]
    · have h := congrArg π.symm (hfix j hj)
      have heq : π.symm j = j := by simpa only [π.symm_apply_apply] using h.symm
      rw [heq]
  have h := congrArg (fun g : StatedSp n K => g * permSp K π) hc
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h

end CFSG.StandardType.QTwoSymplecticCav

end

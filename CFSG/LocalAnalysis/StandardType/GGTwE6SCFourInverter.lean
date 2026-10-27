module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Center
import CFSG.RankThree.Classical2.CentralLiftCommutator
import CFSG.LocalAnalysis.SectionRank.SignLines

public section

namespace CFSG.StandardType.SCFourCover

open scoped commutatorElement

private theorem commutatorElement_eq_self_of_inverts {G : Type*} [Group G] {t u : G}
    (hu : u ^ 3 = 1) (htu : t * u * t⁻¹ = u⁻¹) : ⁅t, u⁆ = u := by
  have h : u⁻¹ = u ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← hu]
    group
  rw [commutatorElement_def, htu, h]
  calc u ^ 2 * u ^ 2 = u ^ 3 * u := by group
    _ = u := by rw [hu, one_mul]

variable {L' R : Type*} [Group L'] [Group R] {ψ : L' →* R}

theorem commutatorElement_pow_three_of_inverts (hker : ψ.ker ≤ Subgroup.center L') {x y : L'}
    (hy : ψ y ^ 3 = 1) (hxy : ψ x * ψ y * (ψ x)⁻¹ = (ψ y)⁻¹) : ⁅x, y⁆ ^ 3 = 1 := by
  have hy3 : y ^ 3 ∈ Subgroup.center L' := hker (by rw [MonoidHom.mem_ker, map_pow, hy])
  have hc : x * y * x⁻¹ * y ∈ Subgroup.center L' :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hxy, inv_mul_cancel])
  have hcomm : Commute (x * y * x⁻¹) y⁻¹ := by
    have h := (show Commute (x * y * x⁻¹ * y) y⁻¹ from
      (Subgroup.mem_center_iff.1 hc y⁻¹).symm).mul_left (Commute.refl y⁻¹)
    rwa [mul_inv_cancel_right] at h
  rw [commutatorElement_def, hcomm.mul_pow, conj_pow, inv_pow, Subgroup.mem_center_iff.1 hy3 x]
  group

theorem apply_commutatorElement_of_induced (hker : ψ.ker ≤ Subgroup.center L')
    {a : MulAut L'} {φ : MulAut R} (h : ∀ l, φ (ψ l) = ψ (a l)) {x y : L'}
    (hy : φ (ψ y) = ψ y) {k : ℤ} (hx : φ (ψ x) = ψ x * ψ y ^ k) : a ⁅x, y⁆ = ⁅x, y⁆ := by
  rw [map_commutatorElement, CFSG.RankThree.Classical2.commutatorElement_eq_of_map_eq ψ hker
    (x' := x * y ^ k) (y' := y) (by rw [← h, hx, map_mul, map_zpow]) (by rw [← h, hy]),
    commutatorElement_def, commutatorElement_def]
  group

theorem exists_induces_conj_of_inverts (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') {A : Subgroup (MulAut L')}
    (hSC : ∀ n : L', (∀ a ∈ A, a n = n) → n ^ 3 = 1 → MulAut.conj n ∈ A) {t u : R}
    (hu : u ^ 3 = 1) (htu : t * u * t⁻¹ = u⁻¹)
    (hfix : ∀ a ∈ A, ∃ φ : MulAut R, (∀ l, φ (ψ l) = ψ (a l)) ∧ φ u = u ∧
      ∃ k : ℤ, φ t = t * u ^ k) :
    ∃ a ∈ A, ∀ l, MulAut.conj u (ψ l) = ψ (a l) := by
  obtain ⟨x, rfl⟩ := hψ t
  obtain ⟨y, rfl⟩ := hψ u
  refine ⟨MulAut.conj ⁅x, y⁆,
    hSC _ (fun a ha => ?_) (commutatorElement_pow_three_of_inverts hker hu htu), fun l => ?_⟩
  · obtain ⟨φ, hφ, h1, k, h2⟩ := hfix a ha
    exact apply_commutatorElement_of_induced hker hφ h1 h2
  · rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, map_commutatorElement,
      commutatorElement_eq_self_of_inverts hu htu]

end CFSG.StandardType.SCFourCover

end

module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenE7Defs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZRootTorus
public import CFSG.RankThree.PartOne.KE.SigmaCentralizer

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.StandardType.TableBExc.E6Three
open CFSG.ComponentClassification.CatLeafProof CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private def e7N : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ :=
  ![![4, 4, 6, 8, 6, 4, 2], ![4, 7, 8, 12, 9, 6, 3], ![6, 8, 12, 16, 12, 8, 4],
    ![8, 12, 16, 24, 18, 12, 6], ![6, 9, 12, 18, 15, 10, 5], ![4, 6, 8, 12, 10, 8, 4],
    ![2, 3, 4, 6, 5, 4, 3]]

private theorem e7_cartan_mul_N (i j : Fin Tag.E7.rank) :
    ∑ k, iform (Pi.single i 1 : Fin Tag.E7.rank → ℤ) (Pi.single k 1) * e7N k j =
      if i = j then 2 else 0 := by
  revert i j
  decide +kernel

private theorem e7N_zero (j : Fin Tag.E7.rank) : e7N 0 j = 2 * e7Theta j := by
  revert j
  decide +kernel

private theorem e7_iform_symm (i k : Fin Tag.E7.rank) :
    iform (Pi.single i 1 : Fin Tag.E7.rank → ℤ) (Pi.single k 1) =
      iform (Pi.single k 1 : Fin Tag.E7.rank → ℤ) (Pi.single i 1) := by
  revert i k
  decide +kernel

theorem exists_e7_coroot_coeffs {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (t : Fin Tag.E7.rank → ZMod p) (ht : ∑ j, (e7Theta j : ZMod p) * t j = 0) :
    ∃ u : Fin Tag.E7.rank → ZMod p, u 0 = 0 ∧ ∀ i,
      ∑ k, u k * ((iform (Pi.single k 1 : Fin Tag.E7.rank → ℤ) (Pi.single i 1) : ℤ) : ZMod p) =
        t i := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have := (ZMod.natCast_eq_zero_iff 2 p).mp h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this)
  refine ⟨fun k => (2 : ZMod p)⁻¹ * ∑ j, (e7N k j : ZMod p) * t j, ?_, ?_⟩
  · simp only [e7N_zero, Int.cast_mul, Int.cast_ofNat, mul_assoc, ← Finset.mul_sum]
    rw [← mul_assoc, inv_mul_cancel₀ h2, one_mul]
    exact ht
  · intro i
    have key : ∀ j, ∑ k, (iform (Pi.single i 1 : Fin Tag.E7.rank → ℤ) (Pi.single k 1) : ZMod p) *
        (e7N k j : ZMod p) = if i = j then 2 else 0 := by
      intro j
      have := congrArg (Int.cast : ℤ → ZMod p) (e7_cartan_mul_N i j)
      push_cast at this
      rw [this]
    calc ∑ k, ((2 : ZMod p)⁻¹ * ∑ j, (e7N k j : ZMod p) * t j) *
          ((iform (Pi.single k 1 : Fin Tag.E7.rank → ℤ) (Pi.single i 1) : ℤ) : ZMod p)
        = (2 : ZMod p)⁻¹ * ∑ j, (∑ k, (iform (Pi.single i 1 : Fin Tag.E7.rank → ℤ)
            (Pi.single k 1) : ZMod p) * (e7N k j : ZMod p)) * t j := by
          simp only [Finset.mul_sum, Finset.sum_mul, e7_iform_symm _ i]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
      _ = t i := by
          simp only [key]
          simp [Finset.sum_ite_eq, mul_comm]
          rw [mul_assoc, mul_inv_cancel₀ h2, mul_one]


private theorem zpow_val_eq_zpow_p {G : Type} [Group G] {p : ℕ} [NeZero p] {ζ : G} (hζ : ζ ^ p = 1)
    (m : ℤ) : ζ ^ ((m : ZMod p).val) = ζ ^ m := by
  rw [zpow_eq_zpow_emod' (x := ζ) m hζ, ← ZMod.val_intCast (n := p) m, zpow_natCast]

theorem rootDiagUnit_zetaVec_mem_rootSpan_D6
    {L : Type} [Field L] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {ζ : Lˣ} (hζ : ζ ^ p = 1)
    {t : Fin Tag.E7.rank → ZMod p} (ht : ∑ j, (e7Theta j : ZMod p) * t j = 0) :
    rootDiagUnit .E7 (zetaVec ζ hζ t) ∈ rootSpan .E7 L e7D6Roots := by
  obtain ⟨u, hu0, hu⟩ := exists_e7_coroot_coeffs hp2 t ht
  let a : Fin Tag.E7.rank → Fin Tag.E7.rank → Lˣ := fun k i =>
    (ζ ^ (u k).val) ^ (iform (Pi.single k 1 : Fin Tag.E7.rank → ℤ) (Pi.single i 1))
  let H : Subgroup (Fin Tag.E7.rank → Lˣ) :=
    (rootSpan .E7 L e7D6Roots).comap (rootDiagUnitHom .E7 L)
  have hk : ∀ k : Fin Tag.E7.rank,
      rootTorusSL2 .E7 L (Pi.single k 1) (ζ ^ (u k).val) = rootDiagUnit .E7 (a k) := by
    intro k
    rw [CFSG.LieType.SeitzGeneration.ExcHighThree.rootTorusSL2_eq_rootDiagUnit_corootPair
      (isRoot_single .E7 k)]
    have hkk : ∀ k : Fin Tag.E7.rank,
        iform (Pi.single k 1 : Fin Tag.E7.rank → ℤ) (Pi.single k 1) = 2 := by
      decide +kernel
    congr 1
    funext i
    rw [hkk k]
    congr 1
    omega
  have haH : ∀ k, a k ∈ H := by
    intro k
    by_cases hk0 : k = 0
    · subst hk0
      have h1 : a 0 = 1 := by
        funext i
        simp [a, hu0]
      rw [h1]
      exact H.one_mem
    · have hmemk : (Pi.single k 1 : Fin Tag.E7.rank → ℤ) ∈ e7D6Roots := by
        refine ⟨isRoot_single .E7 k, ?_⟩
        simp [Pi.single_apply, Ne.symm hk0]
      have hmemk' : -(Pi.single k 1 : Fin Tag.E7.rank → ℤ) ∈ e7D6Roots := by
        refine ⟨IsRoot.neg (isRoot_single .E7 k), ?_⟩
        simp [Pi.single_apply, Ne.symm hk0]
      show rootDiagUnit .E7 (a k) ∈ rootSpan .E7 L e7D6Roots
      rw [← hk k]
      exact rootRankOneGroup_le_rootSpan (isRoot_single .E7 k) hmemk hmemk' ⟨_, rfl⟩
  have hz : zetaVec ζ hζ t = ∏ k, a k := by
    funext i
    rw [zetaVec_apply, Finset.prod_apply]
    have h1 : ∏ k, a k i = ζ ^ (∑ k, ((u k).val : ℤ) *
        iform (Pi.single k 1 : Fin Tag.E7.rank → ℤ) (Pi.single i 1)) := by
      rw [← Finset.prod_zpow_eq_zpow_sum]
      refine Finset.prod_congr rfl fun k _ => ?_
      simp only [a]
      rw [← zpow_natCast, ← zpow_mul]
    rw [h1, ← zpow_val_eq_zpow_p hζ]
    congr 2
    rw [← hu i]
    push_cast
    simp [ZMod.natCast_zmod_val]
  show zetaVec ζ hζ t ∈ H
  rw [hz]
  exact Subgroup.prod_mem _ fun k _ => haH k

theorem rootDiagUnit_zetaVec_single_mem_rootSpan_theta
    {L : Type} [Field L] {p : ℕ} [Fact p.Prime] {ζ : Lˣ} (hζ : ζ ^ p = 1) (s : ZMod p) :
    rootDiagUnit .E7 (zetaVec ζ hζ (Pi.single (0 : Fin Tag.E7.rank) s)) ∈
      rootSpan .E7 L {e7Theta, -e7Theta} := by
  have h1 := CFSG.LieType.SeitzGeneration.ExcHighThree.rootTorusSL2_eq_rootDiagUnit_corootPair
    (τ := .E7) (L := L) isRoot_e7Theta (ζ ^ s.val)
  have h2 : (fun i => (ζ ^ s.val) ^ (2 * iform e7Theta (Pi.single i 1) / iform e7Theta e7Theta)) =
      zetaVec ζ hζ (Pi.single (0 : Fin Tag.E7.rank) s) := by
    funext i
    rw [zetaVec_apply]
    have hθθ : iform e7Theta e7Theta = 2 := by decide +kernel
    have hθi : ∀ i : Fin Tag.E7.rank, iform e7Theta (Pi.single i 1) = if i = 0 then 1 else 0 := by
      decide +kernel
    rw [hθθ, hθi i]
    by_cases hi : i = 0
    · subst hi
      simp
    · simp [hi]
  rw [← h2, ← h1]
  exact rootRankOneGroup_le_rootSpan isRoot_e7Theta (by simp) (by simp) ⟨_, rfl⟩

end CFSG.StandardType.PhiTwoRootGen

end

module

public import CFSG.LieType.Ree.LargeReeInvolutionFusionCoords

public section

namespace CFSG.RankThree.PartOne.SEITZ12

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.LieType.Ree.LargeReeCover

theorem phi4ml_cartanPair_F :
    (F4.cartanPair (f4i 1) (orbitCertRoot F4.tag 43) = 0 ∧
      F4.cartanPair (f4i 2) (orbitCertRoot F4.tag 43) = 1) ∧
    (F4.cartanPair (f4i 1) (orbitCertRoot F4.tag 46) = 1 ∧
      F4.cartanPair (f4i 2) (orbitCertRoot F4.tag 46) = 0) := by
  decide +kernel

set_option linter.unusedSectionVars false

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem phi4ml_B_mem (hK : Nat.card K = 2 ^ (2 * m + 1)) (b c : K) :
    sylowB m K b c ∈ rankOneGroupTwo K m :=
  Subgroup.subset_closure (Or.inl (Or.inl (sylowB_mem_U2 hK b c)))

theorem phi4ml_weight_F (u : Kˣ) :
    ((torusWeight m (orbitCertRoot F4.tag 43) (1, u) : Kˣ) : K) = (u : K) ^ 2 ^ m ∧
      ((torusWeight m (orbitCertRoot F4.tag 46) (1, u) : Kˣ) : K) = (u : K) := by
  obtain ⟨⟨h1, h2⟩, ⟨h1', h2'⟩⟩ := phi4ml_cartanPair_F
  refine ⟨?_, ?_⟩ <;> rw [torusWeight_apply, one_zpow, one_mul] <;> simp only [torusExp1]
  · rw [h1, h2, zero_add, one_mul, show (2 : ℤ) ^ m = ((2 ^ m : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, Units.val_pow_eq_pow_val]
  · rw [h1', h2', zero_mul, add_zero, zpow_one]

theorem phi4ml_torus_F (hK : Nat.card K = 2 ^ (2 * m + 1)) (u : Kˣ) :
    ∃ τ ∈ rankOneGroupTwo K m, ∀ g : K,
      τ * sylowF m K 0 g * τ⁻¹ = sylowF m K 0 ((u : K) ^ 2 ^ m * g) := by
  obtain ⟨w43, w46⟩ := phi4ml_weight_F (m := m) (K := K) u
  refine ⟨pairedTorusHom m (f4i 1) (f4i 2) u,
    Subgroup.subset_closure (Or.inl (Or.inr ⟨u, rfl⟩)), fun g => ?_⟩
  rw [← rankOneTorusPair_right, sylowF_zero_left, sylowF_zero_left, sylowX, sylowX, sylowX,
    sylowX, weyl_conj_mul,
    torusPair_conj_pinnedX m (1, u) (sylowRoot_pos (r := 43) (by norm_num) (by norm_num)).1,
    torusPair_conj_pinnedX m (1, u) (sylowRoot_pos (r := 46) (by norm_num) (by norm_num)).1,
    w43, w46, largeReeSigma_mul, largeReeSigma_pow hK]

set_option linter.unusedVariables false in
theorem phi4ml_weyl_F (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    ∃ n ∈ rankOneGroupTwo K m, ∀ g : K, n * sylowF m K 0 g * n⁻¹ = sylowD m K 0 g := by
  refine ⟨weylTwo K, Subgroup.subset_closure (Or.inr rfl), fun g => ?_⟩
  rw [sylowF_zero_left, sylowD_zero_left, weylTwo_conj_pair (r₁ := 43) (r₁' := 36) (r₂ := 46)
    (r₂' := 39) (by decide) (by decide)]

end CFSG.RankThree.PartOne.SEITZ12

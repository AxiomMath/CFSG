module

public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionCore
public import CFSG.LieType.Steinberg.CentralExt.SUPosLift
public import CFSG.LieType.HighestRoot.GenUnitary
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.StandardType

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits

namespace GGRootSU

section General

variable {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}

theorem mul_comm_of_sub_one_mul {A B : Matrix (Fin n) (Fin n) F}
    (h1 : (A - 1) * (B - 1) = 0) (h2 : (B - 1) * (A - 1) = 0) : A * B = B * A := by
  have e : A * B - B * A = (A - 1) * (B - 1) - (B - 1) * (A - 1) := by noncomm_ring
  rw [h1, h2, sub_zero] at e
  exact sub_eq_zero.1 e

theorem exists_nsmul_of_mem_wt2' {e w : Fin (n / 2) → ℤ} (h : w ∈ wt2 e) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ∧ w = k • e := by
  rcases mem_wt2.1 h with rfl | rfl
  exacts [⟨1, le_rfl, by norm_num, (one_nsmul _).symm⟩, ⟨2, by norm_num, le_rfl, rfl⟩]

theorem mul_eq_zero_of_hasWt_wt2 {e : Fin (n / 2) → ℤ} (he : e ≠ 0)
    (h2 : ∀ a b : Fin n, weight n a - weight n b ≠ 2 • e)
    {N M : Matrix (Fin n) (Fin n) F} (hN : HasWt (wt2 e) N) (hM : HasWt (wt2 e) M) :
    N * M = 0 := by
  have hNM : HasWt (∅ : Set (Fin (n / 2) → ℤ)) (N * M) := hN.mul hM fun a c b hac hcb => by
    exfalso
    obtain ⟨k, hk1, -, hk⟩ := exists_nsmul_of_mem_wt2' hac
    obtain ⟨l, hl1, -, hl⟩ := exists_nsmul_of_mem_wt2' hcb
    have hs : weight n a - weight n b = (k + l) • e := by
      rw [add_nsmul, ← hk, ← hl]
      abel
    by_cases h3 : 3 ≤ k + l
    · exact he (eq_zero_of_weight_sub_eq_nsmul hs h3)
    · have hkl : k + l = 2 := by omega
      rw [hkl] at hs
      exact h2 a b hs
  exact Matrix.ext fun a b => hNM.eq_zero_apply (Set.notMem_empty _)

theorem rootGroup_mul_comm_of_not_two {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ ≠ 0)
    (h2 : ∀ a b : Fin n, weight n a - weight n b ≠ 2 • toStd n γ) :
    ∀ x ∈ rootGroup σ hσ n γ, ∀ y ∈ rootGroup σ hσ n γ, x * y = y * x := by
  intro x hx y hy
  apply mat_injective
  rw [map_mul, map_mul]
  exact mul_comm_of_sub_one_mul
    (mul_eq_zero_of_hasWt_wt2 hγ h2 (hasWt_of_mem_rootGroup hσ hx) (hasWt_of_mem_rootGroup hσ hy))
    (mul_eq_zero_of_hasWt_wt2 hγ h2 (hasWt_of_mem_rootGroup hσ hy) (hasWt_of_mem_rootGroup hσ hx))

omit [Field F] in
theorem ht_two_nsmul' (v : Fin (n / 2) → ℤ) : ht (2 • v) = 2 * ht v := by
  simp [ht, Finset.mul_sum]

omit [Field F] in
theorem weight_sub_ne_two_smul_of_maxHeight {γ₀ : Fin (n / 2) → ℤ}
    (hγ₀ : γ₀ ∈ roots (isFiniteType_cartan n) (divisible n)) (hpos : 0 < ht γ₀)
    (hmax : ∀ δ ∈ roots (isFiniteType_cartan n) (divisible n), ht δ ≤ ht γ₀) (a b : Fin n) :
    weight n a - weight n b ≠ 2 • toStd n γ₀ := by
  intro h
  have hne := toStd_ne_zero_of_mem_roots hγ₀
  obtain ⟨-, hwa⟩ := eq_rev_of_weight_sub_eq_two_smul h hne
  have ha : a ≠ Fin.rev a := fun h' => hne (by rw [← hwa, weight_eq_zero_of_rev_eq h'.symm])
  have h2 : 2 • γ₀ ∈ roots (isFiniteType_cartan n) (divisible n) := by
    rw [roots_eq]
    exact Or.inr (Or.inl ⟨a, ha, by rw [toStd_nsmul_two, hwa]⟩)
  have := hmax _ h2
  rw [ht_two_nsmul'] at this
  omega

end General

section Finite

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} [Fact (Nat.Prime 2)]

theorem rootGroup_mul_comm_of_maxHeight (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ}
    {γ₀ : Fin (rootDatum hF n).rank → ℤ} (hγ₀ : γ₀ ∈ (rootDatum hF n).roots)
    (hmax : ∀ δ ∈ (rootDatum hF n).roots, ht δ ≤ ht γ₀) :
    ∀ x ∈ (rootDatum hF n).rootGroup γ₀, ∀ y ∈ (rootDatum hF n).rootGroup γ₀,
      x * y = y * x :=
  rootGroup_mul_comm_of_not_two (unitaryInvolution_involutive hF) (toStd_ne_zero_of_mem_roots hγ₀)
    (weight_sub_ne_two_smul_of_maxHeight hγ₀ (ht_pos_of_maxHeight (D := rootDatum hF n) hγ₀ hmax)
      hmax)

theorem ggRootSylowCentral_unitary (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n) :
    GGRootSylowCentral (rootDatum hF n) .PSU := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine ggRootSylowCentral_of_longRoot (isCTGroupDatum hF n hn ζ hζ)
    (steinbergExtras hF n hn ζ hζ)
    (CFSG.LieType.Steinberg.CentralExt.SUBruhat.bruhatExtras hF hn ζ hζ)
    (fun γ hγ => isPGroup_rootGroup hσ (toStd_ne_zero_of_mem_roots hγ))
    (CFSG.LieType.Steinberg.CentralExt.SUClosed.coprime_card_torus hF)
    (fun γ₀ hγ₀ hmax => rootGroup_mul_comm_of_maxHeight hF hγ₀ hmax)
    (fun γ₀ _ _ δ hδ e x hx y hy => ?_) fun γ hγ => hγ.longRoot_of_twisted (Or.inl rfl)
  subst e
  exact (CFSG.LieType.HighestRoot.commute_of_mem_rootGroup_two_smul hσ
    (toStd_ne_zero_of_mem_roots hδ) hy hx).symm.eq

end Finite

end GGRootSU

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22f

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def Fix108H (D : Data G) : Prop :=
  H1930 D → ∀ H ∈ hSet D.T D.M, ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ X : Subgroup G, X ≤ H ⊓ D.M →
    Nat.card X = q → Permutes X D.T → ∃ h ∈ H, h ∉ D.M ∧ uniqueFourConj h X ≤ D.M

@[expose] def Final2210 (D : Data G) : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ P₁ P₂ A : Subgroup G, ∀ g z : G,
    P₁ ≤ D.M → P₂ ≤ D.M → IsPGroup q ↥P₁ → IsPGroup q ↥P₂ →
    (∀ x ∈ P₁, x ^ q = 1) → (∀ x ∈ P₂, x ^ q = 1) → q ^ 2 ≤ Nat.card ↥P₁ → q ^ 2 ≤ Nat.card ↥P₂ →
    rankThreeGamma 1 q P₁ ≤ D.M → rankThreeGamma 1 q P₂ ≤ D.M →
    Nat.card ↥A = q → A ≤ P₁ → A ≤ P₂ → z ≠ 1 → z ∈ pCoreOf 2 D.M →
    (∀ a ∈ A, a * z = z * a) → g ∈ centralizer ({z} : Set G) → g ∉ D.M →
    uniqueFourConj g A ≠ A → (∀ a ∈ A, ∀ b ∈ uniqueFourConj g A, a * b = b * a) →
    uniqueFourConj g A ≤ D.M → A ≤ uniqueFourConj g D.M →
    uniqueFourConj g A ≤ normalizer (P₁ : Set G) →
    A ≤ normalizer ((uniqueFourConj g P₂ : Subgroup G) : Set G) → False

theorem uc22p22r_mem_conj_inv (X : Subgroup G) (g x : G) :
    x ∈ uniqueFourConj g⁻¹ X ↔ g⁻¹ * x * g ∈ X := by
  rw [uc22p22f_mem_conj, inv_inv]

theorem uc22p22r_conj_conj (X : Subgroup G) (g h : G) :
    uniqueFourConj h (uniqueFourConj g X) = uniqueFourConj (g * h) X := by
  ext x
  rw [uc22p22f_mem_conj, uc22p22f_mem_conj, uc22p22f_mem_conj,
    show g * h * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ by group]

theorem uc22p22r_conj_self_of_mem (X : Subgroup G) {g : G} (hg : g ∈ X) : uniqueFourConj g X = X := by
  ext x
  rw [uc22p22f_mem_conj]
  constructor
  · intro h
    have h1 := X.mul_mem (X.mul_mem (X.inv_mem hg) h) hg
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h1
  · intro h
    exact X.mul_mem (X.mul_mem hg h) (X.inv_mem hg)

theorem uc22p22r_conj_mono {X Y : Subgroup G} (h : X ≤ Y) (g : G) :
    uniqueFourConj g X ≤ uniqueFourConj g Y := by
  intro x hx
  rw [uc22p22f_mem_conj] at hx ⊢
  exact h hx

theorem uc22p22r_card_conj (X : Subgroup G) (g : G) : Nat.card ↥(uniqueFourConj g X) = Nat.card ↥X :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem uc22p22r_isPGroup_conj {p : ℕ} {X : Subgroup G} (h : IsPGroup p ↥X) (g : G) :
    IsPGroup p ↥(uniqueFourConj g X) :=
  h.map _

theorem uc22p22r_pow_conj {q : ℕ} {X : Subgroup G} (h : ∀ x ∈ X, x ^ q = 1) (g : G) :
    ∀ x ∈ uniqueFourConj g X, x ^ q = 1 := by
  intro x hx
  rw [uc22p22f_mem_conj] at hx
  have h1 := h _ hx
  rw [conj_pow] at h1
  calc x ^ q = g⁻¹ * (g * x ^ q * g⁻¹) * g := by group
    _ = 1 := by rw [h1]; group

theorem uc22p22r_mem_normalizer_conj (X : Subgroup G) (g x : G) :
    x ∈ normalizer ((uniqueFourConj g X : Subgroup G) : Set G) ↔
      g * x * g⁻¹ ∈ normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have h1 := h (g⁻¹ * y * g)
    rw [uc22p22f_mem_conj, uc22p22f_mem_conj,
      show g * (g⁻¹ * y * g) * g⁻¹ = y by group,
      show g * (x * (g⁻¹ * y * g) * x⁻¹) * g⁻¹ = g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹ by group] at h1
    exact h1
  · intro h y
    have h1 := h (g * y * g⁻¹)
    rw [uc22p22f_mem_conj, uc22p22f_mem_conj,
      show g * (x * y * x⁻¹) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ by group]
    exact h1

theorem uc22p22r_conj_le_normalizer {X Y : Subgroup G} (h : Y ≤ normalizer (X : Set G)) (g : G) :
    uniqueFourConj g Y ≤ normalizer ((uniqueFourConj g X : Subgroup G) : Set G) := by
  intro y hy
  rw [uc22p22f_mem_conj] at hy
  exact (uc22p22r_mem_normalizer_conj X g y).2 (h hy)

theorem uc22p22r_maxTwoLocal_conj {M : Subgroup G} (hM : rankThreeIsMaxTwoLocal M) (g : G) :
    rankThreeIsMaxTwoLocal (uniqueFourConj g M) :=
  CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeIsMaxTwoLocal_map hM (MulAut.conj g⁻¹)

theorem uc22p22r_conj_ne_of_not_mem (D : Data G) {g : G} (hg : g ∉ D.M) : uniqueFourConj g D.M ≠ D.M := by
  intro h
  apply hg
  rw [← CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing D.M D.maxLocal,
    Subgroup.mem_normalizer_iff]
  intro x
  rw [← uc22p22f_mem_conj, h]

theorem uc22p22r_gamma_conj {q : ℕ} (hq : q.Prime) {M P : Subgroup G} {k : G} (hk : k ∈ M)
    (hΓ : rankThreeGamma 1 q P ≤ M) : rankThreeGamma 1 q (uniqueFourConj k P) ≤ M := by
  refine uc22p22f_gamma_of_conj hq hk ?_
  have e : (uniqueFourConj k P).map (MulAut.conj k).toMonoidHom = P := by
    ext x
    rw [Subgroup.mem_map_equiv, uc22p22f_mem_conj]
    simp [mul_assoc]
  rw [e]
  exact hΓ

end CFSG.LocalAnalysis.UniquenessCase.UC22

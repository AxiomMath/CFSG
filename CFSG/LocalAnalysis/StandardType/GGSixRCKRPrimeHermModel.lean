module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeHermTransport
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeHermRoot
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSmall

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
open scoped Matrix

theorem exists_suModel_of_hermForm
    {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {q m : ℕ} (hK : Nat.card K = (2 ^ q) ^ 2) (hq : 1 ≤ q) (hW : Module.finrank K W = m)
    (hm : 2 ≤ m) {σ : K ≃+* K} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (β : W →ₛₗ[σ.toRingHom] W →ₗ[K] K) (hβs : β.IsSymm) (hβn : β.SeparatingLeft) :
    ∃ ρ : (ggU .PSU m q).K →* (W ≃ₗ[K] W), Function.Injective ρ ∧
      (∀ g : W ≃ₗ[K] W, g ∈ ρ.range ↔
        (∀ w w', β (g w) (g w') = β w w') ∧ LinearMap.det (g : W →ₗ[K] W) = 1) ∧
      ∃ (β₀ : Fin (ggU .PSU m q).D.rank → ℤ) (v : W), β₀ ∈ (ggU .PSU m q).D.roots ∧
        GGLongRoot (ggU .PSU m q).D β₀ ∧ Nat.card ((ggU .PSU m q).D.rootGroup β₀) = 2 ^ q ∧
        v ≠ 0 ∧ β v v = 0 ∧
        ∀ y ∈ (ggU .PSU m q).D.rootGroup β₀, ∃ c : K, σ c = c ∧
          ∀ w, ρ y w = w + (c * β v w) • v := by
  obtain ⟨g, rfl⟩ : ∃ g, q = g + 1 := ⟨q - 1, by omega⟩
  have hf : 1 ≤ g + 1 := by omega
  let F₀ := GaloisField 2 (2 * (g + 1))
  have hc : Nat.card F₀ = (2 ^ (g + 1)) ^ 2 := by
    dsimp only [F₀]
    exact card_galoisField_two_mul 2 (g + 1) hf
  have hU : ggU .PSU m (g + 1) =
      ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F₀ 2 (g + 1)) m,
        Unitary.rootDatum hc m⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte, F₀]
  obtain ⟨τ, e, ρ, hτ, he, hρ, hinj, hrange⟩ :=
    exists_suModel_of_hermForm_explicit (F₀ := F₀) (K := K) (W := W) (f := g + 1)
      (m := m) hc (by simpa using hK) hW hσ2 hσ1 β hβs hβn
  obtain ⟨β₀, v, hβ₀, hlong, hcard, hv, hiso, hact⟩ :=
    exists_longRoot_transv_of_suModel (F₀ := F₀) (K := K) (W := W) (f := g + 1)
      (m := m) hc hm (σ := σ) β τ hτ e he ρ hρ
  rw [hU]
  exact ⟨ρ, hinj, hrange, β₀, v, hβ₀, hlong, hcard, hv, hiso, hact⟩

theorem isQuasisimple_ggU_PSU
    {m q : ℕ} (hm : 2 ≤ m) (hq : 2 ≤ q) : CFSG.IsQuasisimple (ggU .PSU m q).K := by
  obtain ⟨g, rfl⟩ : ∃ g, q = g + 1 := ⟨q - 1, by omega⟩
  have hf : 1 ≤ g + 1 := by omega
  let F₀ := GaloisField 2 (2 * (g + 1))
  have hc : Nat.card F₀ = (2 ^ (g + 1)) ^ 2 := by
    dsimp only [F₀]
    exact card_galoisField_two_mul 2 (g + 1) hf
  have hU : ggU .PSU m (g + 1) =
      ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F₀ 2 (g + 1)) m,
        Unitary.rootDatum hc m⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte, F₀]
  have h4 : 4 ≤ Nat.card (GaloisField 2 (g + 1)) := by
    rw [GaloisField.card 2 (g + 1) (by omega : g + 1 ≠ 0)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (g + 1) := Nat.pow_le_pow_right (by norm_num) hq
  by_cases hm2 : m = 2
  · subst m
    have hSL : CFSG.IsQuasisimple (ggU .PSL 2 (g + 1)).K := by
      change CFSG.IsQuasisimple
        (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (g + 1)))
      exact CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le
        (K := GaloisField 2 (g + 1)) (m := 2) le_rfl (Or.inr h4)
    obtain ⟨e⟩ := rckRP_nonempty_mulEquiv_PSL_two_PSU_two (g := g + 1) hf
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hSL
  · have hm3 : 3 ≤ m := by omega
    rw [hU]
    refine Unitary.isQuasisimple_SU (F := F₀) (p := 2) (f := g + 1) (n := m) hc hm3 ?_
    intro hnq
    have h2 : 2 ^ (g + 1) = 2 := congrArg Prod.snd hnq
    have h4' : 4 ≤ 2 ^ (g + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (g + 1) := Nat.pow_le_pow_right (by norm_num) hq
    omega

end CFSG.StandardType.RCKRP

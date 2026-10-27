module

public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelFactors
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresTransport

public section

namespace CFSG.StandardType

namespace LayerCyc

open Matrix LayerCores

section Factors

variable {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)] {d : Fin r → ℕ}
  {τ : PiMat D d → PiMat D d} {π : Fin r → Fin r}

variable [∀ i, NeZero (d i)]

omit [∀ i, NeZero (d i)] in
theorem hasCycCore_factorGroup (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    (hfix : ∀ b (hb : π b = b), HasCycCore (matUnitary (isInvol_tauFix hτ hπ hb)))
    (hpair : ∀ b, π b ≠ b → HasCycCore (⊤ : Subgroup (GL (Fin (d b)) (D b)))) (b : Fin r) :
    HasCycCore (factorGroup π hτ hπ b) := by
  unfold factorGroup
  split_ifs with hb
  · exact hfix b hb
  · exact hpair b hb

theorem exists_cycCore_of_factors (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    (hfix : ∀ b (hb : π b = b), HasCycCore (matUnitary (isInvol_tauFix hτ hπ hb)))
    (hpair : ∀ b, π b ≠ b → HasCycCore (⊤ : Subgroup (GL (Fin (d b)) (D b)))) :
    ∃ (β : Type) (S : β → Subgroup (PiMat D d)ˣ), IsCycCoreFamily (unitaryOf hτ) S := by
  choose Sf hSle hSn hder hq using hasCycCore_factorGroup hτ hπ hfix hpair
  refine ⟨{b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥}, fun c => coreOf π hτ Sf c.1,
    fun c => coreOf_le hτ Sf c.1, fun c u hu s hs => conj_mem_coreOf hτ hπ hSn hu hs,
    fun c => ?_, exists_ggDer_le_iSup_coreOf hτ hπ hSle hder, fun c => ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (MulEquiv.ofBijective _ (bijective_coreOf hτ hπ hSle c.1)).symm
      ((hq c.1).resolve_left c.2.2).1
  · exact isCyclic_center_of_mulEquiv
      (MulEquiv.ofBijective _ (bijective_coreOf hτ hπ hSle c.1)).symm
      ((hq c.1).resolve_left c.2.2).2

end Factors

theorem exists_cycCoreFamily_unitaryOf {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)]
    [∀ i, Finite (D i)] [∀ i, CharP (D i) 2] {d : Fin r → ℕ} [∀ i, NeZero (d i)]
    {τ : PiMat D d → PiMat D d} (hτ : IsInvol τ) (hy : ∃ y, y + τ y = 1) :
    ∃ (β : Type) (S : β → Subgroup (PiMat D d)ˣ), IsCycCoreFamily (unitaryOf hτ) S := by
  obtain ⟨π, hπ⟩ := hτ.exists_perm
  have hfix : ∀ b (hb : π b = b), HasCycCore (matUnitary (isInvol_tauFix hτ hπ hb)) := by
    intro b hb
    by_cases hk : ∀ c : D b, tauFix τ b (Matrix.scalar (Fin (d b)) c) =
        Matrix.scalar (Fin (d b)) c
    · obtain ⟨Y, hY⟩ := hy
      refine hasCycCore_alt (isInvol_tauFix hτ hπ hb) hk ⟨Y b, ?_⟩
      have h1 := congrFun hY b
      rwa [Pi.add_apply, apply_tau_eq_tauFix hτ hπ hb, Pi.one_apply] at h1
    · push Not at hk
      exact hasCycCore_herm (isInvol_tauFix hτ hπ hb) hk
  exact exists_cycCore_of_factors hτ hπ hfix (fun b _ => hasCycCore_top_GL (d b))

theorem exists_cycCoreFamily_adjCent {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type}
    [Fintype ι] [DecidableEq ι] {A : Subgroup (GL ι K)} (hA : (Nat.card A : K) ≠ 0)
    {adj : Matrix ι ι K → Matrix ι ι K} (hadj : IsInvol adj)
    (hstab : ∀ X : Matrix ι ι K, (∀ g ∈ A, X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * X) →
      ∀ g ∈ A, adj X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * adj X)
    (hsymd : ∃ Y : Matrix ι ι K, (∀ g ∈ A, Y * (g : Matrix ι ι K) = (g : Matrix ι ι K) * Y) ∧
      Y + adj Y = 1) :
    ∃ (β : Type) (S : β → Subgroup (GL ι K)), IsCycCoreFamily (adjCent A hadj) S := by
  obtain ⟨r, D, d, _, _, _, _, Φ, hΦ, hR⟩ := exists_algHom_pi_matrix_commutant A hA
  have : ∀ i, CharP (D i) 2 := fun i =>
    charP_of_injective_algebraMap (algebraMap K (D i)).injective 2
  obtain ⟨τ, hτ, hτΦ, himg⟩ := exists_tau_of_adj Φ hΦ hR hadj fun X hX =>
    (hR _).mpr (hstab X ((hR X).mp hX))
  have hy : ∃ y, y + τ y = 1 := by
    obtain ⟨Y, hYc, hY⟩ := hsymd
    obtain ⟨y, rfl⟩ := (hR Y).mpr hYc
    exact ⟨y, hΦ (by rw [map_add, hτΦ, hY, map_one])⟩
  obtain ⟨β, S, hS⟩ := exists_cycCoreFamily_unitaryOf hτ hy
  refine ⟨β, fun c => (S c).map (Units.map Φ.toMonoidHom), ?_⟩
  rw [← himg]
  exact hS.map _ (Units.map_injective (f := Φ.toMonoidHom) hΦ)

end LayerCyc

end CFSG.StandardType

end

module

public import CFSG.Quasithin.Background.Harris.L3.Classify

public section

namespace CFSG.Quasithin.G11.Harris.L3

open CFSG.Quasithin CFSG.Quasithin.H.L3Nine CFSG.QuasithinUnique.Setup.X7a Matrix
open scoped MatrixGroups

theorem sl3_classification_wide {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] [Fintype F]
    [CharP F 2] (hF : Fintype.card F = 2 ^ f) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (ρ : Representation (ZMod 2) SL(3, F) W) (hirr : ρ.IsIrreducible)
    (hnt : ∃ g, ρ g ≠ 1) (hdim : Module.finrank (ZMod 2) W ≤ 4 * f + 6) :
    ((∃ ψ : SL(3, F) →* SL(3, F), (∀ g, ψ (ψ g) = g) ∧ ∃ E : W ≃+ (Fin 3 → F),
        ∀ g w, E (ρ g w) = ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E w) ∧
      Module.finrank (ZMod 2) W = 3 * f) ∨
    (∃ k : ℕ, f = 2 * k ∧ Module.finrank (ZMod 2) W = 9 * k ∧
      ∃ hK : Nat.card F = (2 ^ k) ^ 2, ∃ ψ : SL(3, F) →* SL(3, F), (∀ g, ψ (ψ g) = g) ∧
        ∃ E : Multiplicative W ≃* HMod k F, ∀ g u,
          E (Multiplicative.ofAdd (ρ g u)) = rho hK (ψ g) (E (Multiplicative.ofAdd u))) := by
  classical
  have hfin : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  let bas := Module.finBasis (ZMod 2) W
  obtain ⟨a, b, hne, hsum, W₀, ⟨e₀⟩⟩ := B42SL3.exists_label hF (by omega) ρ bas hirr hnt
  have hdim' : ∀ c : (Fin f → Bool) × (Fin f → Bool),
      3 ^ cntS c.1 c.2 * 8 ^ cntH c.1 c.2 ≤
        2 * (tensorRep (F := F) F c.1 c.2 (up3 0 0 1) - 1).rank + 1 :=
    fun c => dim_le_two_mul_rank_tensorRep c.1 c.2
  have hrank := SL3Small.two_mul_finrank_range_le ρ (SL3Small.up3_mul_self (F := F))
  rcases B45SL3.label_cases' (by omega) a b hne _ hdim' hsum with ⟨hS, hH⟩ | ⟨hS, hH, hR4, -⟩ |
      ⟨-, -, -, hR4⟩ | hR5
  · left
    obtain ⟨ψ, hψ, E, hE⟩ := B42SL3.exists_natural_of_single hF ρ bas hirr hS hH W₀ e₀
    refine ⟨⟨ψ, hψ, E, hE⟩, finrank_eq_of_natCard ?_⟩
    rw [Nat.card_congr E.toEquiv, Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card (α := F),
      hF, ← pow_mul, mul_comm]
  · right
    have hlt : (pairOrbit f (a, b)).card < f := by omega
    obtain ⟨m, hm, hfm, hK, ψ, hψ, E, hE⟩ :=
      B45SL3.exists_herm_of_row hF ρ bas hirr hS hH hlt W₀ e₀
    have hcard : Nat.card W = 2 ^ (9 * m) := by
      rw [← card_HMod hm hK]
      exact (Nat.card_congr (Multiplicative.toAdd : Multiplicative W ≃ W).symm).symm.trans
        (Nat.card_congr E.toEquiv)
    exact ⟨m, hfm, finrank_eq_of_natCard hcard, hK, ψ, hψ, E, hE⟩
  · omega
  · omega

theorem sl3_f_one_classification {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ 1) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) SL(3, F) W) (hirr : ρ.IsIrreducible) (hnt : ∃ g, ρ g ≠ 1)
    (hdim : Module.finrank (ZMod 2) W ≤ 6) :
    (∃ ψ : SL(3, F) →* SL(3, F), (∀ g, ψ (ψ g) = g) ∧ ∃ E : W ≃+ (Fin 3 → F),
        ∀ g w, E (ρ g w) = ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E w) ∧
      Module.finrank (ZMod 2) W = 3 := by
  rcases sl3_small_classification' (f := 1) le_rfl hF ρ hirr hnt (by omega) with
    ⟨h, h3⟩ | ⟨k, hk, -⟩
  · exact ⟨h, h3⟩
  · omega

end CFSG.Quasithin.G11.Harris.L3

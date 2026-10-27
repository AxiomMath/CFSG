module

public import CFSG.Quasithin.Background.SL3SmallNat
public import CFSG.Quasithin.Background.SmithB45SL3Label
public import CFSG.Quasithin.Background.SmithB45SL3Herm

public section

namespace CFSG.Quasithin.G11.Harris.L3

open CFSG.Quasithin CFSG.Quasithin.H.L3Nine CFSG.QuasithinUnique.Setup.X7a Matrix
open scoped MatrixGroups

theorem charP_two_of_card {F : Type} [Field F] [Fintype F] {f : ℕ}
    (hF : Fintype.card F = 2 ^ f) : CharP F 2 := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hd : ringChar F ∣ 2 ^ f := by
    rw [← hF, hn]
    exact dvd_pow_self _ n.ne_zero
  have h2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)
  rw [← h2]
  exact ringChar.charP F

theorem finrank_eq_of_natCard {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {d : ℕ} (h : Nat.card W = 2 ^ d) : Module.finrank (ZMod 2) W = d := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h
  exact Nat.pow_right_injective (le_refl 2) h

theorem sl3_small_classification' {f : ℕ} (hf : 1 ≤ f) {F : Type} [Field F] [Fintype F]
    [CharP F 2] (hF : Fintype.card F = 2 ^ f) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (ρ : Representation (ZMod 2) SL(3, F) W) (hirr : ρ.IsIrreducible)
    (hnt : ∃ g, ρ g ≠ 1) (hdim : Module.finrank (ZMod 2) W ≤ 4 * f + 2) :
    ((∃ ψ : SL(3, F) →* SL(3, F), (∀ g, ψ (ψ g) = g) ∧ ∃ E : W ≃+ (Fin 3 → F),
        ∀ g w, E (ρ g w) = ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E w) ∧
      Module.finrank (ZMod 2) W = 3 * f) ∨
    (∃ k : ℕ, f = 2 * k ∧ (k = 1 ∨ k = 2) ∧ Module.finrank (ZMod 2) W = 9 * k ∧
      ∃ hK : Nat.card F = (2 ^ k) ^ 2, ∃ ψ : SL(3, F) →* SL(3, F), (∀ g, ψ (ψ g) = g) ∧
        ∃ E : Multiplicative W ≃* HMod k F, ∀ g u,
          E (Multiplicative.ofAdd (ρ g u)) = rho hK (ψ g) (E (Multiplicative.ofAdd u))) := by
  classical
  have hfin : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  let bas := Module.finBasis (ZMod 2) W
  obtain ⟨a, b, hne, hsum, W₀, ⟨e₀⟩⟩ := B42SL3.exists_label hF hf ρ bas hirr hnt
  have hdim' : ∀ c : (Fin f → Bool) × (Fin f → Bool),
      3 ^ cntS c.1 c.2 * 8 ^ cntH c.1 c.2 ≤
        2 * (tensorRep (F := F) F c.1 c.2 (up3 0 0 1) - 1).rank + 1 :=
    fun c => dim_le_two_mul_rank_tensorRep c.1 c.2
  have hrank := SL3Small.two_mul_finrank_range_le ρ (SL3Small.up3_mul_self (F := F))
  rcases B45SL3.label_cases' hf a b hne _ hdim' hsum with ⟨hS, hH⟩ | ⟨hS, hH, hR4, -⟩ |
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
    have h9 := finrank_eq_of_natCard hcard
    exact ⟨m, hfm, by omega, h9, hK, ψ, hψ, E, hE⟩
  · omega
  · omega

end CFSG.Quasithin.G11.Harris.L3

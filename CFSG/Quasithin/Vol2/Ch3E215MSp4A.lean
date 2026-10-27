module

public import CFSG.Quasithin.Background.SmithB42Sp4Ident
public import CFSG.Quasithin.Background.SmithB42L2Sl2

public section

namespace CFSG.Quasithin.Ch3E215M.Sp4

open CFSG.Quasithin.B42Sp4 CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {F : Type} [Field F] [CharP F 2] [Fintype F]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem finrank_eq_four_of_card_le {f : ℕ} (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (π : antiSp F →* (M ≃ₗ[ZMod 2] M)) [Fact (repOf π).IsIrreducible]
    (hnt : ∃ g, repOf π g ≠ 1) (hcard : Nat.card M ≤ 2 ^ (4 * f)) :
    Module.finrank (EndRing (repOf π)) M = 4 := by
  classical
  obtain ⟨d, hd1, hDcard, hdesc⟩ := sp4_descent hF hf hnt
  have : Module.Finite (EndRing (repOf π)) M := Module.Finite.of_finite
  obtain ⟨E, _, _, _, ιF, ιD, S, hSne, hS, -, hshift, hdimW⟩ :=
    hdesc (Module.finBasis (EndRing (repOf π)) M)
  have hfd : f ≤ S.card * d := by
    have h := n_le_card_mul (n := 2 * f) (d := 2 * d) (by omega) (by omega)
      (fun i hi => Finset.mem_range.mp (hS hi)) hSne hshift
    have h2 : 2 * f ≤ 2 * (S.card * d) := by
      calc 2 * f ≤ S.card * (2 * d) := h
        _ = 2 * (S.card * d) := by ring
    omega
  have hM : Nat.card M = 2 ^ (d * 4 ^ S.card) := by
    rw [natCard_eq_pow_finrank (ρ := repOf π), hDcard, hdimW, ← pow_mul]
  rw [hM] at hcard
  have h1 : d * 4 ^ S.card ≤ 4 * f := (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard
  rw [hdimW]
  have hs1 : 1 ≤ S.card := Finset.card_pos.mpr hSne
  by_contra hne
  have hs2 : 2 ≤ S.card := by
    by_contra h
    have h' : S.card = 1 := by omega
    rw [h', pow_one] at hne
    exact hne rfl
  have h8 := Nat.mul_le_mul_left d (eight_mul_le_four_pow hs2)
  have hsd : 2 ≤ S.card * d := by nlinarith
  nlinarith

theorem exists_apply_eq_of_card_le {f : ℕ} (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (π : antiSp F →* (M ≃ₗ[ZMod 2] M)) [Fact (repOf π).IsIrreducible]
    (hnt : ∃ g, repOf π g ≠ 1) (hcard : Nat.card M ≤ 2 ^ (4 * f)) {w₁ w₂ : M} (h₁ : w₁ ≠ 0)
    (h₂ : w₂ ≠ 0) : ∃ g : antiSp F, π g w₁ = w₂ := by
  obtain ⟨i, φ, hφ⟩ :=
    exists_natural_of_four hF hf π hnt (finrank_eq_four_of_card_le hF hf π hnt hcard)
  have hu : φ w₁ ≠ 0 := fun h => h₁ (φ.injective (h.trans φ.map_zero.symm))
  have hv : φ w₂ ≠ 0 := fun h => h₂ (φ.injective (h.trans φ.map_zero.symm))
  obtain ⟨y, hy⟩ := antiSp_exists_mulVec_eq hu hv
  refine ⟨(minorAut F ^ i).symm y, φ.injective ?_⟩
  rw [hφ, MulEquiv.apply_symm_apply, hy]

omit [Fintype F] in
theorem exists_apply_eq_of_irr [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f)
    {Q : Type} [CommGroup Q] [Finite Q] (hQ : ∀ q : Q, q * q = 1) (ρ : antiSp F →* MulAut Q)
    (hirr : ∀ Y : Subgroup Q, (∀ γ, ∀ q ∈ Y, ρ γ q ∈ Y) → Y = ⊥ ∨ Y = ⊤) (hnt : ρ ≠ 1)
    (hcard : Nat.card Q ≤ 2 ^ (4 * f)) {q₁ q₂ : Q} (h₁ : q₁ ≠ 1) (h₂ : q₂ ≠ 1) :
    ∃ γ : antiSp F, ρ γ q₁ = q₂ := by
  classical
  let _ : Fintype F := Fintype.ofFinite F
  have hFf : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hF
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hQ
  let π : antiSp F →* (W ≃ₗ[ZMod 2] W) := (binPsi θ).toMonoidHom.comp ρ
  have hπ : ∀ γ w, π γ w = binPsi θ (ρ γ) w := fun _ _ => rfl
  have hirrQ : ∀ Y : Subgroup Q, (∀ l ∈ ρ.range, ∀ v ∈ Y, l v ∈ Y) → Y = ⊥ ∨ Y = ⊤ :=
    fun Y hY => hirr Y fun γ q hq => hY _ ⟨γ, rfl⟩ q hq
  have hirrW : ∀ U : Submodule (ZMod 2) W, (∀ γ, ∀ u ∈ U, π γ u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine B42L2.irr_map θ hirrQ U ?_
    rintro _ ⟨_, ⟨γ, rfl⟩, rfl⟩ u hu
    exact hU γ u hu
  have hWQ : Nat.card W = Nat.card Q := (Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd)).symm
  have hne : ∃ q : Q, q ≠ 1 := ⟨q₁, h₁⟩
  have : Nontrivial Q := nontrivial_of_ne q₁ 1 h₁
  have : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hWQ]
    exact Finite.one_lt_card)
  have : Fact (repOf π).IsIrreducible :=
    ⟨(CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff (repOf π)).mpr ⟨inferInstance, hirrW⟩⟩
  have hntπ : ∃ γ, repOf π γ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hnt
    ext γ q
    have h2 : π γ = π 1 :=
      LinearEquiv.toLinearMap_injective ((hall γ).trans (map_one (repOf π)).symm)
    rw [map_one] at h2
    have h3 : ρ γ = 1 := by
      apply (binPsi θ).injective
      rw [map_one]
      exact h2
    rw [h3]
    rfl
  have hw : ∀ q : Q, q ≠ 1 → Multiplicative.toAdd (θ q) ≠ 0 := by
    intro q hq h0
    apply hq
    have h1 : θ q = 1 := Multiplicative.toAdd.injective h0
    rwa [MulEquiv.map_eq_one_iff] at h1
  obtain ⟨γ, hγ⟩ := exists_apply_eq_of_card_le hFf hf π hntπ (hWQ.trans_le hcard)
    (hw q₁ h₁) (hw q₂ h₂)
  refine ⟨γ, θ.injective (Multiplicative.toAdd.injective ?_)⟩
  rw [← B42L2.toAdd_binPsi, ← hπ]
  exact hγ

end CFSG.Quasithin.Ch3E215M.Sp4

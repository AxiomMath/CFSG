module

public import CFSG.Quasithin.Background.SmithB42SL3Trace
public import CFSG.Quasithin.Background.SmithB42SL3Aut
public import CFSG.Quasithin.Background.SmithB42SL3Label

public section

namespace CFSG.Quasithin

namespace B42SL3

open CFSG.QuasithinUnique.Setup.X7a CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply)
open CFSG.QuasithinUnique.Setup.X7b (toMatRep)
open scoped MatrixGroups Matrix

section Key

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {f : ℕ}
  {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
  (ρ : Representation (ZMod 2) SL(3, F) U) (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F)
  (A : Subgroup (U ≃ₗ[ZMod 2] U)) (hA : ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y)
  [CFSG.IsElementaryAbelian 2 A]

omit [Finite U] in
theorem card_innerPart_le_of_two (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (hirr : ρ.IsIrreducible) (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w, b (a w - w) = a w - w) {n : ℕ}
    (bas : Module.Basis (Fin n) (ZMod 2) U) {a b : Fin f → Bool} (hS : cntS a b = 2)
    (hH : cntH a b = 0)
    (W₀ : Subrepresentation (matRep (matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas))))
    (e₀ : W₀.toRepresentation.Equiv (matRep (tensorRep (F := F) F a b))) :
    Nat.card ↥(innerPart ρ hker A hA) ≤ 2 ^ f := by
  classical
  have hNat : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  set I := innerPart ρ hker A hA with hI
  by_cases hbot : I = ⊥
  · rw [hbot, Subgroup.card_bot]
    exact Nat.one_le_two_pow
  obtain ⟨⟨a₀, ha₀I⟩, ha₀1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
  have ha₀1 : a₀ ≠ 1 := fun h => ha₀1' (Subtype.ext h)
  have hlift : ∀ x : ↥I, ∃ t : SL(3, F), t * t = 1 ∧
      ∀ u, ((x : ↥A) : U ≃ₗ[ZMod 2] U) u = ρ t u :=
    fun x => exists_lift_of_inner ρ hker A hA hf hNat hirr x x.2
  choose t ht2 htρ using hlift
  set t₀ := t ⟨a₀, ha₀I⟩ with ht₀
  have ht₀1 : t₀ ≠ 1 := by
    intro h1
    apply ha₀1
    apply Subtype.ext
    refine LinearEquiv.ext fun u => ?_
    have := htρ ⟨a₀, ha₀I⟩ u
    rw [← ht₀, h1, map_one] at this
    exact this
  have ht₀tr := isTransvection_of_involution ht₀1 (ht2 ⟨a₀, ha₀I⟩)
  obtain ⟨i, i', hii', hsi, hsi', hrest⟩ := exists_two_pos hS hH
  have hμ : ∀ x : ↥I, ∃ μ : F, ((t x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) - 1 =
      μ • ((t₀ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) - μ • 1 := by
    intro x
    have hcommρ : ρ (t x) * ρ t₀ = ρ t₀ * ρ (t x) := by
      have hc := CFSG.QuasithinUnique.Setup.Layer.Actor.comm_of_isElementaryAbelian_two
        inferInstance _ (x : ↥A).2 _ a₀.2
      refine LinearMap.ext fun u => ?_
      have h1 := LinearEquiv.congr_fun hc u
      simp only [LinearEquiv.mul_apply] at h1
      rw [Module.End.mul_apply, Module.End.mul_apply, ← htρ x, ← htρ ⟨a₀, ha₀I⟩,
        ← htρ x, ← htρ ⟨a₀, ha₀I⟩]
      exact h1
    have hcomm : t₀ * t x = t x * t₀ :=
      (commute_of_rep ρ hker ht₀tr hcommρ).symm
    have hq : (ρ (t x) - 1) ∘ₗ (ρ t₀ - 1) = 0 := by
      refine LinearMap.ext fun u => ?_
      have h1 := hquad _ a₀.2 _ (x : ↥A).2 u
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply,
        LinearMap.zero_apply]
      rw [← htρ x, ← htρ ⟨a₀, ha₀I⟩, h1, sub_self]
    have hT := quad_of_sub ρ bas W₀ e₀ hq
    obtain ⟨μ, hμ⟩ := eq_smul_of_quadratic (fun p : Fin f => (a p, b p)) (fun p => (p : ℕ))
      hii' hsi hsi' hrest ht₀1 (ht2 ⟨a₀, ha₀I⟩) (ht2 x) hcomm hT
    exact ⟨μ, by rw [hμ, smul_sub]⟩
  choose μ hμeq using hμ
  have hinj : Function.Injective μ := by
    intro x y hxy
    have h1 : ((t x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) - 1 =
        ((t y : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) - 1 := by
      rw [hμeq x, hμeq y, hxy]
    have h2 : t x = t y := Subtype.ext (sub_left_injective h1)
    apply Subtype.ext
    apply Subtype.ext
    refine LinearEquiv.ext fun u => ?_
    rw [htρ x, htρ y, h2]
  have := Nat.card_le_card_of_injective μ hinj
  rwa [hNat] at this

include hker hA in
theorem natural_of_offender (hf : 2 ≤ f) (hF : Fintype.card F = 2 ^ f)
    (hirr : ρ.IsIrreducible) (hA1 : A ≠ ⊥)
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w, b (a w - w) = a w - w)
    (hoff : Nat.card U ≤ Nat.card ↥A * Nat.card {u : U // ∀ a ∈ A, a u = u}) :
    ∃ ψ : SL(3, F) →* SL(3, F), (∀ g, ψ (ψ g) = g) ∧ ∃ E : U ≃+ (Fin 3 → F), ∀ g u,
      E (ρ g u) = ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E u := by
  classical
  have hNat : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have hfinU : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  by_cases hsd : Nonempty (ρ.Equiv ρ.dual)
  · exfalso
    have := self_dual_full_normalizer_no_offender selfDualInvolutionRank hf hF ρ hker hirr hsd
      A hA1 hA
    omega
  have hnt : ∃ x, ρ x ≠ 1 := ⟨up3 0 0 1, fun h => by
    obtain ⟨c, -, hc⟩ := hker _ h
    exact not_scalar_up3 (F := F) ⟨(c : F), hc⟩⟩
  let bas := Module.finBasis (ZMod 2) U
  obtain ⟨a, b, hne, hsum, W₀, ⟨e₀⟩⟩ := exists_label hF (by omega) ρ bas hirr hnt
  have hdim : ∀ c : (Fin f → Bool) × (Fin f → Bool),
      3 ^ cntS c.1 c.2 * 8 ^ cntH c.1 c.2 ≤
        2 * (tensorRep (F := F) F c.1 c.2 (up3 0 0 1) - 1).rank + 1 :=
    fun c => dim_le_two_mul_rank_tensorRep c.1 c.2
  rcases label_cases (by omega) a b hne _ hdim hsum with ⟨hS, hH⟩ | ⟨hS, hH, hR⟩ | hR
  · exact exists_natural_of_single hF ρ bas hirr hS hH W₀ e₀
  · exfalso
    have hk := card_innerPart_le_of_two ρ hker A hA hF (by omega) hirr hquad bas hS hH W₀ e₀
    have := card_mul_card_fix_lt ρ hker A hA hf hF hirr hsd hA1 hk (by omega) (by omega)
    omega
  · exfalso
    have hk := card_innerPart_le ρ hker A hA hf hNat hirr
    have := card_mul_card_fix_lt ρ hker A hA hf hF hirr hsd hA1 hk (by omega) (by omega)
    omega

end Key

end B42SL3

end CFSG.Quasithin

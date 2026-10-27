module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmMinus
public import CFSG.Quasithin.Background.RealizesFaithful
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.Universal.Spin
open scoped Matrix

variable {W : Type} [CommGroup W] [Finite W]

theorem rk_le_mul_of_card_le {F : Type} [Field F] [Finite F] {n d : ℕ} {ι : Type}
    [Fintype ι]
    {W : Type} [CommGroup W] [Finite W] (E : Subgroup W) (φ : ↥E → (ι → F))
    (hφinj : Function.Injective φ) (hE2 : ∀ x ∈ E, x * x = 1)
    (U : AddSubgroup (ι → F)) (hφU : ∀ x : ↥E, φ x ∈ U)
    (hcard : Nat.card ↥U ≤ 2 ^ (d * n)) :
    rk E ≤ d * n := by
  classical
  have hIsP : IsPGroup 2 ↥E := by
    refine isPGroup_two_of_sq_eq_one fun x => ?_
    exact Subtype.ext (by simpa [sq] using hE2 (x : W) x.2)
  have hcardE : Nat.card ↥E = 2 ^ rk E := by
    have h := card_eq_two_pow_mSub (G := W) (U := E) hIsP
    simpa [mSub] using h
  have hle : Nat.card ↥E ≤ Nat.card ↥U := by
    have hinj : Function.Injective (fun x : ↥E => (⟨φ x, hφU x⟩ : ↥U)) := by
      intro x y hxy
      exact hφinj (congrArg Subtype.val hxy)
    exact Nat.card_le_card_of_injective _ hinj
  rw [hcardE] at hle
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (hle.trans hcard)

theorem rk_le_two_mul_of_singularOn
    {W : Type} [CommGroup W] [Finite W]
    {F : Type} [Field F] [Finite F] {n : ℕ} {b c : F}
    (hF : Nat.card F = 2 ^ n) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {W' : Subgroup W}
    (ψ : W' ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (E : Subgroup W) (hEW : E ≤ W') (hE2 : ∀ x ∈ E, x * x = 1)
    (hE : ∀ x (hx : x ∈ E),
      quadMinus 3 F b c (Multiplicative.toAdd (ψ ⟨x, hEW hx⟩)) = 0) :
    rk E ≤ 2 * n := by
  classical
  let φ : ↥E → (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) :=
    fun x => Multiplicative.toAdd (ψ ⟨(x : W), hEW x.2⟩)
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hsub : (⟨(x : W), hEW x.2⟩ : W') = ⟨(y : W), hEW y.2⟩ := by
      apply ψ.injective
      rw [← Multiplicative.ofAdd.injective.eq_iff, ← Multiplicative.ofAdd.injective.eq_iff]
      change Multiplicative.ofAdd (φ x) = Multiplicative.ofAdd (φ y)
      rw [hxy]
    exact Subtype.ext (congrArg (fun z : W' => (z : W)) hsub)
  let S : Set (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) := Set.range φ
  have hSq : ∀ v ∈ S, quadMinus 3 F b c v = 0 := by
    rintro v ⟨x, rfl⟩
    exact hE x x.2
  have hSpol : ∀ u ∈ S, ∀ v ∈ S, QuadraticMap.polar (quadMinus 3 F b c) u v = 0 := by
    rintro u ⟨x, rfl⟩ v ⟨y, rfl⟩
    have hsum : φ (x * y) = φ x + φ y := by
      change Multiplicative.toAdd (ψ ⟨(x : W) * (y : W), hEW (x * y).2⟩) =
        Multiplicative.toAdd (ψ ⟨(x : W), hEW x.2⟩) +
          Multiplicative.toAdd (ψ ⟨(y : W), hEW y.2⟩)
      rw [show (⟨(x : W) * (y : W), hEW (x * y).2⟩ : W') =
        ⟨(x : W), hEW x.2⟩ * ⟨(y : W), hEW y.2⟩ from rfl, map_mul, toAdd_mul]
    have h0 : quadMinus 3 F b c (φ x + φ y) = 0 := by
      rw [← hsum]
      exact hE (x * y) (x * y).2
    have hx : quadMinus 3 F b c (φ x) = 0 := hE x x.2
    have hy : quadMinus 3 F b c (φ y) = 0 := hE y y.2
    rw [QuadraticMap.polar, h0, hx, hy]
    ring
  let U : Submodule F (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) := Submodule.span F S
  have hUQ : ∀ u ∈ U, quadMinus 3 F b c u = 0 :=
    fun u hu => CFSG.ClassicalGroups.Orthogonal.map_eq_zero_of_mem_span hSq hSpol hu
  have hdim : Module.finrank F U ≤ 3 - 1 :=
    CFSG.StandardType.OrdPOm.finrank_le_of_singular_quadMinus (n := 3) hirr (by omega) U hUQ
  have hcard : Nat.card ↥U ≤ 2 ^ (2 * n) := by
    rw [Module.natCard_eq_pow_finrank (K := F), hF]
    calc (2 ^ n) ^ Module.finrank F U = 2 ^ (n * Module.finrank F U) := by rw [pow_mul]
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  exact rk_le_mul_of_card_le E φ hφinj hE2 U.toAddSubgroup
    (fun x => Submodule.subset_span ⟨x, rfl⟩) hcard

@[expose] def K_Omega6Minus_lineStab : Prop :=
  ∀ {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n p : ℕ)
    {F : Type} [Field F] [Finite F] {b c : F},
    Nat.card F = 2 ^ n → (∀ s : F, s ^ 2 + b * s + c ≠ 0) →
      p.Prime → p ≠ 2 → (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] →
      ∀ (W' : Subgroup W) (hW' : StableUnder H W') (hN : NatOmegaMinus H W' ⊥ 6 n)
        (ε : ↥H ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
        (ψ : W' ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)),
      NatCoordsOmegaMinusOn H W' hW' F b c ε ψ →
      ∀ (E : Subgroup W) (hEW : E ≤ W'), rk E = 2 * n →
        (∀ x (hx : x ∈ E),
          StatedQuadMinus 3 F b c (Multiplicative.toAdd (ψ ⟨x, hEW hx⟩)) = 0) →
        ∃ P : Subgroup (MulAut W),
          P ≤ H ⊓ stabSub E ∧ IsPGroup p P ∧ ¬ IsCyclic P

theorem rk_eq_six_mul_of_natOmegaMinus
    {H : Subgroup (MulAut W)} {n : ℕ} {U : Subgroup W}
    (h : NatOmegaMinus H U ⊥ 6 n) : rk U = 6 * n :=
  (s16c1610_rk_natOmegaMinus (by norm_num) h).trans (Nat.mul_comm _ _)

theorem rk_top_eq_eight_mul_of_natSUn
    {H : Subgroup (MulAut W)} {n : ℕ} (h : NatSUn H ⊤ ⊥ 4 n) :
    rk (⊤ : Subgroup W) = 8 * n := by
  obtain ⟨K, _, _, hK, hreal⟩ := h
  have hc := s16c1610_card_of_realizes_nat hreal
  rw [Fintype.card_fin, hK, ← pow_mul, ← pow_mul] at hc
  have hc' : Nat.card ↥(⊤ : Subgroup W) = 2 ^ (8 * n) := by
    rw [hc, Nat.mul_comm n 8]
  exact s16c1610_rk_of_card_two_pow hc'

theorem rk_top_eq_four_mul_of_natOmegaPlus
    {H : Subgroup (MulAut W)} {n : ℕ} (h : NatOmegaPlus H ⊤ ⊥ 4 n) :
    rk (⊤ : Subgroup W) = 4 * n :=
  (s16c1610_rk_natOmegaPlus h).trans (Nat.mul_comm _ _)

theorem exists_natCoords_of_natOmegaPlus {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n : ℕ} (hN : NatOmegaPlus H ⊤ ⊥ 4 n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      ∃ (ε : ↥H ≃* ↥(StatedOmega (StatedQuadPlus 2 F)))
        (ψ : W ≃* Multiplicative (Fin 2 ⊕ Fin 2 → F)), NatCoordsOmegaPlus H F ε ψ := by
  classical
  obtain ⟨-, K, hK, hKf, hK2, π, hπ⟩ := hN
  letI := hK
  haveI : Finite K := hKf
  have hinj : Function.Injective π :=
    CFSG.Quasithin.FFModel.RealizesVia.injective_of_faithful
      (CFSG.Quasithin.FFModel.nat_faithful _) hπ
  obtain ⟨β, hβsurj, hβker, hβe⟩ := (CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ).exists_β
  have hβinj : Function.Injective β := by
    intro a a' hab
    have h1 : β (a * a'⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * a'⁻¹ : ↥(⊤ : Subgroup W)) : W) ∈ (⊥ : Subgroup W) := (hβker (a * a'⁻¹)).1 h1
    have h3 : a * a'⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  let πe : ↥(StatedOmega (StatedQuadPlus 2 K)) ≃* ↥H := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  let up : W ≃* ↥(⊤ : Subgroup W) := Subgroup.topEquiv.symm
  let eβ : ↥(⊤ : Subgroup W) ≃* Multiplicative (Fin (4 / 2) ⊕ Fin (4 / 2) → K) :=
    MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩
  refine ⟨K, hK, hKf, hK2, πe.symm, up.trans eβ, ?_⟩
  intro l s
  obtain ⟨γ, rfl⟩ : ∃ γ, πe γ = l := πe.surjective l
  rw [MulEquiv.symm_apply_apply]
  have hψ : ∀ x : W, (up.trans eβ) x = β ⟨x, Subgroup.mem_top x⟩ := fun x => rfl
  rw [hψ, hψ]
  exact hβe γ ⟨s, Subgroup.mem_top s⟩ (Subgroup.mem_top _)

@[expose] def K_Omega4Plus_nonsingPoint : Prop :=
  ∀ {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (p n : ℕ),
    2 ≤ n → IsOmegaPlus ↥H 4 n → NatOmegaPlus H ⊤ ⊥ 4 n →
      p.Prime → (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] →
        ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ n →
          ∀ (ε : ↥H ≃* ↥(StatedOmega (StatedQuadPlus 2 F)))
            (ψ : W ≃* Multiplicative (Fin 2 ⊕ Fin 2 → F)),
            NatCoordsOmegaPlus H F ε ψ → ∀ v : W,
              StatedQuadPlus 2 F (Multiplicative.toAdd (ψ v)) ≠ 0 →
                ∃ P : Subgroup (MulAut W), P ≤ H ∧ Group.IsPerfect P ∧ p ∣ Nat.card P ∧
                  ∀ e ∈ P, e v = v

theorem stableUnder_of_natOmegaMinus
    {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)} {n : ℕ}
    {W' : Subgroup W} (h : NatOmegaMinus H W' ⊥ 6 n) : StableUnder H W' := by
  obtain ⟨-, K, hK, hKf, b, c, hcard, hbc, π, hπ⟩ := h
  exact fun x hx u hu => hπ.2.2.2.1 ⟨x, hx⟩ u hu

theorem exists_natCoords_of_natOmegaMinusOn
    {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)} {n : ℕ}
    {W' : Subgroup W} (hW' : StableUnder H W') (hN : NatOmegaMinus H W' ⊥ 6 n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (b c : F), Nat.card F = 2 ^ n ∧
      (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
      ∃ (ε : ↥H ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
        (ψ : W' ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)),
        NatCoordsOmegaMinusOn H W' hW' F b c ε ψ := by
  classical
  obtain ⟨-, K, hK, hKf, b, c, hK2, hpoly, π, hπ⟩ := hN
  letI := hK
  haveI : Finite K := hKf
  have hinj : Function.Injective π :=
    CFSG.Quasithin.FFModel.RealizesVia.injective_of_faithful_on
      (CFSG.Quasithin.FFModel.nat_faithful _) hπ
  obtain ⟨β, hβsurj, hβker, hβe⟩ := (CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ).exists_β
  have hβinj : Function.Injective β := by
    intro a a' hab
    have h1 : β (a * a'⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * a'⁻¹ : W') : W) ∈ (⊥ : Subgroup W) := (hβker (a * a'⁻¹)).1 h1
    have h3 : a * a'⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  let πe : ↥(StatedOmega (StatedQuadMinus 3 K b c)) ≃* ↥H :=
    MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  refine ⟨K, hK, hKf, b, c, hK2, hpoly, πe.symm,
    MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩, ?_⟩
  intro l s
  obtain ⟨γ, rfl⟩ : ∃ γ, πe γ = l := πe.surjective l
  rw [MulEquiv.symm_apply_apply]
  exact hβe γ s (hW' (π γ) (π γ).2 s s.2)

@[expose] def K_SU4Nat_totallySingular : Prop :=
  ∀ {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (p n : ℕ),
    2 ≤ n → IsSUn ↥H 4 n → NatSUn H ⊤ ⊥ 4 n →
      p.Prime → (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] →
        ∀ (F : Type) [Field F] [Finite F], Nat.card F = (2 ^ n) ^ 2 →
          ∀ (ε : ↥H ≃* ↥(StatedSU 4 (2 ^ n) F))
            (ψ : W ≃* Multiplicative (Fin 4 → F)),
            NatCoordsSU4 H n F ε ψ → ∀ E : Subgroup W, rk E = 4 * n →
              (∀ x ∈ E, ∑ i, (Multiplicative.toAdd (ψ x)) i ^ (2 ^ n + 1) = 0) →
                ∃ X : Subgroup W, X ≤ E ∧ X ≠ ⊥ ∧
                  ∃ P : Subgroup (MulAut W), P ≤ H ⊓ stabSub X ∧
                    IsElemAbelian p P ∧ ¬ IsCyclic P

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

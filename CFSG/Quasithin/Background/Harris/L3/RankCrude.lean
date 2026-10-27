module

public import CFSG.Quasithin.Background.Harris.L3.Setup
public import CFSG.Quasithin.Background.Harris.L3.Rank
public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall

public section

namespace CFSG.Quasithin.G11.Harris.L3

open CFSG.Open
open scoped MatrixGroups
open CFSG.QuasithinUnique.Setup.X7a CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin.B42SL3

section Crude

variable {F : Type} [Field F] [Fintype F] {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) SL(3, F) U) (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F)
  (A : Subgroup (U ≃ₗ[ZMod 2] U))
  (hA : ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y) [CFSG.IsElementaryAbelian 2 A]

include hker hA in
omit [Fintype F] in
theorem card_eq_card_range (hirr : ρ.IsIrreducible) :
    Nat.card A = Nat.card (normalizerHom ρ hker A hA).range :=
  Nat.card_congr (MonoidHom.ofInjective (normalizerHom_injective ρ hker A hA hirr)).toEquiv

end Crude

theorem card_le_of_sl3_crude {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2 ^ f) {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) SL(3, F) U) (hirr : ρ.IsIrreducible)
    (hker : ∀ g : SL(3, F), ρ g = 1 → g ∈ Subgroup.center SL(3, F))
    (A : Subgroup (U ≃ₗ[ZMod 2] U)) [CFSG.IsElementaryAbelian 2 A]
    (hA : ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y) :
    Nat.card A ≤ 2 ^ (2 * f + 2) := by
  have hNat : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hNat
  have hker' : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F := fun x hx => by
    rw [scalars_eq_center]
    exact hker x hx
  have := isElementaryAbelian_range ρ hker' A hA
  obtain ⟨-, -, h1, -⟩ := elementary_automorphism_rank_bound hf hNat
    (normalizerHom ρ hker' A hA).range
  rw [card_eq_card_range ρ hker' A hA hirr]
  exact h1

section Two

open CFSG.QuasithinUnique.Setup.Family CFSG.LieType.SteinbergBR CFSG.LieType.SteinbergBR.AutGL32

noncomputable def projectiveSLEquivGL32 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    projectiveSL 3 F ≃* GL32 := by
  have hbot : scalars 3 F = ⊥ := by
    rw [scalars_eq_center]
    exact center_specialLinear_eq_bot_of_card_two 3 F hF
  have hinj : Function.Injective (proj 3 F) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have := proj_eq_one_iff.mp hg
    rwa [hbot, Subgroup.mem_bot] at this
  exact ((MulEquiv.ofBijective (proj 3 F) ⟨hinj, proj_surjective 3 F⟩).symm.trans
    (specialLinearEquivOfRingEquiv 3 (ringEquivZMod2 F hF))).trans (slEquivGL 3)

theorem card_le_four_of_equiv_GL32 {E : Type} [Group E] (e : E ≃* GL32) (B : Subgroup (MulAut E))
    [CFSG.IsElementaryAbelian 2 B] : Nat.card B ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Φ := MulAut.congr e
  have : Finite (MulAut E) := Finite.of_equiv _ Φ.symm.toEquiv
  have hcard : Nat.card (MulAut E) = 336 := by
    rw [Nat.card_congr Φ.toEquiv, card_mulAut_GL32]
  have := card_le_sq_of_orderOf (g := Φ.symm alphaAut) (k := 3)
    (by rw [MulEquiv.orderOf_eq, orderOf_alphaAut]) (by rw [hcard]; norm_num) B
  simpa using this

end Two

theorem card_le_of_sl3_two {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) SL(3, F) U) (hirr : ρ.IsIrreducible)
    (hker : ∀ g : SL(3, F), ρ g = 1 → g ∈ Subgroup.center SL(3, F))
    (A : Subgroup (U ≃ₗ[ZMod 2] U)) [CFSG.IsElementaryAbelian 2 A]
    (hA : ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y) :
    Nat.card A ≤ 4 := by
  have hNat : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF]
  have hker' : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F := fun x hx => by
    rw [scalars_eq_center]
    exact hker x hx
  have := isElementaryAbelian_range ρ hker' A hA
  rw [card_eq_card_range ρ hker' A hA hirr]
  exact card_le_four_of_equiv_GL32 (projectiveSLEquivGL32 hNat) _

section Setting

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Γ A L : Subgroup (GLV V)} {m : ℕ}

theorem isElementaryAbelian_of_setting (hs : OneCompSetting Γ A L m) :
    CFSG.IsElementaryAbelian 2 A := by
  obtain ⟨hcomm, hsq⟩ := hs.A_elem
  refine { toIsMulCommutative := hcomm, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
  apply Subtype.ext
  exact hsq x x.2

theorem intertwines_of_setting (hs : OneCompSetting Γ A L m) {F : Type} [Field F]
    (π : SL(3, F) →* ↥L) (hπ : Function.Surjective π) :
    ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines (repOfHom L π) a x y := by
  intro a ha x
  obtain ⟨y, hy⟩ := hπ ⟨a * (π x : GLV V) * a⁻¹, hs.L_normal a (hs.A_le ha) _ (π x).2⟩
  refine ⟨y, fun u => ?_⟩
  rw [repOfHom_apply, repOfHom_apply, hy]
  simp

theorem repOf_ker_of_setting {F : Type} [Field F] (π : SL(3, F) →* ↥L)
    (hker : ∀ g : SL(3, F), π g = 1 → g ∈ Subgroup.center SL(3, F)) :
    ∀ g : SL(3, F), repOfHom L π g = 1 → g ∈ Subgroup.center SL(3, F) := by
  intro g hg
  apply hker
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have := congrArg (fun f : Module.End (ZMod 2) V => f v) hg
  simpa [repOfHom_apply] using this

theorem m_le_of_sl3 [Finite V] (hs : OneCompSetting Γ A L m) {f : ℕ} (hf : 1 ≤ f) {F : Type}
    [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ f) (π : SL(3, F) →* ↥L)
    (hπ : Function.Surjective π) (hker : ∀ g : SL(3, F), π g = 1 → g ∈ Subgroup.center SL(3, F))
    (hsd : ¬ Nonempty ((repOfHom L π).Equiv (repOfHom L π).dual)) : m ≤ 2 * f := by
  have := isElementaryAbelian_of_setting hs
  have h := card_le_of_sl3 hf hF (repOfHom L π) (repOfHom_isIrreducible π hπ hs.L_irr)
    (repOf_ker_of_setting π hker) hsd A (intertwines_of_setting hs π hπ)
  rw [hs.A_card] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem m_le_of_sl3_crude [Finite V] (hs : OneCompSetting Γ A L m) {f : ℕ} (hf : 2 ≤ f)
    {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ f) (π : SL(3, F) →* ↥L)
    (hπ : Function.Surjective π) (hker : ∀ g : SL(3, F), π g = 1 → g ∈ Subgroup.center SL(3, F)) :
    m ≤ 2 * f + 2 := by
  have := isElementaryAbelian_of_setting hs
  have h := card_le_of_sl3_crude hf hF (repOfHom L π) (repOfHom_isIrreducible π hπ hs.L_irr)
    (repOf_ker_of_setting π hker) A (intertwines_of_setting hs π hπ)
  rw [hs.A_card] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem m_le_of_sl3_two [Finite V] (hs : OneCompSetting Γ A L m) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) (π : SL(3, F) →* ↥L) (hπ : Function.Surjective π)
    (hker : ∀ g : SL(3, F), π g = 1 → g ∈ Subgroup.center SL(3, F)) : m ≤ 2 := by
  have := isElementaryAbelian_of_setting hs
  have h := card_le_of_sl3_two hF (repOfHom L π) (repOfHom_isIrreducible π hπ hs.L_irr)
    (repOf_ker_of_setting π hker) A (intertwines_of_setting hs π hπ)
  rw [hs.A_card, show (4 : ℕ) = 2 ^ 2 by norm_num] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

end Setting

end CFSG.Quasithin.G11.Harris.L3

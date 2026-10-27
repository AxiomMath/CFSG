module

public import CFSG.Quasithin.H13.NQBlockOddRankOneBridge

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup
open CFSG.QuasithinUnique.Setup.SL2Modules (upperRootGroup borelSubgroup
  sl2_defining_characteristic_Sylow_normalizer_maximal_Borel natCard_upperRootGroup
  charP_two_of_card_eq)
open CFSG.GorensteinWalter (psl2ProjectiveInfinity)
open scoped MatrixGroups LinearAlgebra.Projectivization Pointwise
open Matrix

variable {F : Type} [Field F] [Fintype F] {n : ℕ}

theorem card_sl2_two (hF : Fintype.card F = 2 ^ n) :
    Nat.card SL(2, F) = 2 ^ n * ((2 ^ n) ^ 2 - 1) ∧ Odd ((2 ^ n) ^ 2 - 1) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_two_of_card_eq hF
  obtain ⟨hcard, -⟩ := sl2_defining_characteristic_Sylow_normalizer_maximal_Borel (F := F) (p := 2)
  refine ⟨by rw [hcard, hF], ?_⟩
  have hn : n ≠ 0 := by
    rintro rfl
    have := Fintype.one_lt_card (α := F)
    rw [hF, pow_zero] at this
    exact lt_irrefl 1 this
  have hev : Even ((2 ^ n) ^ 2) :=
    (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, hn⟩, two_ne_zero⟩)
  have hpos : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  exact Nat.Even.sub_odd hpos hev odd_one

theorem card_dvd_of_isPGroup_of_sl2 {L : Type*} [Group L] (hF : Fintype.card F = 2 ^ n)
    (α : L ≃* SL(2, F)) {Y : Subgroup L} (hY : IsPGroup 2 Y) : Nat.card Y ∣ 2 ^ n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite L := Finite.of_equiv _ α.symm.toEquiv
  obtain ⟨hc, hodd⟩ := card_sl2_two hF
  have hL : Nat.card L = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by rw [Nat.card_congr α.toEquiv, hc]
  obtain ⟨k, hk⟩ := hY.exists_card_eq
  have hdvd : Nat.card Y ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) := hL ▸ Subgroup.card_subgroup_dvd_card Y
  rw [hk] at hdvd ⊢
  exact (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)).dvd_of_dvd_mul_right hdvd

theorem sl2_le_normalizer_of_lt_top [IsSimpleGroup SL(2, F)] (hF : Fintype.card F = 2 ^ n)
    {T M : Subgroup SL(2, F)} (hT : Nat.card T = 2 ^ n) (hM : M < ⊤) (hTM : T ≤ M) :
    M ≤ normalizer (T : Set SL(2, F)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_two_of_card_eq hF
  obtain ⟨-, -, -, -, -, -, -, hsyl⟩ :=
    sl2_defining_characteristic_Sylow_normalizer_maximal_Borel (F := F) (p := 2)
  obtain ⟨P, hTP⟩ := (IsPGroup.of_card (G := ↥T) hT).exists_le_sylow
  have hPcard : Nat.card (P : Subgroup SL(2, F)) ∣ 2 ^ n :=
    card_dvd_of_isPGroup_of_sl2 hF (MulEquiv.refl _) P.isPGroup'
  have hTPeq : T = P :=
    eq_of_le_of_card_ge hTP (by rw [hT]; exact Nat.le_of_dvd (by positivity) hPcard)
  rw [hTPeq] at hTM hT ⊢
  obtain ⟨g, hgT, hgN, -⟩ := hsyl P
  have hstab : MulAction.stabilizer SL(2, F) (g • psl2ProjectiveInfinity F) =
      normalizer ((P : Subgroup SL(2, F)) : Set SL(2, F)) := by
    ext x
    rw [hgN x]
    show x • g • psl2ProjectiveInfinity F = g • psl2ProjectiveInfinity F ↔
      (g⁻¹ * x * g) • psl2ProjectiveInfinity F = psl2ProjectiveInfinity F
    rw [mul_smul, mul_smul, inv_smul_eq_iff]
  have hPα : (P : Subgroup SL(2, F)) ≤ MulAction.stabilizer SL(2, F)
      (g • psl2ProjectiveInfinity F) := hstab ▸ le_normalizer
  have hPn : ((P : Subgroup SL(2, F)).subgroupOf
      (MulAction.stabilizer SL(2, F) (g • psl2ProjectiveInfinity F))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hPα).mpr hstab.le
  have hP1 : (P : Subgroup SL(2, F)) ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hT
    have h1 := Fintype.one_lt_card (α := F)
    rw [hF, ← hT] at h1
    exact lt_irrefl 1 h1
  have htr : ∀ β γ : ℙ F (Fin 2 → F), β ≠ g • psl2ProjectiveInfinity F →
      γ ≠ g • psl2ProjectiveInfinity F → ∃ u ∈ (P : Subgroup SL(2, F)), u • β = γ := by
    intro β γ hβ hγ
    have hβ' : g⁻¹ • β ≠ psl2ProjectiveInfinity F := fun h => hβ (by rw [← h, smul_inv_smul])
    have hγ' : g⁻¹ • γ ≠ psl2ProjectiveInfinity F := fun h => hγ (by rw [← h, smul_inv_smul])
    obtain ⟨u, hu, huβ⟩ := CFSG.Quasithin.H13.NQBlock.exists_upperRootGroup_smul_eq hβ' hγ'
    have huβ' : u • g⁻¹ • β = g⁻¹ • γ := huβ
    refine ⟨g * u * g⁻¹, (hgT _).mpr ?_, ?_⟩
    · rw [show g⁻¹ * (g * u * g⁻¹) * g = u by group]
      exact hu
    · rw [mul_smul, mul_smul, huβ', smul_inv_smul]
  exact hstab ▸ CFSG.Quasithin.H13.U3.simple_transitive_root_proper_overgroups
    (g • psl2ProjectiveInfinity F) hP1 hPα hPn htr hM hTM

end CFSG.Quasithin.H13.NQRigid

module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSLRestOrder
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix

namespace WitOm

theorem card_SL_two {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q) :
    Nat.card (SpecialLinearGroup (Fin 2) F) = (q ^ 2 - 1) * (q ^ 2 - q) / (q - 1) := by
  have : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fintype.card_eq_nat_card, hF]
  simp

theorem padicValNat_two_pow_mul {k m : ℕ} (hm : ¬ 2 ∣ m) : padicValNat 2 (2 ^ k * m) = k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (by positivity) (by rintro rfl; exact hm (dvd_zero 2)),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, add_zero]

theorem not_ggSixSeventeenExcluded_SL2 {G : Type} [Group G] {p f : ℕ} {t : StatedLieTag}
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f)
    (htL : t ≠ .PSL) (htU : t ≠ .PSU) (hp5 : p = 5 → f ≠ 2) {L₁ : Subgroup G}
    (eL : L₁ ≃* SpecialLinearGroup (Fin 2) F) : ¬ GGSixSeventeenExcluded p t f L₁ := by
  have ha : padicValNat 2 (Nat.card (↥L₁ ⧸ Subgroup.center ↥L₁)) = f := by
    rw [SLRest.padicValNat_two_card_quotient_center hF (by omega) eL]
    norm_num
  have hL : Nat.card L₁ = (4 ^ f - 1) * (4 ^ f - 2 ^ f) / (2 ^ f - 1) := by
    rw [Nat.card_congr eL.toEquiv, card_SL_two hF, ← pow_mul, mul_comm f 2, pow_mul]
    norm_num
  have hdvd : Nat.card (↥L₁ ⧸ Subgroup.center ↥L₁) ∣ Nat.card L₁ :=
    Dvd.intro _ (Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L₁)).symm
  have hcase : ∀ N v : ℕ, Nat.card (↥L₁ ⧸ Subgroup.center ↥L₁) = N → padicValNat 2 N = v →
      f = v ∧ N ∣ Nat.card L₁ := fun N v hN hv => ⟨by rw [← ha, hN, hv], hN ▸ hdvd⟩
  rintro (⟨-, hU | hA | hO⟩ | ⟨hp, hL2 | hO⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨k, hk⟩)
  · rcases hU with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · have hN := (CFSG.Timmesfeld.card_statedClassicalModel_two hc).2.1 rfl
      have hv : CFSG.Open.ordTwistedA (4 - 1) (2 ^ 1) = 2 ^ 6 * 405 := by decide
      obtain ⟨rfl, hd⟩ := hcase _ 6 hN (by rw [hv]; exact padicValNat_two_pow_mul (by norm_num))
      rw [hL] at hd
      exact absurd hd (by decide)
    all_goals exact absurd h0 (by norm_num)
  · obtain ⟨eA⟩ := hA
    have hN : Nat.card (↥L₁ ⧸ Subgroup.center ↥L₁) = 360 := by
      rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      rfl
    obtain ⟨rfl, hd⟩ := hcase _ 3 hN (by
      rw [show (360 : ℕ) = 2 ^ 3 * 45 by norm_num]
      exact padicValNat_two_pow_mul (by norm_num))
    rw [hL] at hd
    exact absurd hd (by decide)
  · rcases hO with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · have hN := (CFSG.Timmesfeld.card_statedClassicalModel_two hc).2.2.2.1 rfl
      have hv : CFSG.Open.ordD 4 (2 ^ 1) = 2 ^ 12 * 42525 := by decide
      obtain ⟨rfl, hd⟩ := hcase _ 12 hN (by rw [hv]; exact padicValNat_two_pow_mul (by norm_num))
      rw [hL] at hd
      exact absurd hd (by decide)
    all_goals exact absurd h0 (by norm_num)
  · rcases hL2 with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · have hN := (CFSG.Timmesfeld.card_statedClassicalModel_two hc).1 rfl
      have hv : CFSG.Open.ordA (2 - 1) (2 ^ 2) = 2 ^ 2 * 15 := by decide
      obtain ⟨rfl, -⟩ := hcase _ 2 hN (by rw [hv]; exact padicValNat_two_pow_mul (by norm_num))
      exact hp5 hp rfl
    all_goals exact absurd h0 (by norm_num)
  · rcases hO with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · have hN := (CFSG.Timmesfeld.card_statedClassicalModel_two hc).2.2.2.1 rfl
      have hv : CFSG.Open.ordD 4 (2 ^ 1) = 2 ^ 12 * 42525 := by decide
      obtain ⟨rfl, hd⟩ := hcase _ 12 hN (by rw [hv]; exact padicValNat_two_pow_mul (by norm_num))
      rw [hL] at hd
      exact absurd hd (by decide)
    all_goals exact absurd h0 (by norm_num)
  · exact htL ht
  · exact htU ht
  · rcases hk with ⟨-, hadm, K, _, _, hK, ⟨eY⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · obtain ⟨-, -, hk2, -, -⟩ := hadm
      have : NeZero k := ⟨by omega⟩
      have : Fintype K := Fintype.ofFinite K
      have : CharP K 2 :=
        charP_of_card_eq_prime_pow (f := 2 * f) (by rw [Fintype.card_eq_nat_card, hK])
      have eP := eY.trans (projectiveSpecialLinearGroupEquivStatedProj k K).symm
      have h1 : Nat.card (↥L₁ ⧸ Subgroup.center ↥L₁) =
          Nat.card (SpecialLinearGroup (Fin k) K ⧸ Subgroup.center
            (SpecialLinearGroup (Fin k) K)) := Nat.card_congr eP.toEquiv
      have h2 := SLRest.padicValNat_two_card_quotient_center hK (by omega) (MulEquiv.refl
        (SpecialLinearGroup (Fin k) K))
      rw [← h1, ha, show 2 * f * (k * (k - 1) / 2) = f * (2 * (k * (k - 1) / 2)) by ring,
        Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self k)] at h2
      have h3 : k * (k - 1) = 1 :=
        (Nat.eq_of_mul_eq_mul_left (show 0 < f by omega) ((mul_one f).trans h2)).symm
      have h4 := Nat.even_mul_pred_self k
      rw [h3] at h4
      exact absurd h4 (by decide)
    all_goals exact absurd ht (by decide)

end WitOm

end CFSG.StandardType

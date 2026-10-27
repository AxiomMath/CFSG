module

public import CFSG.LocalAnalysis.StandardType.GGQTwoUnitaryCav
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus

public section

namespace CFSG.StandardType.GGQ2CentPort

open CFSG CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.StandardType CFSG.StandardType.LineU CFSG.StandardType.UnitTB
open CFSG.StandardType.TableB
open CFSG.StandardType.QTwoUnitaryCav

theorem card_range_ggBeta_le_ggGamma {G : Type} [Group G] [Finite G] {L Bs : Subgroup G}
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card (ggBeta L θ hN).range ≤ Nat.card (ggGamma L hN).range := by
  have hker : (ggGamma L hN).ker ≤ (ggBeta L θ hN).ker := by
    intro b hb
    rw [MonoidHom.mem_ker] at hb ⊢
    have hb' : L.normalizerMonoidHom ⟨b, hN b.2⟩ = 1 := hb
    rw [ggBeta_eq, ggLAut_eq_ggInducedAut, hb']
    simp
  have hγ := card_range_mul_card_ker (ggGamma L hN)
  have hβ := card_range_mul_card_ker (ggBeta L θ hN)
  have h1 : Nat.card (ggBeta L θ hN).range * Nat.card (ggBeta L θ hN).ker
      ≤ Nat.card (ggGamma L hN).range * Nat.card (ggBeta L θ hN).ker := by
    calc Nat.card (ggBeta L θ hN).range * Nat.card (ggBeta L θ hN).ker
        = Nat.card (ggGamma L hN).range * Nat.card (ggGamma L hN).ker := by
          rw [hβ, hγ]
      _ ≤ Nat.card (ggGamma L hN).range * Nat.card (ggBeta L θ hN).ker :=
          Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hker)
  exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos

theorem exists_diagModel_twA
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) {d : ℕ} (hd : 5 ≤ d)
    (hd6 : d ≠ 6) (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 1 K d))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K d))
        (LargeEvenGUSet (Fin d) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∃ ψ : ↥(unitarySU 2 1 K d) →* L, UnitTB.Model ψ ∧
      ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin d → K, ActsDiagU ψ a t := by
  classical
  have hd6' : (d, 1) ≠ (6, 1) := fun h => hd6 (congrArg Prod.fst h)
  have hcov : UnitaryCoverAt 1 d K := unitaryCoverAt hK hd hd6'
  by_cases h3d : 3 ∣ d
  · have hSStar : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
    have hBN : B ≤ Subgroup.normalizer (L : Set G) :=
      le_normalizer_of_largeEvenStandardType hS.1.1.1.2.2.2.2.2.2.2
    have hBBs : B ≤ Bs := hS.1.1.2.1.1
    have hL : commutator L = ⊤ := (isQuasisimple_of_largeEvenMarking (K := L) hS.2.1).1
    have hlift : GGTorusLift 3 (ggUnitaryTorusRank 3 d)
        (LargeEvenProj (unitarySU 2 1 K d)) :=
      ggTorusLift_unitary (n := 1) (d := d) (p := 3) hK (by norm_num) (by omega)
        (by rintro ⟨rfl, -⟩; omega) Nat.prime_three (by norm_num)
    have hβ := pow_le_card_range_ggBeta Nat.prime_three hSStar hL θ hBN hlift
    have hd9 : 9 ≤ d := by
      obtain ⟨k, rfl⟩ := h3d
      omega
    have hcard : 3 ^ (d / 3 + 2) ≤ Nat.card (ggGamma L hN).range := by
      have hβ' : 3 ^ (d / 3 + 2) ≤ Nat.card (ggBeta L θ hBN).range := by
        calc 3 ^ (d / 3 + 2) ≤ 3 ^ (d - 3) :=
              Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 3 ^ ggUnitaryTorusRank 3 d := by
              simp only [ggUnitaryTorusRank, if_pos h3d]
          _ ≤ Nat.card (ggBeta L θ hBN).range := hβ
      exact hβ'.trans ((Subgroup.card_le_of_le (range_ggBeta_le θ hBBs hBN hN)).trans
        (card_range_ggBeta_le_ggGamma θ hN))
    exact exists_diagModel_dvd_actual hS hN hK (by norm_num) hd Nat.prime_three (by norm_num)
      h3d hcov θ h3 hcard
  · exact exists_diagModel_coprime_actual hS hN hK (by norm_num) (by omega)
      Nat.prime_three (by norm_num) h3d hcov θ h3

end CFSG.StandardType.GGQ2CentPort

end

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.FourDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.QDefs
public import CFSG.Open.GriessAllModelsStatement
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoCov
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)

private theorem lieModel_of_card_center_dvd_two {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} (hO2 : O2Trivial L) (hcard : Nat.card (Subgroup.center ↥L) ∣ 2)
    {t : StatedLieTag} {n p f : ℕ} (hm : LieModel (↥L ⧸ Subgroup.center ↥L) t n p f) :
    LieModel ↥L t n p f := by
  refine CFSG.Timmesfeld.lieModel_of_center_eq_bot ?_ hm
  rcases (Nat.dvd_prime Nat.prime_two).mp hcard with h1 | h2
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have hPn : (((Subgroup.center ↥L).map L.subtype).subgroupOf L).Normal := by
      have hPeq : ((Subgroup.center ↥L).map L.subtype).subgroupOf L =
          Subgroup.center ↥L := by
        rw [← Subgroup.comap_subtype]
        exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
      rw [hPeq]
      infer_instance
    have hP2 : IsPGroup 2 ((Subgroup.center ↥L).map L.subtype) :=
      IsPGroup.of_card (n := 1) (by
        rw [Subgroup.card_map_of_injective L.subtype_injective, h2]
        norm_num)
    have hbot := hO2 _ (Subgroup.map_subtype_le _) hPn hP2
    have hZbot : Subgroup.center ↥L = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥L) L.subtype_injective).mp hbot
    rw [hZbot] at h2
    simp at h2

private theorem card_center_dvd_of_lieModel (hGA : GriessAllModelsStatement) {W : Type}
    [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} (hLq : IsQuasisimple ↥L)
    {t : StatedLieTag} {n p f : ℕ} (hn : n ≠ 0)
    (hm : LieModel (↥L ⧸ Subgroup.center ↥L) t n p f) :
    Nat.card (Subgroup.center ↥L) ∣ (genericOrders t n p f).1 * (genericOrders t n p f).2 *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) :=
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.center_dvd_table hGA hLq (MulEquiv.refl _)
    (CFSG.Models.LieModel.of_blueprint_of_ne_zero hn hm)

theorem w4Lem10_5Four_of_residualThree
    (hGA : GriessAllModelsStatement)
    (hQ : W4Lem10_5Q) (h3 : W4Lem10_5ResidualThree) : W4Lem10_5Four := by
  intro W _ _ hW Y L p e q hLY hLn hF hLq hO2 hp hp2 he hq hIn
  by_cases hq3 : 3 < q
  · rcases hQ W hW Y L p e q hLY hLn hF hLq hO2 hp hp2 he hq hq3 hIn with
      h8 | ⟨-, h4⟩ | ⟨-, h6⟩ | h4g | ⟨-, h4⟩ | h6g
    · exact Or.inl (by omega)
    · exact Or.inl h4
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl h4g)
    · exact Or.inl h4
    · exact Or.inr (Or.inr h6g)
  rcases hIn with ⟨t, n, p', e', hp', hp2', he', hq', hmodel⟩ | ⟨-, hmodel⟩
  · have h3le : 3 ≤ p' ^ e' := by
      have hp3 : 3 ≤ p' := by
        have := hp'.two_le
        rcases Nat.lt_or_ge p' 3 with h | h
        · exact absurd (by omega : p' = 2) hp2'
        · exact h
      calc 3 ≤ p' := hp3
        _ = p' ^ 1 := (pow_one p').symm
        _ ≤ p' ^ e' := Nat.pow_le_pow_right hp'.pos he'
    obtain ⟨rfl, rfl⟩ : p' = 3 ∧ e' = 1 :=
      Nat.Prime.pow_inj' hp' Nat.prime_three (by omega) (by norm_num)
        (by rw [pow_one]; omega)
    by_cases hU3 : t = .PSU ∧ n = 3
    · obtain ⟨rfl, rfl⟩ := hU3
      have hd := card_center_dvd_of_lieModel hGA hLq (by norm_num) hmodel
      have h1 : Nat.card (Subgroup.center ↥L) ∣ 2 := by
        refine hd.trans ?_
        decide
      exact Or.inr (Or.inl (Or.inl (lieModel_of_card_center_dvd_two hO2 h1 hmodel)))
    by_cases hP4 : t = .PSp ∧ n = 2
    · obtain ⟨rfl, rfl⟩ := hP4
      have hd := card_center_dvd_of_lieModel hGA hLq (by norm_num) hmodel
      have h2 : Nat.card (Subgroup.center ↥L) ∣ 2 := by
        refine hd.trans ?_
        decide
      exact Or.inr (Or.inl (Or.inr (Or.inl (lieModel_of_card_center_dvd_two hO2 h2 hmodel))))
    by_cases hU4 : t = .PSU ∧ n = 4 ∧ Subgroup.center ↥L ≠ ⊥
    · obtain ⟨rfl, rfl, hZ⟩ := hU4
      exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨hmodel, hZ⟩))))
    exact Or.inl (h3 W hW Y L t n hLY hLn hF hLq hO2 hmodel hU3 hP4 hU4)
  · have hZ : Subgroup.center ↥L = ⊥ :=
      CFSG.GH74.GLS.Stage2.Signalizer.Odd87.center_eq_bot_psl2_even hLq (Or.inl rfl) hmodel
    exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl
      (CFSG.Timmesfeld.lieModel_of_center_eq_bot hZ hmodel)))))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

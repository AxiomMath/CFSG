module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSeventeen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenMod
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

variable {G : Type} [Group G] [Finite G]

theorem s16e_two_involution_star (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1214 : F12.R1214 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hconc : Conc4_136 D V₀ V hV L) :
    ∃ t ∈ Mbar D.M (v1Sub D.M V₀ V hV L) V hV, t ^ 2 = 1 ∧ t ≠ 1 ∧
      rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3 := by
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  obtain ⟨t, htM, ht2, ht1, htrk, -⟩ := hconc
  obtain ⟨ρ, -, hρκ⟩ := s16e_two_kappa_equiv D h1217 hset.hyp151 hV
  have hκ : Function.Surjective (s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV
      (s15_Infra_le_v1Sub D.M V₀ V hV L)) :=
    s15_T7_kappa_surjective V₀ _ V hV (s15_Infra_le_v1Sub D.M V₀ V hV L)
  let τ : ↥(Mbar D.M V₀ V hV) := ⟨t, htM⟩
  have hτ2 : τ ^ 2 = 1 := Subtype.ext ht2
  have hτ1 : τ ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hτ'2 : (ρ τ) ^ 2 = 1 := by rw [← map_pow, hτ2, map_one]
  have hτ'1 : ρ τ ≠ 1 := fun h => hτ1 (ρ.injective (by rw [h, map_one]))
  refine ⟨((ρ τ : ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) : MulAut (vStar D.M V₀ V hV L)),
    (ρ τ).2, congrArg Subtype.val hτ'2, fun h => hτ'1 (Subtype.ext h), ?_⟩
  have hcomm := s16_Mod_commSub_zpowers_map _ hκ (t := t)
    (t' := ((ρ τ : ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) : MulAut (vStar D.M V₀ V hV L)))
    (fun w => hρκ τ w)
  rw [hcomm]
  exact le_trans (padicValNat_two_le_of_dvd (Nat.card_pos).ne' (Subgroup.card_map_dvd _ _)) htrk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

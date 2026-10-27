module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.LieModelOrders

public section

namespace CFSG.StandardType

theorem ggHasLabel_of_lieModel_PSU {X : Type} [Group X] {r f : ℕ}
    (h : CFSG.Blueprint.LieModel X .PSU r 2 f) : GGHasLabel ⟨.twA, r - 1, f⟩ X := by
  have hS : CFSG.Open.StatedClassicalModel X .PSU r 2 f := h.statedClassicalModel (by decide)
  have hr3 : 3 ≤ r := hS.1.2.2.1
  have hr : 0 < r := by omega
  dsimp only [GGHasLabel, LargeEvenRawDatum]
  rw [show r - 1 + 1 = r from Nat.succ_pred_eq_of_pos hr]
  exact recipeUnitary_of_statedClassicalModel hS

theorem center_eq_bot_of_lieModel_PSU {X : Type} [Group X] {r f : ℕ}
    (h : CFSG.Blueprint.LieModel X .PSU r 2 f) : Subgroup.center X = ⊥ := by
  have : IsSimpleGroup X := h.isSimpleGroup_of_mem_classicalTags (by decide)
  obtain ⟨-, hf, hr, -⟩ := h.admissible
  have h6 : 2 * 3 ≤ (r - 1) * r := Nat.mul_le_mul (by omega) hr
  have hk : 3 ≤ (r - 1) * r / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  have hfk : 2 ≤ f * ((r - 1) * r / 2) :=
    calc 2 ≤ 1 * 3 := by norm_num
      _ ≤ f * ((r - 1) * r / 2) := Nat.mul_le_mul hf hk
  have h4 : 4 ∣ Nat.card X := by
    rw [h.card_eq_lieOrd (by omega)]
    change 4 ∣ CFSG.Open.ordTwistedA (r - 1) (2 ^ f)
    refine dvd_trans ?_ (EvenSmallLie.CatalogOrders.pow_dvd_ordTwistedA (by omega) (2 ^ f))
    rw [← pow_mul]
    exact (pow_dvd_pow 2 hfk : 2 ^ 2 ∣ 2 ^ (f * ((r - 1) * r / 2)))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hZ | hZ
  · exact hZ
  · have hp : (Nat.card X).Prime :=
      @IsSimpleGroup.prime_card X (Group.commGroupOfCenterEqTop hZ) ‹IsSimpleGroup X›
    have h2 : 2 = Nat.card X :=
      (hp.eq_one_or_self_of_dvd 2 ((by norm_num : 2 ∣ 4).trans h4)).resolve_left (by norm_num)
    rw [← h2] at h4
    norm_num at h4

theorem ggHasLabel_quotCenter_of_lieModel_PSU {X : Type} [Group X] {r f : ℕ}
    (h : CFSG.Blueprint.LieModel X .PSU r 2 f) :
    GGHasLabel ⟨.twA, r - 1, f⟩ (X ⧸ Subgroup.center X) := by
  let e : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_lieModel_PSU h)).trans
      QuotientGroup.quotientBot
  exact largeEvenRawDatum_mono (fun _ _ _ _ ⟨g⟩ => ⟨e.trans g⟩) (ggHasLabel_of_lieModel_PSU h)

end CFSG.StandardType

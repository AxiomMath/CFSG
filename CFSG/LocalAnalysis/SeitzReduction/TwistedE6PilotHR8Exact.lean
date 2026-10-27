module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR8
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotHR8Field
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotHR8FieldNormal

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie
open CFSG.SeitzReduction.UnitaryPilot (NeighbourOvergroupSUm SUmNeighbourAlternative
  SUmNeighbourAlternativeField)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem graphField_neighbour_2E6_X_of_clauses (hcat : SUmCatalogueClausesAtF 6 f)
    (hset : SeitzSetting G L) [CharP K 2] (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2)
    (hξ : TwistedFusionIn (xiAut σ (apply_apply_eq hK hσ)) (classTU (apply_apply_eq hK hσ)))
    {X : Subgroup G} (hX : X = (((E6GraphLevi.thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))
    (hKc : IsComponent Kc)
    (hDK : ⁅(D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Kc⁆ ≠ ⊥)
    (hKt : Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom = Kc) :
    ∃ hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
        normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))),
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ (2 * f) ∧
        ∃ (ε : Kc ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 6 F)
          (φ : F ≃+* F), (∀ x, φ x = x ^ 2 ^ f) ∧
          MulAut.congr ε (Kc.normalizerMonoidHom ⟨_, hsN⟩) =
            CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut 6 F φ *
              CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut 6 F := by
  obtain ⟨-, -, hDX, hDq, hZD, hlie⟩ := neighbour_data_2E6_X hset hf2 hk hK hσ e htC ht hX hDe
  obtain ⟨hcomp, -, -⟩ := neighbour_standard_2E6_X hset hf2 hk hK hσ e htC ht hX htX hDe
  obtain ⟨-, hall⟩ :=
    neighbour_overgroup_2E6_X_of_clauses hcat hset hf2 hk hK hσ e htC ht hξ hX htX hDe
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  have hDm := UnitaryPilot.lieModel_quotient_center_map_oddCore_of_isQuasisimple hDX hDq
    (LinearPilot.lieModel_quotient_center_of_center_eq_bot hZD hlie)
    (ne_bot_of_isQuasisimple hcomp.2.2)
  exact (hall Kc hKc hDK).graphField (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _)
    (orderOf_mk_oddCore ht') hcomp (by norm_num) (six_ne_four_one f)
    (UnitaryPilot.sumEvenTypeDetAt (by norm_num)) hDm hKc hKt

end CFSG.SeitzReduction.TwistedE6Pilot

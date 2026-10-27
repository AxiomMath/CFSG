module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpAut
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalTwoMultiplier
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.HardMathSupport.Solomon.Coordinator.LBIHopf

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType

theorem pumpUpOmegaPlusTenInput_holds :
    PumpUpOmegaPlusTenInput := by
  intro K _ _ W Wk ζ ξ Q A h hmodel
  obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hmodel
  · have hcard : Nat.card (K ⧸ center K) = ordD 5 2 := by
      simpa using (CFSG.Timmesfeld.card_statedClassicalModel_two hcl).2.2.2.1 rfl
    obtain ⟨-, K₀, _, _, hK₀, ⟨e⟩⟩ := hcl
    have hgo : CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus 5 2 1 = (1, 1) := by
      simp [CFSG.Blueprint.Multiplier.genericOrders]
    haveI : NeZero (CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus 5 2 1).1 :=
      ⟨by rw [hgo]; norm_num⟩
    haveI : NeZero (CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus 5 2 1).2 :=
      ⟨by rw [hgo]; norm_num⟩
    obtain ⟨-, ⟨eM⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.OrthogonalTwo.pomegaPlus_two_hopfMultiplier (K := K₀)
        (n := 5) (p := 2) (f := 1) le_rfl hK₀ (by rw [hK₀, pow_one])
    set π : K →* StatedProj (StatedOmega (StatedQuadPlus 5 K₀)) :=
      e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : π.ker = center K := by
      ext x
      rw [MonoidHom.mem_ker]
      change e (QuotientGroup.mk x) = 1 ↔ _
      rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]
    have hZ := CFSG.HardMathSupport.Solomon.Coordinator.lbi_card_ker_dvd π hπ hker.le h.quasi.1 eM
    have h1 : Nat.card (center K) = 1 := by
      rw [← hker]
      refine Nat.eq_one_of_dvd_one (hZ.trans ?_)
      simp only [CFSG.Blueprint.Multiplier.generic, Nat.card_prod, Nat.card_eq_fintype_card,
        Fintype.card_multiplicative, ZMod.card, hgo, mul_one, dvd_refl]
      simp [Fintype.card_prod]
    have hK : Nat.card K = ordD 5 2 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center K), hcard, h1, mul_one]
    obtain ⟨-, hWcl | ⟨hW0, -⟩⟩ := h.W_model
    · have hW := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two hWcl
      have hdvd : Nat.card W ∣ Nat.card K := Subgroup.card_subgroup_dvd_card W
      rw [hW, hK] at hdvd
      revert hdvd
      simp only [CFSG.Open.ordD]
      decide
    · omega
  · omega

end CFSG.GGQ2Prime

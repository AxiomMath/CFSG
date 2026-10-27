module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1InvFixO
import CFSG.LocalAnalysis.StandardType.GGOrthFramePairs
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.StandardType.QTwo

open CFSG.Open CFSG.LieType.ChevTwo
open CFSG.RankThree.Classical2 (orthDerived)

private theorem pmom_eq_zero_or_one {K : Type} [Field K] (hK : Nat.card K = 2) (x : K) :
    x = 0 ∨ x = 1 := by
  obtain ⟨y, _, hyu⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
  have hy1 : y = 1 := (hyu 1 one_ne_zero).symm
  by_cases hx : x = 0
  · exact Or.inl hx
  · exact Or.inr (by rw [hyu x hx, hy1])

theorem qtwoDL1OrthModel_holds : QTwoDL1OrthModel := by
  intro G _ _ p Bs X Φ hF h5 hZ
  classical
  have hQ := Φ.Δ.polarBilin_nondegenerate_of_noFixed Φ.hfix
  have hdim := Φ.Δ.finrank_eq_two_mul_of_noFixed Φ.hfix
  let eX : ↥X ≃* ↥(orthDerived Φ.Q) :=
    ((MonoidHom.ofInjective Φ.hinj).trans (MulEquiv.subgroupCongr Φ.hrange)).symm
  letI : Fintype Φ.F := Fintype.ofFinite Φ.F
  have hcardF : Fintype.card Φ.F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
  let φ : Φ.F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime Φ.F Nat.prime_two hcardF).symm
  obtain ⟨n, hn⟩ : ∃ n, Φ.r = n + 1 := ⟨Φ.r - 1, by omega⟩
  have hn4 : 4 ≤ n := by omega
  have hdim' : Module.finrank Φ.F Φ.V = 2 * (n + 1) := by rw [hdim, hn]
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus Φ.Q hQ
      (n := n + 1) (by omega) hdim' with he | ⟨b, c, hirr, he⟩
  · obtain ⟨e⟩ := he
    have hφ : ∀ v : Fin (n + 1) ⊕ Fin (n + 1) → Φ.F,
        StatedQuadPlus (n + 1) (ZMod 2) (φ ∘ v) = φ (StatedQuadPlus (n + 1) Φ.F v) := by
      intro v
      simp only [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Function.comp_apply,
        map_sum, map_mul]
    refine ⟨Fin (n + 1) ⊕ Fin (n + 1), inferInstance, inferInstance,
      StatedQuadPlus (n + 1) (ZMod 2), ?_, goodQ_plus (n := n) (by omega),
      omegaTwoAutInduced_plus_of_four_le (n := n) hn4, ?_⟩
    · exact eX.trans ((CFSG.RankThree.PartOne.orthDerivedEquiv e).trans
        (((CFSG.RankThree.PartOne.statedOmegaOrthEquiv
            (CFSG.LieType.Universal.Spin.coe_quadPlus (n + 1) Φ.F)).symm).trans
          (((CFSG.Adapters.RankTwoModelTransports.glCongr φ).subgroupMap
              (StatedOmega (StatedQuadPlus (n + 1) Φ.F))).trans
            (MulEquiv.subgroupCongr
              (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ hφ)))))
    · simp only [Fintype.card_sum, Fintype.card_fin, hn]
      omega
  · have hbc : b = 1 ∧ c = 1 := by
      have hc1 : c = 1 := (pmom_eq_zero_or_one hF c).resolve_left fun h0 =>
        hirr 0 (by rw [h0]; ring)
      refine ⟨?_, hc1⟩
      exact (pmom_eq_zero_or_one hF b).resolve_left fun h0 => by
        apply hirr 1
        rw [h0, hc1, one_pow, zero_mul, add_zero, CharTwo.add_self_eq_zero]
    obtain ⟨rfl, rfl⟩ := hbc
    obtain ⟨e⟩ := he
    have hφ : ∀ v : Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2 → Φ.F,
        StatedQuadMinus (n + 1) (ZMod 2) 1 1 (φ ∘ v) =
          φ (StatedQuadMinus (n + 1) Φ.F 1 1 v) := by
      intro v
      simp only [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, Function.comp_apply,
        map_add, map_mul, map_pow, map_sum, map_one, one_mul]
    refine ⟨Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2, inferInstance, inferInstance,
      StatedQuadMinus (n + 1) (ZMod 2) 1 1, ?_, goodQ_minus (n := n) (by omega),
      omegaTwoAutInduced_minus_of_three_le (n := n) (by omega), ?_⟩
    · exact eX.trans ((CFSG.RankThree.PartOne.orthDerivedEquiv e).trans
        (((CFSG.RankThree.PartOne.statedOmegaOrthEquiv
            (CFSG.LieType.Universal.Spin.coe_quadMinus (n + 1) Φ.F 1 1)).symm).trans
          (((CFSG.Adapters.RankTwoModelTransports.glCongr φ).subgroupMap
              (StatedOmega (StatedQuadMinus (n + 1) Φ.F 1 1))).trans
            (MulEquiv.subgroupCongr
              (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ hφ)))))
    · simp only [Fintype.card_sum, Fintype.card_fin, hn]
      omega

end CFSG.StandardType.QTwo

end

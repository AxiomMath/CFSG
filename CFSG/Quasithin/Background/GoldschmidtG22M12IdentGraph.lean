module

public import CFSG.Quasithin.Background.GoldschmidtG22M12IdentUnitary
public import CFSG.Quasithin.Background.F6CatSLEps3Cover

public section

namespace CFSG.Quasithin.F6

namespace G22M12Ident

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Matrix

theorem exists_not_mem_twoResidual {D : Type} [Group D]
    (hidx : (twoResidual (⊤ : Subgroup D)).index = 2) :
    ∃ t : D, t ∉ twoResidual (⊤ : Subgroup D) := by
  by_contra hcon
  push Not at hcon
  have : twoResidual (⊤ : Subgroup D) = ⊤ := (Subgroup.eq_top_iff' _).mpr hcon
  rw [← Subgroup.index_eq_one, hidx] at this
  omega

@[expose] noncomputable def quotBotEquiv {F : Type} [Field F] (H : Subgroup (GL (Fin 3) F)) :
    ↥H ≃* ↥H ⧸ (⊥ : Subgroup (GL (Fin 3) F)).subgroupOf H :=
  QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf H).symm)

section Linear

variable {D : Type} [Group D] [Finite D]

theorem isExtendedByMatrixMap_psl_of_setting {F : Type} [Field F] [Finite F] {p : ℕ}
    [Fact p.Prime] (hF : Nat.card F = p) (hS : F618RecogSetting D)
    (hidx : (twoResidual (⊤ : Subgroup D)).index = 2)
    (eL : ↥(twoResidual (⊤ : Subgroup D)) ≃* StatedProj (StatedSL 3 F)) :
    IsExtendedByMatrixMap (StatedSL 3 F) (StatedScalars (Fin 3) F) (fun A => (A⁻¹)ᵀ) D := by
  obtain ⟨t, ht⟩ := exists_not_mem_twoResidual hidx
  obtain ⟨ε, Θ, g, hΘ, hθ⟩ := classify_linear_stated_psl hF (MulAut.congr eL (actL t))
    (congr_actL_not_isInnerAut hS ht eL) (congr_actL_mul_self_isInnerAut hidx t eL)
  refine isExtendedByMatrixMap_of_lift _ (twoResidual (⊤ : Subgroup D)) hidx ht (eL.trans ε) Θ g
    hΘ fun n m s hm hn => ?_
  exact lift_of_conj_eq (QuotientGroup.mk' _) Θ _ hθ t eL ε rfl n m s hm hn

theorem isExtendedByMatrixMap_sl_of_setting {F : Type} [Field F] [Finite F] {p : ℕ}
    [Fact p.Prime] (hF : Nat.card F = p) (hS : F618RecogSetting D)
    (hidx : (twoResidual (⊤ : Subgroup D)).index = 2)
    (eL : ↥(twoResidual (⊤ : Subgroup D)) ≃* ↥(StatedSL 3 F)) :
    IsExtendedByMatrixMap (StatedSL 3 F) ⊥ (fun A => (A⁻¹)ᵀ) D := by
  obtain ⟨t, ht⟩ := exists_not_mem_twoResidual hidx
  obtain ⟨ε, g, hg⟩ := classify_linear_stated_sl hF (MulAut.congr eL (actL t))
    (congr_actL_not_isInnerAut hS ht eL) (congr_actL_mul_self_isInnerAut hidx t eL)
  refine isExtendedByMatrixMap_of_lift _ (twoResidual (⊤ : Subgroup D)) hidx ht
    ((eL.trans ε).trans (quotBotEquiv _)) (ε * MulAut.congr eL (actL t) * ε⁻¹) g hg
    fun n m s hm hn => ?_
  have hn' : (eL.trans ε) n = s := by
    apply (quotBotEquiv (StatedSL 3 F)).injective
    exact hn
  have h1 := lift_of_conj_eq (MonoidHom.id ↥(StatedSL 3 F)) (ε * MulAut.congr eL (actL t) * ε⁻¹)
    (ε * MulAut.congr eL (actL t) * ε⁻¹) (fun s => rfl) t eL ε rfl n m s hm hn'
  change quotBotEquiv (StatedSL 3 F) ((eL.trans ε) m) = _
  rw [h1]
  rfl

end Linear

section Unitary

variable {D : Type} [Group D] [Finite D]

theorem isExtendedByMatrixMap_psu_of_setting {F : Type} [Field F] {p : ℕ}
    (h : UnitaryFieldData p 1 F) (hp2 : p ≠ 2) (hS : F618RecogSetting D)
    (hidx : (twoResidual (⊤ : Subgroup D)).index = 2)
    (eL : ↥(twoResidual (⊤ : Subgroup D)) ≃* StatedProj (StatedSU 3 p F)) :
    IsExtendedByMatrixMap (StatedSU 3 p F) (StatedScalars (Fin 3) F) (fun A => (A⁻¹)ᵀ) D := by
  obtain ⟨t, ht⟩ := exists_not_mem_twoResidual hidx
  obtain ⟨ε, Θ, g, hΘ, hθ⟩ := classify_unitary_stated_psu (pow_one p).symm h hp2
    (MulAut.congr eL (actL t)) (congr_actL_not_isInnerAut hS ht eL)
    (congr_actL_mul_self_isInnerAut hidx t eL)
  refine isExtendedByMatrixMap_of_lift _ (twoResidual (⊤ : Subgroup D)) hidx ht (eL.trans ε) Θ g
    hΘ fun n m s hm hn => ?_
  exact lift_of_conj_eq (QuotientGroup.mk' _) Θ _ hθ t eL ε rfl n m s hm hn

theorem isExtendedByMatrixMap_su_of_setting {F : Type} [Field F] {p : ℕ}
    (h : UnitaryFieldData p 1 F) (hp2 : p ≠ 2) (hS : F618RecogSetting D)
    (hidx : (twoResidual (⊤ : Subgroup D)).index = 2)
    (eL : ↥(twoResidual (⊤ : Subgroup D)) ≃* ↥(StatedSU 3 p F)) :
    IsExtendedByMatrixMap (StatedSU 3 p F) ⊥ (fun A => (A⁻¹)ᵀ) D := by
  obtain ⟨t, ht⟩ := exists_not_mem_twoResidual hidx
  obtain ⟨ε, g, hg⟩ := classify_unitary_stated_su (pow_one p).symm h hp2
    (MulAut.congr eL (actL t)) (congr_actL_not_isInnerAut hS ht eL)
    (congr_actL_mul_self_isInnerAut hidx t eL)
  refine isExtendedByMatrixMap_of_lift _ (twoResidual (⊤ : Subgroup D)) hidx ht
    ((eL.trans ε).trans (quotBotEquiv _)) (ε * MulAut.congr eL (actL t) * ε⁻¹) g hg
    fun n m s hm hn => ?_
  have hn' : (eL.trans ε) n = s := by
    apply (quotBotEquiv (StatedSU 3 p F)).injective
    exact hn
  have h1 := lift_of_conj_eq (MonoidHom.id ↥(StatedSU 3 p F))
    (ε * MulAut.congr eL (actL t) * ε⁻¹) (ε * MulAut.congr eL (actL t) * ε⁻¹) (fun s => rfl) t
    eL ε rfl n m s hm hn'
  change quotBotEquiv (StatedSU 3 p F) ((eL.trans ε) m) = _
  rw [h1]
  rfl

end Unitary

end G22M12Ident

section Main

open G22M12Ident CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

variable {D : Type} [Group D] [Finite D]

theorem isSLEps3GraphExt_of_setting_psl (hS : F618RecogSetting D)
    (hidx : (twoResidual (⊤ : Subgroup D)).index = 2) {p : ℕ} (hp4 : p % 4 = 1)
    (hK : StatedClassicalModel (TwoResidualQuot D) .PSL 3 p 1) : IsSLEps3GraphExt p D := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hadm, F, instF, instFin, hF, ⟨eK⟩⟩ := hK
  have hp : p.Prime := hadm.1
  have : Fact p.Prime := ⟨hp⟩
  have hF' : Nat.card F = p := by rw [hF, pow_one]
  refine ⟨hp, ?_⟩
  by_cases hZ : Subgroup.center ↥(twoResidual (⊤ : Subgroup D)) = ⊥
  · refine ⟨F, instF, instFin, Or.inl ⟨hp4, hF', Or.inr ?_⟩⟩
    exact isExtendedByMatrixMap_psl_of_setting hF' hS hidx
      ((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans
        eK)
  · obtain ⟨F', instF', instFin', hF2, ⟨eL⟩⟩ := (slEps3CoverFact_holds
      ↥(twoResidual (⊤ : Subgroup D)) hS.quasisimple hS.center hZ p hp hp2).1
      ⟨hadm, F, instF, instFin, hF, ⟨eK⟩⟩
    exact ⟨F', instF', instFin', Or.inl ⟨hp4, hF2,
      Or.inl (isExtendedByMatrixMap_sl_of_setting hF2 hS hidx eL)⟩⟩

theorem isSLEps3GraphExt_of_setting_psu (hS : F618RecogSetting D)
    (hidx : (twoResidual (⊤ : Subgroup D)).index = 2) {p : ℕ} (hp4 : p % 4 = 3)
    (hK : StatedClassicalModel (TwoResidualQuot D) .PSU 3 p 1) : IsSLEps3GraphExt p D := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hadm, F, instF, instFin, hF, ⟨eK⟩⟩ := hK
  have hp : p.Prime := hadm.1
  have : Fact p.Prime := ⟨hp⟩
  have hF' : Nat.card F = p ^ 2 := by rw [hF, pow_one]
  refine ⟨hp, ?_⟩
  by_cases hZ : Subgroup.center ↥(twoResidual (⊤ : Subgroup D)) = ⊥
  · have h : UnitaryFieldData p 1 F := ⟨hp, le_rfl, by rw [hF', mul_one]⟩
    have eK' : TwoResidualQuot D ≃* StatedProj (StatedSU 3 p F) := by
      rw [← pow_one p]
      exact eK
    refine ⟨F, instF, instFin, Or.inr ⟨hp4, hF', Or.inr ?_⟩⟩
    exact isExtendedByMatrixMap_psu_of_setting h hp2 hS hidx
      ((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans
        eK')
  · obtain ⟨F', instF', instFin', hF2, ⟨eL⟩⟩ := (slEps3CoverFact_holds
      ↥(twoResidual (⊤ : Subgroup D)) hS.quasisimple hS.center hZ p hp hp2).2
      ⟨hadm, F, instF, instFin, hF, ⟨eK⟩⟩
    have h : UnitaryFieldData p 1 F' := ⟨hp, le_rfl, by rw [hF2, mul_one]⟩
    exact ⟨F', instF', instFin', Or.inr ⟨hp4, hF2,
      Or.inl (isExtendedByMatrixMap_su_of_setting h hp2 hS hidx eL)⟩⟩

end Main

end CFSG.Quasithin.F6

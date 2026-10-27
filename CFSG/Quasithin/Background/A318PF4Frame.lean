module

public import CFSG.Quasithin.Background.A318PF4Z
public import CFSG.Quasithin.Background.A318PInn
public import CFSG.Quasithin.Background.A318PQuotes
public import CFSG.RankThree.PartTwo.KFacts.AutLargeRee
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartTwo.KFacts

section Gamma

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem map_reeFixed_eq_reeGamma'
    (a : ℕ) :
    (reeFixed ReeTag.F4 K a).map (adjointGroup ReeTag.F4.tag K).subtype =
      ReeTag.F4.reeGamma K a := by
  rw [reeGamma_eq_reeFixedGroup, reeFixedGroup_eq_map_reeFixed]

@[expose] noncomputable def reeFixedEquivGamma
    (a : ℕ) :
    ↥(reeFixed ReeTag.F4 K a) ≃* ↥(ReeTag.F4.reeGamma K a) :=
  (Subgroup.equivMapOfInjective (reeFixed ReeTag.F4 K a) (adjointGroup ReeTag.F4.tag K).subtype
    Subtype.val_injective).trans (MulEquiv.subgroupCongr (map_reeFixed_eq_reeGamma' a))

theorem coe_reeFixedEquivGamma
    (a : ℕ) (y : ↥(reeFixed ReeTag.F4 K a)) :
    ((reeFixedEquivGamma a y : ↥(ReeTag.F4.reeGamma K a)) : ModGL ReeTag.F4.tag K) =
      ((y : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) :=
  rfl

theorem exists_nine_gamma
    (a : ℕ) (σ : K ≃+* K) :
    ∃ E : Subgroup ↥(ReeTag.F4.reeGamma K a), Nat.card E = 9 ∧ IsElemAbelian 3 E ∧
      ∀ y ∈ E, ReeTag.F4.reeGammaFieldAut K a σ y = y := by
  obtain ⟨E, hE9, hEel, hEF, hEσ⟩ := exists_nine_f4 (K := K) a σ
  have hle : E ≤ reeFixed ReeTag.F4 K a := fun y hy => (mem_reeFixed ReeTag.F4 K a).2 (hEF y hy)
  set ψ : ↥(reeFixed ReeTag.F4 K a) ≃* ↥(ReeTag.F4.reeGamma K a) := reeFixedEquivGamma a with hψ
  have hinj : Function.Injective ψ.toMonoidHom := ψ.injective
  have hcard : Nat.card (E.subgroupOf (reeFixed ReeTag.F4 K a)) = 9 := by
    rw [← hE9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  refine ⟨(E.subgroupOf (reeFixed ReeTag.F4 K a)).map ψ.toMonoidHom, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj, hcard]
  · exact CFSG.SectionRank.isElemAbelian_map
      (CFSG.SectionRank.isElemAbelian_subgroupOf hEel _) ψ.toMonoidHom
  · rintro _ ⟨y, hy, rfl⟩
    apply Subtype.ext
    rw [coe_reeGammaFieldAut]
    exact hEσ _ (Subgroup.mem_subgroupOf.1 hy)

@[expose] noncomputable def innFrameF4
    (a : ℕ) (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    InnFrame ↥(ReeTag.F4.reeGamma K a) (K ≃+* K) where
  fld := ReeTag.F4.reeGammaFieldAutHom K a
  fld_inter := fun c hc => (largeRee_automorphism_normal_form ha hK).2 c hc
  three_mem := fun α _ _ => by
    obtain ⟨x, β, h⟩ := (largeRee_automorphism_normal_form ha hK).1 α
    exact ⟨MulAut.conj x, ⟨x, rfl⟩, β, h⟩
  nine := fun c _ => exists_nine_gamma a c

end Gamma

theorem qLieThreeRank_native
    : QLieThreeRank := by
  intro X _ _ S _ hC _ ⟨f, _, _, hm⟩ _ hX
  obtain ⟨K, _, _, _, a, ha, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_reeFixed_of_model hm
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := hK
  exact innFrame_core hC ((innFrameF4 a ha hK').ofMulEquiv (e.trans (reeFixedEquivGamma a))) hX

end A318P

end CFSG.Quasithin

module

public import CFSG.Quasithin.EmptyFaithful.Gold14610LiftBij
public import CFSG.Quasithin.EmptyFaithful.Gold14610LiftCat
public import CFSG.Quasithin.EmptyFaithful.Gold14610LiftCenter
public import CFSG.Quasithin.EmptyFaithful.Gold14610LiftNotLe
public import CFSG.Quasithin.EmptyFaithful.Gold14610LiftQuasi
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36

public section


namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native

namespace Gold14610

theorem gold14610LiftOfStruct
    : Gold14610F618Struct → Gold14610Lift := by
  intro hStruct G _ _ T M H u I I₂ c hsyl _hLT hT hF h1 h1' h2
  have S : Setting146 G T M := c.setting
  set I₁ := i1Of1469 T M I with hI₁
  have hs : Group.IsSolvable ↥(CFSG.pPrimeCore 3 ↥I) := hT.isSolvable_pPrimeCore
  have hsyl2 : IsSylowTwoOf (Open.pCore 2 ↥I) (CFSG.pPrimeCore 3 ↥I) :=
    hT.isSylowTwoOf_pCore_pPrimeCore
  have hI₁I : I₁ ≤ I := i1Of1469_le T M I
  have hI₂I : I₂ ≤ I := hT.1 ▸ le_sup_right
  have hinf : I₁ ⊓ I₂ = T ⊓ I := inf_eq_of_isSylowTwoOf hT hsyl le_sup_right c.le_I₂
  obtain ⟨hint, ham⟩ : imgMod3 I I₁ ⊓ imgMod3 I I₂ = imgMod3 I (I₁ ⊓ I₂) ∧
      IsGoldschmidtAmalgam (imgMod3 I I₁) (imgMod3 I I₂) := by
    rcases hT.goldschmidt_mod_pPrimeCore with ⟨hi, ham, -⟩ | ⟨hc1, hc2, -⟩
    · refine ⟨?_, ham⟩
      rw [show imgMod3 I I₁ ⊓ imgMod3 I I₂ = _ from hi]
      have : I₁.subgroupOf I ⊓ I₂.subgroupOf I = (I₁ ⊓ I₂).subgroupOf I :=
        (Subgroup.comap_inf _ _ _).symm
      rw [this]
      try rfl
    · exfalso
      apply c.c2
      have e1 := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_subgroupOf 2 I₁ I hI₁I
      have e2 := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_subgroupOf 2 I₂ I hI₂I
      rw [hc1] at e1
      rw [hc2] at e2
      have e3 : (pCoreOf 2 I₁).subgroupOf I = (pCoreOf 2 I₂).subgroupOf I := e1.trans e2.symm
      rw [Subgroup.subgroupOf_inj,
        inf_eq_left.mpr ((CFSG.LieType.BorelTits.pCoreOf_le 2 I₁).trans hI₁I),
        inf_eq_left.mpr ((CFSG.LieType.BorelTits.pCoreOf_le 2 I₂).trans hI₂I)] at e3
      exact e3
  obtain ⟨Kb, hKbc, hKbn, hKbF, hcase⟩ := hStruct _ _ _ ham hF h1 h1' h2
  obtain ⟨K, hKc, rfl⟩ := (imgMod3_bijOn I hs).surjOn (mem_cComp_top_of_isComponent hKbc)
  have hKI : K ≤ I := le_of_mem_cComp hKc
  have hsub : IsSubnormal K I := subnormal_of_mem_cComp hKc
  have hn : I ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_imgMod3_normal hs hKc hKbn
  have hB : CFSG.IsQuasisimple ↥(imgMod3 I K) := hKbc.1
  have hcen : ∀ z ∈ Subgroup.center ↥(imgMod3 I K), ¬ Even (orderOf z) := fun z hz =>
    not_even_orderOf_of_mem_center ham.pCore_eq_bot hKbn hz
  have := S.hyp.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat S.hyp.nonabelian S.hyp.qtke).1
  have hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
    isQuasisimple_pCore_quotient hloc a36CoreForSQTKCat_proved c.hI.1.1.2 hKc hsyl2 hB hcen
  have hext := centralExt3_imgMod3 hKI hsub hsyl2 hq hB
  have hcat : ∃ (Y : Type) (_ : Group Y), F618Core Y ∧ CentralExt3 (↥K ⧸ CFSG.pCore 2 ↥K) Y :=
    ⟨_, inferInstance, hKbF, hext⟩
  obtain ⟨Zb, hZn, hdec, hZ, hidx⟩ : ∃ Zb : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I), Zb.Normal ∧
      (⊤ : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I)) =
        imgMod3 I K ⊔ Zb ⊔ (imgMod3 I I₁ ⊓ imgMod3 I I₂) ∧
      ¬ twoResidual (imgMod3 I I₁) ≤ Zb ∧
      (I = K ⊔ (T ⊓ I) ∨ Cat3Type (↥K ⧸ CFSG.pCore 2 ↥K)) := by
    rcases hcase with ⟨hdec, hr1, hr2⟩ | ⟨Zb, hZn, hdec, hZ, p, hp, hpm, hL2⟩
    · refine ⟨⊥, Subgroup.normal_bot, by rw [sup_bot_eq]; exact hdec, ?_, Or.inl ?_⟩
      · intro h
        exact F6.not_twoResidual_le_pCoreOf_left ham.toIsGoldschmidtTriple (h.trans bot_le)
      · rw [← hinf]
        exact eq_sup_inf_of_twoResidual_le hKI hn hT hr1 hr2
    · exact ⟨Zb, hZn, hdec, hZ, Or.inr ⟨_, inferInstance, ⟨p, hp, hpm, hL2⟩, hext⟩⟩
  refine ⟨K, hKc, hKI, hn, hq, ?_, hcat, hidx⟩
  exact not_le_of_decomposition c hKI hsyl hT hint hZn hdec hZ

end Gold14610

end CFSG.Quasithin

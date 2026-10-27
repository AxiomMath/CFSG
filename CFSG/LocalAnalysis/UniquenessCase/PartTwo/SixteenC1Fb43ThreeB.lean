module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Fb43ThreeA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbW0

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def s16c1Gamma0Bar (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Set (Subgroup (MulAut (Vtil V₀ V hV))) :=
  {B | B ≠ ⊥ ∧ ∃ A ∈ E3.gammaSet V 0 D.T, barSub V₀ V hV A = B}

theorem s16c1_gamma0Bar_stable (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {B : Subgroup (MulAut (Vtil V₀ V hV))}
    (hB : B ∈ s16c1Gamma0Bar D V₀ V hV) (hBS : B ≤ barSub V₀ V hV D.T ⊓ lBar V₀ V hV L)
    {n : MulAut (Vtil V₀ V hV)}
    (hn : n ∈ normalizer ((barSub V₀ V hV D.T ⊓ lBar V₀ V hV L : Subgroup _) :
      Set (MulAut (Vtil V₀ V hV))) ⊓ lBar V₀ V hV L) :
    B.map (MulAut.conj n).toMonoidHom ∈ s16c1Gamma0Bar D V₀ V hV := by
  have hB' : B ≠ ⊥ ∧ ∃ A ∈ E3.gammaSet V 0 D.T, barSub V₀ V hV A = B := hB
  obtain ⟨hB0, A, hA, hAB⟩ := hB'
  have hM : D.M ≤ stabTil V₀ V := s16c1_M_le_stabTil hS
  have hT : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM
  have hLM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV hS.setting.hyp151.le
  have hnM : n ∈ barSub V₀ V hV D.M := hLM hn.2
  obtain ⟨m, hm, hmM, hmN, hmn⟩ :=
    s16c1_normalizer_lift hM hT inf_le_left hnM hn.1
  have hAT₁ : A ≤ D.T ⊓ preBarSub D.M V₀ V hV
      (barSub V₀ V hV D.T ⊓ lBar V₀ V hV L) := by
    intro a ha
    have haT : a ∈ D.T := hA.1 ha
    have haM : a ∈ D.M := hT.le haT
    have has : a ∈ stabTil V₀ V := hM haM
    refine ⟨haT, (mem_preBarSub D.M V₀ V hV _).2 ⟨haM, has, ?_⟩⟩
    have hmemA : actTil V₀ V hV ⟨a, has⟩ ∈ barSub V₀ V hV A :=
      actTil_mem_barSub V₀ V hV ha has
    exact hBS (hAB ▸ hmemA)
  have hAconj : A.map (MulAut.conj m).toMonoidHom ∈ E3.gammaSet V 0 D.T :=
    s16c1_gammaSet_conj_mem inf_le_left hmN hAT₁ hA
  have hm' : m⁻¹ ∈ stabTil V₀ V := (stabTil V₀ V).inv_mem hm
  have hconj : A.map (MulAut.conj m).toMonoidHom = conjSubgroup A m⁻¹ := by
    unfold conjSubgroup
    rw [inv_inv]
  have htil : (actTil V₀ V hV ⟨m⁻¹, hm'⟩)⁻¹ = n := by
    rw [show (actTil V₀ V hV ⟨m⁻¹, hm'⟩)⁻¹ =
        actTil V₀ V hV (⟨m⁻¹, hm'⟩ : stabTil V₀ V)⁻¹ from (map_inv _ _).symm]
    rw [show (⟨m⁻¹, hm'⟩ : stabTil V₀ V)⁻¹ = ⟨m, hm⟩ from Subtype.ext (by simp)]
    exact hmn
  have hEq : barSub V₀ V hV (A.map (MulAut.conj m).toMonoidHom) =
      B.map (MulAut.conj n).toMonoidHom := by
    rw [hconj, s15_Infra_barSub_conjSubgroup V₀ V hV hm' A, htil, hAB]
  change B.map (MulAut.conj n).toMonoidHom ≠ ⊥ ∧
    ∃ A ∈ E3.gammaSet V 0 D.T, barSub V₀ V hV A = B.map (MulAut.conj n).toMonoidHom
  refine ⟨?_, A.map (MulAut.conj m).toMonoidHom, hAconj, hEq⟩
  intro hbot
  exact hB0 ((Subgroup.map_eq_bot_iff_of_injective (H := B) (MulAut.conj n).injective).1 hbot)

theorem s16c1_wClos_le_preBarSub (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {Q : Subgroup (MulAut (Vtil V₀ V hV))}
    (hQ : ∀ A ∈ E3.gammaSet V 0 D.T, barSub V₀ V hV A ≤ Q) :
    E3.wClos V 0 D.T ≤ D.T ⊓ preBarSub D.M V₀ V hV Q := by
  have hM : D.M ≤ stabTil V₀ V := s16c1_M_le_stabTil hS
  have hT : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM
  unfold E3.wClos
  refine le_inf (iSup₂_le fun A hA => hA.1) (iSup₂_le fun A hA => fun a ha => ?_)
  have haT : a ∈ D.T := hA.1 ha
  have haM : a ∈ D.M := hT.le haT
  have has : a ∈ stabTil V₀ V := hM haM
  refine (mem_preBarSub D.M V₀ V hV Q).2 ⟨haM, has, ?_⟩
  exact hQ A hA (actTil_mem_barSub V₀ V hV ha has)

theorem s16c1_wClos_ne_bot_pGroup (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) :
    E3.wClos V 0 D.T ≠ ⊥ ∧ IsPGroup 2 ↥(E3.wClos V 0 D.T) := by
  have pf := hS.setting.hyp151.hyp125.pairFacts
  have hT : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM
  have hVn : (V.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer pf.le_M).2 pf.le_normalizer
  have hVT : V ≤ D.T := hT.le_of_normal pf.le_M hVn pf.elemAbelian.isPGroup
  have hVmem : V ∈ E3.gammaSet V 0 D.T := by
    refine ⟨hVT, ⟨1, ?_, ?_⟩⟩
    · simp [conjSubgroup_one]
    · rw [conjSubgroup_one, E3.mQuot_self]
  have hVle : V ≤ E3.wClos V 0 D.T := le_iSup₂_of_le V hVmem le_rfl
  have hne : E3.wClos V 0 D.T ≠ ⊥ := by
    intro hbot
    exact pf.ne_bot (le_bot_iff.1 (hVle.trans (le_of_eq hbot)))
  refine ⟨hne, ?_⟩
  have hWle : E3.wClos V 0 D.T ≤ D.T := by
    unfold E3.wClos
    exact iSup₂_le fun A hA => hA.1
  exact hT.isPGroup.to_le hWle

theorem r16_43_3_of (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D) (h42 : R16_42 D) (h43 : R16_43_1 D)
    (hkitB : OmegaKitB) : R16_43_3 D := by
  intro V₀ V L hV hS hc
  have hk := hkitB (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1
  have hM : D.M ≤ stabTil V₀ V := s16c1_M_le_stabTil hS
  have hT : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM
  have hsyl := s16c1_sylow_lBar hS hk.1
  have hmem : ∀ A ∈ E3.gammaSet V 0 D.T,
      barSub V₀ V hV A ≤ barSub V₀ V hV D.T ⊓ lBar V₀ V hV L ∧
        (barSub V₀ V hV A ≠ ⊥ → barSub V₀ V hV A ∈ E3.aSet 2 (lBar V₀ V hV L)) :=
    fun A hA => s16c1_gamma_barSub_mem D hSg h1219 h21 h22 h42 h43 hS hc hA
  obtain ⟨E, hEn, hE3, hEc⟩ := hk.2.2.2 (barSub V₀ V hV D.T ⊓ lBar V₀ V hV L) hsyl
    (s16c1Gamma0Bar D V₀ V hV)
    (fun B hB => by
      obtain ⟨hB0, A, hA, rfl⟩ := hB
      exact ⟨(hmem A hA).2 hB0, (hmem A hA).1⟩)
    (fun B hB n hn => by
      obtain ⟨hB0, A, hA, hAB⟩ := hB
      exact s16c1_gamma0Bar_stable D hS ⟨hB0, A, hA, hAB⟩
        (by rw [← hAB]; exact (hmem A hA).1) hn)
  set Q : Subgroup (MulAut (Vtil V₀ V hV)) := ⨆ B ∈ s16c1Gamma0Bar D V₀ V hV, B with hQdef
  have hAQ : ∀ A ∈ E3.gammaSet V 0 D.T, barSub V₀ V hV A ≤ Q := by
    intro A hA
    by_cases h0 : barSub V₀ V hV A = ⊥
    · rw [h0]
      exact bot_le
    · exact le_iSup₂_of_le (barSub V₀ V hV A) ⟨h0, A, hA, rfl⟩ le_rfl
  have hQT : Q ≤ barSub V₀ V hV D.T :=
    iSup₂_le fun B hB => by
      obtain ⟨-, A, hA, rfl⟩ := hB
      exact (hmem A hA).1.trans inf_le_left
  have hLM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV hS.setting.hyp151.le
  obtain ⟨X, hXM, hX3, hXc, hXN⟩ := s16c1_frattini_lift hM hT hQT hE3
    ((hEn.trans inf_le_right).trans hLM) (hEn.trans inf_le_left) hEc
  have hW : E3.wClos V 0 D.T ≤ D.T ⊓ preBarSub D.M V₀ V hV Q :=
    s16c1_wClos_le_preBarSub D hS hAQ
  have hY2 : IsPGroup 2 ↥(D.T ⊓ preBarSub D.M V₀ V hV Q) :=
    hT.isPGroup.to_le inf_le_left
  have hYM : D.T ⊓ preBarSub D.M V₀ V hV Q ≤ D.M := inf_le_left.trans hT.le
  have hN := E3.e3_15_normalizer hT hYM hY2 hW
  obtain ⟨hW0, hW2⟩ := s16c1_wClos_ne_bot_pGroup D hS
  have hp : 3 ∈ D.sig := by
    rw [hc.2.2.1]
    exact Set.mem_singleton 3
  exact normalizer_le_of_noncyclic D h61 hp hXM hX3 hXc hW0 hW2 (hXN.trans hN)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

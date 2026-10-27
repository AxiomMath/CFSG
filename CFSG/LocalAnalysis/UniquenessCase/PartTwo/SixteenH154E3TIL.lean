module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoSyl
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_normalizer_lift (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMΓ : D.M ≤ stabTil ⊥ V) (Ut : Subgroup (Vtil ⊥ V hV))
    {p : ℕ} [hp : Fact p.Prime] {E₀ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hEM : E₀ ≤ Mbar D.M ⊥ V hV) (hEp : IsPGroup p E₀) (hEc : ¬ IsCyclic ↥E₀)
    (hEn : E₀ ≤ Subgroup.normalizer
      ((barSub ⊥ V hV D.T ⊓ centSub Ut : Subgroup (MulAut (Vtil ⊥ V hV))) :
        Set (MulAut (Vtil ⊥ V hV)))) :
    ∃ P : Subgroup G,
      P ≤ D.M ⊓ normalizer
        ((D.T ⊓ centralizer ((preTil ⊥ V hV Ut : Subgroup G) : Set G) : Subgroup G) : Set G) ∧
      IsPGroup p P ∧ ¬ IsCyclic ↥P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTΓ : D.T ≤ stabTil ⊥ V := D.sylowM.le.trans hMΓ
  have hTM : D.T.subgroupOf (stabTil ⊥ V) ≤ D.M.subgroupOf (stabTil ⊥ V) :=
    Subgroup.subgroupOf_mono (stabTil ⊥ V) D.sylowM.le
  have hT' : CFSG.ABGLocalTools.IsSylowOf 2 (D.T.subgroupOf (stabTil ⊥ V))
      (D.M.subgroupOf (stabTil ⊥ V)) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (stabTil ⊥ V)]
    rw [Subgroup.map_subgroupOf_eq_of_le hTΓ, Subgroup.map_subgroupOf_eq_of_le hMΓ]
    exact D.sylowM
  let Zt : Subgroup (Vtil ⊥ V hV) := Ut
  let Z : Subgroup G := preTil ⊥ V hV Ut
  have hZpre : Z = preTil ⊥ V hV Zt := rfl
  let Tbar : Subgroup (MulAut (Vtil ⊥ V hV)) :=
    (D.T.subgroupOf (stabTil ⊥ V)).map (actTil ⊥ V hV)
  let B : Subgroup (MulAut (Vtil ⊥ V hV)) := Tbar ⊓ centSub Zt
  have hTbar : CFSG.ABGLocalTools.IsSylowOf 2 Tbar (Mbar D.M ⊥ V hV) :=
    s16c7_isSylowOf_map hT' (actTil ⊥ V hV)
  obtain ⟨E, hEMbar, hE7, hEnc, hEnorm⟩ : ∃ E : Subgroup (MulAut (Vtil ⊥ V hV)),
      E ≤ Mbar D.M ⊥ V hV ∧ IsPGroup p E ∧ ¬ IsCyclic ↥E ∧
      E ≤ Subgroup.normalizer ((Tbar ⊓ centSub Zt : Subgroup _) : Set _) :=
    ⟨E₀, hEM, hEp, hEc, hEn⟩
  have hB : B ≤ Tbar := inf_le_left
  have hE : E ≤ Mbar D.M ⊥ V hV := hEMbar
  have hEB : E ≤ Subgroup.normalizer (B : Set (MulAut (Vtil ⊥ V hV))) := hEnorm
  obtain ⟨P, hPle, hP7, hPnc⟩ :=
    s16h_frattini_lift_noncyclic_pgroup (Γ := ↥(stabTil ⊥ V))
      (Q := MulAut (Vtil ⊥ V hV)) (actTil ⊥ V hV) hTM hT' (B := B) (E := E)
      hB hE hEB hE7 hEnc
  let H : Subgroup ↥(stabTil ⊥ V) :=
    (D.T.subgroupOf (stabTil ⊥ V)) ⊓ B.comap (actTil ⊥ V hV)
  have hPleH : P ≤ (D.M.subgroupOf (stabTil ⊥ V)) ⊓
      Subgroup.normalizer (H : Set ↥(stabTil ⊥ V)) := hPle
  have hHmap : H.map (stabTil ⊥ V).subtype = D.T ⊓ Subgroup.centralizer (Z : Set G) := by
    dsimp only [H]
    rw [Subgroup.map_inf _ _ _ (Subgroup.subtype_injective (stabTil ⊥ V)),
      Subgroup.map_subgroupOf_eq_of_le hTΓ]
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_inf] at hy
      rw [Subgroup.mem_inf]
      refine ⟨hy.1, ?_⟩
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy.2
      have hzcent : (actTil ⊥ V hV) z ∈ centSub Zt := by
        have hzB : (actTil ⊥ V hV) z ∈ B := hz
        exact (Subgroup.mem_inf.1 (show (actTil ⊥ V hV) z ∈ Tbar ⊓ centSub Zt from hzB)).2
      have hzy' : z = ⟨y, hTΓ hy.1⟩ := Subtype.ext hzy
      have hzcent' : (actTil ⊥ V hV) ⟨y, hTΓ hy.1⟩ ∈ centSub Zt := by
        rwa [hzy'] at hzcent
      have hyPre : y ∈ Subgroup.centralizer (preTil ⊥ V hV Zt) :=
        (s16h_mem_centralizer_preTil_iff hV hTΓ Zt hy.1).mpr hzcent'
      rwa [← hZpre] at hyPre
    · intro y hy
      rw [Subgroup.mem_inf] at hy
      rw [Subgroup.mem_inf]
      refine ⟨hy.1, ?_⟩
      have hyPre : y ∈ Subgroup.centralizer (preTil ⊥ V hV Zt) := by
        rw [hZpre] at hy
        exact hy.2
      have hycent : (actTil ⊥ V hV) ⟨y, hTΓ hy.1⟩ ∈ centSub Zt :=
        (s16h_mem_centralizer_preTil_iff hV hTΓ Zt hy.1).mp hyPre
      refine Subgroup.mem_map.2 ⟨⟨y, hTΓ hy.1⟩, ?_, rfl⟩
      show (actTil ⊥ V hV) ⟨y, hTΓ hy.1⟩ ∈ Tbar ⊓ centSub Zt
      exact ⟨Subgroup.mem_map_of_mem (actTil ⊥ V hV)
        (Subgroup.mem_subgroupOf.2 hy.1), hycent⟩
  refine ⟨P.map (stabTil ⊥ V).subtype, ?_, hP7.map (stabTil ⊥ V).subtype, ?_⟩
  · calc P.map (stabTil ⊥ V).subtype
        ≤ ((D.M.subgroupOf (stabTil ⊥ V)) ⊓
            Subgroup.normalizer (H : Set ↥(stabTil ⊥ V))).map
            (stabTil ⊥ V).subtype := Subgroup.map_mono hPleH
      _ = (D.M.subgroupOf (stabTil ⊥ V)).map (stabTil ⊥ V).subtype ⊓
            (Subgroup.normalizer (H : Set ↥(stabTil ⊥ V))).map
              (stabTil ⊥ V).subtype :=
            Subgroup.map_inf _ _ _ (Subgroup.subtype_injective (stabTil ⊥ V))
      _ ≤ (D.M.subgroupOf (stabTil ⊥ V)).map (stabTil ⊥ V).subtype ⊓
            Subgroup.normalizer (H.map (stabTil ⊥ V).subtype) :=
            inf_le_inf_left _ (Subgroup.le_normalizer_map (stabTil ⊥ V).subtype)
      _ = D.M ⊓ Subgroup.normalizer
            ((D.T ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) : Set G) := by
            rw [Subgroup.map_subgroupOf_eq_of_le hMΓ, hHmap]
  · intro hcyc
    haveI : IsCyclic ↥(P.map (stabTil ⊥ V).subtype) := hcyc
    exact hPnc (isCyclic_of_injective
      (Subgroup.equivMapOfInjective P (stabTil ⊥ V).subtype
        (Subgroup.subtype_injective (stabTil ⊥ V))).toMonoidHom
      (Subgroup.equivMapOfInjective P (stabTil ⊥ V).subtype
        (Subgroup.subtype_injective (stabTil ⊥ V))).injective)

theorem s16h_e3_preTil_imgTil_eq {V U : Subgroup G} (hV : IsElemAbelian 2 V) (hUV : U ≤ V) :
    preTil ⊥ V hV (imgTil ⊥ V hV U) = U := by
  refine le_antisymm ?_ (le_trans (le_inf le_rfl hUV) (le_preTil_imgTil ⊥ V hV U))
  intro g hg
  obtain ⟨x, hx, hxg⟩ := (mem_preTil ⊥ V hV _).1 hg
  have hx' : mkTil ⊥ V hV x ∈ imgTil ⊥ V hV U := hxg
  obtain ⟨y, hyU, hyx⟩ := (mem_imgTil ⊥ V hV U _).1 hx'
  have hxy : x.val * (y.val)⁻¹ = 1 :=
    Subgroup.mem_bot.1 ((mkTil_eq_iff ⊥ V hV x y).1 hyx.symm)
  rw [← hx, mul_inv_eq_one.1 hxy]
  exact hyU

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

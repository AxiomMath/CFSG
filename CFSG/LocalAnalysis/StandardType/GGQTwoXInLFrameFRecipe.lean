module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFSp
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFOm
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFUni
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFAbs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.Held
open CFSG.RankThree.Classical2 (orthDerived)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQTwoFRConcl_of_cfg_sp {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {m : ℕ} {E : Subgroup ↥(CFSG.Open.StatedSp m K)}
    {x : ↥(CFSG.Open.StatedSp m K)} {L D J : Subgroup ↥(CFSG.Open.StatedSp m K)}
    (hC : GGQTwoFRCfg E x L D J) : GGQTwoFRConcl E x L D J := by
  obtain ⟨_, _, _, _, _, _, _, hM, hτ2, hU⟩ := ggQTwoUFrame_of_cfg_sp hK hC
  exact ggQTwoFRConcl_of_frame hC (ggQTwoFRFrame_of_uFrame hC hM hτ2 hU)

theorem ggQTwoFRConcl_of_cfg_orth {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {E : Subgroup ↥(orthDerived Q)} {x : ↥(orthDerived Q)} {L D J : Subgroup ↥(orthDerived Q)}
    (hC : GGQTwoFRCfg E x L D J) : GGQTwoFRConcl E x L D J := by
  obtain ⟨_, _, _, _, _, _, _, hM, hτ2, hU⟩ := ggQTwoUFrame_of_cfg_orth hK hQ hC
  exact ggQTwoFRConcl_of_frame hC (ggQTwoFRFrame_of_uFrame hC hM hτ2 hU)

private noncomputable def orthOmegaEquiv {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] (Q' : QuadraticForm K (ι → K)) :
    ↥(LargeEvenOmega (⇑Q')) ≃* ↥(orthDerived Q') :=
  let e := CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K
  have hmap : (LargeEvenOmega (⇑Q')).map e.toMonoidHom = orthDerived Q' := by
    change (CFSG.Open.StatedOmega (⇑Q')).map e.toMonoidHom = orthDerived Q'
    rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (Q := Q') rfl]
    exact Subgroup.map_comap_eq_self_of_surjective e.surjective (orthDerived Q')
  (MulEquiv.subgroupMap e (LargeEvenOmega (⇑Q'))).trans (MulEquiv.subgroupCongr hmap)

theorem ggQTwoFRRecipe_sp {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (m : ℕ) :
    GGQTwoFRRecipe (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGSpSet K m)) := by
  have : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := 1) hK
  refine ⟨?_, ?_⟩
  · intro φ hφ
    have h := matConjImage_gsp_subset_inn (K := K) m hφ
    obtain ⟨r, hr⟩ := (MonoidHom.mem_range).1 h
    exact ⟨r, hr.symm⟩
  · intro E x L D J hC
    obtain ⟨e⟩ := nonempty_largeEvenProj_equiv_of_card_two hK (LargeEvenSpGroup K m)
    exact GGQTwoFRConcl.of_map e (ggQTwoFRConcl_of_cfg_sp hK (hC.map e))

theorem ggQTwoFRRecipe_omegaPlus {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (m : ℕ) :
    GGQTwoFRRecipe (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) (LargeEvenInnSet _) := by
  have : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := 1) hK
  let Q' : QuadraticForm K (Fin m ⊕ Fin m → K) := TableBOrth.qPlusForm K m
  obtain ⟨e₁⟩ := nonempty_largeEvenProj_equiv_of_card_two hK
    (LargeEvenOmega (LargeEvenQPlus K m))
  let e₂ : ↥(LargeEvenOmega (LargeEvenQPlus K m)) ≃* ↥(orthDerived Q') :=
    (MulEquiv.subgroupCongr (by rw [TableBOrth.coe_qPlusForm])).trans (orthOmegaEquiv Q')
  let e : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)) ≃* ↥(orthDerived Q') :=
    e₁.trans e₂
  refine ⟨?_, ?_⟩
  · intro φ hφ
    change φ ∈ Set.range MulAut.conj at hφ
    obtain ⟨r, hr⟩ := hφ
    exact ⟨r, hr.symm⟩
  · intro E x L D J hC
    exact GGQTwoFRConcl.of_map e
      (ggQTwoFRConcl_of_cfg_orth hK (TableBOrth.nondegenerate_qPlusForm (K := K) m)
        (hC.map e))

theorem ggQTwoFRRecipe_omegaMinus {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (m : ℕ)
    {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGQTwoFRRecipe (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))
      (LargeEvenInnSet _) := by
  have : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := 1) hK
  let Q' : QuadraticForm K (LargeEvenMinusIdx m → K) := TableBOrth.qMinusForm K m b c
  obtain ⟨e₁⟩ := nonempty_largeEvenProj_equiv_of_card_two hK
    (LargeEvenOmega (LargeEvenQMinus m b c))
  let e₂ : ↥(LargeEvenOmega (LargeEvenQMinus m b c)) ≃* ↥(orthDerived Q') :=
    (MulEquiv.subgroupCongr (by rw [TableBOrth.coe_qMinusForm])).trans (orthOmegaEquiv Q')
  let e : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)) ≃* ↥(orthDerived Q') :=
    e₁.trans e₂
  refine ⟨?_, ?_⟩
  · intro φ hφ
    change φ ∈ Set.range MulAut.conj at hφ
    obtain ⟨r, hr⟩ := hφ
    exact ⟨r, hr.symm⟩
  · intro E x L D J hC
    exact GGQTwoFRConcl.of_map e
      (ggQTwoFRConcl_of_cfg_orth hK (TableBOrth.nondegenerate_qMinusForm (K := K) m hbc)
        (hC.map e))

end CFSG.StandardType

end

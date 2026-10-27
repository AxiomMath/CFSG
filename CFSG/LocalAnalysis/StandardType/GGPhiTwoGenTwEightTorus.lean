module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwEightLang
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionLang
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreFrame
public import CFSG.LocalAnalysis.WeakClosure81.SU3RankRoots
public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeD4Torus
public import CFSG.Adapters.TauCetiExceptional.BigCellEndgameE
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoFrame
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoD4
public import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization
public import CFSG.RankThree.PartOne.Q1327T.Item7D4W
public import CFSG.RankThree.PartOne.KE6.EqpOpp
public import CFSG.LieType.Chevalley.GraphFixedRankOneImage
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeDiag

public noncomputable section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Malle.SeitzCube
open scoped MatrixGroups

@[expose] def frameVG : Submodule (ZMod 3) (Fin 6 → ZMod 3) where
  carrier := {t | t 0 = t 5 ∧ t 2 = t 4}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨by simp [Pi.add_apply, ha1, hb1], by simp [Pi.add_apply, ha2, hb2]⟩
  smul_mem' := by
    intro c a ha
    exact ⟨by simp [Pi.smul_apply, ha.1], by simp [Pi.smul_apply, ha.2]⟩

@[expose] def frameW : Submodule (ZMod 3) (Fin 6 → ZMod 3) where
  carrier := {t | t 1 = 0 ∧ t 3 = 0 ∧ t 0 + t 5 = 0 ∧ t 2 + t 4 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    obtain ⟨ha1, ha3, ha05, ha24⟩ := ha
    obtain ⟨hb1, hb3, hb05, hb24⟩ := hb
    refine ⟨by simp [Pi.add_apply, ha1, hb1], by simp [Pi.add_apply, ha3, hb3], ?_, ?_⟩
    · simp only [Pi.add_apply]; linear_combination ha05 + hb05
    · simp only [Pi.add_apply]; linear_combination ha24 + hb24
  smul_mem' := by
    intro c a ha
    obtain ⟨ha1, ha3, ha05, ha24⟩ := ha
    refine ⟨by simp [Pi.smul_apply, ha1], by simp [Pi.smul_apply, ha3], ?_, ?_⟩
    · simp only [Pi.smul_apply]
      rw [← smul_add, ha05, smul_zero]
    · simp only [Pi.smul_apply]
      rw [← smul_add, ha24, smul_zero]

@[expose] def frameCoroot : Fin 4 → (Fin 6 → ZMod 3) :=
  ![![0, 2, 2, 2, 2, 0], ![2, 2, 1, 0, 1, 2], ![1, 2, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 0]]

private lemma zmod_mul_four : ∀ a : ZMod 3, a * 4 = a := by decide
private lemma zmod_mul_three : ∀ a : ZMod 3, a * 3 = 0 := by decide
private lemma zmod_mul_six : ∀ a : ZMod 3, a * 6 = 0 := by decide
private lemma zmod_mul_twelve : ∀ a : ZMod 3, a * 12 = 0 := by decide

private lemma frameVG_inf_frameW : frameVG ⊓ frameW = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro t ht
  obtain ⟨hVG, hW⟩ := ht
  simp only [frameVG, frameW] at hVG hW
  obtain ⟨h1, h3, h05, h24⟩ := hW
  rw [← hVG.1] at h05
  rw [← hVG.2] at h24
  have ht0 : t 0 = 0 := by
    have h : (2 : ZMod 3) * t 0 = 0 := by linear_combination h05
    exact (mul_eq_zero.mp h).resolve_left (by decide)
  have ht2 : t 2 = 0 := by
    have h : (2 : ZMod 3) * t 2 = 0 := by linear_combination h24
    exact (mul_eq_zero.mp h).resolve_left (by decide)
  have ht5 : t 5 = 0 := by rw [← hVG.1, ht0]
  have ht4 : t 4 = 0 := by rw [← hVG.2, ht2]
  funext k
  fin_cases k <;> simp [ht0, ht2, ht4, ht5, h1, h3]

private lemma frameVG_sup_frameW : frameVG ⊔ frameW = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro t
  let v : Fin 6 → ZMod 3 :=
    ![2 * (t 0 + t 5), 4 * t 1, 2 * (t 2 + t 4), 4 * t 3, 2 * (t 2 + t 4), 2 * (t 0 + t 5)]
  let w : Fin 6 → ZMod 3 :=
    ![2 * (t 0 - t 5), 0, 2 * (t 2 - t 4), 0, 2 * (t 4 - t 2), 2 * (t 5 - t 0)]
  have hv : v ∈ frameVG := by
    refine ⟨?_, ?_⟩ <;> simp [v]
  have hw : w ∈ frameW := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [w] <;> ring
  refine Submodule.mem_sup.mpr ⟨v, hv, w, hw, ?_⟩
  have hvw : v + w = t := by
    funext k
    fin_cases k <;> simp [v, w] <;> ring_nf <;> simp [zmod_mul_four]
  exact hvw

theorem frameVG_isCompl_frameW : IsCompl frameVG frameW :=
  ⟨disjoint_iff.mpr frameVG_inf_frameW, codisjoint_iff.mpr frameVG_sup_frameW⟩

private def frameVGEquiv : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] frameVG where
  toFun u := ⟨![u 0, u 1, u 2, u 3, u 2, u 0], by simp [frameVG]⟩
  invFun t := ![t.1 0, t.1 1, t.1 2, t.1 3]
  left_inv u := by
    funext k
    fin_cases k <;> rfl
  right_inv t := by
    refine Subtype.ext ?_
    funext k
    fin_cases k <;> simp [frameVG] <;> (try exact t.2.2); (try exact t.2.1)
  map_add' u v := by
    refine Subtype.ext ?_
    funext k
    fin_cases k <;> simp [Pi.add_apply]
  map_smul' c u := by
    refine Subtype.ext ?_
    funext k
    fin_cases k <;> simp [Pi.smul_apply]

theorem frameVG_finrank : Module.finrank (ZMod 3) frameVG = 4 := by
  have h := LinearEquiv.finrank_eq frameVGEquiv
  rw [Module.finrank_fin_fun] at h
  exact h.symm

theorem frameVG_decomp (t : Fin TwistTag.E6.tag.rank → ZMod 3) (ht : t ∈ frameVG) :
    t = (2 * ((t 3).val : ℤ)) • frameCoroot 0 +
      (((t 2).val : ℤ) + 2 * ((t 3).val : ℤ)) • frameCoroot 1 +
      (((t 0).val : ℤ) + ((t 2).val : ℤ) + 2 * ((t 3).val : ℤ)) • frameCoroot 2 +
      (((t 0).val : ℤ) + ((t 1).val : ℤ) + 2 * ((t 2).val : ℤ)) • frameCoroot 3 := by
  revert t
  change ∀ t : Fin 6 → ZMod 3, t ∈ frameVG →
    t = (2 * ((t 3).val : ℤ)) • frameCoroot 0 +
      (((t 2).val : ℤ) + 2 * ((t 3).val : ℤ)) • frameCoroot 1 +
      (((t 0).val : ℤ) + ((t 2).val : ℤ) + 2 * ((t 3).val : ℤ)) • frameCoroot 2 +
      (((t 0).val : ℤ) + ((t 1).val : ℤ) + 2 * ((t 2).val : ℤ)) • frameCoroot 3
  intro t ht
  simp only [frameVG] at ht
  funext k
  fin_cases k <;>
    simp [frameCoroot, ht.1, ht.2] <;>
    ring_nf <;>
    simp [zmod_mul_four, zmod_mul_three, zmod_mul_six, zmod_mul_twelve]

end CFSG.StandardType.PhiTwoRootGen

end

module

public import CFSG.LocalAnalysis.StandardType.GGLangRatComp
public import CFSG.RankThree.PartOne.S11c.G2Torus
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section SL2

variable {L : Type} [Field L]

theorem HSL_eq_uvu_two [CharP L 2] (t : Lˣ) :
    (HSL t : SL2 L) = uSL (t : L) * vSL ((t⁻¹ : Lˣ) : L) * uSL (t : L) *
      (uSL 1 * vSL 1 * uSL 1) := by
  have h : (t : L) * ((t⁻¹ : Lˣ) : L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_HSL, coe_uSL, coe_vSL]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h, CharTwo.add_self_eq_zero]

theorem HSL_inv_eq_vuv_two [CharP L 2] (s : Lˣ) :
    (HSL s⁻¹ : SL2 L) = vSL (s : L) * uSL ((s⁻¹ : Lˣ) : L) * vSL (s : L) *
      (vSL 1 * uSL 1 * vSL 1) := by
  have h : (s : L) * ((s⁻¹ : Lˣ) : L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_HSL, coe_uSL, coe_vSL]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h, CharTwo.add_self_eq_zero]

end SL2

section Step

variable
  {τ : Tag} {L : Type} [Field L] [CharP L 2]

theorem step_rootSL2_HSL (D : LangDatum τ L) {Fr : L →+* L} {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (h₁ : ∀ c, D.step (pinnedX τ L γ c) = pinnedX τ L (-γ) (Fr c))
    (h₂ : ∀ c, D.step (pinnedX τ L (-γ) c) = pinnedX τ L γ (Fr c)) (t : Lˣ) :
    D.step (rootSL2 τ L γ (HSL t)) = rootSL2 τ L γ (HSL (Units.map Fr.toMonoidHom t)⁻¹) := by
  rw [HSL_eq_uvu_two t, HSL_inv_eq_vuv_two (Units.map Fr.toMonoidHom t)]
  simp only [map_mul, CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo hγ,
    CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo hγ, h₁, h₂, map_one, Units.coe_map,
    Units.coe_map_inv]
  rfl

theorem rootSL2_HSL_mem_model_of_step (D : LangDatum τ L) {Fr : L →+* L}
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (h₁ : ∀ c, D.step (pinnedX τ L γ c) = pinnedX τ L (-γ) (Fr c))
    (h₂ : ∀ c, D.step (pinnedX τ L (-γ) c) = pinnedX τ L γ (Fr c)) {t : Lˣ}
    (ht : Units.map Fr.toMonoidHom t = t⁻¹) : rootSL2 τ L γ (HSL t) ∈ D.model := by
  refine ⟨(exceptional_Lang_root_rank_one_data τ L γ).2.2.2.2.1 _, ?_⟩
  change D.step (rootSL2 τ L γ (HSL t)) = rootSL2 τ L γ (HSL t)
  rw [step_rootSL2_HSL D hγ h₁ h₂, ht, inv_inv]

theorem rootSL2_HSL_mem_rationalComponent_of_step
    [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {Fr : L →+* L}
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ componentRoots (rootCharHom a) i)
    (h₁ : ∀ c, S.D.step (pinnedX τ L γ c) = pinnedX τ L (-γ) (Fr c))
    (h₂ : ∀ c, S.D.step (pinnedX τ L (-γ) c) = pinnedX τ L γ (Fr c))
    (hW : rootSL2 τ L γ WSL ∈ S.Γ)
    {t : Lˣ} (ht : Units.map Fr.toMonoidHom t = t⁻¹)
    {m : ℕ} (hm : Odd m) (htm : t ^ m = 1) :
    rootSL2 τ L γ (HSL t) ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  have hγr : IsRoot τ γ := (isRootComponent_componentRoots i).isRoot γ hγ
  exact rootSL2_HSL_mem_rationalComponent_of_model_odd S i hγ hW
    (rootSL2_HSL_mem_model_of_step S.D hγr h₁ h₂ ht) hm htm

theorem rootSL2_HSL_mem_rationalComponent_of_entrywise_step
    [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {Fr : L →+* L} {w : WeylGroup τ}
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
    (hw : ∀ v : Fin τ.rank → ℤ, w • v = -v)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ componentRoots (rootCharHom a) i)
    (hW : rootSL2 τ L γ WSL ∈ S.Γ)
    {t : Lˣ} (ht : Units.map Fr.toMonoidHom t = t⁻¹)
    {m : ℕ} (hm : Odd m) (htm : t ^ m = 1) :
    rootSL2 τ L γ (HSL t) ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  have hγr : IsRoot τ γ := (isRootComponent_componentRoots i).isRoot γ hγ
  set b : Fin τ.rank → Lˣ := fun j => t ^ corootPair γ (Pi.single j 1) with hb
  have hlin : ∀ δ : Fin τ.rank → ℤ,
      corootPair γ δ = ∑ j, δ j * corootPair γ (Pi.single j 1) := by
    intro δ
    have hp := iform_self_pos_of_isRoot hγr
    refine mul_right_cancel₀ hp.ne' ?_
    rw [corootPair_mul hγr, Finset.sum_mul]
    have hif : iform γ δ = ∑ j, δ j * iform γ (Pi.single j 1) := by
      conv_lhs => rw [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.eq_sum_single δ]
      rw [iform_finset_sum_right]
      exact Finset.sum_congr rfl fun j _ => by rw [iform_smul_right]
    rw [hif, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, corootPair_mul hγr]
    ring
  have hSL2 : rootSL2 τ L γ (HSL t) = rootDiagUnit τ b := by
    rw [hb]
    exact CFSG.RankThree.PartOne.rootSL2_HSL_eq_rootDiagUnit hγr _
      (fun δ _ => hlin δ) t
  have hΦdiag : S.D.Φ (rootDiagUnit τ b) =
      rootDiagUnit τ (fun j => Units.map Fr.toMonoidHom (b j)) := by
    rw [hΦ]
    refine Units.ext ?_
    rw [Units.coe_map]
    exact entrywise_rootDiag Fr b
  have hFr_b : (fun j => Units.map Fr.toMonoidHom (b j)) = b⁻¹ := by
    funext j
    rw [hb]
    simp only [Pi.inv_apply, map_zpow, ht, inv_zpow]
  have hw_inv : ∀ v : Fin τ.rank → ℤ, w⁻¹ • v = -v := by
    intro v
    have h1 : w • (w⁻¹ • v) = v := by rw [← mul_smul, mul_inv_cancel, one_smul]
    have h2 : w • (w⁻¹ • v) = -(w⁻¹ • v) := hw _
    rw [h1] at h2
    have h3 := congrArg Neg.neg h2
    simpa using h3.symm
  have hweyl : CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w
      (fun j => Units.map Fr.toMonoidHom (b j)) = b := by
    rw [hFr_b]
    funext j
    simp only [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct, hw_inv]
    have hneg : rootChar (b⁻¹) (-(Pi.single j 1 : Fin τ.rank → ℤ)) =
        (rootChar (b⁻¹) (Pi.single j 1))⁻¹ := by
      rw [show -(Pi.single j 1 : Fin τ.rank → ℤ) = 0 - Pi.single j 1 by simp,
        rootChar_sub, rootChar_zero, one_mul]
    rw [hneg, rootChar_inv_apply, inv_inv,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.rootChar_single]
  have hmodel_diag : rootDiagUnit τ b ∈ S.D.model := by
    refine S.D.mem_model.2 ⟨?_, ?_⟩
    · exact hSL2 ▸ CFSG.LieType.Chevalley.rootSL2_mem_adjointGroup γ (HSL t)
    · change S.D.n * S.D.Φ (rootDiagUnit τ b) * S.D.n⁻¹ = rootDiagUnit τ b
      rw [hΦdiag, hn,
        CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit, hweyl]
  exact rootSL2_HSL_mem_rationalComponent_of_model_odd (t := t) S i hγ hW
    (hSL2.symm ▸ hmodel_diag) hm htm

end Step

end CFSG.StandardType.LangRat

end

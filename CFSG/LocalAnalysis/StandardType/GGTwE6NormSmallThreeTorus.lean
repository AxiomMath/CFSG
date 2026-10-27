module

public import CFSG.LocalAnalysis.StandardType.GGTwE6EltSmallFrame
public import CFSG.LocalAnalysis.StandardType.GGLangRatStep
import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools

public section

namespace CFSG.StandardType.TwE6NormThree

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups

section SL2

variable {L : Type} [Field L]

private theorem conjSL_diagUnitOne_WSL_eq (s : Lˣ) :
    RankThree.Classical.conjSL (RankThree.Classical.diagUnitOne s) (WSL : SL2 L) = HSL s * WSL := by
  ext i j
  rw [RankThree.Classical.coe_conjSL, RankThree.Classical.coe_diagUnitOne,
    RankThree.Classical.coe_diagUnitOne_inv, Matrix.SpecialLinearGroup.coe_mul, coe_HSL, coe_WSL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem WSL_conj_HSL_eq (z : Lˣ) : (WSL : SL2 L) * HSL z * WSL⁻¹ = (HSL z)⁻¹ := by
  rw [← hslHom_apply, ← map_inv, hslHom_apply, hslHom_apply, mul_inv_eq_iff_eq_mul]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_HSL, coe_WSL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end SL2

section Weyl

theorem rootSL2_WSL_conj_rootDiagUnit {L : Type} [Field L] {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (c : Fin TwistTag.E6.tag.rank → Lˣ) :
    rootSL2 TwistTag.E6.tag L γ WSL * rootDiagUnit TwistTag.E6.tag c *
        (rootSL2 TwistTag.E6.tag L γ WSL)⁻¹ =
      rootDiagUnit TwistTag.E6.tag c *
        (rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ (rootChar c γ)))⁻¹ := by
  have h := RankThree.Chevalley.rootDiagUnit_conj_rootSL2 c hγ WSL
  rw [conjSL_diagUnitOne_WSL_eq, map_mul,
    TwE6EltSmall.rootSL2_HSL_eq_rootDiagUnit_corootTuple hγ] at h
  have hcomm : Commute (rootDiagUnit TwistTag.E6.tag c)
      (rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ (rootChar c γ))) := by
    rw [Commute, SemiconjBy, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  have hH : rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ (rootChar c γ)) =
      rootDiagUnit TwistTag.E6.tag c * rootSL2 TwistTag.E6.tag L γ WSL *
        (rootDiagUnit TwistTag.E6.tag c)⁻¹ * (rootSL2 TwistTag.E6.tag L γ WSL)⁻¹ := by
    rw [h, mul_inv_cancel_right]
  rw [hcomm.inv_right.eq, hH]
  group

theorem rootSL2_WSL_conj_corootTuple {L : Type} [Field L] {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (z : Lˣ) :
    rootSL2 TwistTag.E6.tag L γ WSL * rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ z) *
        (rootSL2 TwistTag.E6.tag L γ WSL)⁻¹ =
      (rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ z))⁻¹ := by
  rw [← TwE6EltSmall.rootSL2_HSL_eq_rootDiagUnit_corootTuple hγ, ← map_inv, ← map_inv,
    ← map_mul, ← map_mul, WSL_conj_HSL_eq]

end Weyl

theorem exists_corootTuple_inv_eq_pow {L : Type} [Field L] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 3)
    (γ : Fin TwistTag.E6.tag.rank → ℤ) {z : Lˣ} (hz : z ^ 3 = 1) :
    ∃ k : ℕ, (rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ z))⁻¹ =
      rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ) ^ k := by
  have hpow : ∀ j : ℕ, rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ (ζ ^ j)) =
      rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ) ^ j := fun j => by
    rw [rootDiagUnit_pow]
    congr 1
    funext k
    simp only [TwE6RootAs.corootTuple, Pi.pow_apply]
    rw [← zpow_natCast, ← zpow_natCast (ζ ^ _), ← zpow_mul, ← zpow_mul, mul_comm]
  have h1 : TwE6RootAs.corootTuple γ (1 : Lˣ) = 1 := funext fun k => one_zpow _
  obtain ⟨m, -, rfl⟩ := hζ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity 3 z).2 hz)
  refine ⟨2 * m, inv_eq_of_mul_eq_one_right ?_⟩
  rw [hpow, ← pow_add, show m + 2 * m = 3 * m by ring, pow_mul, ← hpow, hζ.pow_eq_one, h1,
    rootDiagUnit_one, one_pow]

section Ennola

theorem rootDiagUnit_corootTuple_mem_rationalComponent {K : Type} [Field K] [Finite K] {n : ℕ}
    {σ : K ≃+* K} {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (D : CFSG.LieType.SeitzGeneration.ExcWideThree.TwLangData K σ (2 ^ n) A)
    (hv : ∀ γ, D.v • permLattice TwistTag.E6.perm γ = -γ) {p : ℕ}
    (S : LangSetup TwistTag.E6.tag (AlgebraicClosure K) p)
    (hSD : S.D = LangDatum.ofTwist TwistTag.E6 D.Fr (2 ^ n) D.hFr D.v D.hg0C D.hg0)
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {ζ : (AlgebraicClosure K)ˣ} (hζ : IsPrimitiveRoot ζ 3)
    {a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ} (i : KernelComponent (rootCharHom a))
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom a) i) :
    rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ) ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hγr : IsRoot TwistTag.E6.tag γ := (isRootComponent_componentRoots i).isRoot γ hγ
  have hstep : ∀ δ, IsRoot TwistTag.E6.tag δ → ∀ c,
      S.D.step (pinnedX TwistTag.E6.tag (AlgebraicClosure K) δ c) =
        pinnedX TwistTag.E6.tag (AlgebraicClosure K) (-δ) (D.Fr c) := fun δ hδ c => by
    rw [hSD]
    exact TwE6EltSmall.ennola_step_pinnedX D hv hK hδ c
  have hFr : Units.map D.Fr.toMonoidHom ζ = ζ⁻¹ := by
    obtain ⟨m, hm⟩ := h3
    have hq : Units.map D.Fr.toMonoidHom ζ = ζ ^ 2 ^ n :=
      Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val]; exact D.hFr _)
    refine eq_inv_of_mul_eq_one_left ?_
    rw [hq, ← pow_succ, hm, pow_mul, hζ.pow_eq_one, one_pow]
  rw [← TwE6EltSmall.rootSL2_HSL_eq_rootDiagUnit_corootTuple hγr]
  exact LangRat.rootSL2_HSL_mem_rationalComponent_of_step S i hγ (hstep γ hγr)
    (fun c => by simpa only [neg_neg] using hstep (-γ) (IsRoot.neg hγr) c)
    (TwE6EltSmall.ennola_rootSL2_WSL_mem_Γ D hv S hSD hn hK hσ hγr)
    hFr (by norm_num) hζ.pow_eq_one

end Ennola

end CFSG.StandardType.TwE6NormThree

end

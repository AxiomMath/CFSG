module

public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourOutD4Type
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourOutD4Cent
import CFSG.LocalAnalysis.StandardType.GGTwE6D5CoreSpin
import CFSG.LocalAnalysis.StandardType.GGTwE6K1LineAux
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Plumb
import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24


theorem exists_not_inner_of_d4 (hS : E6LeviThreeToralBar)
    {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {h : twistedE6InndiagGL K σ} (hh1 : h ≠ 1) (hh3 : h ^ 3 = 1)
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hfE : twistedE6InndiagConj K σ h ∈ E)
    (hEI : E ≤ (twistedE6InndiagConj K σ).range)
    (hnt : ¬ E6AdToral (((E.comap (twistedE6InndiagConj K σ)).map
      (twistedE6InndiagGL K σ).subtype).map
        (baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K)))))
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.LieType.Seitz.fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))))
    (hEJ : ∀ e ∈ E, J.map e.toMonoidHom = J)
    (hCJ : ∀ e ∈ E, (∀ c ∈ J, e c = c) → e ∈ Subgroup.zpowers (twistedE6InndiagConj K σ h))
    (hmark : LargeEvenMarking ↥J (fun lab' _ _ _ _ _ => lab' = ⟨.D, 4, n⟩)) :
    ∃ e ∈ E, ¬ ∃ x ∈ J, ∀ l ∈ J, e l = x * l * x⁻¹ := by
  classical
  have h30 := twE6MatFixDim_eq_30_of_d4 hS hn h3 hK hσ hh1 hh3 hE hcard hfE hEI hnt hJ hEJ hCJ
    hmark
  by_contra hcon
  push Not at hcon
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K 2]
    decide
  have hinj : Function.Injective (twistedE6InndiagConj K σ) :=
    twE6_conj_injective K σ (2 ^ n) hσ hK hq2
  obtain ⟨D⟩ := d4t2pl_nonempty_lineLangIota K σ (2 ^ n) hK3 hσ hK hq2 h hh1 hh3
  obtain ⟨i, -, hJi⟩ := D.toTwE6LineLang.exists_rationalComponent hJ
  have hin := twistInner_of_d4 h3 D.toTwE6LineLang h30 i hJi hmark
  have hall : (kernelRoots (rootCharHom D.a)).ncard = 24 := by
    have := D.hker
    omega
  haveI : Fact (ringChar K).Prime := ⟨D.hℓ⟩
  haveI := D.hchar
  have hcomp0 : ∀ (x : ↥(twistedE6InndiagGL K σ)) (y : ↥(twistedE6RootGroup K σ)),
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((twistedE6InndiagConj K σ x y : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
          (baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K))⁻¹ := by
    intro x y
    rw [twistedE6InndiagConj_apply, map_mul, map_mul, map_inv]
  obtain ⟨P, hPcj, hPlf, hPι⟩ : ∃ P : D4T2PlumbData ↥(twistedE6RootGroup K σ)
      ↥(twistedE6InndiagGL K σ) (ModGL Tag.E6 (AlgebraicClosure K)),
      P.cj = twistedE6InndiagConj K σ ∧
      (∀ x : ↥(twistedE6InndiagGL K σ), P.lf x = D.S.D.g0⁻¹ *
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) :
          ModGL Tag.E6 (AlgebraicClosure K)) * D.S.D.g0) ∧ P.ι = D.ι :=
    ⟨D4T2PlumbData.ofBaseChange (twistedE6InndiagConj K σ)
      ((baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))).comp
        (twistedE6InndiagGL K σ).subtype)
      ((baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))).comp
        (twistedE6RootGroup K σ).subtype) D.ι D.S.D.g0 hinj
      ((baseChangeGL_injective _).comp (Subgroup.subtype_injective _)) D.hinj D.hι hcomp0,
      rfl, fun x => D4T2PlumbData.ofBaseChange_lf .., rfl⟩
  have key : ∀ g : ↥(twistedE6InndiagGL K σ), twistedE6InndiagConj K σ g ∈ E →
      P.lf g ∈ toralRootGroup Tag.E6 (AlgebraicClosure K) D.a := by
    intro g hgE
    obtain ⟨x, hxJ, hx⟩ := hcon _ hgE
    have hxR : D.ι x ∈ rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i := by
      rw [← hJi]
      exact Subgroup.mem_map_of_mem _ hxJ
    have hxG : D.ι x ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := by
      have hxΓ : D.ι x ∈ D.S.Γ := by
        rw [← D.hrange]
        exact MonoidHom.mem_range.2 ⟨x, rfl⟩
      exact (D.S.D.mem_model.1 (D.S.Γ_le_model hxΓ)).1
    have hgG : P.lf g ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := by
      rw [hPlf]
      exact (D.S.D.mem_model.1 (D.hlift g g.2)).1
    have hyc : ∀ z ∈ rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i,
        Commute ((D.ι x)⁻¹ * P.lf g) z := by
      intro z hz
      rw [← hJi] at hz
      obtain ⟨l, hl, rfl⟩ := hz
      have h1 := P.comp g l
      rw [hPcj, hPι, hx l hl, map_mul, map_mul, map_inv] at h1
      show (D.ι x)⁻¹ * P.lf g * D.ι l = D.ι l * ((D.ι x)⁻¹ * P.lf g)
      calc (D.ι x)⁻¹ * P.lf g * D.ι l
          = (D.ι x)⁻¹ * (P.lf g * D.ι l * (P.lf g)⁻¹) * P.lf g := by group
        _ = (D.ι x)⁻¹ * (D.ι x * D.ι l * (D.ι x)⁻¹) * P.lf g := by rw [h1]
        _ = D.ι l * ((D.ι x)⁻¹ * P.lf g) := by group
    have hyH := mem_torusGroup_of_commute_d4 D.toTwE6LineLang h30 i hin
      (mul_mem (inv_mem hxG) hgG) hyc
    have hxT : D.ι x ∈ toralRootGroup Tag.E6 (AlgebraicClosure K) D.a :=
      (le_sup_right : rootSpan Tag.E6 (AlgebraicClosure K) (kernelRoots (rootCharHom D.a)) ≤
        toralRootGroup Tag.E6 (AlgebraicClosure K) D.a)
        (CFSG.StandardType.TwE6D5Core.rationalComponent_le_rootSpan D.S D.hT i hxR)
    have hyT : (D.ι x)⁻¹ * P.lf g ∈ toralRootGroup Tag.E6 (AlgebraicClosure K) D.a :=
      (le_sup_left : torusGroup Tag.E6 (AlgebraicClosure K) ≤
        toralRootGroup Tag.E6 (AlgebraicClosure K) D.a) hyH
    have hgT := mul_mem hxT hyT
    rwa [mul_inv_cancel_left] at hgT
  apply hnt
  refine (e6AdToral_map_conj (inv_mem D.S.D.g0_mem) _).1 (hS (AlgebraicClosure K) (ringChar K)
    hK3 (isAlgebraic_zmod_algebraicClosure_of_finite K (ringChar K)) D.a D.hap (by simp [hall]) _
    ((isElemAbelian_baseChange_comap hinj hE).map _) ?_)
  rintro _ ⟨_, ⟨_, ⟨g, hgE, rfl⟩, rfl⟩, rfl⟩
  have hg := key g hgE
  rw [hPlf] at hg
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  exact hg

end CFSG.StandardType.SCFourCover

end

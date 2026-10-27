module

public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreFuseFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsCoreDefs
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjCore
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Lang
import CFSG.LocalAnalysis.StandardType.GGTwE6RootKernelCount
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
import CFSG.RankThree.PartTwo.Sec11.KS11Lie5ProofConjLang
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwLangConsumers
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwVacuity
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Adj
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4StandardParabolic
import CFSG.RankThree.PartOne.K133H.G2Plane

public section

set_option linter.unusedSectionVars false

namespace CFSG.StandardType.TwE6CorootCore

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.SeitzReduction CFSG.SeitzReduction.TwistedE6Pilot
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Chevalley
open CFSG.LieType.Chevalley.E6GraphLevi (thetaSL2)

theorem exists_conj_eq_thetaSL2_pow_of_coroot_conj {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ f) {k : Type}
    [Field k] [Algebra k K] (hk : Nat.card k = 2 ^ f)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (t : ModGL TwistTag.E6.tag K) (ht : t ∈ twistedE6InndiagGL K σ)
    (γ : Fin TwistTag.E6.tag.rank → ℤ) (hγ : IsRoot TwistTag.E6.tag γ) (p : ℕ) (_hp : p.Prime)
    (hpq : p ∣ 2 ^ f + 1) (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    (hcor : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) t * g0 =
      rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ)) :
    ∃ c ∈ twistedE6InndiagGL K σ, ∃ A : SL2 k, orderOf A = Nat.card k + 1 ∧ ∃ m : ℕ,
      A ^ m ≠ 1 ∧ c * t * c⁻¹ =
        (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (A ^ m) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero
    (E6GraphHighestRoot.two_eq_zero_of_card hf hk)
  have : CharP K 2 := TwistedE6Pilot.charP_two_of_card hf hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA⟩ := F4Pilot.exists_orderOf_eq_natCard_add_one (K := k)
  obtain ⟨l, P, -, hlq, hP⟩ :=
    exists_inv_mul_map_mul_eq_HSL_of_finrank (TwistedE6Pilot.finrank_eq_two hf hk hK) hA
  have hlo : orderOf l = Nat.card k + 1 := by
    have e : P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k K) A * P =
        MulAut.conj P⁻¹ (Matrix.SpecialLinearGroup.map (algebraMap k K) A) := by
      rw [MulAut.conj_apply, inv_inv]
    rw [← F4Pilot.orderOf_HSL, ← hP, e, ← MulEquiv.coe_toMonoidHom,
      orderOf_injective _ (MulAut.conj P⁻¹).injective,
      orderOf_injective _ (F4Pilot.SL2_map_injective (algebraMap k K)), hA]
  obtain ⟨lL, hlL⟩ : ∃ x : (AlgebraicClosure K)ˣ,
      x = Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom l := ⟨_, rfl⟩
  have hlLo : orderOf lL = Nat.card k + 1 := by
    rw [hlL, orderOf_injective _ (Units.map_injective
      (f := (algebraMap K (AlgebraicClosure K)).toMonoidHom) (algebraMap K _).injective), hlo]
  have hζq : ζ ^ (Nat.card k + 1) = 1 := by
    obtain ⟨c, hc⟩ := hpq
    rw [hk, hc, pow_mul, hζ, one_pow]
  obtain ⟨m, -, hm⟩ := (IsPrimitiveRoot.iff_orderOf.2 hlLo).eq_pow_of_mem_rootsOfUnity
    ((mem_rootsOfUnity _ ζ).2 hζq)
  have hAm : A ^ m ≠ 1 := fun h => hζ1 (by
    rw [← hm, ← orderOf_dvd_iff_pow_eq_one, hlLo, ← hA]
    exact orderOf_dvd_of_pow_eq_one h)
  obtain ⟨PL, hPL⟩ : ∃ X : SL2 (AlgebraicClosure K),
      X = Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) P := ⟨_, rfl⟩
  obtain ⟨BL, hBL⟩ : ∃ X : SL2 (AlgebraicClosure K),
      X = Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))
        (Matrix.SpecialLinearGroup.map (algebraMap k K) A) := ⟨_, rfl⟩
  have hPBL : PL⁻¹ * BL * PL = HSL lL := by
    rw [hPL, hBL, hlL, ← E6GraphLevi.map_HSL, ← hP, map_mul, map_mul, map_inv]
  set Fr : AlgebraicClosure K →+* AlgebraicClosure K :=
    iterateFrobenius (AlgebraicClosure K) 2 f with hFrdef
  have hFr : ∀ c, Fr c = c ^ 2 ^ f := fun c => by rw [hFrdef, iterateFrobenius_def]
  have hBF : Matrix.SpecialLinearGroup.map Fr BL = BL := by
    have : Fintype k := Fintype.ofFinite k
    have hfix : ∀ a : k, Fr (algebraMap K (AlgebraicClosure K) (algebraMap k K a)) =
        algebraMap K (AlgebraicClosure K) (algebraMap k K a) := fun a => by
      rw [hFr, ← map_pow, ← map_pow, ← hk, Nat.card_eq_fintype_card, FiniteField.pow_card]
    rw [hBL]
    ext i j
    simp [hfix]
  have hB : PL⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))
      (Matrix.SpecialLinearGroup.map (algebraMap k K) (A ^ m)) * PL = HSL ζ := by
    have e : (PL⁻¹ * BL * PL⁻¹⁻¹) ^ m = PL⁻¹ * BL ^ m * PL⁻¹⁻¹ := conj_pow
    rw [inv_inv] at e
    rw [← hm, ← F4Pilot.HSL_pow, ← hPBL, e, hBL, map_pow, map_pow]
  let T : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    thetaSL2 (AlgebraicClosure K)
      (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))
        (Matrix.SpecialLinearGroup.map (algebraMap k K) (A ^ m)))
  have hHSL : thetaSL2 (AlgebraicClosure K) (HSL ζ) =
      rootDiagUnit TwistTag.E6.tag (EPilot.highDiag TwistTag.E6.tag ζ) := by
    have htag : EPilot.highDiag Tag.E6 ζ = EPilot.highDiag TwistTag.E6.tag ζ := by
      simp [TwistTag.tag]
    rw [← htag]
    exact thetaSL2_HSL ζ
  have hT : T = thetaSL2 (AlgebraicClosure K) PL *
      rootDiagUnit TwistTag.E6.tag (EPilot.highDiag TwistTag.E6.tag ζ) *
        (thetaSL2 (AlgebraicClosure K) PL)⁻¹ := by
    have h' : (thetaSL2 (AlgebraicClosure K) PL)⁻¹ * T *
        thetaSL2 (AlgebraicClosure K) PL =
        rootDiagUnit TwistTag.E6.tag (EPilot.highDiag TwistTag.E6.tag ζ) := by
      have h1 := congrArg (thetaSL2 (AlgebraicClosure K)) hB
      rw [hHSL] at h1
      simpa only [map_mul, map_inv] using h1
    rw [← h']
    group
  obtain ⟨w, hw⟩ := EPilot.exists_smul_eq_highRoot (τ := TwistTag.E6.tag) (Or.inl rfl) hγ
  let n : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w
  let dγ : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ)
  let dθ : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    rootDiagUnit TwistTag.E6.tag (EPilot.highDiag TwistTag.E6.tag ζ)
  have hθd : dθ = n * dγ * n⁻¹ :=
    (rootDiagUnit_eq_conj_canonicalRep_iff _ _ w).2 fun μ => by
      rw [EPilot.rootChar_highDiag, TwE6RootKill.rootChar_corootTuple,
        ← EPilot.iform_highRoot (τ := TwistTag.E6.tag) (Or.inl rfl) (w • μ), ← hw,
        iform_smul, CFSG.LieType.Steinberg.Adjoint.iform_comm]
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h
    refine hζ1 (Units.ext ?_)
    have hv : (ζ : AlgebraicClosure K) ^ 2 = (1 : AlgebraicClosure K) ^ 2 := by
      simpa using congrArg Units.val h
    exact CharTwo.sq_injective hv
  have hcent : graphCentralizer TwistTag.E6.tag (AlgebraicClosure K) dθ =
      torusGroup TwistTag.E6.tag (AlgebraicClosure K) ⊔
        rootSpan TwistTag.E6.tag (AlgebraicClosure K) (EPilot.perpRoots TwistTag.E6.tag) := by
    change toralCentralizer TwistTag.E6.tag (AlgebraicClosure K)
        (EPilot.highDiag TwistTag.E6.tag ζ) =
      torusGroup TwistTag.E6.tag (AlgebraicClosure K) ⊔
        rootSpan TwistTag.E6.tag (AlgebraicClosure K) (EPilot.perpRoots TwistTag.E6.tag)
    rw [EPilot.toralCentralizer_highDiag (τ := TwistTag.E6.tag) (Or.inl rfl) hζ1 hζ2]
  have hirr : IsPointIrreducible (AlgebraicClosure K)
      (transportPoints (modGLPoint TwistTag.E6.tag (AlgebraicClosure K))
        (graphCentralizer TwistTag.E6.tag (AlgebraicClosure K) dθ)) := by
    rw [hcent]
    exact isPointIrreducible_torusGroup_sup_rootSpan
      (S := EPilot.perpRoots TwistTag.E6.tag) fun α hα => (EPilot.mem_perpRoots_iff.mp hα).1
  have hk : thetaSL2 (AlgebraicClosure K) PL ∈
      adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    change rootSL2 TwistTag.E6.tag (AlgebraicClosure K) e6HighestRoot PL ∈ _
    exact rootSL2_mem_adjointGroup e6HighestRoot PL
  have hn : n ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    change canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w ∈ _
    exact canonicalRep_mem_adjointGroup _ (AlgebraicClosure K) w
  have hx : thetaSL2 (AlgebraicClosure K) PL * n * g0⁻¹ ∈
      adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    mul_mem (mul_mem hk hn) (inv_mem hg0C)
  have hQG : ∀ g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
      frobTwistGL TwistTag.E6.tag (AlgebraicClosure K) 2 f
        (diagramMap TwistTag.E6 (AlgebraicClosure K)) g ∈
        adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    intro g hg
    rw [frobTwistGL_apply]
    exact conj_mem_adjointGroup_of_map_eq
      (map_conj_diagramMap TwistTag.E6 (AlgebraicClosure K) (Or.inl rfl)) _
      (entrywiseFrobGL_mem 2 f hg)
  have hFA : frobTwistGL TwistTag.E6.tag (AlgebraicClosure K) 2 f
      (diagramMap TwistTag.E6 (AlgebraicClosure K)) T = T := by
    have h2L : (2 : AlgebraicClosure K) = 0 := by
      simpa using CharP.cast_eq_zero (AlgebraicClosure K) 2
    have h1 : Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))
        (Matrix.SpecialLinearGroup.map (algebraMap k K) (A ^ m)) = BL ^ m := by
      rw [map_pow, map_pow, ← hBL]
    have hmap : Matrix.SpecialLinearGroup.map Fr
        (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))
          (Matrix.SpecialLinearGroup.map (algebraMap k K) (A ^ m))) =
        Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))
          (Matrix.SpecialLinearGroup.map (algebraMap k K) (A ^ m)) := by
      rw [h1, map_pow, hBF]
    change twistHom TwistTag.E6 (AlgebraicClosure K) Fr T = T
    rw [E6GraphLevi.twistHom_thetaSL2 h2L, hmap]
  have hFs : frobTwistGL TwistTag.E6.tag (AlgebraicClosure K) 2 f
      (diagramMap TwistTag.E6 (AlgebraicClosure K))
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) t) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) t := by
    have hΓ : baseChangeGL (algebraMap K (AlgebraicClosure K)) t ∈
        twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr :=
      map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two hf hK σ hσ Fr hFr
        (Subgroup.mem_map_of_mem _ ht)
    exact ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 (AlgebraicClosure K) Fr).1 hΓ).2
  have hs : baseChangeGL (algebraMap K (AlgebraicClosure K)) t = g0 * dγ * g0⁻¹ := by
    change baseChangeGL (algebraMap K (AlgebraicClosure K)) t =
      g0 * rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ) * g0⁻¹
    rw [← hcor]
    group
  have hd : dγ = n⁻¹ * dθ * n := by
    rw [hθd]
    group
  have hxs : (thetaSL2 (AlgebraicClosure K) PL * n * g0⁻¹) *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) t *
      (thetaSL2 (AlgebraicClosure K) PL * n * g0⁻¹)⁻¹ = T := by
    rw [hs, hd, hT]
    rw [show dθ = rootDiagUnit TwistTag.E6.tag (EPilot.highDiag TwistTag.E6.tag ζ) from rfl]
    group
  obtain ⟨y, hyC, hyF, hy⟩ :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.exists_fixed_conj_of_lang
      (τ := TwistTag.E6.tag) (L := AlgebraicClosure K) 2 hf
      (diagramMap TwistTag.E6 (AlgebraicClosure K)) hQG hirr hk hT hFA hFs hx hxs
  obtain ⟨c, hcΓ, hc⟩ :=
    RecipeExcLang.exists_mem_twInndiag_of_twist_fixed hf hK hσ hFr hyC hyF
  refine ⟨c, NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL σ hcΓ, A, hA, m, hAm, ?_⟩
  have hR : baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (A ^ m)) = T :=
    baseChangeGL_rootSL2_of_charTwo _ isRoot_e6HighestRoot _
  apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
  rw [map_mul, map_mul, map_inv, hc, hy, hR]

theorem exists_conj_eq_thetaSL2_pow {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ f) {k : Type}
    [Field k] [Algebra k K] (hk : Nat.card k = 2 ^ f)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2 ^ f)
    (v : WeylGroup TwistTag.E6.tag)
    (hv : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    (t : ModGL TwistTag.E6.tag K) (_ht : t ∈ twistedE6InndiagGL K σ)
    (γ : Fin TwistTag.E6.tag.rank → ℤ) (hγ : IsRoot TwistTag.E6.tag γ) (p : ℕ) (_hp : p.Prime)
    (hpq : p ∣ 2 ^ f + 1) (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    (hcor : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) t * g0 =
      rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ)) :
    ∃ c ∈ twistedE6InndiagGL K σ, ∃ A : SL2 k, orderOf A = Nat.card k + 1 ∧ ∃ m : ℕ,
      A ^ m ≠ 1 ∧ c * t * c⁻¹ =
        (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (A ^ m) :=
  exists_conj_eq_thetaSL2_pow_of_coroot_conj σ hf hK hσ hk g0 hg0C t _ht γ hγ p _hp hpq ζ
    hζ hζ1 hcor

end CFSG.StandardType.TwE6CorootCore

end

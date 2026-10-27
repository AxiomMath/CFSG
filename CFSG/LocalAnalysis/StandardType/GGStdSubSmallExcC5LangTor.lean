module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5LangElt
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5Frame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTorus
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLang

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus TableBExc TableBExcTwo TableBExcTwoFusion
  TableBExcTwoTB

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Omega

variable {K : Type} [Field K] [CharP K 2] {ω : (AlgebraicClosure K)ˣ}

theorem omega_cube (hω : (ω : AlgebraicClosure K) ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact pow_three_of_sq_add hω)

theorem omega_orderOf (hω : (ω : AlgebraicClosure K) ^ 2 + ω + 1 = 0) : orderOf ω = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (omega_cube hω) fun h => ?_
  have h1 : (1 : AlgebraicClosure K) ^ 2 + 1 + 1 = 0 := by simpa [h] using hω
  have h2 : (2 : AlgebraicClosure K) = 0 := CharTwo.two_eq_zero
  exact one_ne_zero (by linear_combination h1 - h2)

end Omega

section Torus

variable
  {τ : Tag} {d : ℕ} {K : Type} [Field K] [CharP K 2]
  {ω : (AlgebraicClosure K)ˣ}

theorem langG_conj_rho_HSL (F : OrthFrame τ d)
    (hω : (ω : AlgebraicClosure K) ^ 2 + ω + 1 = 0) (i : Fin (d + 1)) :
    langG F hω * rho (AlgebraicClosure K) F i (HSL ω) * (langG F hω)⁻¹ =
      adjointMap τ (algebraMap K (AlgebraicClosure K)) (tGen K F i) := by
  have hP : langP hω * HSL ω * (langP hω)⁻¹ = uSL 1 * vSL 1 := by
    rw [langP_mul_HSL, mul_inv_cancel_right]
  rw [langG, ExcFrameIso.frameProd_conj_rho, hP, tGen, adjointMap_rho, map_uSL_mul_vSL]

@[expose] noncomputable def langEmb (F : OrthFrame τ d)
    (hω : (ω : AlgebraicClosure K) ^ 2 + ω + 1 = 0) :
    adjointGroup τ K →* ModGL τ (AlgebraicClosure K) :=
  (MulAut.conj (langG F hω : ModGL τ (AlgebraicClosure K))⁻¹).toMonoidHom.comp
    ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup τ K).subtype)

theorem langEmb_apply (F : OrthFrame τ d) (hω : (ω : AlgebraicClosure K) ^ 2 + ω + 1 = 0)
    (x : adjointGroup τ K) :
    langEmb F hω x = (langG F hω : ModGL τ (AlgebraicClosure K))⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
        (langG F hω : ModGL τ (AlgebraicClosure K)) := by
  change (MulAut.conj (langG F hω : ModGL τ (AlgebraicClosure K))⁻¹) _ = _
  rw [MulAut.conj_apply, inv_inv]
  rfl

theorem langEmb_injective (F : OrthFrame τ d) (hω : (ω : AlgebraicClosure K) ^ 2 + ω + 1 = 0) :
    Function.Injective (langEmb F hω) :=
  (MulAut.conj _).injective.comp
    ((baseChangeGL_injective _).comp (Subgroup.subtype_injective _))

theorem langEmb_tGen (F : OrthFrame τ d) (hω : (ω : AlgebraicClosure K) ^ 2 + ω + 1 = 0)
    (i : Fin (d + 1)) :
    langEmb F hω (tGen K F i) =
      ((rho (AlgebraicClosure K) F i (HSL ω) : adjointGroup τ (AlgebraicClosure K)) :
        ModGL τ (AlgebraicClosure K)) := by
  have h := congrArg Subtype.val (langG_conj_rho_HSL F hω i)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_adjointMap] at h
  rw [langEmb_apply, ← h]
  group

theorem Hel_nsmul {L : Type} [Field L] (x : Fin τ.rank → ℤ) (u : Lˣ) (n : ℕ) :
    Hel (L := L) (τ := τ) (n • x) u = Hel x u ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, Hel_zero]
  | succ n ih => rw [succ_nsmul, Hel_add, ih, pow_succ]

theorem frameLift_single (F : OrthFrame τ d) (i : Fin (d + 1)) (c : ZMod 3) :
    frameLift F (Pi.single i c) = c.val • F.root i := by
  rw [frameLift, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

@[expose] def dualVec (F : OrthFrame τ d) (v : Fin (d + 1) → ZMod 3) : Fin τ.rank → ZMod 3 :=
  fun k => v ⬝ᵥ frameDual F (Pi.single k 1)

theorem Hchar_frameLift (F : OrthFrame τ d) (hω : (ω : AlgebraicClosure K) ^ 2 + ω + 1 = 0)
    (v : Fin (d + 1) → ZMod 3) :
    Hchar (frameLift F v) ω = E6Three.zetaVec ω (omega_cube hω) (dualVec F v) := by
  funext k
  rw [E6Three.zetaVec_apply, dualVec, ← iform_frameLift,
    pow_val_intCast_eq_zpow (omega_orderOf hω)]
  rfl

@[expose] noncomputable def frameTorusHom (F : OrthFrame τ d)
    (hω : (ω : AlgebraicClosure K) ^ 2 + ω + 1 = 0) :
    Multiplicative (Fin (d + 1) → ZMod 3) →* ModGL τ (AlgebraicClosure K) where
  toFun v := rootDiagUnit τ (E6Three.zetaVec ω (omega_cube hω) (dualVec F (Multiplicative.toAdd v)))
  map_one' := by
    have : dualVec F 0 = 0 := funext fun k => by simp [dualVec]
    rw [toAdd_one, this]
    convert rootDiagUnit_one (τ := τ) (K := AlgebraicClosure K)
    funext k
    simp [E6Three.zetaVec_apply]
  map_mul' a b := by
    have : dualVec F (Multiplicative.toAdd a + Multiplicative.toAdd b) =
        dualVec F (Multiplicative.toAdd a) + dualVec F (Multiplicative.toAdd b) :=
      funext fun k => by simp [dualVec, add_dotProduct]
    rw [toAdd_mul, this, ExcFrames.zetaVec_add, rootDiagUnit_mul]

theorem frameTorusHom_apply (F : OrthFrame τ d)
    (hω : (ω : AlgebraicClosure K) ^ 2 + ω + 1 = 0) (v : Fin (d + 1) → ZMod 3) :
    frameTorusHom F hω (Multiplicative.ofAdd v) = Hel (frameLift F v) ω := by
  change rootDiagUnit τ (E6Three.zetaVec ω (omega_cube hω) (dualVec F v)) = _
  rw [Hel, Hchar_frameLift F hω]

theorem langEmb_tE (hτ : τ = .E7 ∨ τ = .E8) (F : OrthFrame τ d)
    (hω : (ω : AlgebraicClosure K) ^ 2 + ω + 1 = 0) (v : Fin (d + 1) → ZMod 3) :
    langEmb F hω (tE K F (Multiplicative.ofAdd v)) = Hel (frameLift F v) ω := by
  classical
  have hsl : SimplyLacedTag τ := by rcases hτ with rfl | rfl <;> simp [SimplyLacedTag]
  have key : (langEmb F hω).comp (tD K F) = (frameTorusHom F hω).comp
      (MulEquiv.piMultiplicative fun _ : Fin (d + 1) => ZMod 3).symm.toMonoidHom := by
    refine MonoidHom.pi_ext fun i a => ?_
    have hL1 : tD K F (Pi.mulSingle i a) = tGen K F i ^ (Multiplicative.toAdd a).val := by
      rw [tD, MonoidHom.noncommPiCoprod_mulSingle, tC_apply]
    have hR1 : (MulEquiv.piMultiplicative fun _ : Fin (d + 1) => ZMod 3).symm
        (Pi.mulSingle i a) =
        Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd a) : Fin (d + 1) → ZMod 3) := by
      refine Multiplicative.toAdd.injective ?_
      funext j
      simp only [MulEquiv.piMultiplicative_symm_apply, toAdd_ofAdd, Pi.mulSingle_apply,
        Pi.single_apply]
      split_ifs <;> rfl
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hL1, hR1, map_pow]
    rw [langEmb_tGen, frameTorusHom_apply, frameLift_single, Hel_nsmul,
      Hel_root_eq_rootSL2 hsl (F.isRoot i)]
    rfl
  have h := congrArg (fun f => f (fun j => Multiplicative.ofAdd (v j))) key
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
  rw [tE_apply, h]
  exact frameTorusHom_apply F hω v

theorem Hel_frameLift_neg_dual {F : OrthFrame τ d} (hF : FrameParseval F)
    (hω : (ω : AlgebraicClosure K) ^ 2 + ω + 1 = 0) (γ : Fin τ.rank → ℤ) :
    Hel (frameLift F (-frameDual F γ)) ω = Hel γ ω := by
  unfold Hel
  congr 1
  funext l
  simp only [Hchar]
  rw [← pow_val_intCast_eq_zpow (omega_orderOf hω), ← pow_val_intCast_eq_zpow (omega_orderOf hω),
    iform_frameLift_neg_dual hF γ l]

end Torus

end CFSG.StandardType.SmallExc

end

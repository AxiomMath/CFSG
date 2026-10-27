module

public import CFSG.LocalAnalysis.StandardType.GGTwE6FrameFixPpdLang
public import CFSG.LocalAnalysis.StandardType.GGTwE6FrameFixPpdWeyl
public import CFSG.LocalAnalysis.StandardType.GGTwE6FrameCard
public import CFSG.LocalAnalysis.StandardType.GGTwE6LangRetype
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Torus
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagTwE6Glue
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Core
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Torus
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.AlgebraicGroups.ToralCentralizerIdentity
public import CFSG.LieType.Chevalley.SignKernelPositiveRepresentatives
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.RankThree.GF2n.Stroth80.Sec3Zsig
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL46
public import CFSG.Mathlib.RingTheory.UnitOrderOf
public import CFSG.CGT.Timmesfeld75.Forms
public import CFSG.RankThree.GF2n.Stroth80.Anisotropic
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec36
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.HardMathSupport.Lang.E6Descent

open CFSG.HardMathSupport.Timmesfeld.Torality CFSG.RankThree.Classical2
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley

private theorem kernelReflectionGroup_eq_closure_familyKernel
    {K : Type} [Field K] (a : Fin Tag.E6.rank → Kˣ) :
    CFSG.LieType.Chevalley.kernelReflectionGroup a =
      Subgroup.closure {s : WeylGroup Tag.E6 |
        ∃ α ∈ familyKernel (fun _ : Unit => a), s = rootReflection α} := by
  rw [CFSG.LieType.AlgebraicGroups.kernelReflectionGroup_eq_kernelWeylGroup_rootCharHom,
    CFSG.LieType.Chevalley.kernelWeylGroup_eq_closure]
  congr 1
  ext s
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨α, ⟨hα.1, fun _ => hα.2⟩, rfl⟩
  · rintro ⟨α, hα, rfl⟩
    exact ⟨α, ⟨hα.1, hα.2 ()⟩, rfl⟩

private theorem canonicalRep_conj_twist_rootDiagUnit
    {Ω : Type} [Field Ω] (Fr : Ω →+* Ω) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {w : WeylGroup Tag.E6} {c : Fin Tag.E6.rank → Ωˣ}
    (hc : weylAct w (c ^ (-(q : ℤ))) = c) :
    canonicalRep (coxeterSystem Tag.E6) Ω (w * twE6W0) *
        twistE6 Ω Fr (rootDiagUnit Tag.E6 c) *
        (canonicalRep (coxeterSystem Tag.E6) Ω (w * twE6W0))⁻¹ =
      rootDiagUnit Tag.E6 c := by
  have hFd : twistE6 Ω Fr (rootDiagUnit Tag.E6 c) =
      (TwistedDiag.n0 Ω)⁻¹ * rootDiagUnit Tag.E6 ((c ^ q)⁻¹) * TwistedDiag.n0 Ω := by
    have h := TwistedDiag.theta_rootDiagUnit (q := q) Fr hFr c
    rw [TwistedDiag.theta_apply] at h
    calc twistE6 Ω Fr (rootDiagUnit Tag.E6 c)
        = (TwistedDiag.n0 Ω)⁻¹ * ((TwistedDiag.n0 Ω) *
            twistE6 Ω Fr (rootDiagUnit Tag.E6 c) * (TwistedDiag.n0 Ω)⁻¹) *
            TwistedDiag.n0 Ω := by group
      _ = (TwistedDiag.n0 Ω)⁻¹ * rootDiagUnit Tag.E6 ((c ^ q)⁻¹) * TwistedDiag.n0 Ω := by
            rw [h]
  obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (R := Ω) w twE6W0
  have hnv : canonicalRep (coxeterSystem Tag.E6) Ω (w * twE6W0) =
      k⁻¹ * canonicalRep (coxeterSystem Tag.E6) Ω w * TwistedDiag.n0 Ω := by
    calc canonicalRep (coxeterSystem Tag.E6) Ω (w * twE6W0)
        = k⁻¹ * (k * canonicalRep (coxeterSystem Tag.E6) Ω (w * twE6W0)) := by group
      _ = k⁻¹ * (canonicalRep (coxeterSystem Tag.E6) Ω w * TwistedDiag.n0 Ω) := by
          rw [← hkk]
          rfl
      _ = k⁻¹ * canonicalRep (coxeterSystem Tag.E6) Ω w * TwistedDiag.n0 Ω := by group
  have hkcomm : ∀ t : Fin Tag.E6.rank → Ωˣ,
      k⁻¹ * rootDiagUnit Tag.E6 t * k = rootDiagUnit Tag.E6 t := by
    intro t
    calc k⁻¹ * rootDiagUnit Tag.E6 t * k
        = k⁻¹ * (rootDiagUnit Tag.E6 t * k) := by group
      _ = k⁻¹ * (k * rootDiagUnit Tag.E6 t) := by
          rw [rootDiagUnit_mul_comm_of_mem_torusGroup t hk]
      _ = rootDiagUnit Tag.E6 t := by group
  calc canonicalRep (coxeterSystem Tag.E6) Ω (w * twE6W0) *
        twistE6 Ω Fr (rootDiagUnit Tag.E6 c) *
        (canonicalRep (coxeterSystem Tag.E6) Ω (w * twE6W0))⁻¹
      = (canonicalRep (coxeterSystem Tag.E6) Ω (w * twE6W0) * (TwistedDiag.n0 Ω)⁻¹) *
          rootDiagUnit Tag.E6 ((c ^ q)⁻¹) *
          (TwistedDiag.n0 Ω * (canonicalRep (coxeterSystem Tag.E6) Ω (w * twE6W0))⁻¹) := by
        rw [hFd]
        group
    _ = (k⁻¹ * canonicalRep (coxeterSystem Tag.E6) Ω w) *
          rootDiagUnit Tag.E6 ((c ^ q)⁻¹) *
          ((canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ * k) := by
        rw [hnv]
        group
    _ = k⁻¹ * (canonicalRep (coxeterSystem Tag.E6) Ω w *
          rootDiagUnit Tag.E6 ((c ^ q)⁻¹) *
          (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹) * k := by group
    _ = k⁻¹ * rootDiagUnit Tag.E6
          (weylAct w ((c ^ q)⁻¹)) * k := by
        rw [HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit w _]
    _ = rootDiagUnit Tag.E6 (weylAct w ((c ^ q)⁻¹)) := hkcomm _
    _ = rootDiagUnit Tag.E6 c := by
        have hqinv : (c ^ q)⁻¹ = c ^ (-(q : ℤ)) := by
          funext i
          simp only [Pi.inv_apply, Pi.pow_apply]
          rw [zpow_neg, zpow_natCast]
        rw [hqinv, hc]

private theorem mem_Rgrp_conj_rootDiagUnit
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (Fr : Ω →+* Ω) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {y : ModGL Tag.E6 Ω} (hy : y ∈ adjointGroup Tag.E6 Ω) {w : WeylGroup Tag.E6}
    (hwy : y⁻¹ * twistE6 Ω Fr y =
      canonicalRep (coxeterSystem Tag.E6) Ω (w * twE6W0))
    {c : Fin Tag.E6.rank → Ωˣ} (hc : weylAct w (c ^ (-(q : ℤ))) = c) :
    y * rootDiagUnit Tag.E6 c * y⁻¹ ∈ TwistedDiag.Rgrp Ω Fr := by
  have hdT : rootDiagUnit Tag.E6 c ∈ torusGroup Tag.E6 Ω :=
    rootDiagUnit_mem_torusGroup c
  have hdG : rootDiagUnit Tag.E6 c ∈ adjointGroup Tag.E6 Ω :=
    CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup' hdT
  rw [TwistedDiag.mem_Rgrp]
  constructor
  · exact mul_mem (mul_mem hy hdG) (inv_mem hy)
  · have hFy : twistE6 Ω Fr y = y * canonicalRep (coxeterSystem Tag.E6) Ω (w * twE6W0) := by
      calc twistE6 Ω Fr y = y * (y⁻¹ * twistE6 Ω Fr y) := by group
        _ = y * canonicalRep (coxeterSystem Tag.E6) Ω (w * twE6W0) := by rw [hwy]
    have hkey := canonicalRep_conj_twist_rootDiagUnit (q := q) Fr hFr hc
    calc twistE6 Ω Fr (y * rootDiagUnit Tag.E6 c * y⁻¹)
        = twistE6 Ω Fr y * twistE6 Ω Fr (rootDiagUnit Tag.E6 c) * (twistE6 Ω Fr y)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
      _ = y * (canonicalRep (coxeterSystem Tag.E6) Ω (w * twE6W0) *
            twistE6 Ω Fr (rootDiagUnit Tag.E6 c) *
            (canonicalRep (coxeterSystem Tag.E6) Ω (w * twE6W0))⁻¹) * y⁻¹ := by
            rw [hFy]
            group
      _ = y * rootDiagUnit Tag.E6 c * y⁻¹ := by rw [hkey]

private theorem ne_three_of_orderOf_pow_two {f r e : ℕ}
    (he : e = 12 ∨ e = 18)
    (hord : orderOf ((2 ^ f : ℕ) : ZMod r) = e) : r ≠ 3 := by
  rintro rfl
  rw [Nat.cast_pow] at hord
  have h2o : orderOf (2 : ZMod 3) = 2 := by
    refine orderOf_eq_prime ?_ ?_ <;> decide
  have hdvd : orderOf ((2 : ZMod 3) ^ f) ∣ orderOf (2 : ZMod 3) := orderOf_pow_dvd f
  rw [h2o] at hdvd
  have hle : e ≤ 2 := Nat.le_of_dvd (by norm_num) (hord ▸ hdvd)
  rcases he with rfl | rfl <;> omega

private theorem exists_retyped_lang
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2] [Fact (Nat.Prime 2)]
    {f : ℕ} (hf : 1 ≤ f)
    {y : ModGL Tag.E6 Ω} (hy : y ∈ adjointGroup Tag.E6 Ω)
    {a : Fin Tag.E6.rank → Ωˣ} {u v : WeylGroup Tag.E6}
    (hyn : y⁻¹ * twistE6 Ω (iterateFrobenius Ω 2 f) y =
      canonicalRep (coxeterSystem Tag.E6) Ω (u * twE6W0))
    {q : ℕ} (hq : q = 2 ^ f) (huqz : weylAct u (a ^ (-(q : ℤ))) = a)
    (hv : v * (u * twE6W0)⁻¹ ∈ CFSG.LieType.Chevalley.kernelReflectionGroup a) :
    ∃ y' ∈ adjointGroup Tag.E6 Ω,
      y'⁻¹ * twistE6 Ω (iterateFrobenius Ω 2 f) y' =
        canonicalRep (coxeterSystem Tag.E6) Ω v ∧
      y' * rootDiagUnit Tag.E6 a * y'⁻¹ = y * rootDiagUnit Tag.E6 a * y⁻¹ := by
  classical
  have hFrq : ∀ c, iterateFrobenius Ω 2 f c = c ^ q := by
    intro c
    rw [iterateFrobenius_def, hq]
  let yT : ModGL TwistTag.E6.tag Ω := y
  have hF : twistHom TwistTag.E6 Ω (iterateFrobenius Ω 2 f) yT =
      yT * canonicalRep (coxeterSystem TwistTag.E6.tag) Ω (u * twE6W0) := by
    change twistE6 Ω (iterateFrobenius Ω 2 f) y =
      y * canonicalRep (coxeterSystem Tag.E6) Ω (u * twE6W0)
    calc twistE6 Ω (iterateFrobenius Ω 2 f) y =
        y * (y⁻¹ * twistE6 Ω (iterateFrobenius Ω 2 f) y) := by group
      _ = y * canonicalRep (coxeterSystem Tag.E6) Ω (u * twE6W0) := by rw [hyn]
  have hfix : ∀ s' : Unit,
      canonicalRep (coxeterSystem TwistTag.E6.tag) Ω (u * twE6W0) *
      twistHom TwistTag.E6 Ω (iterateFrobenius Ω 2 f)
        (rootDiagUnit TwistTag.E6.tag ((fun _ : Unit => a) s')) *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) Ω (u * twE6W0))⁻¹ =
        rootDiagUnit TwistTag.E6.tag ((fun _ : Unit => a) s') := by
    intro s'
    change canonicalRep (coxeterSystem Tag.E6) Ω (u * twE6W0) *
      twistE6 Ω (iterateFrobenius Ω 2 f)
        (rootDiagUnit Tag.E6 ((fun _ : Unit => a) s')) *
      (canonicalRep (coxeterSystem Tag.E6) Ω (u * twE6W0))⁻¹ =
        rootDiagUnit Tag.E6 ((fun _ : Unit => a) s')
    exact canonicalRep_conj_twist_rootDiagUnit (q := q)
      (iterateFrobenius Ω 2 f) hFrq huqz
  have hker := kernelReflectionGroup_eq_closure_familyKernel (K := Ω) a
  have hw : v * (u * twE6W0)⁻¹ ∈
      Subgroup.closure {s : WeylGroup Tag.E6 |
        ∃ α ∈ familyKernel (fun _ : Unit => a), s = rootReflection α} := hker ▸ hv
  obtain ⟨z, hz, hzy⟩ :=
    CFSG.StandardType.LangRetype.exists_lang_retype_twisted (L := Ω) (ℓ := 2)
      (t := TwistTag.E6) (f := f) hf (fun _ : Unit => a) hF hfix hw
  let zE : ModGL Tag.E6 Ω := z
  have hzE : zE ∈ familyGroup (K := Ω) (fun _ : Unit => a) := hz
  have hzyE : (y * zE)⁻¹ * twistE6 Ω (iterateFrobenius Ω 2 f) (y * zE) =
      canonicalRep (coxeterSystem Tag.E6) Ω v := hzy
  have hzC : zE ∈ CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer Tag.E6 Ω
      (fun _ : Unit => a) :=
    CFSG.HardMathSupport.Timmesfeld.Torality.familyGroup_le_familyCentralizer
      (K := Ω) (a := fun _ : Unit => a) hzE
  have hzG : zE ∈ adjointGroup Tag.E6 Ω :=
    (CFSG.HardMathSupport.Timmesfeld.Torality.mem_familyCentralizer.1 hzC).1
  have hzcomm : rootDiagUnit Tag.E6 a * zE * (rootDiagUnit Tag.E6 a)⁻¹ = zE :=
    (CFSG.HardMathSupport.Timmesfeld.Torality.mem_familyCentralizer.1 hzC).2 ()
  have hzd : zE * rootDiagUnit Tag.E6 a * zE⁻¹ = rootDiagUnit Tag.E6 a := by
    have hdz : rootDiagUnit Tag.E6 a * zE = zE * rootDiagUnit Tag.E6 a := by
      calc rootDiagUnit Tag.E6 a * zE =
          (rootDiagUnit Tag.E6 a * zE * (rootDiagUnit Tag.E6 a)⁻¹) *
            rootDiagUnit Tag.E6 a := by group
        _ = zE * rootDiagUnit Tag.E6 a := by rw [hzcomm]
    calc zE * rootDiagUnit Tag.E6 a * zE⁻¹ =
        (zE * rootDiagUnit Tag.E6 a) * zE⁻¹ := rfl
      _ = (rootDiagUnit Tag.E6 a * zE) * zE⁻¹ := by rw [← hdz]
      _ = rootDiagUnit Tag.E6 a := by group
  refine ⟨y * zE, mul_mem hy hzG, hzyE, ?_⟩
  calc (y * zE) * rootDiagUnit Tag.E6 a * (y * zE)⁻¹ =
      y * (zE * rootDiagUnit Tag.E6 a * zE⁻¹) * y⁻¹ := by group
    _ = y * rootDiagUnit Tag.E6 a * y⁻¹ := by rw [hzd]

theorem ggTwE6FrameFixPpdInput_holds :
    GGTwE6FrameFixPpdInput := by
  intro f hf h3 M' S hInn hSM hSI hSel hmax α hαM hαI hα3 hαS
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 (2 * f)
  let σ : K ≃+* K := frobQEquiv hf
  have hK : Nat.card K = (2 ^ f) ^ 2 := by
    change Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, σ c = c ^ 2 ^ f := fun c => frobQ_apply 2 f c
  let Ω := AlgebraicClosure K
  let Fr : Ω →+* Ω := iterateFrobenius Ω 2 f
  have hFr : ∀ c, Fr c = c ^ 2 ^ f := fun c => iterateFrobenius_def 2 f c
  let q := 2 ^ f
  have hFrq : ∀ c, Fr c = c ^ q := hFr
  haveI : CharP K 2 := charP_two_of_card (m := f * 2) (by rw [hK, pow_mul])
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have halg : letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.isAlgebraic_zmod_algebraicClosure_of_finite K 2
  let Cσ := ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
  let M'σ : Subgroup (MulAut Cσ) := M'
  let Sσ : Subgroup (MulAut Cσ) := S
  let ασ : MulAut Cσ := α
  have hInnσ : (MulAut.conj : Cσ →* MulAut Cσ).range ≤ M'σ := hInn
  have hSMσ : Sσ ≤ M'σ := hSM
  have hSIσ : Sσ ≤ LayerSixE.twInndiagAut f := hSI
  have hSelσ : IsElemAbelian 3 Sσ := hSel
  have hmaxσ : ∀ X : Subgroup (MulAut Cσ), X ≤ M'σ → IsElemAbelian 3 X →
      Nat.card X ≤ Nat.card Sσ := hmax
  have hαMσ : ασ ∈ M'σ := hαM
  have hαIσ : ασ ∈ LayerSixE.twInndiagAut f := hαI
  have hα3σ : ασ ^ 3 = 1 := hα3
  have hαSσ : ∀ m ∈ M'σ, m⁻¹ * ασ * m ∉ Sσ := hαS
  have hSI' : Sσ ≤ (RecipeExcLang.twConj K σ).range := by
    rw [← twInndiagAut_eq_range_twConj hf]
    exact hSIσ
  have hαrange : ασ ∈ (NoOffTwE6Three.rgrpConjAut hf hK σ hσ Fr hFr).range := by
    rw [NoOffTwE6Three.rgrpConjAut_range hf hK σ hσ Fr hFr]
    rw [← twInndiagAut_eq_range_twConj hf]
    exact hαIσ
  obtain ⟨s, hsα⟩ := hαrange
  have hs3 : (s : ModGL Tag.E6 Ω) ^ 3 = 1 := by
    have h : (NoOffTwE6Three.rgrpConjAut hf hK σ hσ Fr hFr) (s ^ 3) =
        (NoOffTwE6Three.rgrpConjAut hf hK σ hσ Fr hFr) 1 := by
      rw [map_pow, map_one, hsα, hα3σ]
    have h' := NoOffTwE6Three.rgrpConjAut_injective hf hK σ hσ Fr hFr h
    exact congrArg Subtype.val h'
  have h5 : 3 ^ 5 ≤ Nat.card Sσ :=
    TwE6FrameCard.three_pow_five_le_card_of_maximal h3 hInnσ hmaxσ
  obtain ⟨g₁, hg₁, hgn₁, hSle⟩ :=
    TwE6DD2.exists_cubeTorus_lang hf hK σ hσ h3 Fr hFr hSelσ hSI' h5
  obtain ⟨y, hyG, a, u, ha3, huq, hs_eq, hyn⟩ :=
    TwE6FrameFixPpd.exists_lang_datum_of_pow_three (Ω := Ω) halg hf Fr hFr s.2 hs3
  have hpow : a ^ (2 ^ f) = a⁻¹ := by
    obtain ⟨k, hk⟩ := h3
    funext i
    have hi : a i ^ 3 = 1 := ha3 i
    have hik : a i ^ (2 ^ f + 1) = 1 := by
      rw [hk, pow_mul, hi, one_pow]
    rw [pow_succ] at hik
    show a i ^ (2 ^ f) = (a i)⁻¹
    exact eq_inv_of_mul_eq_one_left hik
  have hua : weylAct u a = a := by
    have h := huq
    rw [hpow, inv_inv] at h
    exact h
  have hker := kernelReflectionGroup_eq_closure_familyKernel (K := Ω) a
  have hqinv : (a ^ q)⁻¹ = a ^ (-(q : ℤ)) := by
    funext i
    simp only [Pi.inv_apply, Pi.pow_apply]
    rw [zpow_neg, zpow_natCast]
  have huqz : weylAct u (a ^ (-(q : ℤ))) = a := by
    rw [← hqinv]
    exact huq
  by_cases hu : u ∈ CFSG.LieType.Chevalley.kernelReflectionGroup a
  ·
    have hvI : twE6W0 * (u * twE6W0)⁻¹ ∈
        CFSG.LieType.Chevalley.kernelReflectionGroup a := by
      have h : twE6W0 * (u * twE6W0)⁻¹ = u⁻¹ := by
        rw [mul_inv_rev]
        group
      rw [h]
      exact Subgroup.inv_mem _ hu
    obtain ⟨y₂, hy₂G, hy₂n, hy₂conj⟩ :=
      exists_retyped_lang (Ω := Ω) hf (hq := rfl) (huqz := huqz) (hv := hvI) hyG hyn
    have hzy₂ : y₂⁻¹ * twistE6 Ω Fr y₂ = TwistedDiag.n0 Ω := hy₂n
    have hs_eq₂ : s = y₂ * rootDiagUnit Tag.E6 a * y₂⁻¹ := by
      rw [hs_eq, ← hy₂conj]
    have hxR : y₂ * rootDiagUnit Tag.E6 a * y₂⁻¹ ∈ TwistedDiag.Rgrp Ω Fr :=
      TwE6DD2.conj_cubeTorus_le_Rgrp Fr hFr h3 hy₂G hzy₂
        (Subgroup.mem_map_of_mem (MulAut.conj y₂).toMonoidHom
          (TwE6DD2.rootDiagUnit_mem_cubeTorus ha3))
    have hαlc : ασ ∈ TwE6DD2.langCube hf hK σ hσ Fr hFr y₂ := by
      have hmem : (NoOffTwE6Three.rgrpConjAut hf hK σ hσ Fr hFr)
          ⟨y₂ * rootDiagUnit Tag.E6 a * y₂⁻¹, hxR⟩ ∈
          TwE6DD2.langCube hf hK σ hσ Fr hFr y₂ :=
        (TwE6DD2.mem_langCube hf hK σ hσ Fr hFr).2 ⟨a, ha3, hxR, rfl⟩
      rw [show (⟨y₂ * rootDiagUnit Tag.E6 a * y₂⁻¹, hxR⟩ :
          ↥(TwistedDiag.Rgrp Ω Fr)) = s from Subtype.ext hs_eq₂.symm, hsα] at hmem
      exact hmem
    obtain ⟨β, hβInn, hβlc⟩ :=
      TwE6FrameFixPpd.exists_inn_conj_langCube (n := f) hf hK σ hσ h3 Fr hFr
        hy₂G hzy₂ hg₁ hgn₁
    have hβM : β ∈ M'σ := hInnσ hβInn
    have hβα : β * ασ * β⁻¹ ∈ TwE6DD2.langCube hf hK σ hσ Fr hFr g₁ := by
      rw [← hβlc]
      exact Subgroup.mem_map_of_mem (MulAut.conj β).toMonoidHom hαlc
    let X : Subgroup (MulAut Cσ) :=
      TwE6DD2.langCube hf hK σ hσ Fr hFr g₁ ⊓ M'σ
    have hXel : IsElemAbelian 3 X :=
      (TwE6DD2.isElemAbelian_langCube hf hK σ hσ Fr hFr g₁).mono inf_le_left
    have hXle : X ≤ M'σ := inf_le_right
    have hSX : Sσ ≤ X := le_inf hSle hSMσ
    have hmaxX : Nat.card X ≤ Nat.card Sσ := hmaxσ X hXle hXel
    have hSXeq : Sσ = X := Subgroup.eq_of_le_of_card_ge hSX hmaxX
    have hmemX : β * ασ * β⁻¹ ∈ X :=
      ⟨hβα, mul_mem (mul_mem hβM hαMσ) (Subgroup.inv_mem M'σ hβM)⟩
    have hmemS : β * ασ * β⁻¹ ∈ Sσ := by
      rw [hSXeq]
      exact hmemX
    exact (hαSσ β⁻¹ (Subgroup.inv_mem M'σ hβM) hmemS).elim
  ·
    obtain ⟨e, he, hE3⟩ :=
      TwE6FrameFixPpd.exists_weylAct_eq_of_not_mem_kernelReflectionGroup (K := Ω) ha3 hua hu
    have he' : e = 12 ∨ e = 18 := by
      simpa [ggOutdiagExpsTwE6] using he
    have he2 : 2 ≤ e * f := by rcases he' with rfl | rfl <;> omega
    have he6 : e * f ≠ 6 := by rcases he' with rfl | rfl <;> omega
    obtain ⟨r, hr, hr2, hord⟩ :=
      CFSG.RankThree.GF2n.Stroth80.exists_prime_orderOf_two_eq (e := e * f) he2 he6
    have hordq : orderOf ((2 ^ f : ℕ) : ZMod r) = e := by
      have h := orderOf_pow_of_dvd (x := (2 : ZMod r)) (n := f) (by omega)
        (by rw [hord]; exact dvd_mul_left f e)
      rw [hord, Nat.mul_div_left e (by omega)] at h
      simpa using h
    have hrΩ : (r : Ω) ≠ 0 := by
      intro h
      rw [CharP.cast_eq_zero_iff Ω 2 r] at h
      exact hr2 (Nat.prime_dvd_prime_iff_eq Nat.prime_two hr |>.mp h).symm
    obtain ⟨ζ, hζo⟩ := CFSG.exists_unit_orderOf_eq_of_isAlgClosed (k := Ω) (n := r) hrΩ
    obtain ⟨u', hu'ker, c, hcr, hcne, hcact⟩ := hE3 r (2 ^ f) hr hordq ζ hζo
    have hcact' : weylAct u' (c ^ (-(q : ℤ))) = c := hcact
    have hvII : (u' * twE6W0) * (u * twE6W0)⁻¹ ∈
        CFSG.LieType.Chevalley.kernelReflectionGroup a := by
      have h : (u' * twE6W0) * (u * twE6W0)⁻¹ = u' * u⁻¹ := by
        rw [mul_inv_rev]
        group
      rw [h]
      exact hu'ker
    obtain ⟨y₃, hy₃G, hy₃n, hy₃conj⟩ :=
      exists_retyped_lang (Ω := Ω) hf (hq := rfl) (huqz := huqz) (hv := hvII) hyG hyn
    have hs_eq₃ : s = y₃ * rootDiagUnit Tag.E6 a * y₃⁻¹ := by
      rw [hs_eq, ← hy₃conj]
    let x : ModGL Tag.E6 Ω := y₃ * rootDiagUnit Tag.E6 c * y₃⁻¹
    have hxR : x ∈ TwistedDiag.Rgrp Ω Fr :=
      mem_Rgrp_conj_rootDiagUnit Fr hFrq hy₃G hy₃n hcact'
    haveI : Fact r.Prime := ⟨hr⟩
    have hcord : orderOf c = r := by
      refine orderOf_eq_prime ?_ hcne
      funext i
      exact hcr i
    have hdcord : orderOf (rootDiagUnit Tag.E6 c) = r := by
      have h := orderOf_injective (rootDiagUnitHom Tag.E6 Ω) rootDiagUnit_injective c
      rw [hcord] at h
      change orderOf ((rootDiagUnitHom Tag.E6 Ω) c) = r
      exact h
    have hxord : orderOf x = r := by
      change orderOf (y₃ * rootDiagUnit Tag.E6 c * y₃⁻¹) = r
      rw [show orderOf (y₃ * rootDiagUnit Tag.E6 c * y₃⁻¹) =
          orderOf (rootDiagUnit Tag.E6 c) from
        (SemiconjBy.orderOf_eq y₃ (x := rootDiagUnit Tag.E6 c)
          (y := y₃ * rootDiagUnit Tag.E6 c * y₃⁻¹)
          (by unfold SemiconjBy; group)).symm, hdcord]
    have hcd : rootDiagUnit Tag.E6 c * rootDiagUnit Tag.E6 a =
        rootDiagUnit Tag.E6 a * rootDiagUnit Tag.E6 c := by
      rw [← rootDiagUnit_mul, ← rootDiagUnit_mul]
      exact congrArg (rootDiagUnit Tag.E6) (mul_comm c a)
    have hxs : x * s = s * x := by
      rw [hs_eq₃]
      change (y₃ * rootDiagUnit Tag.E6 c * y₃⁻¹) *
          (y₃ * rootDiagUnit Tag.E6 a * y₃⁻¹) =
        (y₃ * rootDiagUnit Tag.E6 a * y₃⁻¹) *
          (y₃ * rootDiagUnit Tag.E6 c * y₃⁻¹)
      calc (y₃ * rootDiagUnit Tag.E6 c * y₃⁻¹) *
            (y₃ * rootDiagUnit Tag.E6 a * y₃⁻¹)
          = y₃ * (rootDiagUnit Tag.E6 c * rootDiagUnit Tag.E6 a) *
              y₃⁻¹ := by group
        _ = y₃ * (rootDiagUnit Tag.E6 a * rootDiagUnit Tag.E6 c) *
              y₃⁻¹ := by rw [hcd]
        _ = (y₃ * rootDiagUnit Tag.E6 a * y₃⁻¹) *
              (y₃ * rootDiagUnit Tag.E6 c * y₃⁻¹) := by group
    let R := TwistedDiag.Rgrp Ω Fr
    let C := TwistedDiag.Cgrp K σ.toRingHom Ω
    obtain ⟨-, -, hCnorm, hCidx, -⟩ :=
      TwistedDiag.cgrp_facts (ℓ := 2) hf K hK σ.toRingHom hσ h3 Ω Fr hFr
    haveI : (C.subgroupOf R).Normal := hCnorm
    have hrel : (C.subgroupOf R).relIndex ⊤ = 3 := by
      have h1 : (C.subgroupOf R).relIndex (R.subgroupOf R) = C.relIndex R :=
        Subgroup.relIndex_subgroupOf (le_refl R)
      have h2 : R.subgroupOf R = ⊤ := Subgroup.subgroupOf_self R
      rw [← h2, h1, hCidx]
    have hx3C : x ^ 3 ∈ C := by
      have hp : (⟨x, hxR⟩ : R) ^ ((C.subgroupOf R).relIndex ⊤) ∈ C.subgroupOf R :=
        Subgroup.pow_relIndex_mem (H := C.subgroupOf R) (K := ⊤) (g := ⟨x, hxR⟩)
          (Subgroup.mem_top _)
      rw [hrel] at hp
      exact hp
    have hxrC : x ^ r ∈ C := by
      rw [← hxord, pow_orderOf_eq_one]
      exact one_mem C
    have hrne3 : r ≠ 3 := ne_three_of_orderOf_pow_two he' hordq
    have hcop : Nat.Coprime 3 r :=
      (Nat.coprime_primes Nat.prime_three hr).2 (Ne.symm hrne3)
    have hxC : x ∈ C := CFSG.StandardType.mem_of_pow_mem_of_coprime hcop hx3C hxrC
    obtain ⟨z₀, hz₀C, hz₀x⟩ := Subgroup.mem_map.1 hxC
    have hz₀ord : orderOf z₀ = r := by
      have h := orderOf_injective (baseChangeGL (algebraMap K Ω))
        (baseChangeGL_injective (algebraMap K Ω)) z₀
      rw [hz₀x, hxord] at h
      exact h.symm
    let wΓ : ↥(RecipeExcLang.twInndiagGroup K σ) :=
      (NoOffTwE6Three.twInndiagEquivRgrp hf hK σ hσ Fr hFr).symm s
    have hαw : ασ = RecipeExcLang.twConj K σ wΓ := by
      rw [← hsα]
      rfl
    let wΓT : ModGL TwistTag.E6.tag K := wΓ
    let wΓE : ModGL Tag.E6 K := wΓT
    have hbw : baseChangeGL (algebraMap K Ω) wΓE = (s : ModGL Tag.E6 Ω) := by
      have h := NoOffTwE6Three.twInndiagEquivRgrp_apply hf hK σ hσ Fr hFr wΓ
      have hw : NoOffTwE6Three.twInndiagEquivRgrp hf hK σ hσ Fr hFr wΓ = s :=
        (NoOffTwE6Three.twInndiagEquivRgrp hf hK σ hσ Fr hFr).apply_symm_apply s
      rw [hw] at h
      exact h.symm
    have hzfix : wΓE * z₀ * wΓE⁻¹ = z₀ := by
      apply baseChangeGL_injective (algebraMap K Ω)
      rw [map_mul, map_mul, map_inv, hbw, hz₀x]
      calc (s : ModGL Tag.E6 Ω) * x * (s : ModGL Tag.E6 Ω)⁻¹
          = x * (s : ModGL Tag.E6 Ω) * (s : ModGL Tag.E6 Ω)⁻¹ := by
              rw [← hxs]
        _ = x := by group
    have hαz : ασ ⟨z₀, hz₀C⟩ = ⟨z₀, hz₀C⟩ := by
      apply Subtype.ext
      rw [hαw, RecipeExcLang.coe_twConj]
      exact hzfix
    refine ⟨r, ⟨e, he, hr, hord⟩, ⟨⟨z₀, hz₀C⟩, ?_, ?_⟩⟩
    · exact (Subgroup.orderOf_mk z₀ hz₀C).trans hz₀ord
    · exact hαz

end CFSG.StandardType

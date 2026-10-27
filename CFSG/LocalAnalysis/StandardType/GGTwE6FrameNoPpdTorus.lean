module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Torus
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwA2ConjLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusActPow
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCentralizer
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Arith
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE7
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoCore
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagLiftConv
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.E6FourPlane
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E7FourPlane
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KGD.D4QA1
public import CFSG.RankThree.PartOne.SLB4A.ClassExcRest
public import CFSG.Walter.JRFacts
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

namespace CFSG.StandardType.TwE6FrameNoPpd

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b
  CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Steinberg

private lemma canonicalRep_inv_conj_rootDiagUnit {Ω : Type} [Field Ω]
    (w : WeylGroup Tag.E6) (a : Fin Tag.E6.rank → Ωˣ) :
    (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ * rootDiagUnit Tag.E6 a *
        canonicalRep (coxeterSystem Tag.E6) Ω w =
      rootDiagUnit Tag.E6 (weylAct w⁻¹ a) := by
  have h := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit
      (K := Ω) w (weylAct w⁻¹ a)
  rw [← weylAct_mul, mul_inv_cancel, weylAct_one] at h
  rw [← h]
  group

private lemma theta_mem_familyGroup {Ω : Type} [Field Ω] [IsAlgClosed Ω] {n : ℕ}
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n) {b : Fin Tag.E6.rank → Ωˣ}
    {g : ModGL Tag.E6 Ω} (hg : g ∈ familyGroup (K := Ω) (fun _ : Unit => b)) :
    TwistedDiag.theta Fr g ∈ familyGroup (K := Ω) (fun _ : Unit => b) := by
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos (by norm_num : (0 : ℕ) < 2) n)
    exact ⟨x, by rw [hFr, hx]⟩
  have himg : (fun α => SmallQ3.twE6W0 • permLattice TwistTag.E6.perm α) ''
      familyKernel (fun _ : Unit => b) = familyKernel (fun _ : Unit => b) := by
    ext β
    constructor
    · rintro ⟨α, ⟨hα, hαa⟩, rfl⟩
      refine ⟨?_, fun i => ?_⟩
      · dsimp only
        rw [SmallQ3.twE6W0_smul_permLattice]
        exact IsRoot.neg hα
      · dsimp only
        rw [SmallQ3.twE6W0_smul_permLattice]
        exact (SmallQ3.rootChar_neg_vec_E6Four (τ := Tag.E6) b α).trans
          (by have h : rootChar b α = 1 := hαa i; rw [h, inv_one])
    · rintro ⟨hβ, hβa⟩
      refine ⟨-β, ⟨IsRoot.neg hβ, fun i => ?_⟩, ?_⟩
      · exact (SmallQ3.rootChar_neg_vec_E6Four (τ := Tag.E6) b β).trans
          (by have h : rootChar b β = 1 := hβa i; rw [h, inv_one])
      · simp only
        rw [SmallQ3.twE6W0_smul_permLattice, neg_neg]
  have h := twFrob_mem_familyGroup (t := TwistTag.E6) (L := Ω) hFrs
    SmallQ3.twE6W0 (fun _ : Unit => b) himg hg
  exact h

theorem exists_weylAct_eq_of_mem_thetaFixed
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (halg : letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω) {n : ℕ} (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) {b : Fin Tag.E6.rank → Ωˣ} {x : ModGL Tag.E6 Ω}
    (hx : x ∈ TwistedDiag.thetaFixed Fr)
    (hxb : x * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 b * x) {r : ℕ} (hr : r.Prime)
    (hr5 : 5 < r) (hxr : x ^ r = 1) (hx1 : x ≠ 1) :
    ∃ (c : Fin Tag.E6.rank → Ωˣ) (u : WeylGroup Tag.E6), (∀ i, c i ^ r = 1) ∧ c ≠ 1 ∧
      u ∈ kernelReflectionGroup b ∧ weylAct u (c ^ (-(2 ^ n : ℤ))) = c := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hxC, hxθ⟩ := (TwistedDiag.mem_thetaFixed (Fr := Fr)).1 hx
  let B : Subgroup (ModGL Tag.E6 Ω) := Subgroup.zpowers x
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 ⟨r, hr.pos, hxr⟩
  haveI : Finite B := finite_zpowers.2 hfin
  have hBfin : (B : Set (ModGL Tag.E6 Ω)).Finite :=
    Set.toFinite (B : Set (ModGL Tag.E6 Ω))
  have hBle : B ≤ adjointGroup Tag.E6 Ω := Subgroup.zpowers_le.mpr hxC
  have hBcomm : ∀ y ∈ B, rootDiagUnit Tag.E6 b * y = y * rootDiagUnit Tag.E6 b := by
    intro y hy
    have hcent : B ≤ Subgroup.centralizer
        ({rootDiagUnit Tag.E6 b} : Set (ModGL Tag.E6 Ω)) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxb)
    exact Subgroup.mem_centralizer_iff.1 (hcent hy) (rootDiagUnit Tag.E6 b)
      (Set.mem_singleton _)
  have hexp : ∀ y ∈ B, y ^ r = 1 := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm k (r : ℤ), zpow_mul, zpow_natCast, hxr,
      one_zpow]
  obtain ⟨z, hzC, hzcomm, hzmono⟩ :=
    exists_conj_le_monomial_centralizer_bar (τ := Tag.E6) (L := Ω) (ℓ := 2) (p := r)
      (hℓ := by omega) (halg := halg) (a := b) (B := B)
      (hB := hBle) (hBfin := hBfin) (hBa := hBcomm) (hexp := hexp)
  let y : ModGL Tag.E6 Ω := z * x * z⁻¹
  have hyM : y ∈ monomialSubgroup Tag.E6 Ω :=
    by simpa [y] using hzmono x (Subgroup.mem_zpowers x)
  have hyr : y ^ r = 1 := by
    rw [show y = z * x * z⁻¹ from rfl, conj_pow, hxr, mul_one, mul_inv_cancel]
  let wimg : WeylGroup Tag.E6 := weylQuotientHom Tag.E6 Ω ⟨y, hyM⟩
  have hwpow : wimg ^ r = 1 := weylQuotientHom_pow_eq_one hyM hyr
  have hw1 : wimg = 1 := by
    have hordr : orderOf wimg ∣ r := orderOf_dvd_of_pow_eq_one hwpow
    have hordW : orderOf wimg ∣ Nat.card (WeylGroup Tag.E6) := orderOf_dvd_natCard wimg
    rcases (Nat.dvd_prime hr).mp hordr with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      rw [h1, CFSG.RankThree.E6.card_weylGroup_E6] at hordW
      exact CFSG.RankThree.E6.not_dvd_51840 hr hr5 hordW
  have hyT : y ∈ torusGroup Tag.E6 Ω :=
    mem_torusGroup_of_weylQuotientHom_eq_one hyM (by simpa [wimg] using hw1)
  obtain ⟨c0, hc0⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hyT
  have hc0' : z * x * z⁻¹ = rootDiagUnit Tag.E6 c0 := by simpa [y] using hc0
  have hzFC : z ∈ familyCentralizer Tag.E6 Ω (fun _ : Unit => b) := by
    refine mem_familyCentralizer.2 ⟨hzC, fun _ => ?_⟩
    rw [hzcomm, mul_inv_cancel_right]
  obtain ⟨w, hwStab, m, hmF, hz_eq⟩ :=
    familyCentralizer_le_mul Tag.E6 Ω (fun _ : Unit => b) hzFC
  let nw : ModGL Tag.E6 Ω := canonicalRep (coxeterSystem Tag.E6) Ω w
  have hnorm : nw ∈ Subgroup.normalizer
      (familyGroup (K := Ω) (fun _ : Unit => b) : Set (ModGL Tag.E6 Ω)) := by
    simpa [nw] using canonicalRep_mem_normalizer_familyGroup (K := Ω) hwStab
  let m' : ModGL Tag.E6 Ω := nw⁻¹ * m * nw
  have hm'F : m' ∈ familyGroup (K := Ω) (fun _ : Unit => b) := by
    have hnorm' : nw⁻¹ ∈ Subgroup.normalizer
        (familyGroup (K := Ω) (fun _ : Unit => b) : Set (ModGL Tag.E6 Ω)) := inv_mem hnorm
    have := (Subgroup.mem_normalizer_iff.1 hnorm' m).1 hmF
    simpa [m', inv_inv] using this
  have hxm : m' * x * m'⁻¹ = rootDiagUnit Tag.E6 (weylAct w⁻¹ c0) := by
    calc m' * x * m'⁻¹ = nw⁻¹ * (m * nw * x * (m * nw)⁻¹) * nw := by
          simp only [m']
          group
      _ = nw⁻¹ * (z * x * z⁻¹) * nw := by rw [← hz_eq]
      _ = nw⁻¹ * rootDiagUnit Tag.E6 c0 * nw := by rw [hc0']
      _ = rootDiagUnit Tag.E6 (weylAct w⁻¹ c0) := by
          simpa [nw] using canonicalRep_inv_conj_rootDiagUnit (Ω := Ω) w c0
  let c : Fin Tag.E6.rank → Ωˣ := weylAct w⁻¹ c0
  have hxm' : m' * x * m'⁻¹ = rootDiagUnit Tag.E6 c := hxm
  have hx_eq : x = m'⁻¹ * rootDiagUnit Tag.E6 c * m' := by
    calc x = m'⁻¹ * (m' * x * m'⁻¹) * m' := by group
      _ = m'⁻¹ * rootDiagUnit Tag.E6 c * m' := by rw [hxm']
  have htheta_m' : TwistedDiag.theta Fr m' ∈ familyGroup (K := Ω) (fun _ : Unit => b) :=
    theta_mem_familyGroup (Ω := Ω) (n := n) Fr hFr hm'F
  have hhF : TwistedDiag.theta Fr m' * m'⁻¹ ∈
      familyGroup (K := Ω) (fun _ : Unit => b) :=
    mul_mem htheta_m' (inv_mem hm'F)
  have hθd : TwistedDiag.theta Fr (rootDiagUnit Tag.E6 c) =
      rootDiagUnit Tag.E6 ((c ^ (2 ^ n))⁻¹) :=
    TwistedDiag.theta_rootDiagUnit Fr (q := 2 ^ n) hFr c
  have hmain : m'⁻¹ * rootDiagUnit Tag.E6 c * m' =
      (TwistedDiag.theta Fr m')⁻¹ * rootDiagUnit Tag.E6 ((c ^ (2 ^ n))⁻¹) *
        TwistedDiag.theta Fr m' := by
    calc m'⁻¹ * rootDiagUnit Tag.E6 c * m' = x := hx_eq.symm
      _ = TwistedDiag.theta Fr x := hxθ.symm
      _ = TwistedDiag.theta Fr (m'⁻¹ * rootDiagUnit Tag.E6 c * m') := by rw [hx_eq]
      _ = (TwistedDiag.theta Fr m')⁻¹ * TwistedDiag.theta Fr (rootDiagUnit Tag.E6 c) *
            TwistedDiag.theta Fr m' := by rw [map_mul, map_mul, map_inv]
      _ = (TwistedDiag.theta Fr m')⁻¹ * rootDiagUnit Tag.E6 ((c ^ (2 ^ n))⁻¹) *
            TwistedDiag.theta Fr m' := by rw [hθd]
  have hconj_h : (TwistedDiag.theta Fr m' * m'⁻¹) * rootDiagUnit Tag.E6 c *
      (TwistedDiag.theta Fr m' * m'⁻¹)⁻¹ =
      rootDiagUnit Tag.E6 ((c ^ (2 ^ n))⁻¹) := by
    have h1 : m'⁻¹ * rootDiagUnit Tag.E6 c =
        (TwistedDiag.theta Fr m')⁻¹ * rootDiagUnit Tag.E6 ((c ^ (2 ^ n))⁻¹) *
          TwistedDiag.theta Fr m' * m'⁻¹ := by
      calc m'⁻¹ * rootDiagUnit Tag.E6 c =
          (m'⁻¹ * rootDiagUnit Tag.E6 c * m') * m'⁻¹ := by group
        _ = ((TwistedDiag.theta Fr m')⁻¹ * rootDiagUnit Tag.E6 ((c ^ (2 ^ n))⁻¹) *
              TwistedDiag.theta Fr m') * m'⁻¹ := by rw [hmain]
        _ = (TwistedDiag.theta Fr m')⁻¹ * rootDiagUnit Tag.E6 ((c ^ (2 ^ n))⁻¹) *
              TwistedDiag.theta Fr m' * m'⁻¹ := by group
    calc (TwistedDiag.theta Fr m' * m'⁻¹) * rootDiagUnit Tag.E6 c *
          (TwistedDiag.theta Fr m' * m'⁻¹)⁻¹
        = TwistedDiag.theta Fr m' * (m'⁻¹ * rootDiagUnit Tag.E6 c) *
            (m' * (TwistedDiag.theta Fr m')⁻¹) := by group
      _ = TwistedDiag.theta Fr m' *
            ((TwistedDiag.theta Fr m')⁻¹ * rootDiagUnit Tag.E6 ((c ^ (2 ^ n))⁻¹) *
              TwistedDiag.theta Fr m' * m'⁻¹) *
            (m' * (TwistedDiag.theta Fr m')⁻¹) := by rw [h1]
      _ = rootDiagUnit Tag.E6 ((c ^ (2 ^ n))⁻¹) := by group
  have hhFC : TwistedDiag.theta Fr m' * m'⁻¹ ∈
      familyCentralizer Tag.E6 Ω (fun _ : Unit => b) :=
    (familyGroup_le_familyCentralizer (K := Ω) (fun _ : Unit => b)) hhF
  obtain ⟨w', hw'Stab, t, htT, u, hu, v, hv, hfac⟩ :=
    familyCentralizer_factors Tag.E6 Ω (fun _ : Unit => b)
      (TwistedDiag.theta Fr m' * m'⁻¹) hhFC
  have huF : u ∈ familyGroup (K := Ω) (fun _ : Unit => b) :=
    Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hu)
  have hvF : v ∈ familyGroup (K := Ω) (fun _ : Unit => b) :=
    Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hv)
  have huPos : u ∈ posUnipotent Tag.E6 Ω :=
    (iSup₂_le fun α hα => le_iSup₂_of_le (f := fun β (_ : β ∈ {β : Fin Tag.E6.rank → ℤ |
      IsRoot Tag.E6 β ∧ 0 < height β}) => rootSubgroup Tag.E6 Ω β) α
      ⟨hα.1.1, hα.2.2⟩ le_rfl) hu
  have hvPos : v ∈ posUnipotent Tag.E6 Ω :=
    (iSup₂_le fun α hα => le_iSup₂_of_le (f := fun β (_ : β ∈ {β : Fin Tag.E6.rank → ℤ |
      IsRoot Tag.E6 β ∧ 0 < height β}) => rootSubgroup Tag.E6 Ω β) α
      ⟨hα.1.1, hα.2.2.1⟩ le_rfl) hv
  have huB : u ∈ borelGroup Tag.E6 Ω := Subgroup.mem_sup_right huPos
  have hvB : v ∈ borelGroup Tag.E6 Ω := Subgroup.mem_sup_right hvPos
  let nw' : ModGL Tag.E6 Ω := canonicalRep (coxeterSystem Tag.E6) Ω w'
  have hnw'F : nw' ∈ familyGroup (K := Ω) (fun _ : Unit => b) := by
    have hEq : nw' = (t * u)⁻¹ * (TwistedDiag.theta Fr m' * m'⁻¹) * v⁻¹ := by
      rw [hfac]
      simp only [nw']
      group
    rw [hEq]
    exact mul_mem (mul_mem (inv_mem (mul_mem (Subgroup.mem_sup_left htT) huF)) hhF)
      (inv_mem hvF)
  have hnw'T : nw' ∈ toralRootGroup Tag.E6 Ω b := by
    rw [← CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.familyGroup_unit_eq_toralRootGroup
      (L := Ω) (a := b)]
    exact hnw'F
  have hw'K : w' ∈ kernelReflectionGroup b :=
    mem_kernelReflectionGroup_of_canonicalRep_mem_gen (k := Ω) (a := b) (w := w')
      (by simpa [nw'] using hnw'T)
  have hbruhat : (TwistedDiag.theta Fr m' * m'⁻¹) ∈ bruhatCell Tag.E6 Ω w' :=
    mem_bruhatCell.2 ⟨t * u, mul_mem (Subgroup.mem_sup_left htT) (Subgroup.mem_sup_right huPos),
      v, hvB, by simpa [nw'] using hfac.symm⟩
  have hconj_lemma : rootDiagUnit Tag.E6 ((c ^ (2 ^ n))⁻¹) =
      canonicalRep (coxeterSystem Tag.E6) Ω w' * rootDiagUnit Tag.E6 c *
        (canonicalRep (coxeterSystem Tag.E6) Ω w')⁻¹ :=
    rootDiagUnit_eq_conj_canonicalRep_of_mem_bruhatCell (a := (c ^ (2 ^ n))⁻¹) (b := c)
      hbruhat hconj_h
  have hweyl : (c ^ (2 ^ n))⁻¹ = weylAct w' c := by
    apply DiagTorus.rootDiagUnit_injective
    calc rootDiagUnit Tag.E6 ((c ^ (2 ^ n))⁻¹)
        = canonicalRep (coxeterSystem Tag.E6) Ω w' * rootDiagUnit Tag.E6 c *
            (canonicalRep (coxeterSystem Tag.E6) Ω w')⁻¹ := hconj_lemma
      _ = rootDiagUnit Tag.E6 (weylAct w' c) :=
          CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit
            (K := Ω) w' c
  have hfinal : weylAct w'⁻¹ (c ^ (-(2 ^ n : ℤ))) = c := by
    have harg : c ^ (-(2 ^ n : ℤ)) = (c ^ (2 ^ n))⁻¹ := by
      rw [zpow_neg]
      rfl
    rw [harg, hweyl, ← weylAct_mul, inv_mul_cancel, weylAct_one]
  have hdcr : (rootDiagUnit Tag.E6 c) ^ r = 1 := by
    rw [← hxm']
    rw [conj_pow, hxr, mul_one, mul_inv_cancel]
  have hc_pow : ∀ i, c i ^ r = 1 := by
    have hcr : c ^ r = 1 := by
      apply DiagTorus.rootDiagUnit_injective
      rw [rootDiagUnit_pow' (L := Ω) c r, rootDiagUnit_one, hdcr]
    intro i
    simpa using congrFun hcr i
  have hc_ne : c ≠ 1 := by
    intro hc1
    apply hx1
    have hd1 : rootDiagUnit Tag.E6 c = 1 := by rw [hc1, rootDiagUnit_one]
    have hx1' : m' * x * m'⁻¹ = 1 := by rw [hxm', hd1]
    calc x = m'⁻¹ * (m' * x * m'⁻¹) * m' := by group
      _ = 1 := by rw [hx1']; group
  exact ⟨c, w'⁻¹, hc_pow, hc_ne, (kernelReflectionGroup b).inv_mem hw'K, hfinal⟩

end CFSG.StandardType.TwE6FrameNoPpd

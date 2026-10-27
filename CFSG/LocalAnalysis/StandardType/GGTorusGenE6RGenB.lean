module

public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootTorus
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsT
public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6Cover
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6InOrb
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE6
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Pairs
public import CFSG.ClassicalInvolution.Q3.Q3ExcPinned
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7TwistMain
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalLocalComponentSplit
public import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem isComponentOf_map_of_injective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) {K L : Subgroup G}
    (h : IsComponentOf K L) : IsComponentOf (K.map f) (L.map f) := by
  obtain ⟨hKL, hs, hq⟩ := h
  exact ⟨Subgroup.map_mono hKL, CFSG.Assembly.IsSubnormal.map f hs,
    CFSG.Assembly.IsQuasisimple.of_mulEquiv (K.equivMapOfInjective f hf).symm hq⟩

private theorem map_baseChange_eq_derived
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n) :
    (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
        (baseChangeGL (τ := Tag.E6) (algebraMap K Ω)) =
      ⁅CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel
          (τ := Tag.E6) (twistHom TwistTag.E6 Ω Fr),
        CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel
          (τ := Tag.E6) (twistHom TwistTag.E6 Ω Fr)⁆ := by
  exact (exceptional_ambient_twisted_Frobenius_fixed_normalizer (p := 2) (f := n) TwistTag.E6
    Nat.prime_two hn K hK σ.toRingHom (by simpa using hσ) Ω Fr hFr).2.2.2.2.1.symm

private theorem finite_fixModel_of_frob
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) :
    Finite (CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel
      (τ := Tag.E6) (twistHom TwistTag.E6 Ω Fr)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hcharK : CharP K 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    refine charP_of_card_eq_prime_pow (p := 2) (f := 2 * n) ?_
    rw [← Nat.card_eq_fintype_card, hK]
    ring_nf
  haveI hcharΩ : CharP Ω 2 := (RingHom.charP_iff_charP (algebraMap K Ω) 2).1 hcharK
  haveI hAlgClosed : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hFr' : Fr = iterateFrobenius Ω 2 n := by
    refine RingHom.ext fun c => ?_
    rw [hFr, iterateFrobenius_def]
  have hQ : CFSG.LieType.AlgebraicGroups.entrywiseFrobGL TwistTag.E6.tag Ω 2 n
      (diagramMap TwistTag.E6 Ω) = diagramMap TwistTag.E6 Ω := by
    simpa only [zpow_one] using CFSG.LieType.AlgebraicGroups.entrywiseFrobGL_diagramMap_zpow
      (t := TwistTag.E6) (L := Ω) 2 n (1 : ℤ)
  have hQd : (diagramMap TwistTag.E6 Ω) ^ 2 = 1 := by
    have h := diagramMap_pow_order (t := TwistTag.E6) (K := Ω)
    rwa [show TwistTag.E6.order = 2 from rfl] at h
  have hfin := CFSG.LieType.AlgebraicGroups.finite_fixedPointsIn_frobTwistGL
    (τ := TwistTag.E6.tag) (e := n) (d := 2) (p := 2) (k := Ω) hn (by norm_num) hQ hQd
  rw [CFSG.ComponentClassification.Burgoyne.E2.TwE6In.fixedPointsIn_eq_twistedFixedGroup
    (p := 2) (k := Ω) n, ← hFr'] at hfin
  exact hfin

theorem tspec_exists_coroot_in_component
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ}
    (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D)
    {x : Fin Tag.E6.rank → ZMod 3} (hx : x ≠ 0) {J : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hJ : IsComponentOf J (ggFix (D.ad x))) :
    ∃ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α ∧ ∀ s : Ωˣ, s ^ (2 ^ n + 1) = 1 →
      ∃ u : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom), u ∈ J ∧ u ∈ D.Tor ∧
        baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (u : ModGL TwistTag.E6.tag K) =
          g * TwE6Coroot.coroot α s * g⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hcharK : CharP K 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    refine charP_of_card_eq_prime_pow (p := 2) (f := 2 * n) ?_
    rw [← Nat.card_eq_fintype_card, hK]
    ring_nf
  haveI hcharΩ : CharP Ω 2 := (RingHom.charP_iff_charP (algebraMap K Ω) 2).1 hcharK
  haveI hAlgClosed : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let Φ : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω := twistHom TwistTag.E6 Ω Fr
  let Γ' : Subgroup (ModGL Tag.E6 Ω) :=
    ⁅CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ,
      CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ⁆
  let bc : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →* ModGL Tag.E6 Ω :=
    (baseChangeGL (τ := Tag.E6) (algebraMap K Ω)).comp (Subgroup.subtype _)
  have hmap : (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
      (baseChangeGL (τ := Tag.E6) (algebraMap K Ω)) = Γ' := by
    rw [map_baseChange_eq_derived hn hK σ hσ Fr hFr]
  have hfinF : Finite (CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ) := by
    simpa only [Φ] using finite_fixModel_of_frob hn hK Fr hFr
  have hgC : g ∈ adjointGroup Tag.E6 Ω := hL.1
  have hg : CFSG.RankThree.Classical2.twistE6 Ω Fr g =
      g * CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.n0 Ω := by
    have h := hL.2
    calc CFSG.RankThree.Classical2.twistE6 Ω Fr g
        = g * (g⁻¹ * CFSG.RankThree.Classical2.twistE6 Ω Fr g) := by group
      _ = g * CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.n0 Ω := by rw [h]
  have hnΓ : ∀ k, g * weylElt Tag.E6 Ω k 1 * g⁻¹ ∈ Γ' := by
    intro k
    rw [← hD.nb_eq k]
    have hmem : baseChangeGL (algebraMap K Ω)
        ((D.nb k : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) : ModGL TwistTag.E6.tag K) ∈
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
          (baseChangeGL (τ := Tag.E6) (algebraMap K Ω)) :=
      ⟨(D.nb k).1, (D.nb k).2, rfl⟩
    rwa [hmap] at hmem
  have hap : ∀ k, zetaVec ζ hζ x k ^ 3 = 1 := by
    intro k
    rw [zetaVec_apply]
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have haq : ∀ k, zetaVec ζ hζ x k ^ (2 ^ n + 1) = 1 := by
    intro k
    obtain ⟨m, hm⟩ := h3
    rw [zetaVec_apply, hm, pow_mul]
    rw [show (ζ ^ (x k).val) ^ 3 = 1 by simpa [zetaVec_apply] using hap k, one_pow]
  have h1 : rootDiagUnit Tag.E6 (zetaVec ζ hζ x) ≠ 1 := by
    intro h
    apply hx
    have hz : zetaVec ζ hζ x = 1 := by
      apply rootDiagUnit_injective (τ := Tag.E6) (K := Ω)
      rw [h, rootDiagUnit_one]
    have h0 : zetaVec (τ := Tag.E6) ζ hζ (0 : Fin Tag.E6.rank → ZMod 3) = 1 := by
      funext i
      simp [zetaVec_apply]
    exact zetaVec_injective (τ := Tag.E6) hζo hζ (hz.trans h0.symm)
  obtain ⟨hxR, hdiag⟩ := hD.diag_eq x
  let a' : ModGL Tag.E6 Ω := g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹
  have hxR' : a' ∈ CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.Rgrp Ω Fr := hxR
  have hdiag' : D.ad x = NoOffTwE6Three.rgrpConjAut hn hK σ hσ Fr hFr ⟨a', hxR'⟩ := hdiag
  have hrange : ∀ c, bc c ∈ Γ' := fun c => by
    have hmem : bc c ∈ (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
        (baseChangeGL (τ := Tag.E6) (algebraMap K Ω)) :=
      ⟨c.1, c.2, rfl⟩
    rwa [hmap] at hmem
  let ψ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →* ↥Γ' := bc.codRestrict Γ' hrange
  have hψ_coe : ∀ c, (ψ c : ModGL Tag.E6 Ω) = bc c := fun c => rfl
  have hψ_surj : Function.Surjective ψ := by
    intro y
    have hy : (y : ModGL Tag.E6 Ω) ∈ (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
        (baseChangeGL (τ := Tag.E6) (algebraMap K Ω)) := by
      rw [hmap]
      exact y.2
    obtain ⟨c, hcC, hc⟩ := hy
    refine ⟨⟨c, hcC⟩, Subtype.ext ?_⟩
    rw [hψ_coe]
    change baseChangeGL (algebraMap K Ω) c = (y : ModGL Tag.E6 Ω)
    exact hc
  have hψ_inj : Function.Injective ψ := by
    intro c₁ c₂ h
    apply Subtype.ext
    apply baseChangeGL_injective (τ := Tag.E6) (algebraMap K Ω)
    change bc c₁ = bc c₂
    exact congrArg (fun z : ↥Γ' => (z : ModGL Tag.E6 Ω)) h
  have hker : ψ.ker ≤ Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
    rw [(MonoidHom.ker_eq_bot_iff ψ).2 hψ_inj]
    exact bot_le
  have ha'fix : a' ∈ CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ := hxR
  have hfixmap : (CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ).map
      (MulAut.conj a').toMonoidHom = CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      change a' * y * a'⁻¹ ∈ CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ
      exact (CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ).mul_mem
        ((CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ).mul_mem ha'fix hy)
        ((CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ).inv_mem ha'fix)
    · intro z hz
      refine ⟨a'⁻¹ * z * a', (CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ).mul_mem
        ((CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ).mul_mem
          ((CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ).inv_mem ha'fix) hz) ha'fix, ?_⟩
      change a' * (a'⁻¹ * z * a') * a'⁻¹ = z
      group
  have hΓ'map : Γ'.map (MulAut.conj a').toMonoidHom = Γ' := by
    change (⁅CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ,
      CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ⁆ : Subgroup (ModGL Tag.E6 Ω)).map
        (MulAut.conj a').toMonoidHom = Γ'
    rw [Subgroup.map_commutator, hfixmap]
  have hmem : ∀ y ∈ Γ', a' * y * a'⁻¹ ∈ Γ' := by
    intro y hy
    have hy' : (MulAut.conj a') y ∈ Γ'.map (MulAut.conj a').toMonoidHom := ⟨y, hy, rfl⟩
    rw [hΓ'map] at hy'
    exact hy'
  have hfixmap_inv : (CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ).map
      (MulAut.conj a'⁻¹).toMonoidHom = CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      change a'⁻¹ * y * a' ∈ CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ
      exact (CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ).mul_mem
        ((CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ).mul_mem
          ((CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ).inv_mem ha'fix) hy) ha'fix
    · intro z hz
      refine ⟨a' * z * a'⁻¹, (CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ).mul_mem
        ((CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ).mul_mem ha'fix hz)
        ((CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ).inv_mem ha'fix), ?_⟩
      change a'⁻¹ * (a' * z * a'⁻¹) * a' = z
      group
  have hΓ'map_inv : Γ'.map (MulAut.conj a'⁻¹).toMonoidHom = Γ' := by
    change (⁅CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ,
      CFSG.HardMathSupport.Timmesfeld.CrossChar.fixModel Φ⁆ : Subgroup (ModGL Tag.E6 Ω)).map
        (MulAut.conj a'⁻¹).toMonoidHom = Γ'
    rw [Subgroup.map_commutator, hfixmap_inv]
  have hmem_inv : ∀ y ∈ Γ', a'⁻¹ * y * a' ∈ Γ' := by
    intro y hy
    have hy' : (MulAut.conj a'⁻¹) y ∈ Γ'.map (MulAut.conj a'⁻¹).toMonoidHom := ⟨y, hy, rfl⟩
    rw [hΓ'map_inv] at hy'
    exact hy'
  let b : MulAut ↥Γ' :=
    { toFun := fun y => ⟨a' * (y : ModGL Tag.E6 Ω) * a'⁻¹, hmem y y.2⟩
      invFun := fun y => ⟨a'⁻¹ * (y : ModGL Tag.E6 Ω) * a', hmem_inv y y.2⟩
      left_inv := fun y => Subtype.ext (by group)
      right_inv := fun y => Subtype.ext (by group)
      map_mul' := fun y z => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        group) }
  have hb_apply : ∀ y : ↥Γ', (b y : ModGL Tag.E6 Ω) = a' * (y : ModGL Tag.E6 Ω) * a'⁻¹ :=
    fun y => rfl
  have hab : ∀ l, b (ψ l) = ψ (D.ad x l) := by
    intro l
    apply Subtype.ext
    rw [hb_apply, hψ_coe, hψ_coe, hdiag']
    exact (rgrpConjAut_baseChangeGL hn hK σ hσ Fr hFr ⟨a', hxR'⟩ l).symm
  have hcomp := isComponentOf_map_ggFix_of_central hψ_surj hker hab hJ
  have hcomp' := isComponentOf_map_of_injective (Subgroup.subtype Γ') Subtype.val_injective hcomp
  have h1' : (J.map ψ).map (Subgroup.subtype Γ') = J.map bc := by
    rw [Subgroup.map_map,
      show (Subgroup.subtype Γ').comp ψ = bc from MonoidHom.ext fun l => rfl]
  have h2' : (ggFix b).map (Subgroup.subtype Γ') = Γ' ⊓ Subgroup.centralizer {a'} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, ?_⟩
      have hzz : (b z : ModGL Tag.E6 Ω) = (z : ModGL Tag.E6 Ω) := congrArg Subtype.val hz
      rw [hb_apply] at hzz
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        change (z : ModGL Tag.E6 Ω) * a' = a' * (z : ModGL Tag.E6 Ω)
        calc (z : ModGL Tag.E6 Ω) * a' = (a' * (z : ModGL Tag.E6 Ω) * a'⁻¹) * a' := by rw [hzz]
          _ = a' * (z : ModGL Tag.E6 Ω) := by group)
    · rintro ⟨hyΓ, hyC⟩
      refine ⟨⟨y, hyΓ⟩, ?_, rfl⟩
      apply Subtype.ext
      rw [hb_apply]
      have hyC' : y * a' = a' * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
      rw [← hyC']
      group
  rw [h1', h2'] at hcomp'
  have hq2 : Even (2 ^ n) :=
    ⟨2 ^ (n - 1), by rw [← two_mul, mul_comm, ← pow_succ, Nat.sub_add_cancel hn]⟩
  have hqpow : IsPrimePow (2 ^ n) :=
    (isPrimePow_nat_iff (2 ^ n)).mpr ⟨2, n, Nat.prime_two, by omega, rfl⟩
  obtain ⟨α, hα, hχ, hc⟩ := TwE6Coroot.exists_corootTorus_le_frame
    (L := Ω) (Fr := Fr) (q := 2 ^ n) (g := g) (p := 3)
    (a := zetaVec ζ hζ x) (K' := J.map bc)
    (pow_pos (by norm_num) n) hq2 hFr hqpow hfinF hgC hg hnΓ Nat.prime_three (by norm_num)
    hap haq h1 (isComponentOf_iff_open.mp hcomp')
  refine ⟨α, hα, fun s hs => ?_⟩
  obtain ⟨u, huJ, hueq⟩ := hc s hs
  refine ⟨u, huJ, ?_, ?_⟩
  · rw [hD.tor_eq]
    have hueq' : baseChangeGL (algebraMap K Ω) u.1 =
        g * TwE6Coroot.coroot α s * g⁻¹ := hueq
    rw [hueq']
    exact ⟨TwE6Coroot.coroot α s,
      rootDiagUnit_mem_torusGroup (CFSG.SeitzReduction.E6Pilot.corootTuple α s), by rfl⟩
  · exact hueq

end CFSG.StandardType.E6ThreeModel

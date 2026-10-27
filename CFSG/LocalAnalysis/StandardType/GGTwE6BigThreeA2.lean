module

public import CFSG.LocalAnalysis.StandardType.GGTwE6BigLineDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6K1ThreeA2Orbit
public import CFSG.LocalAnalysis.StandardType.GGTwE6LemmaKFinal
public import CFSG.LocalAnalysis.StandardType.GGTwE6SigmaTorus
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeOuter
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeShape
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.Order216
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairRigid
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Normalizer
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Torus
public import CFSG.LocalAnalysis.StandardType.GGTwE6D4RootFacts
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcCtx
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcPlumb
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSmall
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATArith
public import CFSG.HardMathSupport.Solomon.Coordinator.L3G515Core
public import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
public import CFSG.Quasithin.Background.A3Structure314
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.F6CatRecogL2
public import CFSG.Quasithin.Background.F6CatRecogTools2
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.EmptyFaithful.Insp9Cases4
public import CFSG.Quasithin.EmptyFaithful.S153D44
public import CFSG.Quasithin.H13.A5S136b
public import CFSG.Quasithin.H13.A5S136c
public import CFSG.Quasithin.H13.A5Y1367c
public import CFSG.Quasithin.Vol2.Ch10SecA1011
public import CFSG.Quasithin.Vol2.Ch10SecB5Easy
public import CFSG.Quasithin.Vol2.Ch10SecB6C27
public import CFSG.Quasithin.Vol2.Ch10SecB6Lt
public import CFSG.Quasithin.Vol2.Ch10SecB6Prep
public import CFSG.Quasithin.Vol2.Ch10SecB6Rank
public import CFSG.Quasithin.Vol2.Ch10SecB6S21
public import CFSG.Quasithin.Vol2.Ch10SecB6Syl
public import CFSG.Quasithin.Vol2.Ch10SecKGC27b
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGC
public import CFSG.Quasithin.Vol2.Ch9KGFFQR
public import CFSG.Quasithin.Vol2.Ch9KGFFQRCase
public import CFSG.Walter.J1Props
public import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.SCFourCover
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Lang.E6Descent

private theorem ggTwE6BigThreeA2_exists_order34_subgroup
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hK : Nat.card K = 4)
    (hσ : ∀ c, σ c = c ^ 2) {h : twistedE6InndiagGL K σ} (hh1 : h ≠ 1) (hh3 : h ^ 3 = 1)
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : 3 ^ 4 ≤ Nat.card E) (hfE : twistedE6InndiagConj K σ h ∈ E) :
    ∃ X : Subgroup (MulAut (twistedE6RootGroup K σ)),
      X ≤ E ∧ twistedE6InndiagConj K σ h ∈ X ∧ Nat.card X = 3 ^ 4 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hinj := twistedE6InndiagConj_injective Nat.prime_two (le_refl 1)
    (hK.trans (by norm_num)) σ hσ
  have hconj3 : twistedE6InndiagConj K σ h ^ 3 = 1 := by rw [← map_pow, hh3, map_one]
  have hconj1 : twistedE6InndiagConj K σ h ≠ 1 := fun h1 =>
    hh1 (hinj (h1.trans (map_one (twistedE6InndiagConj K σ)).symm))
  have hord : orderOf (twistedE6InndiagConj K σ h) = 3 := orderOf_eq_prime hconj3 hconj1
  set H : Subgroup (MulAut (twistedE6RootGroup K σ)) :=
    Subgroup.zpowers (twistedE6InndiagConj K σ h) with hHdef
  have hHcard : Nat.card H = 3 := by rw [hHdef, Nat.card_zpowers]; exact hord
  have hHle : H ≤ E := by rw [hHdef]; exact Subgroup.zpowers_le.2 hfE
  have hHdvd : Nat.card H ∣ 3 ^ 4 := by rw [hHcard]; norm_num
  have hEp : IsPGroup 3 ↥E := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    exact ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 (x : MulAut _) x.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hk4 : 4 ≤ k := by
    apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp
    rw [← hk]
    exact hcard
  have hEdvd : 3 ^ 4 ∣ Nat.card E := by
    rw [hk]
    exact Nat.pow_dvd_pow 3 hk4
  obtain ⟨X, hXcard, hHX, hXE⟩ := Sylow.exists_subgroup_card_pow_prime_le_le
    Nat.prime_three hHdvd hEdvd hHle
  refine ⟨X, hXE, hHX ?_, hXcard⟩
  rw [hHdef]
  exact Subgroup.mem_zpowers _

private theorem ggTwE6BigThreeA2_toral_of_le
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    {E X : Subgroup (MulAut (twistedE6RootGroup K σ))} (hXE : X ≤ E)
    (htor : E6AdToral (((E.comap (twistedE6InndiagConj K σ)).map
        (twistedE6InndiagGL K σ).subtype).map
          (baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))))) :
    E6AdToral (((X.comap (twistedE6InndiagConj K σ)).map
        (twistedE6InndiagGL K σ).subtype).map
          (baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K)))) :=
  e6AdToral_mono
    (Subgroup.map_mono (Subgroup.map_mono (Subgroup.comap_mono hXE))) htor

private theorem ggTwE6BigThreeA2_rho_eq_neg
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] {q : ℕ} (hq : 0 < q) {Fr : Ω →+* Ω}
    (hFr : ∀ c, Fr c = c ^ q) {g : ModGL Tag.E6 Ω} (hgC : g ∈ adjointGroup Tag.E6 Ω)
    (hg : twistHom TwistTag.E6 Ω Fr g = g * canonicalRep (coxeterSystem Tag.E6) Ω
      CFSG.HardMathSupport.Lang.E6Descent.twE6W0)
    {p : ℕ} (S : LangSetup Tag.E6 Ω p)
    (hSD : S.D = LangDatum.ofTwist TwistTag.E6 Fr q hFr
      CFSG.HardMathSupport.Lang.E6Descent.twE6W0 hgC hg)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    S.ρ γ = -γ := by
  have hρ := frobRootMap_ofTwist_apply hq hFr hgC hg (hSD ▸ S.frob) hγ
  have hρ' : S.ρ γ = CFSG.HardMathSupport.Lang.E6Descent.twE6W0 •
      permLattice CFSG.RankThree.E6.e6Rho γ := hρ
  calc S.ρ γ = CFSG.HardMathSupport.Lang.E6Descent.twE6W0 •
        permLattice CFSG.RankThree.E6.e6Rho γ := hρ'
    _ = -γ := by
      rw [CFSG.HardMathSupport.Lang.E6Descent.twE6W0_smul,
        CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.permLattice_permLattice']

private theorem ggTwE6BigThreeA2_goodLang_of_lemmaK
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hK : Nat.card K = 4)
    (hσ : ∀ c, σ c = c ^ 2) {h : twistedE6InndiagGL K σ}
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2)
    {g : ModGL Tag.E6 (AlgebraicClosure K)} (hgC : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hg : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g = g *
      canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K)
        CFSG.HardMathSupport.Lang.E6Descent.twE6W0)
    (hmem : baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL TwistTag.E6.tag K) ∈
      (LangDatum.ofTwist TwistTag.E6 Fr 2 hFr CFSG.HardMathSupport.Lang.E6Descent.twE6W0 hgC
        hg).torus.map (MulAut.conj g).toMonoidHom)
    (hup : (baseChangeGL (algebraMap K (AlgebraicClosure K))
      (h : ModGL TwistTag.E6.tag K)) ^ 3 = 1)
    (hu1 : baseChangeGL (algebraMap K (AlgebraicClosure K))
      (h : ModGL TwistTag.E6.tag K) ≠ 1) :
    ∃ D : TwE6LineLang K σ 2 h, D.S.D = LangDatum.ofTwist TwistTag.E6 Fr 2 hFr
      CFSG.HardMathSupport.Lang.E6Descent.twE6W0 hgC hg := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card]; exact hK.trans (by norm_num))
  have hchar : ringChar K = 2 := ringChar.eq K 2
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime Nat.prime_two (le_refl 1)
    Nat.prime_three (by norm_num) (by decide)
  let D : LangDatum Tag.E6 (AlgebraicClosure K) :=
    LangDatum.ofTwist TwistTag.E6 Fr 2 hFr CFSG.HardMathSupport.Lang.E6Descent.twE6W0 hgC hg
  have hΦ : D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr := rfl
  set ι₁ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K) with hι₁
  set u : ModGL Tag.E6 (AlgebraicClosure K) :=
    baseChangeGL ι₁ (h : ModGL TwistTag.E6.tag K) with hu
  set ι₀ : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K) :=
    (baseChangeGL ι₁).comp (twistedE6RootGroup K σ).subtype with hι₀
  have hι₀inj : Function.Injective ι₀ :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hrange₀ : ι₀.range = (twistedE6RootGroup K σ).map (baseChangeGL ι₁) := by
    change ((baseChangeGL ι₁).comp (twistedE6RootGroup K σ).subtype).range =
      Subgroup.map (baseChangeGL ι₁) (twistedE6RootGroup K σ)
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom := by
    rw [hrange₀]
    exact Γ_eq_map_twistedE6RootGroup Nat.prime_two (le_refl 1) (hK.trans (by norm_num))
      hσ hFr D hΦ
  have hfin : Finite D.model := finite_model_twistedE6 Nat.prime_two (le_refl 1)
    (hK.trans (by norm_num)) hσ hFr D hΦ
  have hβ' : ∀ c, ι₀ (twistedE6InndiagConj K σ h c) = u * ι₀ c * u⁻¹ := fun c => by
    change baseChangeGL ι₁ ((twistedE6InndiagConj K σ h c : twistedE6RootGroup K σ) :
        ModGL TwistTag.E6.tag K) =
      baseChangeGL ι₁ (h : ModGL TwistTag.E6.tag K) *
        baseChangeGL ι₁ (c : ModGL TwistTag.E6.tag K) *
        (baseChangeGL ι₁ (h : ModGL TwistTag.E6.tag K))⁻¹
    rw [twistedE6InndiagConj_apply, map_mul, map_mul, map_inv]
  have hup' : u ^ 3 = 1 := by rw [hu]; exact hup
  have hu1' : u ≠ 1 := by rw [hu]; exact hu1
  have hmem' : u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom := by rw [hu]; exact hmem
  have hq' : 5 ≤ p₀ ∨ 4 ≤ D.q := by
    show 5 ≤ p₀ ∨ 4 ≤ 2
    simpa using hq₀
  obtain ⟨S, a, ι, hSD, hT, hap, h1, hinj, hrange, hconjι, hg0⟩ :=
    exists_langSetup_conj_of_toral_datum (ℓ := 2) (f := 1) Nat.prime_two (le_refl 1) D
      (by rw [show D.q = 2 from rfl, pow_one]) hp₀ hp₀ℓ hq' hfin ι₀ hι₀inj hΓ
      (twistedE6InndiagConj K σ h) hβ' hmem' hup' hu1'
  have hL3 : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    CFSG.HardMathSupport.Lang.E6Descent.three_ne_zero_of_dvd_card_add_one (ℓ := 2) (f := 1)
      (le_refl 1) (by norm_num)
  have hqep : (2 : ℕ) = ringChar K ^ 1 := by rw [hchar, pow_one]
  have hKp : Nat.card K = (ringChar K ^ 1) ^ 2 := by
    rw [hchar, pow_one]; exact hK.trans (by norm_num)
  have hSigp : ∀ c, σ c = c ^ (ringChar K ^ 1) := by
    intro c; rw [hchar, pow_one]; exact hσ c
  have hRingp : (ringChar K).Prime := by rw [hchar]; exact Nat.prime_two
  have hCharp : CharP (AlgebraicClosure K) (ringChar K) := by rw [hchar]; exact inferInstance
  have hp0lp : p₀ ≠ ringChar K := by rw [hchar]; exact hp₀ℓ
  have hq0p : 5 ≤ p₀ ∨ 4 ≤ ringChar K ^ 1 := by rw [hchar, pow_one]; simpa using hq₀
  have hSqp : S.D.q = ringChar K ^ 1 := by rw [hSD, hchar, pow_one]; rfl
  have hg0p : S.D.g0 * rootDiagUnit Tag.E6 a * S.D.g0⁻¹ =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL TwistTag.E6.tag K) := by
    rw [hSD]; exact hg0
  have hSp : ∃ (t : TwistTag) (ht : t.tag = .E6)
      (Fr' : AlgebraicClosure K →+* AlgebraicClosure K),
      (∀ c, Fr' c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 (AlgebraicClosure K) t ht * Units.map (entrywiseHom Fr') g *
        (diagramAt .E6 (AlgebraicClosure K) t ht)⁻¹ :=
    ⟨TwistTag.E6, rfl, Fr, (fun c => by rw [hSD]; exact hFr c), (fun g => by rw [hSD]; rfl)⟩
  have hkerp : twE6MatFixDim K σ h = 6 + (kernelRoots (rootCharHom a)).ncard :=
    twE6MatFixDim_eq_of_conj σ h S.D.g0 a hg0p
  have hTamep := langSetup_hTame_of_prime S Nat.prime_three hL3 (fun hh => absurd hh (by decide))
    hT hap h1
  let Dlang : TwE6LineLang K σ 2 h :=
    { e := 1, he := Nat.zero_lt_one, hqe := hqep, hℓ := hRingp,
      hK' := hKp, hσ' := hSigp, hL3 := hL3, hchar := hCharp, p₀ := p₀, hp₀ := hp₀,
      hp₀ℓ := hp0lp, hq₀ := hq0p, S := S, a := a, ι := ι, hSq := hSqp, hT := hT,
      hap := hap, h1 := h1, hinj := hinj, hrange := hrange, hconj := hconjι,
      hg0 := hg0p, hS := hSp, hker := hkerp, hTame := hTamep }
  exact ⟨Dlang, by rw [hSD]⟩

private theorem ggTwE6BigThreeA2_isAlgebraic_of_ringEquiv_algebraMap
    {k K Ω : Type*} [Field k] [Field K] [Field Ω] [Algebra K Ω] [Algebra k Ω]
    (τ : k ≃+* K) (halg : ∀ x, algebraMap k Ω x = algebraMap K Ω (τ x))
    (h : Algebra.IsAlgebraic K Ω) : Algebra.IsAlgebraic k Ω := by
  refine Algebra.IsAlgebraic.mk fun ω => ?_
  obtain ⟨p, hp, hp0⟩ := h.isAlgebraic ω
  refine ⟨p.map τ.symm.toRingHom, ?_, ?_⟩
  · rw [Polynomial.map_ne_zero_iff τ.symm.injective]
    exact hp
  · rw [Polynomial.aeval_def] at hp0 ⊢
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap k Ω).comp τ.symm.toRingHom = algebraMap K Ω := by
      ext x
      change (algebraMap k Ω) (τ.symm x) = (algebraMap K Ω) x
      rw [halg (τ.symm x), RingEquiv.apply_symm_apply]
    rw [hcomp]
    exact hp0

private theorem ggTwE6BigThreeA2_exists_good_lang
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hK : Nat.card K = 4)
    (hσ : ∀ c, σ c = c ^ 2) {h : twistedE6InndiagGL K σ} (hh1 : h ≠ 1) (hh3 : h ^ 3 = 1)
    {E X : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : CFSG.Open.IsElemAbelian 3 E)
    (hXE : X ≤ E) (hfX : twistedE6InndiagConj K σ h ∈ X) (hXcard : Nat.card X = 3 ^ 4)
    (hR : E ≤ (twistedE6InndiagConj K σ).range)
    (htor : E6AdToral (((X.comap (twistedE6InndiagConj K σ)).map
        (twistedE6InndiagGL K σ).subtype).map
          (baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))))) :
    ∃ D : TwE6LineLang K σ 2 h, ∀ γ, IsRoot Tag.E6 γ → D.S.ρ γ = -γ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card]; exact hK.trans (by norm_num))
  let Ω := AlgebraicClosure K
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  let Fr : Ω →+* Ω := iterateFrobenius Ω 2 1
  have hFrLem : ∀ c, Fr c = c ^ (2 ^ 1) := fun c => iterateFrobenius_def 2 1 c
  have hFr2 : ∀ c, Fr c = c ^ 2 := fun c => iterateFrobenius_def 2 1 c
  let XΩ : Subgroup (ModGL Tag.E6 Ω) :=
    ((X.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagGL K σ).subtype).map
      (baseChangeGL (τ := Tag.E6) (algebraMap K Ω))
  have hinj : Function.Injective (twistedE6InndiagConj K σ) :=
    twistedE6InndiagConj_injective Nat.prime_two (le_refl 1) (hK.trans (by norm_num)) σ hσ
  have hXR : XΩ ≤ TwistedDiag.Rgrp Ω Fr :=
    (Subgroup.map_mono (Subgroup.map_subtype_le _)).trans
      (map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two (le_refl 1)
        (hK.trans (by norm_num)) σ hσ Fr hFrLem)
  have hXel : IsElemAbelian 3 XΩ :=
    isElemAbelian_baseChange_comap hinj (CFSG.Open.IsElemAbelian.mono hE hXE)
  have hXcardΩ : Nat.card XΩ = 3 ^ 4 := by
    have h1 : Nat.card XΩ = Nat.card ((X.comap (twistedE6InndiagConj K σ)).map
        (twistedE6InndiagGL K σ).subtype) :=
      Subgroup.card_map_of_injective (baseChangeGL_injective _)
    have h2 : Nat.card ((X.comap (twistedE6InndiagConj K σ)).map
        (twistedE6InndiagGL K σ).subtype) = Nat.card (X.comap (twistedE6InndiagConj K σ)) :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    have h3 : (X.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagConj K σ) = X :=
      Subgroup.map_comap_eq_self (hXE.trans hR)
    have h4 : Nat.card (X.comap (twistedE6InndiagConj K σ)) = Nat.card X := by
      rw [← Subgroup.card_map_of_injective hinj, h3]
    rw [h1, h2, h4, hXcard]
  have hXt : CFSG.StandardType.NoOffTwE6Three.IsToralE6 Ω XΩ := by
    obtain ⟨C, hC, hCtor⟩ := htor
    exact ⟨C⁻¹, inv_mem hC, fun x hx => by simpa using hCtor x hx⟩
  let k := GaloisField 2 (2 * 1)
  haveI : Fintype k := Fintype.ofFinite k
  have hcardk : Fintype.card k = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      CFSG.LieType.Universal.card_galoisField_two_mul 2 1 (le_refl 1), hK]
    norm_num
  let τ : k ≃+* K := FiniteField.ringEquivOfCardEq hcardk
  letI : Algebra k Ω := ((algebraMap K Ω).comp τ.toRingHom).toAlgebra
  haveI : IsAlgClosure k Ω :=
    ⟨IsAlgClosure.isAlgClosed K,
      ggTwE6BigThreeA2_isAlgebraic_of_ringEquiv_algebraMap τ (fun x => rfl)
        (AlgebraicClosure.isAlgebraic K)⟩
  have h30 : (3 : Ω) ≠ 0 :=
    CFSG.HardMathSupport.Lang.E6Descent.three_ne_zero_of_dvd_card_add_one (ℓ := 2) (f := 1)
      (le_refl 1) (by norm_num)
  obtain ⟨ζ, hζ, hζo⟩ := CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.exists_cube_root h30
  obtain ⟨g, hgC, hgn, hgX⟩ :=
    CFSG.StandardType.TwE6LemmaK.ggTwE6ThreeToralTypeMinusOneInput (f := 1) (le_refl 1)
      (by norm_num) Ω Fr hFrLem hζ hζo hXR hXel hXcardΩ hXt
  have hg : twistHom TwistTag.E6 Ω Fr g =
      g * canonicalRep (coxeterSystem Tag.E6) Ω twE6W0 := inv_mul_eq_iff_eq_mul.1 hgn
  have hxX : baseChangeGL (algebraMap K Ω) (h : ModGL TwistTag.E6.tag K) ∈ XΩ := by
    refine Subgroup.mem_map.2 ⟨(h : ModGL TwistTag.E6.tag K), ?_, rfl⟩
    refine Subgroup.mem_map.2 ⟨h, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    exact hfX
  have hmem : baseChangeGL (algebraMap K Ω) (h : ModGL TwistTag.E6.tag K) ∈
      (LangDatum.ofTwist TwistTag.E6 Fr 2 hFr2 twE6W0 hgC hg).torus.map
        (MulAut.conj g).toMonoidHom := by
    obtain ⟨v, hv⟩ := hgX _ hxX
    refine Subgroup.mem_map.2 ⟨rootDiagUnit Tag.E6
      (CFSG.StandardType.TableBExc.E6Three.zetaVec ζ hζ v), ?_, ?_⟩
    · refine (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf).2
        ⟨rootDiagUnit_mem_torusGroup _, ?_⟩
      exact conj_twistE6_rootDiagUnit_of_cube hFr2 (by norm_num) _
        (fun i => CFSG.StandardType.KGL.TwLayer.zetaVec_apply_pow_three hζ _ i)
    · show g * rootDiagUnit Tag.E6
        (CFSG.StandardType.TableBExc.E6Three.zetaVec ζ hζ v) * g⁻¹ =
        baseChangeGL (algebraMap K Ω) (h : ModGL TwistTag.E6.tag K)
      rw [hv]
  have hup : (baseChangeGL (algebraMap K Ω) (h : ModGL TwistTag.E6.tag K)) ^ 3 = 1 := by
    rw [← map_pow, show (h : ModGL TwistTag.E6.tag K) ^ 3 = 1 from by
      rw [← Subgroup.coe_pow, hh3, Subgroup.coe_one], map_one]
  have hu1 : baseChangeGL (algebraMap K Ω) (h : ModGL TwistTag.E6.tag K) ≠ 1 := by
    intro h1
    exact hh1 (Subtype.ext (baseChangeGL_injective (algebraMap K Ω)
      (h1.trans (map_one (baseChangeGL (algebraMap K Ω))).symm)))
  obtain ⟨D, hSD⟩ :=
    ggTwE6BigThreeA2_goodLang_of_lemmaK σ hK hσ Fr hFr2 hgC hg hmem hup hu1
  exact ⟨D, fun γ hγ =>
    ggTwE6BigThreeA2_rho_eq_neg (q := 2) (by norm_num) hFr2 hgC hg D.S hSD hγ⟩

private theorem ggTwE6BigThreeA2_orbit_one_of_rho_neg
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {h : twistedE6InndiagGL K σ}
    (D : TwE6LineLang K σ 2 h)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → D.S.ρ γ = -γ)
    (i : KernelComponent (rootCharHom D.a)) :
    componentOrbitLength D.S.ρ (componentRoots (rootCharHom D.a) i) = 1 := by
  refine componentOrbitLength_eq_one ?_ ?_
  · exact (finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1
  · intro γ hγ
    rw [hρ γ hγ.1.1]
    exact (isRootComponent_componentRoots i).neg_mem γ hγ

private theorem ggTwE6BigThreeA2_false_of_orbit_one
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hK : Nat.card K = 4)
    (hσ : ∀ c, σ c = c ^ 2) {h : twistedE6InndiagGL K σ} (hh1 : h ≠ 1) (hh3 : h ^ 3 = 1)
    (hdim : twE6MatFixDim K σ h = 24) (D : TwE6LineLang K σ 2 h)
    (hone : ∀ i : KernelComponent (rootCharHom D.a),
      componentOrbitLength D.S.ρ (componentRoots (rootCharHom D.a) i) = 1)
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.LieType.Seitz.fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)))) :
    False := by
  obtain ⟨i, hqs, -⟩ := D.exists_rationalComponent hJ
  have h3q : 3 ∣ D.S.D.q + 1 := D.three_dvd_sq (by norm_num)
  have hi6 := (twE6LineLang_orbit_one_or_three D hdim (by norm_num)).1 i
  obtain ⟨ψ, σ', π, hψ, hΨ, hπ⟩ := exists_unitary_frame_of_odd_orbit D.S D.hL3 D.hT D.hap D.h1 i
    hi6 (by rw [hone i]) h3q
  have h216 : Nat.card (rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) ∣ 216 :=
    (rationalComponent_of_unitary_frame_T D.S D.hT i (le_refl 3) hψ hΨ π hπ).2
      (by rw [hone i, pow_one, D.sq_eq])
  obtain ⟨hperf, hsimp, -⟩ := hqs
  haveI := hperf
  haveI := hsimp
  haveI : Nontrivial ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) :=
    (QuotientGroup.mk_surjective (s := Subgroup.center _)).nontrivial
  exact Group.IsPerfect.not_isSolvable _ (isSolvable_of_card_dvd_216 h216)

theorem ggTwE6BigThreeA2_holds :
    GGTwE6BigThreeA2 := by
  intro K _ _ σ hK hσ h hh1 hh3 hdim E hE hcard hfE hR htor J hJ
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card]; exact hK.trans (by norm_num))
  obtain ⟨X, hXE, hfX, hXcard⟩ :=
    ggTwE6BigThreeA2_exists_order34_subgroup σ hK hσ hh1 hh3 hE hcard hfE
  have htorX := ggTwE6BigThreeA2_toral_of_le σ hXE htor
  obtain ⟨D, hρneg⟩ :=
    ggTwE6BigThreeA2_exists_good_lang σ hK hσ hh1 hh3 hE hXE hfX hXcard hR htorX
  exact ggTwE6BigThreeA2_false_of_orbit_one σ hK hσ hh1 hh3 hdim D
    (fun i => ggTwE6BigThreeA2_orbit_one_of_rho_neg σ D hρneg i) hJ

end CFSG.StandardType

end

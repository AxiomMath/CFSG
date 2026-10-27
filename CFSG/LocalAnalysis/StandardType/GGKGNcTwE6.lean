module

public import CFSG.LocalAnalysis.StandardType.GGKGNotCDefs
public import CFSG.LocalAnalysis.StandardType.GGKGNotCLabel
public import CFSG.LocalAnalysis.StandardType.GGKGDefs
import CFSG.LocalAnalysis.StandardType.GGKGNcRank4

public section

namespace CFSG.StandardType.KG

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.RecipeExcLang
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.CanonTriL
open CFSG.LocalAnalysis.GLTheoremA.I141F.Exc
open scoped MatrixGroups commutatorElement

theorem kgNotC_twE6_of_inndiag
    {K : Type}
    [Field K]
    [Finite K]
    {q : TauCeti.PrimePower}
    (hK : Nat.card K = (q.p ^ q.exponent) ^ 2)
    {σ : K ≃+* K}
    (hσ : ∀ (c : K), (σ : K → K) c = c ^ q.p ^ q.exponent)
    {p : ℕ}
    (hp : Nat.Prime p)
    (hp2 : p ≠ 2)
    (hpq : p ≠ q.p)
    (hq2 : q.p = 2)
    {h : ↥(CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagGL K σ)}
    (hp1 : h ^ p = 1)
    (hh1 : h ≠ 1)
    {J : Subgroup ↥(CFSG.LieType.Chevalley.twistedE6RootGroup K σ)}
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        ((CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj K σ :
            ↥(CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagGL K σ) →
              MulAut ↥(CFSG.LieType.Chevalley.twistedE6RootGroup K σ))
          h))) :
    CFSG.StandardType.KG.KGNotCLieType 2 ↥J := by
  classical
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_setup_prime q.prime_p
      q.exponent_pos hp hp2 hpq
  have hmon : MonomialToralAt Tag.E6 p :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_exc
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E6_five
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E7_five
      (by simp) hp hp2
  obtain ⟨LS, a, ι, _hSq, hΦ, hT, hap, h1, hinj, hrange, hconj⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_langSetup_of_inndiag_twE6_of_prime
      q.prime_p q.exponent_pos hK σ hσ hp hpq hp₀ hp₀ℓ hq₀ hmon (twistedE6InndiagConj K σ h)
      (h : ModGL TwistTag.E6.tag K) h.2 (twistedE6InndiagConj_apply h)
      (by rw [← Subgroup.coe_pow, hp1]; rfl) (fun h' => hh1 (Subtype.ext h'))
  have hTame :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime LS hp
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.natCast_ne_zero_algebraicClosure_of_ne
        q.prime_p hp hK hpq) (fun h => absurd h (by decide)) hT hap h1
  obtain ⟨i, hqi, hJR⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup
    LS hp ι hinj hrange _ hconj hT hap h1 hTame hJ
  let eJ : ↥J ≃* ↥(rationalComponent LS.ρ LS.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  have hℓL : ringChar (AlgebraicClosure K) = q.p := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_algebraicClosure]
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow
      (n := q.exponent * 2) q.prime_p (by have := q.exponent_pos; omega)
      (by rw [hK, ← pow_mul])
  have hNG := kgNotC_rationalComponent_E6 LS hp hT hap h1 i hqi
  rw [hℓL, hq2] at hNG
  exact hNG.of_mulEquiv eJ.symm

theorem kgNotC_twE6
    {S : Type}
    [Group S]
    [Finite S]
    {labL : CFSG.Open.GLALabel}
    {β : MulAut S}
    {p : ℕ}
    (hp : Nat.Prime p)
    (hp2 : p ≠ 2)
    (hcen : Eq (α := Subgroup S) (Subgroup.center S) ⊥)
    (hin : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S labL β)
    (hβp : β ^ p = 1)
    (hβ1 : β ≠ 1)
    (ht : labL.tag = CFSG.Assembly.LargeEvenLieTag.twE6)
    {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β)) :
    CFSG.StandardType.KG.KGNotCLieType 2 ↥J := by
  classical
  have hS : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel S (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hβmem : β ∈ innAutDerived S :=
    mem_innAutDerived_of_innDiagKind_exc hcen (Or.inr (Or.inr (Or.inr (Or.inr ht)))) hin
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hS
  obtain ⟨t, r, n⟩ := labL
  simp only at ht
  subst ht
  have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .twistedE6 0 2 n := hM
  have hn : 1 ≤ n := hLM.admissible.2.1
  obtain ⟨-, K₀, _, _, hK₀, σ₀, hσ₀, ⟨e₀⟩⟩ :=
    CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
  let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
  have hq : q.card = 2 ^ n := TauCeti.PrimePower.card_def q
  have hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid := TauCeti.LieTypeIndex.valid_twistedE6 q
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K₀ (by rw [hK₀, hq])
    σ₀ (fun x => by rw [hq]; exact hσ₀ x)
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  let ψ : S ≃* ↥(twistedE6RootGroup K σ) :=
    ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans e₀).trans
      (b.trans eK)
  have hβ : MulAut.congr ψ β ∈ innAutDerived ↥(twistedE6RootGroup K σ) :=
    (mem_innAutDerived_congr ψ).2 hβmem
  have hβ'p : (MulAut.congr ψ β) ^ p = 1 := by rw [← map_pow, hβp, map_one]
  have hβ'1 : MulAut.congr ψ β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr ψ).injective (by rw [h, map_one]))
  have hJ' := isComponentOf_transport ψ β hJ
  have hpq : p ≠ q.p := hp2
  obtain ⟨h, hh, hp1, hh1⟩ :=
    exists_twE6Inndiag_of_mem_innAutDerived (σ := σ) hK hσ hβ hβ'p hβ'1
  rw [← hh] at hJ'
  have hNG := kgNotC_twE6_of_inndiag (σ := σ) hK hσ hp hp2 hpq rfl hp1 hh1 hJ'
  exact hNG.of_mulEquiv (J.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm

theorem kgExcTw_holds
    :
    KGSimpleOn FamExcTw := by
  intro p hp hp2 S _ _ lab α K hF hlab hcen hin hαp hα1 hK k f hk hlabK
  exfalso
  have hfix : ggFixSub α = fixSubgroup α := by ext x; rfl
  rw [hfix] at hK
  have hKo : CFSG.Open.IsComponentOf K (fixSubgroup α) :=
    (CFSG.Assembly.isComponentOf_iff_open).mp hK
  have ht : lab.tag = CFSG.Assembly.LargeEvenLieTag.twE6 := hF
  have hNG := kgNotC_twE6 hp hp2 hcen hin hαp hα1 ht hKo
  exact kg_false_of_notC hk hNG hlabK

end CFSG.StandardType.KG

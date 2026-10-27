module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynTri
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CDynE
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutTriD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynExc

public section

namespace CFSG.StandardType.RCKSmall

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.S265C.DynE (TagLieType)

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie
  CFSG.LocalAnalysis.GLTheoremA.RationalModel
open scoped MatrixGroups

section TagLieTriD4

theorem rck_tagLie_trialityModel
    {q : TauCeti.PrimePower} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (q.p ^ q.exponent) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent)) (hq2 : q.p = 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    {β : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hβmem : β ∈ innAutDerived ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1)
    {J : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    TagLieType (fun t => t = .PSL ∨ t = .PSU) 2 ↥J := by
  classical
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have hpq : p ≠ q.p := by rw [hq2]; exact hp2
  have hβinn : β ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range :=
    sup_le le_rfl (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6outtrid4_commutator_le_range
      q.prime_p q.exponent_pos hK σ hσ) hβmem
  obtain ⟨x, rfl⟩ := hβinn
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective
  have hxp : x ^ p = 1 :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZ (by rw [map_pow, hβp, map_one])
  have hx1 : x ≠ 1 := fun h => hβ1 (by rw [h, map_one])
  have hmon : MonomialToralAt Tag.D4 p := by
    by_cases hp3 : p = 3
    · subst hp3
      exact monomialToralAt_three_of_block a2BlockToral_D4
    · exact monomialToralAt_of_not_dvd hp
        (CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4 hp
          (by have := hp.two_le; omega))
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime q.prime_p q.exponent_pos hp hp2 hpq
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_triD4_of_prime q.prime_p q.exponent_pos hK σ hσ hp hpq hp₀ hp₀ℓ
      hq₀ hmon x hxp hx1
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne q.prime_p hp hK hpq
  have hTame := langSetup_hTame_of_prime S hp hpL (fun h => absurd h (by decide)) hT hap h1
  obtain ⟨i, hqs, hJR⟩ :=
    components_of_langSetup S hp ι hinj hrange (MulAut.conj x) hconj hT hap h1 hTame hJ
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hA := typeAShape_d4Class S hp hpL hTp h1 i
  have hAC : ringChar (AlgebraicClosure K) = 2 := by
    rw [ringChar_algebraicClosure, ← hq2]
    exact ringChar_eq_of_card_eq_pow (n := q.exponent * 3) q.prime_p
      (by have := q.exponent_pos; omega) (by rw [hK, ← pow_mul])
  have hnot : TagLieType (fun t => t = .PSL ∨ t = .PSU) (ringChar (AlgebraicClosure K))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    CFSG.LocalAnalysis.GLTheoremA.S265C.DynE.tagLie_rationalComponent_typeA S hp hT hap h1 i hA
      hqs
  rw [hAC] at hnot
  let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  exact TagLieType.of_mulEquiv hnot eJ.symm

end TagLieTriD4

theorem rck_tagLie_triD4
    {S : Type} [Group S] [Finite S] {labL : GLALabel}
    {β : MulAut S} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥)
    (hin : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S labL β) (hβp : β ^ p = 1)
    (hβ1 : β ≠ 1) (ht : labL.tag = .triD4)
    {J : Subgroup S} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    TagLieType (fun t => t = .PSL ∨ t = .PSU) 2 ↥J := by
  classical
  have hnd : labL.tag ≠ .B2der ∧ labL.tag ≠ .G2der ∧ labL.tag ≠ .twF4der := by
    rw [ht]
    exact ⟨by decide, by decide, by decide⟩
  have hS : HasLabel S (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hβmem : β ∈ innAutDerived S :=
    CFSG.LocalAnalysis.GLTheoremA.I141F.Tri.mem_innAutDerived_of_innDiagKind_of_not_derived
      hcen hnd hin
  have hlam := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.lambda2_of_hasLabel hS
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hS
  obtain ⟨t, r, n⟩ := labL
  simp only at ht
  subst ht
  have hn1 : 1 ≤ n := by
    rw [CFSG.Assembly.LargeEvenInLambda2] at hlam
    exact hlam.1
  have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .trialityD4 0 2 n := hM
  have hce := CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
  obtain ⟨-, K₀, _, _, hK₀, σ₀, hσ₀, ⟨e₀⟩⟩ := hce
  let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
  have hq : q.card = 2 ^ n := TauCeti.PrimePower.card_def q
  have hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid := by simp
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv K₀ (by rw [hK₀, hq])
    σ₀ (fun x => by rw [hq]; exact hσ₀ x)
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eK⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  let ψ : S ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans e₀).trans
      (b.trans eK)
  have hβ'mem : MulAut.congr ψ β ∈ innAutDerived _ := (mem_innAutDerived_congr ψ).2 hβmem
  have hβ'p : (MulAut.congr ψ β) ^ p = 1 := by rw [← map_pow, hβp, map_one]
  have hβ'1 : MulAut.congr ψ β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr ψ).injective (by rw [h, map_one]))
  let ψh : S →* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := ψ.toMonoidHom
  have hJ' : CFSG.Open.IsComponentOf (J.map ψh) (fixSubgroup (MulAut.congr ψ β)) :=
    CFSG.LocalAnalysis.GLTheoremA.CanonTriL.isComponentOf_transport ψ β hJ
  have hnot : TagLieType (fun t => t = .PSL ∨ t = .PSU) 2 ↥(J.map ψh) :=
    rck_tagLie_trialityModel hK σ hσ rfl hp hp2 hβ'mem hβ'p hβ'1 hJ'
  let eJ : ↥(J.map ψh) ≃* ↥J := (J.equivMapOfInjective ψh ψ.injective).symm
  exact TagLieType.of_mulEquiv hnot eJ

end CFSG.StandardType.RCKSmall

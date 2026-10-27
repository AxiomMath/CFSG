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

theorem kgNotC_adjointE
    {τ : CFSG.Blueprint.Chevalley.Tag}
    (hτ : τ = CFSG.Blueprint.Chevalley.Tag.E6 ∨ τ = CFSG.Blueprint.Chevalley.Tag.E7 ∨
      τ = CFSG.Blueprint.Chevalley.Tag.E8)
    {K : Type}
    [Field K]
    [Finite K]
    (hK2 : ringChar K = 2)
    {p : ℕ}
    (hp : Nat.Prime p)
    (hp2 : p ≠ 2)
    {β : MulAut ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K)}
    (hβmem : Membership.mem (γ := Subgroup (MulAut ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K)))
      (CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
        ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K)) β)
    (hβp : β ^ p = 1)
    (hβ1 : β ≠ 1)
    {J : Subgroup ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K)}
    (hJ : CFSG.Open.IsComponentOf J (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β)) :
    CFSG.StandardType.KG.KGNotCLieType 2 ↥J := by
  classical
  obtain ⟨h, _hh, hβh, hp1, hh1⟩ :=
    exists_inndiag_of_mem_innAutDerived_E hτ hp β hβmem hβp hβ1
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcardK⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hcardK
  have hpℓ : p ≠ ringChar K := by rw [hK2]; exact hp2
  have hpK : ¬ p ∣ Nat.card K := fun h' =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow (hK ▸ h')))
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ f.pos hp hp2 hpℓ
  have hp₀K : ¬ p₀ ∣ Nat.card K := fun hd =>
    hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow (hK ▸ hd)))
  have hq₀' : 5 ≤ p₀ ∨ 4 ≤ Nat.card K := by rw [hK]; exact hq₀
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt τ p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with rfl | rfl | rfl <;> simp) hp hp2
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ :=
    single_edge_perfect τ K (by rcases hτ with rfl | rfl | rfl <;> simp)
  obtain ⟨S, a, ι, _hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime (τ := τ) (Or.inr (Or.inr hτ)) hp hpK hp₀ hp₀K hq₀'
      hmon hperf β h (baseChange_mem_adjointGroup_of_mem_inndiag _hh) hβh hp1 hh1
  have hℓL : ringChar (AlgebraicClosure K) = ringChar K := ringChar_algebraicClosure K
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hp (by rw [hℓL]; exact hpℓ.symm)
  have hsmall : τ = .G2 → 5 ≤ p ∨ 4 ≤ S.D.q := fun h' =>
    absurd h' (by rcases hτ with rfl | rfl | rfl <;> decide)
  have hTame := langSetup_hTame_of_prime S hp hpL hsmall hT hap h1
  obtain ⟨i, hqs, hJR⟩ := components_of_langSetup S hp ι hinj hrange β hconj hT hap h1 hTame hJ
  let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  have hch : ringChar (AlgebraicClosure K) = 2 := by rw [hℓL, hK2]
  have hNG := kgNotC_rationalComponent_E hτ S hp hT hap h1 i hqs
  rw [hch] at hNG
  exact hNG.of_mulEquiv eJ.symm

theorem kgNotC_of_adjointEquiv
    {S : Type}
    [Group S]
    [Finite S]
    {τ : CFSG.Blueprint.Chevalley.Tag}
    (hτ : τ = CFSG.Blueprint.Chevalley.Tag.E6 ∨ τ = CFSG.Blueprint.Chevalley.Tag.E7 ∨
      τ = CFSG.Blueprint.Chevalley.Tag.E8)
    {K : Type}
    [Field K]
    [Finite K]
    {n : ℕ}
    (hK : Nat.card K = 2 ^ n)
    (ψ : S ≃* ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K))
    {β : MulAut S}
    (hβmem : Membership.mem (γ := Subgroup (MulAut S))
      (CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived S) β)
    {p : ℕ}
    (hp : Nat.Prime p)
    (hp2 : p ≠ 2)
    (hβp : β ^ p = 1)
    (hβ1 : β ≠ 1)
    {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β)) :
    CFSG.StandardType.KG.KGNotCLieType 2 ↥J := by
  have hK2 : ringChar K = 2 := by
    haveI := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
    exact ringChar.eq K 2
  have hβ'mem : MulAut.congr ψ β ∈ innAutDerived _ := (mem_innAutDerived_congr ψ).2 hβmem
  have hβ'p : (MulAut.congr ψ β) ^ p = 1 := by rw [← map_pow, hβp, map_one]
  have hβ'1 : MulAut.congr ψ β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr ψ).injective (by rw [h, map_one]))
  have hJG := kgNotC_adjointE hτ hK2 hp hp2 hβ'mem hβ'p hβ'1
    (isComponentOf_transport ψ β hJ)
  exact hJG.of_mulEquiv (J.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm

theorem kgNotC_E
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
    (ht : labL.tag = CFSG.Assembly.LargeEvenLieTag.E6 ∨
      labL.tag = CFSG.Assembly.LargeEvenLieTag.E7 ∨ labL.tag = CFSG.Assembly.LargeEvenLieTag.E8)
    {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β)) :
    CFSG.StandardType.KG.KGNotCLieType 2 ↥J := by
  classical
  have hS : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel S (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hβmem : β ∈ innAutDerived S := mem_innAutDerived_of_innDiagKind_exc hcen
    (Or.inr (ht.imp id (Or.imp id Or.inl))) hin
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hS
  obtain ⟨t, r, n⟩ := labL
  simp only at ht
  rcases ht with rfl | rfl | rfl
  · have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .E6 0 2 n := hM
    obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ :=
      CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
    have hZ : Subgroup.center ↥(adjointGroup .E6 K) = ⊥ := center_adjointGroup_eq_bot
    exact kgNotC_of_adjointEquiv (Or.inl rfl) hK
      ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans
        (e₀.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)))
      hβmem hp hp2 hβp hβ1 hJ
  · have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .E7 0 2 n := hM
    obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ :=
      CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
    have hZ : Subgroup.center ↥(adjointGroup .E7 K) = ⊥ := center_adjointGroup_eq_bot
    exact kgNotC_of_adjointEquiv (Or.inr (Or.inl rfl)) hK
      ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans
        (e₀.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)))
      hβmem hp hp2 hβp hβ1 hJ
  · have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .E8 0 2 n := hM
    obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ :=
      CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
    have hZ : Subgroup.center ↥(adjointGroup .E8 K) = ⊥ := center_adjointGroup_eq_bot
    exact kgNotC_of_adjointEquiv (Or.inr (Or.inr rfl)) hK
      ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans
        (e₀.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)))
      hβmem hp hp2 hβp hβ1 hJ

theorem kgExcE_holds
    :
    KGSimpleOn FamExcE := by
  intro p hp hp2 S _ _ lab α K hF hlab hcen hin hαp hα1 hK k f hk hlabK
  exfalso
  have hfix : ggFixSub α = fixSubgroup α := by ext x; rfl
  rw [hfix] at hK
  have hKo : CFSG.Open.IsComponentOf K (fixSubgroup α) :=
    (CFSG.Assembly.isComponentOf_iff_open).mp hK
  have h := kgNotC_E hp hp2 hcen hin hαp hα1
    (hF : lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) hKo
  exact kg_false_of_notC hk h hlabK

end CFSG.StandardType.KG

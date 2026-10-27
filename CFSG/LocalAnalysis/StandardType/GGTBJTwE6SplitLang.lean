module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.LieType.Chevalley.Canonical
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLang
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.LieType.SeitzGeneration
  CFSG.RankThree.Classical2 CFSG.HardMathSupport.Timmesfeld.LangTorus


@[expose] noncomputable def twE6SplitDatum {L : Type} [Field L] (Fr : L →+* L) (q : ℕ)
    (hFr : ∀ c, Fr c = c ^ q) : LangDatum TwistTag.E6.tag L where
  Φ := twistHom TwistTag.E6 L Fr
  q := q
  n := canonicalRep (coxeterSystem TwistTag.E6.tag) L 1
  g0 := 1
  steinberg := ⟨Fr, hFr, diagramMap TwistTag.E6 L, Or.inr ⟨TwistTag.E6, rfl, rfl⟩, fun _ => rfl⟩
  n_weyl := ⟨1, rfl⟩
  g0_mem := one_mem _
  lang := by rw [map_one, one_mul, canonicalRep_one]

theorem twE6SplitDatum_step_pinnedX_one {L : Type} [Field L] [CharP L 2] (Fr : L →+* L) (q : ℕ)
    (hFr : ∀ c, Fr c = c ^ q) {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) :
    (twE6SplitDatum Fr q hFr).step (pinnedX TwistTag.E6.tag L γ 1) =
      pinnedX TwistTag.E6.tag L (permLattice TwistTag.E6.perm γ) 1 := by
  obtain ⟨ε, hε, h⟩ := diagramMap_conj_pinnedX (K := L) TwistTag.E6 hγ
  have e1 := CFSG.RankThree.Chevalley.eq_one_of_mul_self_eq_one_of_charTwo hε
  have hn : (twE6SplitDatum Fr q hFr).n = 1 := canonicalRep_one _ _
  have h1 : (twE6SplitDatum Fr q hFr).step (pinnedX TwistTag.E6.tag L γ 1) =
      diagramMap TwistTag.E6 L * Units.map (entrywiseHom Fr) (pinnedX TwistTag.E6.tag L γ 1) *
        (diagramMap TwistTag.E6 L)⁻¹ := by
    simp only [LangDatum.step, MonoidHom.comp_apply, MulAut.conj_apply, hn, one_mul, inv_one,
      mul_one]
    rfl
  rw [h1, units_map_entrywiseHom_pinnedX, map_one, h, e1, one_mul]

theorem exists_ggTBJTwE6SplitSetup
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hp : p.Prime)
    (hq : 5 ≤ p ∨ 2 ≤ n) (hpq : ¬ p ∣ 2 ^ n) :
    ∃ (S : LangSetup TwistTag.E6.tag (AlgebraicClosure K) p)
      (e : twistedE6RootGroup K σ ≃* S.Γ),
      (∀ x, (e x : ModGL TwistTag.E6.tag (AlgebraicClosure K)) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K)) ∧
      (∀ γ, IsRoot TwistTag.E6.tag γ → S.ρ γ = permLattice TwistTag.E6.perm γ) ∧
      S.D.q = 2 ^ n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  let Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius (AlgebraicClosure K) 2 n
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  let D := twE6SplitDatum Fr (2 ^ n) hFr
  have hΦ : D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr := rfl
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved TwistTag.E6.tag (AlgebraicClosure K) D
  have hn0 : n ≠ 0 := by omega
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : AlgebraicClosure K) = 0 := by
    constructor
    · change IsPrimePow (2 ^ n)
      exact Nat.prime_two.isPrimePow.pow hn0
    · change (((2 ^ n : ℕ)) : AlgebraicClosure K) = 0
      exact (CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 (2 ^ n)).2 (dvd_pow_self 2 hn0)
  have hfin : Finite D.model :=
    finite_model_twistedE6 (ℓ := 2) Nat.prime_two hn hK hσ hFr D hΦ
  let S : LangSetup TwistTag.E6.tag (AlgebraicClosure K) p :=
    D.toSetup p ρ hρ hp (hq.imp_right fun h => show 4 ≤ 2 ^ n from calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h) hqpow hpq hfin
  let e : twistedE6RootGroup K σ ≃* S.Γ :=
    twistedE6EquivΓ (ℓ := 2) Nat.prime_two hn hK hσ hFr D hΦ
  refine ⟨S, e, fun x => ?_, ?_, rfl⟩
  · have h := coe_twistedE6EquivΓ (ℓ := 2) Nat.prime_two hn hK hσ hFr D hΦ x
    have hg0 : D.g0 = 1 := rfl
    rw [hg0, inv_one, one_mul, mul_one] at h
    exact h
  · intro γ hγ
    have hγ' : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm γ) :=
      (isRoot_latticePerm_iff (π := TwistTag.E6.perm) TwistTag.E6.cartan_perm γ).2 hγ
    have hmem : D.step (pinnedX TwistTag.E6.tag (AlgebraicClosure K) γ 1) ∈
        rootSubgroup TwistTag.E6.tag (AlgebraicClosure K) (ρ γ) := by
      rw [← hρ.map_rootSubgroup γ hγ]
      exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ⟨1, rfl⟩)
    rw [twE6SplitDatum_step_pinnedX_one Fr (2 ^ n) hFr hγ] at hmem
    exact (eq_of_pinnedX_one_mem_rootSubgroup hγ' ((hρ.isRoot_iff γ).2 hγ) hmem).symm

end CFSG.StandardType

end

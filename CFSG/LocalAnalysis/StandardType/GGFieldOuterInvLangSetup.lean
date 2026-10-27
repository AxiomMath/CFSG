module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidSplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwLangConsumers
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Adj
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.K133H.G2Plane
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Sec21 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Open (IsElemAbelian)

private theorem ggPA2_isPrimePow_card (K : Type) [Field K] [Finite K] :
    IsPrimePow (Nat.card K) := by
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.isPrimePow_card K

private theorem ggPA2_cast_card_eq_zero (K : Type) [Field K] [Finite K] :
    ((Nat.card K : ℕ) : AlgebraicClosure K) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  rw [← map_natCast (algebraMap K (AlgebraicClosure K)), Nat.card_eq_fintype_card,
    FiniteField.cast_card_eq_zero K, map_zero]

private theorem ggPA2_not_dvd_card (K : Type) [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card K := by
  intro h
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hf] at h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))

theorem exists_langSetup_conj_of_prime_bound
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type) [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hbound : 5 ≤ p ∨ 4 ≤ Nat.card K)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup τ} {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (b : adjointGroup τ K) (hbp : b ^ p = 1)
    (hbT : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (b : ModGL τ K) * g0 ∈
      (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0).torus) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) p) (a : Fin τ.rank → (AlgebraicClosure K)ˣ)
      (ι : adjointGroup τ K →* ModGL τ (AlgebraicClosure K)),
      S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0 ∧ rootDiagUnit τ a ∈ S.E ∧
      (∀ i, a i ^ p = 1) ∧ Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι c = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL τ K) * g0) ∧
      ∀ c, ι (b * c * b⁻¹) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  let D : LangDatum τ (AlgebraicClosure K) :=
    LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0
  let ι₀ : adjointGroup τ K →* ModGL τ (AlgebraicClosure K) :=
    (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup τ K).subtype
  let u₀ : ModGL τ (AlgebraicClosure K) :=
    baseChangeGL (algebraMap K (AlgebraicClosure K)) (b : ModGL τ K)
  have hd := CFSG.HardMathSupport.Timmesfeld.CrossChar.langDescent_ofFrobenius
    hτ w K hFr hg0C hg0
  have hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom := hd.Γ_eq
  have hfin : Finite D.model := hd.finite_model
  have hι₀ : Function.Injective ι₀ :=
    (baseChangeGL_injective (algebraMap K (AlgebraicClosure K))).comp
      (Subgroup.subtype_injective _)
  have hmem : u₀ ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom := by
    refine ⟨D.g0⁻¹ * u₀ * D.g0, hbT, ?_⟩
    change MulAut.conj D.g0 (D.g0⁻¹ * u₀ * D.g0) = u₀
    rw [MulAut.conj_apply]
    group
  have hup : u₀ ^ p = 1 := by
    have h := map_pow ι₀ b p
    rw [hbp, map_one] at h
    exact h.symm
  have hβ : ∀ c : adjointGroup τ K, ι₀ (b * c * b⁻¹) = u₀ * ι₀ c * u₀⁻¹ := by
    intro c
    rw [map_mul, map_mul, map_inv]
    rfl
  obtain ⟨y, hy, hyu⟩ := hmem
  have hyu' : y = D.g0⁻¹ * u₀ * D.g0 := by
    have h : D.g0 * y * D.g0⁻¹ = u₀ := hyu
    rw [← h]
    group
  obtain ⟨a, ha⟩ :=
    exists_rootDiagUnit_eq_of_mem_torusGroup
      (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hy).1
  have hyp : y ^ p = 1 := by
    have h := conj_pow (a := D.g0⁻¹) (b := u₀) (i := p)
    rw [inv_inv] at h
    rw [hyu', h, hup]
    group
  have hap : ∀ i, a i ^ p = 1 := by
    have h1 : rootDiagUnit τ (a ^ p) = rootDiagUnit τ 1 := by
      have h2 : rootDiagUnit τ (a ^ p) = rootDiagUnit τ a ^ p :=
        (rootDiagUnitHom τ (AlgebraicClosure K)).map_pow a p
      rw [h2, ← ha, hyp, CFSG.LieType.Chevalley.rootDiagUnit_one]
    have h3 : a ^ p = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
    exact fun i => congrFun h3 i
  have hq : 5 ≤ p ∨ 4 ≤ D.q := hbound
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : AlgebraicClosure K) = 0 :=
    ⟨ggPA2_isPrimePow_card K, ggPA2_cast_card_eq_zero K⟩
  have hpq : ¬ p ∣ D.q := ggPA2_not_dvd_card K hp hp2
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved τ (AlgebraicClosure K) D
  let ι : adjointGroup τ K →* ModGL τ (AlgebraicClosure K) :=
    (MulAut.conj D.g0⁻¹).toMonoidHom.comp ι₀
  have hι : ∀ c : adjointGroup τ K,
      ι c = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL τ K) * g0 := by
    intro c
    change (MulAut.conj D.g0⁻¹) (ι₀ c) = _
    rw [MulAut.conj_apply, inv_inv]
    rfl
  have hΓr : ι.range = D.Γ := by
    rw [hΓ]
    exact MonoidHom.range_comp (MulAut.conj D.g0⁻¹).toMonoidHom ι₀
  have hyΓ : y ∈ D.Γ := by
    rw [hΓ]
    refine ⟨ι₀ b, ⟨b, rfl⟩, ?_⟩
    change MulAut.conj D.g0⁻¹ (ι₀ b) = y
    rw [MulAut.conj_apply, inv_inv]
    exact hyu'.symm
  refine ⟨D.toSetup p ρ hρ hp hq hqpow hpq hfin, a, ι, rfl, ?_, hap,
    (MulAut.conj D.g0⁻¹).injective.comp hι₀, ?_, hι, ?_⟩
  · show rootDiagUnit τ a ∈ D.torsion p
    rw [LangDatum.mem_torsion, Subgroup.mem_inf]
    exact ⟨⟨ha ▸ hy, ha ▸ hyΓ⟩, ha ▸ hyp⟩
  · show ι.range = D.Γ
    exact hΓr
  · intro c
    change (MulAut.conj D.g0⁻¹) (ι₀ (b * c * b⁻¹)) =
      rootDiagUnit τ a * (MulAut.conj D.g0⁻¹) (ι₀ c) * (rootDiagUnit τ a)⁻¹
    rw [hβ c, MulAut.conj_apply, MulAut.conj_apply, ← ha, hyu']
    group

theorem exists_langSetup_conj
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK4 : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup τ} {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (b : adjointGroup τ K) (hbp : b ^ p = 1)
    (hbT : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (b : ModGL τ K) * g0 ∈
      (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0).torus) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) p) (a : Fin τ.rank → (AlgebraicClosure K)ˣ)
      (ι : adjointGroup τ K →* ModGL τ (AlgebraicClosure K)),
      S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0 ∧ rootDiagUnit τ a ∈ S.E ∧
      (∀ i, a i ^ p = 1) ∧ Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι c = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL τ K) * g0) ∧
      ∀ c, ι (b * c * b⁻¹) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹ := by
  have hτ' : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inl h
  exact exists_langSetup_conj_of_prime_bound hτ' K hp hp2 (Or.inr hK4)
    hFr hg0C hg0 b hbp hbT

end CFSG.StandardType

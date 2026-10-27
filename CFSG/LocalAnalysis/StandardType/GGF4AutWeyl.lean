module

public import CFSG.LocalAnalysis.StandardType.GGAutomizerMap
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeylTorus
public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankE6
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Three
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoRank
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Torus
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneCoord
public import CFSG.RankThree.Chevalley.G2F4FiniteFieldFixedMatrices
public import CFSG.LieType.Chevalley.GraphFixedData
public import Mathlib.FieldTheory.Finite.Extension
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames
public import CFSG.HardMathSupport.Lang.AnisoE6.CatBridge
public import CFSG.HardMathSupport.Lang.AnisoE6.E6InF4
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.SeitzGeneration.ExcTwistedClasses
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.CTP.SeitzFineG2
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.StronglyEmbedded.ParityCriterion
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.SeitzGeneration
open CFSG.Open (IsElemAbelian)

namespace F4AutWeyl

theorem autTriple_of_map_congr {G₁ G₂ : Type} [Group G₁] [Group G₂] {p : ℕ}
    {B : Subgroup G₁} {B' : Subgroup G₂} (e : ↥B ≃* ↥B') {A : Subgroup (MulAut ↥B)}
    (h : 2 ^ 4 * Nat.factorial 4 ≤ Nat.card (A.map (MulAut.congr e).toMonoidHom) ∧
      GGReflGenerated p (A.map (MulAut.congr e).toMonoidHom) ∧
      ∀ b : ↥B', (∀ φ ∈ A.map (MulAut.congr e).toMonoidHom, φ b = b) → b = 1) :
    2 ^ 4 * Nat.factorial 4 ≤ Nat.card A ∧ GGReflGenerated p A ∧
      ∀ b : ↥B, (∀ φ ∈ A, φ b = b) → b = 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  set c := (MulAut.congr e).toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.congr e).injective
  have hcsymm : ∀ φ, MulAut.congr e.symm (c φ) = φ := fun φ =>
    MulEquiv.ext fun b => by simp [hc, MulAut.congr_apply]
  have hrefl : ∀ φ : MulAut ↥B, GGIsReflection p (c φ) ↔ GGIsReflection p φ := by
    intro φ
    constructor
    · intro hr
      rw [← hcsymm φ]
      exact ggIsReflection_congr e.symm hr.1 hr.2
    · intro hr
      exact ggIsReflection_congr e hr.1 hr.2
  refine ⟨?_, ?_, fun b hb => ?_⟩
  · rwa [Subgroup.card_map_of_injective hcinj] at h1
  · refine le_antisymm (fun φ hφ => ?_) ((Subgroup.closure_le _).2 fun φ hφ => hφ.1)
    have hcφ : c φ ∈ A.map c := Subgroup.mem_map_of_mem c hφ
    rw [h2] at hcφ
    have hS : {ψ | ψ ∈ A.map c ∧ GGIsReflection p ψ} =
        c '' {φ | φ ∈ A ∧ GGIsReflection p φ} := by
      ext ψ
      constructor
      · rintro ⟨⟨φ₁, hφ₁, rfl⟩, hr⟩
        exact ⟨φ₁, ⟨hφ₁, (hrefl φ₁).1 hr⟩, rfl⟩
      · rintro ⟨φ₁, ⟨hφ₁, hr⟩, rfl⟩
        exact ⟨Subgroup.mem_map_of_mem c hφ₁, (hrefl φ₁).2 hr⟩
    rw [hS, ← MonoidHom.map_closure] at hcφ
    obtain ⟨φ₁, hφ₁, hφ₁φ⟩ := hcφ
    rwa [hcinj hφ₁φ] at hφ₁
  · have h4 : e b = 1 := h3 (e b) fun ψ hψ => by
      obtain ⟨φ, hφ, rfl⟩ := hψ
      change e (φ (e.symm (e b))) = e b
      rw [MulEquiv.symm_apply_apply, hb φ hφ]
    exact e.injective (h4.trans (map_one e).symm)

theorem exists_fixed_mul_inv {Γ : Type*} [Group Γ] (σ : Γ →* Γ) (hσ : ∀ x, σ (σ x) = x)
    {E : Subgroup Γ} (hE : ∀ e ∈ E, σ e = e) {N : ℕ}
    (hodd : ∀ c ∈ Subgroup.centralizer (E : Set Γ), c ^ (2 * N + 1) = 1) {n : Γ}
    (hn : n ∈ Subgroup.normalizer (E : Set Γ)) :
    ∃ z ∈ Subgroup.centralizer (E : Set Γ), σ (n * z⁻¹) = n * z⁻¹ := by
  set c := n⁻¹ * σ n with hc
  have hcC : c ∈ Subgroup.centralizer (E : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h1 : n * e * n⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 hn e).1 he
    have h2 : σ (n * e * n⁻¹) = n * e * n⁻¹ := hE _ h1
    rw [map_mul, map_mul, map_inv, hE e he] at h2
    calc e * (n⁻¹ * σ n) = n⁻¹ * (n * e * n⁻¹) * σ n := by group
      _ = n⁻¹ * (σ n * e * (σ n)⁻¹) * σ n := by rw [h2]
      _ = n⁻¹ * σ n * e := by group
  have hσc : σ c = c⁻¹ := by rw [hc, map_mul, map_inv, hσ, mul_inv_rev, inv_inv]
  have hσn : σ n = n * c := by rw [hc, mul_inv_cancel_left]
  refine ⟨c ^ N, Subgroup.pow_mem _ hcC N, ?_⟩
  rw [map_mul, map_inv, map_pow, hσc, inv_pow, inv_inv, hσn, mul_assoc]
  congr 1
  rw [← pow_succ', eq_inv_iff_mul_eq_one, ← pow_add]
  convert hodd c hcC using 2
  ring

private theorem eq_one_or_two_of_four_le_degCount {e : ℕ} (h : 4 ≤ degCount .E6 e) :
    e = 1 ∨ e = 2 := by
  have h30 := le_thirty_of_degCount_pos (Or.inr (Or.inl rfl)) (lt_of_lt_of_le (by norm_num) h)
  interval_cases e <;> first | exact Or.inl rfl | exact Or.inr rfl | (exfalso; revert h; decide)

theorem dvd_card_sq_sub_one_of_card_F4
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 4) :
    p ∣ Nat.card K ^ 2 - 1 := by
  set e := orderOf ((Nat.card K : ℕ) : ZMod p) with he
  have hinj : Function.Injective (ExcHighThree.embE6F4 K) :=
    Subtype.val_injective.comp (ExcHighThree.isoE6F4 K).injective
  have hle := rankLE_E6 hp hp2 he.symm (E.map (ExcHighThree.embE6F4 K))
    (TableB.isElemAbelian_map hE _)
  rw [Subgroup.card_map_of_injective hinj, hcard] at hle
  have h4 : 4 ≤ degCount .E6 e := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
  rw [dvd_pow_sub_one_iff_orderOf Nat.card_pos he.symm]
  rcases eq_one_or_two_of_four_le_degCount h4 with h | h <;> rw [h]
  norm_num

end F4AutWeyl

theorem ggAutomizer_adjointF4_of_card
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 4) :
    2 ^ 4 * Nat.factorial 4 ≤ Nat.card (ggAutomizer ⊤ E) ∧ GGReflGenerated p (ggAutomizer ⊤ E) ∧
      ∀ e : ↥E, (∀ φ ∈ ggAutomizer ⊤ E, φ e = e) → e = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq2 : p ∣ Nat.card K ^ 2 - 1 := F4AutWeyl.dvd_card_sq_sub_one_of_card_F4 hp hp2 hE hcard
  let L := FiniteField.Extension K 2 2
  have hLK : Nat.card L = Nat.card K ^ 2 := FiniteField.natCard_extension K 2 2
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have hpL : p ∣ Nat.card L - 1 := hLK ▸ hq2
  let Fr : L →+* L := (FiniteField.Extension.frob K 2 2).toRingEquiv.toRingHom
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => FiniteField.Extension.frob_apply K 2 2
  have hFr2 : ∀ c, Fr (Fr c) = c := by
    intro c
    have := Fintype.ofFinite L
    rw [hFr, hFr, ← pow_mul, ← sq, ← hLK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hbij : Function.Bijective Fr := (FiniteField.Extension.frob K 2 2).toRingEquiv.bijective
  have hfix := frobenius_fixed_eq_map_of_bijective (τ := .F4) (Or.inr rfl) Fr hFr hbij
  let σ : adjointGroup .F4 L →* adjointGroup .F4 L := TableBF4Two.adjointMap Fr
  have hσ : ∀ x : adjointGroup .F4 L, ((σ x : adjointGroup .F4 L) : ModGL .F4 L) =
      Units.map (entrywiseHom Fr) (x : ModGL .F4 L) := fun x => Units.ext rfl
  have hσ2 : ∀ x, σ (σ x) = x := by
    intro x
    refine Subtype.ext (Units.ext ?_)
    rw [hσ, hσ]
    change entrywise Fr (entrywise Fr _) = _
    rw [entrywise_entrywise, show Fr.comp Fr = RingHom.id L from RingHom.ext hFr2, entrywise_id]
  set φ := TableBF4Two.adjointMap (algebraMap K L) with hφ
  have hφinj : Function.Injective φ := TableBF4Two.adjointMap_injective _
  have hφfix : ∀ k, σ (φ k) = φ k := by
    intro k
    have hk : ((φ k : adjointGroup .F4 L) : ModGL .F4 L) ∈
        adjointGroup .F4 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) :=
      hfix ▸ ⟨(k : ModGL .F4 K), k.2, rfl⟩
    exact Subtype.ext ((hσ _).trans hk.2)
  have hσfix : ∀ x, σ x = x → ∃ k, φ k = x := by
    intro x hx
    have hx' : (x : ModGL .F4 L) ∈
        adjointGroup .F4 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) :=
      ⟨x.2, (hσ x).symm.trans (congrArg Subtype.val hx)⟩
    rw [hfix] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  have hE' : IsElemAbelian p (E.map φ) := TableB.isElemAbelian_map hE φ
  have hcard' : Nat.card (E.map φ) = p ^ 4 := by
    rw [Subgroup.card_map_of_injective hφinj, hcard]
  obtain ⟨g, hg⟩ := ggF4ToralRankInput_of_three hp hp2 hpL (fun _ => ggF4ThreeRankInput_holds)
    (E.map φ) hE' hcard'.ge
  set V := TableBF4.torusPow L p with hV
  have hmemV : ∀ y, y ∈ V ↔ g⁻¹ * y * g ∈ E.map φ := by
    intro y
    rw [← hg, Subgroup.mem_map_equiv]
    rfl
  have hCV := F4AutWeyl.F4_adjointGroup_inf_centralizer_torusPow_of_ne_two (k := L) hp hp2
    (by rw [Nat.card_units]; exact hpL)
  have hcent : ∀ x ∈ Subgroup.centralizer ((E.map φ : Subgroup (adjointGroup .F4 L)) :
      Set (adjointGroup .F4 L)), ((g * x * g⁻¹ : adjointGroup .F4 L) : ModGL .F4 L) ∈
        torusGroup .F4 L := by
    intro x hx
    rw [← hCV]
    refine ⟨(g * x * g⁻¹).2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    have hhV : (⟨h, torusGroup_le_adjointGroup_F4 hh.1⟩ : adjointGroup .F4 L) ∈ V :=
      ⟨hh.1, Subtype.ext (by rw [Subgroup.coe_pow, hh.2, OneMemClass.coe_one])⟩
    have h1 := Subgroup.mem_centralizer_iff.1 hx _ ((hmemV _).1 hhV)
    have h2 : (⟨h, torusGroup_le_adjointGroup_F4 hh.1⟩ : adjointGroup .F4 L) * (g * x * g⁻¹) =
        (g * x * g⁻¹) * ⟨h, torusGroup_le_adjointGroup_F4 hh.1⟩ := by
      calc _ = g * ((g⁻¹ * ⟨h, torusGroup_le_adjointGroup_F4 hh.1⟩ * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * ⟨h, torusGroup_le_adjointGroup_F4 hh.1⟩ * g)) * g⁻¹ := by rw [h1]
        _ = _ := by group
    exact congrArg Subtype.val h2
  obtain ⟨N, hN⟩ : ∃ N, Nat.card L - 1 = 2 * N + 1 := by
    have := Fintype.ofFinite K
    obtain ⟨f, -, hf⟩ := FiniteField.card K 2
    have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
    have hf1 : 1 ≤ (f : ℕ) := f.pos
    have h4 : 4 ≤ Nat.card L := by
      rw [hLK, hK, ← pow_mul]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ ((f : ℕ) * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ∣ Nat.card L := by
      rw [hLK, hK]
      exact dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    obtain ⟨m, hm⟩ := h2
    exact ⟨m - 1, by omega⟩
  have hodd : ∀ c ∈ Subgroup.centralizer ((E.map φ : Subgroup (adjointGroup .F4 L)) :
      Set (adjointGroup .F4 L)), c ^ (2 * N + 1) = 1 := by
    intro c hc
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hcent c hc)
    have h1 : (g * c * g⁻¹) ^ (Nat.card L - 1) = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, ha, OneMemClass.coe_one, rootDiagUnit_pow]
      convert rootDiagUnit_one (τ := .F4) (K := L)
      funext i
      rw [Pi.pow_apply, Pi.one_apply, ← Nat.card_units, pow_card_eq_one']
    rw [conj_pow, conj_eq_one_iff, hN] at h1
    exact h1
  set ψ := (MulAut.conj g).toMonoidHom.comp φ with hψ
  have hψinj : Function.Injective ψ := (MulAut.conj g).injective.comp hφinj
  have hEV : E.map ψ = V := by rw [hψ, ← Subgroup.map_map]; exact hg
  have hW : ∀ w : WeylGroup .F4, ∃ h ∈ (⊤ : Subgroup (adjointGroup .F4 K)).map ψ,
      ∃ t ∈ torusGroup .F4 L, (h : ModGL .F4 L) = t * canonicalRep (coxeterSystem .F4) L w := by
    intro w
    set nw : adjointGroup .F4 L :=
      ⟨canonicalRep (coxeterSystem .F4) L w, canonicalRep_mem_adjointGroup _ L w⟩ with hnw
    have hnwV := F4AutWeyl.canonicalRep_mem_normalizer_torusPow_F4 L p w
    have hn : g⁻¹ * nw * g ∈ Subgroup.normalizer ((E.map φ : Subgroup (adjointGroup .F4 L)) :
        Set (adjointGroup .F4 L)) := by
      refine Subgroup.mem_normalizer_iff.2 fun x => ?_
      have e1 : x ∈ E.map φ ↔ g * x * g⁻¹ ∈ V := by
        rw [hmemV, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
      have e2 : g⁻¹ * (nw * (g * x * g⁻¹) * nw⁻¹) * g =
          g⁻¹ * nw * g * x * (g⁻¹ * nw * g)⁻¹ := by group
      rw [e1, Subgroup.mem_normalizer_iff.1 hnwV (g * x * g⁻¹),
        hmemV (nw * (g * x * g⁻¹) * nw⁻¹), e2]
    obtain ⟨z, hz, hσz⟩ := F4AutWeyl.exists_fixed_mul_inv σ hσ2
      (fun e he => by obtain ⟨k, -, rfl⟩ := he; exact hφfix k) hodd hn
    obtain ⟨k, hk⟩ := hσfix _ hσz
    have htz := hcent _ (Subgroup.inv_mem _ hz)
    refine ⟨ψ k, ⟨k, Subgroup.mem_top k, rfl⟩, canonicalRep (coxeterSystem .F4) L w *
        ((g * z⁻¹ * g⁻¹ : adjointGroup .F4 L) : ModGL .F4 L) *
        (canonicalRep (coxeterSystem .F4) L w)⁻¹,
      (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := L) w) _).1 htz, ?_⟩
    have h1 : ψ k = nw * (g * z⁻¹ * g⁻¹) := by
      change g * φ k * g⁻¹ = _
      rw [hk]
      group
    rw [h1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hnw]
    group
  have hB := F4AutWeyl.ggAutomizer_torusPow_F4 hp hp2 hpL hW
  rw [F4AutWeyl.ggAutomizer_map_eq hψinj ⊤ E hEV] at hB
  exact F4AutWeyl.autTriple_of_map_congr _ hB

end CFSG.StandardType

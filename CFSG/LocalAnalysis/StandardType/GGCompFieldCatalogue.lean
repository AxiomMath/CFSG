module

public import CFSG.LocalAnalysis.StandardType.GGCompFieldLieModel
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxAll
public import CFSG.LocalAnalysis.StandardType.GGLayerChevAdjoint
public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E6Aux.Diag
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Diag
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CatTw
public import CFSG.LieType.Chevalley.TwistedE6RootGroupPerfect
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeLift
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSp
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxSymplectic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
public import CFSG.RankThree.PartOne.KEXC.Basic
public import CFSG.RankThree.PartOne.TCX.Ree.Perm

public section

namespace CFSG.StandardType

open CFSG.Open TauCeti CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived inner_le_innAutDerived
  commutator_le_innAutDerived)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie (fieldSize suzRee compRel compRelC)
open CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.TwistedE6

theorem ggCompFieldDataQ_of_catalogue
    {S : Type} [Group S] [Finite S] (d : ValidLieTypeIndex)
    (hd : d.1.characteristic = 2) (hdsr : ¬ suzRee d.1) {k : ℕ} (hk : fieldSize d.1 = 2 ^ k)
    (e : S ≃* (CFSGIndex.lie d).Group) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {β : MulAut S}
    (hβ : β ∈ innAutDerived S) (hβp : β ^ p = 1) {C : Subgroup S}
    (hC : IsComponentOf C (fixSubgroup β)) : GGCompFieldDataQ (fieldSize d.1) C := by
  classical
  by_cases hβ1 : β = 1
  · subst hβ1
    have hfix : fixSubgroup (1 : MulAut S) = ⊤ := by
      ext x
      simp [mem_fixSubgroup]
    rw [hfix] at hC
    haveI := (CFSG.Assembly.lie_finite_simple d).2
    haveI : IsSimpleGroup S := e.isSimpleGroup
    have hnc : ∃ a b : S, a * b ≠ b * a := by
      by_contra hcomm
      push_neg at hcomm
      have htop : Subgroup.center ↥C = ⊤ :=
        eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hcomm g x)
      haveI := hC.2.2.2
      obtain ⟨a, b, hab⟩ := exists_pair_ne (↥C ⧸ Subgroup.center ↥C)
      apply hab
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      exact QuotientGroup.eq.2 (by rw [htop]; trivial)
    have hZ : Subgroup.center S = ⊥ :=
      CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnc
    have hQS : CFSG.Open.IsQuasisimple S := by
      have h :=
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_of_isSimpleGroup
          (inferInstance : IsSimpleGroup S) hnc
      exact ⟨h.1.commutator_eq_top, h.2.1⟩
    have hCt : C = ⊤ :=
      CFSG.LocalAnalysis.GLTheoremA.eq_top_of_isComponentOf_of_isQuasisimple hQS hC
    subst hCt
    have hZC : Subgroup.center ↥(⊤ : Subgroup S) = ⊥ := by
      rw [← Subgroup.map_center_eq (Subgroup.topEquiv (G := S)).symm, hZ, Subgroup.map_bot]
    let φ : ↥(⊤ : Subgroup S) ⧸ Subgroup.center ↥(⊤ : Subgroup S) ≃* (CFSGIndex.lie d).Group :=
      ((QuotientGroup.quotientMulEquivOfEq hZC).trans QuotientGroup.quotientBot).trans
        (Subgroup.topEquiv.trans e)
    exact ggCompFieldDataQ_of_compRelC hC.2.2 hd hdsr hk
      (i := .lie d) (Or.inl ⟨rfl, ⟨1, le_rfl, (pow_one _).symm⟩, id⟩) φ
  · have hpq : p ≠ d.1.characteristic := by rw [hd]; exact hp2
    have hI : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.CompIdxAt p d.1 S :=
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.compIdxAt_of_mulEquiv e.symm
        (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.lieCompIdx_all d p hp hp2 hpq trivial)
    obtain ⟨i, ⟨φ⟩, hrel⟩ := hI β hβ hβp hβ1 C hC
    exact ggCompFieldDataQ_of_compRelC hC.2.2 hd hdsr hk hrel φ

theorem ggExcCompFieldInputQ
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (s : ↥(adjointGroup τ K)) (hs : s ^ p = 1) (C : Subgroup ↥(adjointGroup τ K))
    (hC : IsComponentOf C (Subgroup.centralizer ({s} : Set ↥(adjointGroup τ K)))) :
    GGCompFieldDataQ (Nat.card K) C := by
  haveI := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  let q₀ : PrimePower := ⟨2, n, Nat.prime_two, n.pos⟩
  have hk : Nat.card K = q₀.card := by
    rw [Nat.card_eq_fintype_card, hn, PrimePower.card_def]
  have hq₀ : q₀.card = 2 ^ (n : ℕ) := PrimePower.card_def q₀
  have hv0 : ∀ c : LieTypeIndex, c.InStandardRange → ¬ c.IsDuplicateRepresentative →
      c.Valid := fun c h1 h2 => (LieTypeIndex.valid_iff c).2 ⟨h1, h2⟩
  haveI : Finite ↥(adjointGroup τ K) := inferInstance
  have hβ : MulAut.conj s ∈ innAutDerived ↥(adjointGroup τ K) :=
    inner_le_innAutDerived _ ⟨s, rfl⟩
  have hβp : (MulAut.conj s) ^ p = 1 := by rw [← map_pow, hs, map_one]
  rw [← CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_fixSubgroup_conj] at hC
  rw [hk]
  rcases hτ with rfl | rfl | rfl
  · have hv : (LieTypeIndex.F4 q₀).Valid := hv0 _ (by
      rw [LieTypeIndex.inStandardRange_iff]; trivial) (by
      rw [LieTypeIndex.isDuplicateRepresentative_iff]; exact fun h => h)
    obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_adjointGroup_catEquiv
      (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).f4 hv hk
    exact ggCompFieldDataQ_of_catalogue ⟨_, hv⟩ (LieTypeIndex.characteristic_F4 q₀) (fun h => h)
      hq₀ e hp hp2 hβ hβp hC
  · have hv : (LieTypeIndex.E7 q₀).Valid := LieTypeIndex.valid_E7 q₀
    obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_adjointGroup_catEquiv
      (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e7 hv hk
    exact ggCompFieldDataQ_of_catalogue ⟨_, hv⟩ (LieTypeIndex.characteristic_E7 q₀) (fun h => h)
      hq₀ e hp hp2 hβ hβp hC
  · have hv : (LieTypeIndex.E8 q₀).Valid := hv0 _ (by
      rw [LieTypeIndex.inStandardRange_iff]; trivial) (by
      rw [LieTypeIndex.isDuplicateRepresentative_iff]; exact fun h => h)
    obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_adjointGroup_catEquiv
      (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e8 hv hk
    exact ggCompFieldDataQ_of_catalogue ⟨_, hv⟩ (LieTypeIndex.characteristic_E8 q₀) (fun h => h)
      hq₀ e hp hp2 hβ hβp hC

theorem LayerSixE.autFix_zpowers_eq {C : Type} [Group C] (α : MulAut C) :
    CFSG.StandardType.LayerSixE.autFix (Subgroup.zpowers α) = fixSubgroup α := by
  ext x
  constructor
  · intro h
    exact h α (Subgroup.mem_zpowers α)
  · intro h β hβ
    have hs : α ∈ MulAction.stabilizer (MulAut C) x := h
    exact (Subgroup.zpowers_le.mpr hs) hβ

theorem ggE6CompFieldInputQ
    (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (α : MulAut ↥(adjointGroup .E6 K))
    (hα : α ∈ CFSG.StandardType.LayerSixE.inndiagAut .E6 K) (hαp : α ^ p = 1)
    (X : Subgroup ↥(adjointGroup .E6 K))
    (hX : IsComponentOf X (CFSG.StandardType.LayerSixE.autFix (Subgroup.zpowers α))) :
    GGCompFieldDataQ (Nat.card K) X := by
  haveI := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  let q₀ : PrimePower := ⟨2, n, Nat.prime_two, n.pos⟩
  have hk : Nat.card K = q₀.card := by
    rw [Nat.card_eq_fintype_card, hn, PrimePower.card_def]
  have hq₀ : q₀.card = 2 ^ (n : ℕ) := PrimePower.card_def q₀
  have hβ : α ∈ innAutDerived ↥(adjointGroup .E6 K) :=
    commutator_le_innAutDerived _
      (CFSG.HardMathSupport.Dickson.Sec6.I923.e6Inndiag_le_commutator K hα)
  rw [LayerSixE.autFix_zpowers_eq] at hX
  rw [hk]
  have hv : (LieTypeIndex.E6 q₀).Valid := LieTypeIndex.valid_E6 q₀
  obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_adjointGroup_catEquiv
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e6 hv hk
  exact ggCompFieldDataQ_of_catalogue ⟨_, hv⟩ (LieTypeIndex.characteristic_E6 q₀) (fun h => h) hq₀ e
    hp hp2 hβ hαp hX

theorem ggTwE6CompFieldInputQ
    (f : ℕ) (hf : 1 ≤ f) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
    (hα : α ∈ CFSG.StandardType.LayerSixE.twInndiagAut f) (hαp : α ^ p = 1)
    (X : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
    (hX : IsComponentOf X (CFSG.StandardType.LayerSixE.autFix (Subgroup.zpowers α))) :
    GGCompFieldDataQ (2 ^ f) X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 (2 * f)
  let σ : K ≃+* K := CFSG.StandardType.frobQEquiv hf
  have hK : Nat.card K = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  let q₀ : PrimePower := ⟨2, f, Nat.prime_two, by omega⟩
  have hq₀ : q₀.card = 2 ^ f := PrimePower.card_def q₀
  have hv : (LieTypeIndex.twistedE6 q₀).Valid := LieTypeIndex.valid_twistedE6 q₀
  obtain ⟨e⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.catEquiv_twistedE6_of_field q₀ hv
    K (by rw [hq₀, hK]) σ (fun c => by rw [hq₀]; exact frobQ_apply 2 f c)
  have hC : commutator (twistedE6RootGroup K σ) = ⊤ :=
    commutator_twistedE6RootGroup_eq_top Nat.prime_two hf hK σ (frobQ_apply 2 f)
  have h1 : CFSG.StandardType.LayerSixE.twInndiagAut f =
      twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
    rw [CFSG.StandardType.LayerSixE.twInndiagAut]
    exact congrArg₂ (· ⊔ ·) rfl
      (CFSG.StandardType.NoOffTwE6Three.range_compatParamAut_eq_twistedE6Diag
        (K := GaloisField 2 (2 * f)) (σ := CFSG.StandardType.frobQEquiv hf))
  have hle := CFSG.HardMathSupport.Dickson.Sec6.I923.twistedE6Inndiag_le_commutator σ hK
    (frobQ_apply 2 f) hC
  have hβ : α ∈ innAutDerived ↥(twistedE6RootGroup K σ) :=
    commutator_le_innAutDerived _ (hle (h1 ▸ hα))
  rw [LayerSixE.autFix_zpowers_eq] at hX
  have hres := ggCompFieldDataQ_of_catalogue (S := ↥(twistedE6RootGroup K σ)) ⟨_, hv⟩
    (LieTypeIndex.characteristic_twistedE6 q₀) (fun h => h) hq₀ e.symm hp hp2 hβ hαp hX
  rw [show fieldSize (LieTypeIndex.twistedE6 q₀) = 2 ^ f from hq₀] at hres
  exact hres

end CFSG.StandardType

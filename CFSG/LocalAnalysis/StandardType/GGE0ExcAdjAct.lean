module

public import CFSG.LocalAnalysis.StandardType.GGE0ExcAdjNormal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeAssemblyHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutRest
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXQuasi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9LabHolds
public import CFSG.LocalAnalysis.GLTheoremA.S10.CaseGamma
public import CFSG.LocalAnalysis.StandardType.GGOutTwoCommInnerHolds
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestCore
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1315b
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Parity
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151DiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeD4ThreeHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6KernelExitFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcAdj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4FixMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamChar2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpModelPairedMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthPairMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDescIndSymp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthModelAnalysis
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthCatCatalogue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthAsmPlus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthAsmMinus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriLang
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLinStatedInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeReeF4LargeRFHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6CompAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6Conn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniInner
public import CFSG.Quasithin.Background.B3ThreeModel
public import CFSG.Quasithin.Background.B3ThreeStruct
public import CFSG.Quasithin.Background.G2Omega4PlusModule
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompO
public import CFSG.Quasithin.EmptyFaithful.R3c19B
public import CFSG.Quasithin.EmptyFaithful.S143FF
public import CFSG.Quasithin.EmptyFaithful.S143Final
public import CFSG.Quasithin.EmptyFaithful.S143HD
public import CFSG.Quasithin.EmptyFaithful.S143IG
public import CFSG.Quasithin.EmptyFaithful.S143JB
public import CFSG.Quasithin.EmptyFaithful.S143KO
public import CFSG.Quasithin.EmptyFaithful.S143KP
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15421
public import CFSG.RankThree.PartOne.N143.HighEvenU

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA (chevQuotHom chevAut chevAut_chevQuotHom)
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremA.T171Sh
open CFSG.LocalAnalysis.GLTheoremA.T171D4
open CFSG.LocalAnalysis.GLTheoremA.T263.DX
open CFSG.LocalAnalysis.GLTheoremA.S172X
open CFSG.GroupActions
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient
  onCenterQuotient_apply_mk)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived Outer inner
  mem_innAutDerived_congr inner_map_congr)

private theorem fixSubgroup_conj_eq_centralizer {R : Type} [Group R] (x : R) :
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x) =
      Subgroup.centralizer ({x} : Set R) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  · intro h
    rw [← h]
    group

private theorem indAut_pow_eq_one {G : Type} [Group G] {q k : ℕ} {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hgp : g ^ k = 1) :
    indAut q L g hg ^ k = 1 := by
  have e : (⟨g⁻¹, Subgroup.inv_mem _ hg⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ k = 1 :=
    Subtype.ext (by simp [inv_pow, hgp])
  show chevAut q L ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ ^ k = 1
  rw [← map_pow, e, map_one]

private theorem isChevSimple_of_mulEquiv' {r : ℕ} {S S' : Type} [Group S] [Group S']
    (e : S ≃* S') (h : IsChevSimple r S) : IsChevSimple r S' := by
  rcases h with ⟨i, hi, ⟨e'⟩⟩ | ⟨i, hi, ⟨e'⟩⟩
  · exact Or.inl ⟨i, hi, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr ⟨i, hi, ⟨e.symm.trans e'⟩⟩

private theorem exists_congr_indAut_eq_centerQuotientHom {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {J : Subgroup G}
    (hqP : CFSG.Open.IsQuasisimple (PQuot p J)) (hqJ : CFSG.Open.IsQuasisimple ↥J)
    {y : G} (hy : y ∈ Subgroup.normalizer (J : Set G)) :
    ∃ (ι : PSimple p J ≃* (↥J ⧸ Subgroup.center ↥J))
      (hstab : MulAut.conj y⁻¹ ∈ subgroupStabAut J),
      MulAut.congr ι (indAut p J y hy) =
        centerQuotientHom ↥J (subgroupStabRestrict J ⟨MulAut.conj y⁻¹, hstab⟩) := by
  classical
  have hN' : y⁻¹ ∈ Subgroup.normalizer (J : Set G) := Subgroup.inv_mem _ hy
  have hstab : MulAut.conj y⁻¹ ∈ subgroupStabAut J := by
    show J.map (MulAut.conj y⁻¹).toMonoidHom = J
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).1 hN'
  obtain ⟨ι, hι⟩ := CFSG.LocalAnalysis.GLTheoremA.I141F.u9_exists_pSimple_equiv_centerQuot
    hp hqP hqJ (CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_nontrivial hqP)
    (MonoidHom.id ↥J) Function.surjective_id
  have hι' : ∀ a : ↥J, ι (chevQuotHom p J a) = QuotientGroup.mk a := fun a => hι a
  refine ⟨ι, hstab, ?_⟩
  ext z
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective z
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hsymm : ι.symm (QuotientGroup.mk a) = chevQuotHom p J a := by
    rw [← hι' a, MulEquiv.symm_apply_apply]
  rw [hsymm]
  rw [show indAut p J y hy = chevAut p J ⟨y⁻¹, Subgroup.inv_mem _ hy⟩ from rfl]
  rw [chevAut_chevQuotHom]
  rw [hι' (J.normalizerMonoidHom ⟨y⁻¹, Subgroup.inv_mem _ hy⟩ a)]
  rw [show centerQuotientHom ↥J (subgroupStabRestrict J ⟨MulAut.conj y⁻¹, hstab⟩) =
      onCenterQuotient (subgroupStabRestrict J ⟨MulAut.conj y⁻¹, hstab⟩) from rfl]
  rw [show (QuotientGroup.mk a : ↥J ⧸ Subgroup.center ↥J) =
      QuotientGroup.mk' (Subgroup.center ↥J) a from rfl, onCenterQuotient_apply_mk]
  congr 1

theorem ggE0_adjoint_innDiagOn
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {s w : ↥(adjointGroup τ K)} (hs1 : s ≠ 1) (hsp : s ^ p = 1) (hwp : w ^ p = 1)
    (hw : w ∈ Subgroup.centralizer {s})
    {X : Subgroup ↥(adjointGroup τ K)} (hX : IsComponentOf X (Subgroup.centralizer {s})) :
    LargeEvenMarking ↥X (fun _ _ _ _ _ _ => True) →
      CFSG.LocalAnalysis.GLTheoremA.S10.InnDiagOn 2 (Subgroup.zpowers w) X := by
  intro hm
  classical
  haveI : Finite ↥(adjointGroup τ K) := CFSG.LieType.Chevalley.generated_group_finite τ K
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj s) =
      Subgroup.centralizer ({s} : Set ↥(adjointGroup τ K)) :=
    fixSubgroup_conj_eq_centralizer s
  have hfixEq : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj s) =
      CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj s) :=
    Subgroup.ext fun _ => Iff.rfl
  have hXfix : IsComponentOf X
      (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj s)) := by
    rw [← hfixEq, hfix]
    exact hX
  have hN : w ∈ Subgroup.normalizer (X : Set ↥(adjointGroup τ K)) :=
    ggE0_adjoint_normalizes hτ hp hp2 hs1 hsp hX hw
  have hqX_open : CFSG.Open.IsQuasisimple ↥X := hX.2.2
  have hqX_nat : CFSG.IsQuasisimple ↥X :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥X).1 hX.2.2
  have hdvd : 2 ∣ Nat.card (↥X ⧸ Subgroup.center ↥X) :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.two_dvd_card_of_simple_nonabelian
      hqX_nat.2.1 hqX_nat.2.2
  have hKX : CFSG.Open.IsSubnormal X
      (Subgroup.centralizer ({s} : Set ↥(adjointGroup τ K))) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open X _).1 hX.2.1
  have hJcompFix : CFSG.Open.GLAPComponent 2
      (Subgroup.centralizer ({s} : Set ↥(adjointGroup τ K))) X :=
    CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple Nat.prime_two hKX hqX_open hdvd
  have hqOpen : CFSG.Open.IsQuasisimple (PQuot 2 X) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent Nat.prime_two hJcompFix
  have hqNat : CFSG.IsQuasisimple (PQuot 2 X) :=
    CFSG.LocalAnalysis.GLTheoremA.S172X.isQuasisimple_of_open hqOpen
  have hchevTwo : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevTwo
      (↥X ⧸ Subgroup.center ↥X) := isChevTwo_of_largeEvenMarking hm
  have hchevCenter : IsChevSimple 2 (↥X ⧸ Subgroup.center ↥X) :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1315b.isChevSimple_two_of_isChevTwo hchevTwo
  obtain ⟨ePS⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T263.DX.nonempty_pSimple_equiv_of_dvd
      Nat.prime_two hqX_nat hdvd
  have hchevJ : IsChevSimple 2 (PSimple 2 X) :=
    isChevSimple_of_mulEquiv' (MulEquiv.symm ePS) hchevCenter
  have hpOdd : Odd p := hp.odd_of_ne_two hp2
  have hpow : indAut 2 X w hN ^ p = 1 := indAut_pow_eq_one hN hwp
  have hconclInner (hmem : indAut 2 X w hN ∈ inner (PSimple 2 X)) :
      CFSG.LocalAnalysis.GLTheoremA.S10.InnDiagOn 2 (Subgroup.zpowers w) X :=
    inner_innDiag_holds Nat.prime_two hJcompFix hchevJ hN
      ((indAut_mem_inner_iff Nat.prime_two hJcompFix hN).1 hmem)
  by_cases h360 : Nat.card (PSimple 2 X) = 360
  · obtain ⟨lab, -, hM⟩ := largeEvenMarking_markedModel_centerQuot hm
    have hcard' : Nat.card (↥X ⧸ Subgroup.center ↥X) = 360 :=
      (Nat.card_congr ePS.toEquiv).symm.trans h360
    have htag : lab.tag = .B2der := by
      by_contra hne
      exact ggMarkedModel_card_ne_three_sixty hne hM hcard'
    obtain ⟨e6⟩ := nonempty_alternatingGroup_of_markedModel_b2der htag hM
    exact hconclInner (RawAut.mem_inner_of_isPGroup_outer
      (CFSG.LargeExtraspecial.DW.isPGroup_outer_alt6 (ePS.trans e6)) hpOdd hpow)
  · have hτD4 : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
      rcases hτ with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    have hτG2 : τ = .G2 → 4 ≤ Nat.card K := fun hG2 => by
      rw [hG2] at hτ
      rcases hτ with h | h | h <;> exact absurd h (by decide)
    have hτE6 : τ = .E6 → p = 3 → ¬ 3 ∣ Nat.card K - 1 := fun hE6 _ => by
      rw [hE6] at hτ
      rcases hτ with h | h | h <;> exact absurd h (by decide)
    have hA : ExcAdjCompInnAut :=
      excAdjCompInnAut_of excKernelCompAction_holds e6CentralizerConnOddExcKernels_holds
    have hD4 := excAdjD4Inner_holds hτD4 K p hp hp2 hτE6
    obtain ⟨ι, hstab, hbridge⟩ :=
      exists_congr_indAut_eq_centerQuotientHom Nat.prime_two hqOpen hqX_open hN
    have hcard' : Nat.card (↥X ⧸ Subgroup.center ↥X) ≠ 360 := by
      intro h
      exact h360 (by rw [Nat.card_congr ι.toEquiv]; exact h)
    have hwinv : (w⁻¹) ^ p = 1 := by rw [inv_pow, hwp, inv_one]
    have hws : w * s = s * w := Subgroup.mem_centralizer_singleton_iff.mp hw
    have hcomm' : s * w⁻¹ = w⁻¹ * s := Commute.inv_right (Commute.symm hws)
    have hcenterMem : centerQuotientHom ↥X
        (subgroupStabRestrict X ⟨MulAut.conj w⁻¹, hstab⟩) ∈
        innAutDerived (↥X ⧸ Subgroup.center ↥X) :=
      hA hτD4 K p hp hp2 hτG2 hτE6 s w⁻¹ hs1 hsp hwinv hcomm' X hXfix hcard' hstab
    have hmemMI : indAut 2 X w hN ∈ innAutDerived (PSimple 2 X) := by
      refine (mem_innAutDerived_congr ι).1 ?_
      rw [hbridge]
      exact hcenterMem
    rcases hchevJ with hon | hamb
    · obtain ⟨i, hi, ⟨e⟩⟩ := hon
      cases i with
      | cyclic _ _ => exact absurd hi (by simp [onLie])
      | alternating _ _ => exact absurd hi (by simp [onLie])
      | sporadic _ => exact absurd hi (by simp [onLie])
      | lie dd =>
        obtain ⟨idx, hv⟩ := dd
        have hval := (TauCeti.LieTypeIndex.valid_iff _).1 hv
        cases idx with
        | A n q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_A n q]; exact hi
          exact innAutDerivedInnDiag_linear 2 X w hN Nat.prime_two hqNat
            ⟨.lie ⟨.A n q, hv⟩, ⟨n, q, rfl, hq2⟩, ⟨e⟩⟩ hmemMI
        | twistedA n q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_twistedA n q]; exact hi
          exact innAutDerivedInnDiag_unitary 2 X w hN Nat.prime_two hqNat
            ⟨.lie ⟨.twistedA n q, hv⟩, ⟨n, q, rfl, hq2⟩, ⟨e⟩⟩ hmemMI
        | B n q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_B n q]; exact hi
          have hr : 2 ≤ n := by
            have h := hval.1
            simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
            omega
          exact innAutDerivedInnDiag_rest 2 X w hN Nat.prime_two hqNat
            ⟨.lie ⟨.B n q, hv⟩, ⟨hr, hq2⟩, ⟨e⟩⟩ hmemMI
        | C n q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_C n q]; exact hi
          have hr : 3 ≤ n := by
            have h := hval.1
            simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
            omega
          exact innAutDerivedInnDiag_rest 2 X w hN Nat.prime_two hqNat
            ⟨.lie ⟨.C n q, hv⟩, ⟨by omega, hq2⟩, ⟨e⟩⟩ hmemMI
        | D n q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_D n q]; exact hi
          by_cases hn4 : n = 4
          · subst hn4
            have hcatD4 : catalogIs (↥X ⧸ Subgroup.center ↥X)
                (onLie fun i : TauCeti.LieTypeIndex =>
                  ∃ q : TauCeti.PrimePower, i = .D 4 q ∧ q.p = 2) :=
              ⟨.lie ⟨.D 4 q, hv⟩, ⟨q, rfl, hq2⟩, ⟨ι.symm.trans e⟩⟩
            have hcenterInner : centerQuotientHom ↥X
                (subgroupStabRestrict X ⟨MulAut.conj w⁻¹, hstab⟩) ∈
                inner (↥X ⧸ Subgroup.center ↥X) :=
              hD4 s w⁻¹ hs1 hsp hwinv hcomm' X hXfix hcatD4 hstab hcenterMem
            have hmemInn : indAut 2 X w hN ∈ inner (PSimple 2 X) := by
              refine (Subgroup.mem_map_iff_mem (f := (MulAut.congr ι).toMonoidHom)
                (MulAut.congr ι).injective).1 ?_
              rw [inner_map_congr ι]
              change MulAut.congr ι (indAut 2 X w hN) ∈
                inner (↥X ⧸ Subgroup.center ↥X)
              rw [hbridge]
              exact hcenterInner
            exact hconclInner hmemInn
          · have hr : 4 ≤ n := by
              have h := hval.1
              simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
              omega
            exact innAutDerivedInnDiag_rest 2 X w hN Nat.prime_two hqNat
              ⟨.lie ⟨.D n q, hv⟩, ⟨by omega, hq2⟩, ⟨e⟩⟩ hmemMI
        | twistedD n q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_twistedD n q]; exact hi
          exact innAutDerivedInnDiag_rest 2 X w hN Nat.prime_two hqNat
            ⟨.lie ⟨.twistedD n q, hv⟩,
              ⟨TauCeti.LieTypeIndex.four_le_of_twistedD_inStandardRange hval.1, hq2⟩,
              ⟨e⟩⟩ hmemMI
        | E6 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_E6 q]; exact hi
          exact innAutDerivedInnDiag_rest 2 X w hN Nat.prime_two hqNat
            ⟨.lie ⟨.E6 q, hv⟩, hq2, ⟨e⟩⟩ hmemMI
        | E7 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_E7 q]; exact hi
          exact innAutDerivedInnDiag_rest 2 X w hN Nat.prime_two hqNat
            ⟨.lie ⟨.E7 q, hv⟩, hq2, ⟨e⟩⟩ hmemMI
        | E8 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_E8 q]; exact hi
          exact innAutDerivedInnDiag_rest 2 X w hN Nat.prime_two hqNat
            ⟨.lie ⟨.E8 q, hv⟩, hq2, ⟨e⟩⟩ hmemMI
        | F4 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_F4 q]; exact hi
          exact innAutDerivedInnDiag_rest 2 X w hN Nat.prime_two hqNat
            ⟨.lie ⟨.F4 q, hv⟩, hq2, ⟨e⟩⟩ hmemMI
        | G2 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_G2 q]; exact hi
          exact innAutDerivedInnDiag_rest 2 X w hN Nat.prime_two hqNat
            ⟨.lie ⟨.G2 q, hv⟩, hq2, ⟨e⟩⟩ hmemMI
        | twistedE6 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_twistedE6 q]; exact hi
          exact innAutDerivedInnDiag_rest 2 X w hN Nat.prime_two hqNat
            ⟨.lie ⟨.twistedE6 q, hv⟩, hq2, ⟨e⟩⟩ hmemMI
        | trialityD4 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_trialityD4 q]; exact hi
          exact innAutDerivedInnDiag_rest 2 X w hN Nat.prime_two hqNat
            ⟨.lie ⟨.trialityD4 q, hv⟩, hq2, ⟨e⟩⟩ hmemMI
        | suzuki m =>
          have hr : 1 ≤ m := by
            have h := hval.1
            simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
            omega
          exact innAutDerivedInnDiag_rest 2 X w hN Nat.prime_two hqNat
            ⟨.lie ⟨.suzuki m, hv⟩, hr, ⟨e⟩⟩ hmemMI
        | reeG2 m =>
          exact absurd (hi.symm.trans (TauCeti.LieTypeIndex.characteristic_reeG2 m))
            (by norm_num)
        | reeF4 m =>
          have hr : 1 ≤ m := by
            have h := hval.1
            simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
            omega
          exact innAutDerivedInnDiag_rest 2 X w hN Nat.prime_two hqNat
            ⟨.lie ⟨.reeF4 m, hv⟩, hr, ⟨e⟩⟩ hmemMI
        | tits =>
          exact hconclInner (RawAut.mem_inner_of_isPGroup_outer
            (isPGroup_outer_of_tits hv e) hpOdd hpow)
    · exact hconclInner (RawAut.mem_inner_of_isPGroup_outer
        (isPGroup_outer_of_ambiguous_two hamb) hpOdd hpow)

end CFSG.StandardType

end

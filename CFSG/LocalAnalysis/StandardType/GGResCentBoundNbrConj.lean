module

public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbr
public import CFSG.LocalAnalysis.StandardType.GGNbrCanCartan
public import CFSG.LocalAnalysis.StandardType.GGResCentBound
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrSpaces
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrWeylA
public import CFSG.LocalAnalysis.StandardType.GGReflClosedOfWeyl
public import CFSG.LocalAnalysis.StandardType.GGWeylMatrixAut
public import CFSG.LocalAnalysis.StandardType.GGTBXDatumOfTor
public import CFSG.LocalAnalysis.StandardType.GGTBTorDatum
public import CFSG.LocalAnalysis.StandardType.GGPZWeylD
public import CFSG.GroupTheory.ConjKerCenter
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZDet
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepPos
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepTransfer
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineAux
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinearNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar
public import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeFrame
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA2
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitary
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRest
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCubeHolds
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCube
public import CFSG.LocalAnalysis.StandardType.GGF4NbrAutReflKGHolds
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBE6Three
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHeart
public import CFSG.LocalAnalysis.StandardType.GGResFixedWeylCentralizer
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerClassicalModel
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBScWeyl

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteNbrFix
public import CFSG.LocalAnalysis.StandardType.GGTBFixIrred
public import CFSG.LocalAnalysis.StandardType.GGResSevenNbr
public import CFSG.LocalAnalysis.StandardType.GGIrred937TwE6
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Inn
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Center

public import CFSG.LocalAnalysis.StandardType.GGTBWNormSmall

public import CFSG.LocalAnalysis.StandardType.GGResTwDInverterLSplit
public import CFSG.LocalAnalysis.StandardType.GGQ2P3Hyp
public import CFSG.LocalAnalysis.StandardType.GGRCLinRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixAux
public import CFSG.LocalAnalysis.StandardType.ZS.Adapter
public import CFSG.LocalAnalysis.StandardType.ZS.Support
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtLemmas
public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Basic

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineClassical
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineClassicalLabel
public import CFSG.LocalAnalysis.StandardType.GGResXDichotomy
public import CFSG.LocalAnalysis.StandardType.GGTBXDatumResRest2
public import CFSG.LocalAnalysis.StandardType.GGTBWeylRowResRest2Cases
public import CFSG.LocalAnalysis.StandardType.GGResSeven
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoSeven
public import CFSG.LocalAnalysis.StandardType.GGTWRowData
public import CFSG.HardMathSupport.Kantor79.LongRootGroup

public section
namespace CFSG.StandardType
open CFSG CFSG.Assembly CFSG.Open
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggBstarComm_map_eq_spanSub {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} {Λ : Type} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive Bs ≃+ V) {φ : Λ → MulAut Bs} {h : Λ → V} {a : Λ → Module.Dual (ZMod p) V}
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - a i v • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hcl : ggAutomizer X Bs = Subgroup.closure (Set.range φ)) :
    (ggBstarComm X Bs).map Bs.subtype = ggSpanSub ι (Submodule.span (ZMod p) (Set.range h)) := by
  apply le_antisymm
  · rintro _ ⟨c,hc,rfl⟩
    exact coe_mem_ggSpanSub_iff.mpr (ggBstarComm_le_span hlin hcl hc)
  · rintro _ ⟨v,hv,rfl⟩
    have hspan := l6tr_span_eq (p := p) hlin hrefl hcl
    rw [hspan] at hv
    have hvC : Additive.toMul (ι.symm v) ∈ ggBstarComm X Bs := by
      refine Submodule.span_induction (p := fun v _ => Additive.toMul (ι.symm v) ∈ ggBstarComm X Bs)
        ?_ ?_ ?_ ?_ hv
      · rintro _ ⟨⟨g,w⟩,rfl⟩
        let b := Additive.toMul (ι.symm w)
        have heq : Additive.toMul (ι.symm (ggLin (p := p) ι g.1 w - w)) = b⁻¹ * g.1 b := by
          apply Additive.ofMul.injective
          apply ι.injective
          rw [ofMul_toMul,ι.apply_symm_apply,ofMul_mul,ofMul_inv,map_add,map_neg,
            ← ggLin_apply_ofMul (p := p),ofMul_toMul,ι.apply_symm_apply]
          abel
        rw [heq]
        exact Subgroup.subset_closure ⟨b,g.1,g.2,rfl⟩
      · simp [ggBstarComm]
      · intro v w _ _ hv hw
        rw [map_add,toMul_add]
        exact Subgroup.mul_mem _ hv hw
      · intro c v _ hv
        have heq : Additive.toMul (ι.symm (c • v)) = (Additive.toMul (ι.symm v)) ^ c.val := by
          apply Additive.ofMul.injective
          apply ι.injective
          rw [ofMul_toMul,ι.apply_symm_apply,ofMul_pow,map_nsmul,
            ofMul_toMul,ι.apply_symm_apply,← Nat.cast_smul_eq_nsmul (ZMod p),ZMod.natCast_zmod_val]
        rw [heq]
        exact Subgroup.pow_mem _ hv _
    exact ⟨_,hvC,rfl⟩

theorem ggSpanSub_coroot_axis_le {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} {Λ : Type} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive Bs ≃+ V) {φ : Λ → MulAut Bs} {h : Λ → V} {a : Λ → Module.Dual (ZMod p) V}
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - a i v • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hcl : ggAutomizer X Bs = Subgroup.closure (Set.range φ)) (y : Bs) :
    (ggBstarComm X Bs).map Bs.subtype ⊔ Subgroup.zpowers (y : G) ≤
      ggSpanSub ι (Submodule.span (ZMod p) (Set.range h) ⊔
        Submodule.span (ZMod p) {ι (Additive.ofMul y)}) := by
  apply sup_le
  · rw [ggBstarComm_map_eq_spanSub ι hlin hrefl hcl]
    rintro _ ⟨v,hv,rfl⟩
    exact ⟨v,Submodule.mem_sup_left hv,rfl⟩
  · apply Subgroup.zpowers_le.mpr
    exact coe_mem_ggSpanSub_iff.mpr (Submodule.mem_sup_right
      (Submodule.mem_span_singleton_self (ι (Additive.ofMul y))))

theorem GGResXDatum.reflGenerated {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (hD : GGResXDatum p Bs X) : GGReflGenerated p (ggAutomizer X Bs) := by
  obtain ⟨Λ,hΛf,hΛd,M,C,V,hVadd,hVmod,ι,φ,h,a,hM,hC,hlin,hrefl,hpair,⟨f,hf⟩,hcl⟩ := hD
  exact ggIndep_reflGenerated_of_closure hrefl hcl

theorem GGResHyp.join_det_sq_eq_one_of_dichotomy
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive Bs ≃+ V)
    {g : MulAut Bs} (hg : g ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs) :
    (ggLin (p := p) ι g).det ^ 2 = 1 := by
  have hL : GGReflGenerated p (ggAutomizer L Bs) := by
    rcases (hX G p B Bs x L D J y K hH).1 with hL|hseven
    · exact hL.reflGenerated
    · obtain ⟨labJ,labL,hΛJ,hΛL,hJ,hL,hrow⟩ := hseven
      obtain ⟨hp7,hLabel⟩ := hrow
      exact (ggSeven_L_absurd hTCJ hRig hH.1 hp7 hH.2.2.2.2.1 hΛL hL hLabel).elim
  exact ggLin_det_sq_eq_one_of_reflGen hH.1.tableB_facts.2.1 ι
    (ggIndep_reflGenerated_sup hL hH.2.2.2.2.2.1) hg

theorem card_inner_le_half_of_d4 {G : Type} [Group G] [Finite G]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (f : M.Group ≃* G) (e : Fin 4 ≃ Λ) (hM : M = (ggCoxeterMatrixD 4).reindex e) :
    2 * Nat.card (MulAut.conj : G →* MulAut G).range = Nat.card G := by
  have hcenter : Nat.card (Subgroup.center G) = 2 := by
    rw [← Nat.card_congr (Subgroup.centerCongr f).toEquiv]
    subst hM
    rw [Nat.card_congr (Subgroup.centerCongr ((ggCoxeterMatrixD 4).reindexGroupEquiv e)).toEquiv,
      ggCoxeterD_center 4 (by norm_num)]
    norm_num
  have h := Subgroup.card_ker_mul_card_range (MulAut.conj : G →* MulAut G)
  rwa [CFSG.GroupTheory.ker_conj_eq_center,hcenter] at h

theorem ggNbr_card_stabilizer_le_inner_mul_commutant {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hcardK : p ^ 3 ≤ Nat.card ↥(Bs ⊓ K)) (hy : y ∈ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) (φ : Λ → MulAut ↥Bs)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hRC : GGReflConjSimple p (ggAutomizer K Bs) φ)
    (f : M.Group ≃* ↥(ggAutomizer K Bs))
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    {d z : ℕ} (hdiag : Nat.card {σ : Λ ≃ Λ // ∀ i j, M (σ i) (σ j) = M i j} ≤ d)
    (hz : Nat.card ↥(((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)) ⊓
        Subgroup.centralizer (Set.range φ)) ≤ z) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)) ≤
        Nat.card (MulAut.conj : (ggAutomizer K Bs) →* MulAut (ggAutomizer K Bs)).range * d * z := by
  classical
  let H := (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
    MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)
  let act : MulAction ↥H (Λ → MulAut ↥Bs) := ggResCentConjAction H
  let : SMul ↥H (Λ → MulAut ↥Bs) := act.toSMul
  let : MulAction ↥H (Λ → MulAut ↥Bs) := act
  have hnorm : ∀ n : H, n.1 ∈ Subgroup.normalizer (ggAutomizer K Bs : Set (MulAut ↥Bs)) :=
    fun n => ggNbr_stabilizer_le_normalizer_of_card_inf hH hcardK hy n.2
  have ho := ggResCent_conj_orbit_bound_inner hM hrefl hRC f hf hnorm hdiag
  have horbit : Nat.card (MulAction.orbit ↥H φ) ≤ Nat.card (MulAut.conj : (ggAutomizer K Bs) →* MulAut (ggAutomizer K Bs)).range * d := by
    change Nat.card (Set.range (fun n : H => (ggResCentConjAction H).smul n φ)) ≤ _
    exact ho
  let : Fintype ↥H := Fintype.ofFinite _
  let : Fintype (MulAction.orbit ↥H φ) := Fintype.ofFinite _
  let : Fintype (MulAction.stabilizer ↥H φ) := Fintype.ofFinite _
  have hmul : Nat.card (MulAction.orbit ↥H φ) * Nat.card (MulAction.stabilizer ↥H φ) = Nat.card H := by
    simpa only [Nat.card_eq_fintype_card] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group ↥H φ
  let Z : Subgroup H := MulAction.stabilizer H φ
  have hm : Z.map H.subtype = H ⊓ Subgroup.centralizer (Set.range φ) := by
    ext g
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨n.2, ?_⟩
      change (n : MulAut Bs) ∈ Subgroup.centralizer (Set.range φ)
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨i, rfl⟩
      have hi : n.1 * φ i * n.1⁻¹ = φ i := by
        have hfix : (ggResCentConjAction H).smul n φ = φ := hn
        have h := congrFun hfix i
        change MulAut.conj (n : MulAut Bs) (φ i) = φ i at h
        simpa only [MulAut.conj_apply] using h
      have h := congrArg (fun v => v * n.1) hi
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using h.symm
    · rintro ⟨hg, hgc⟩
      refine ⟨⟨g, hg⟩, ?_, rfl⟩
      change (ggResCentConjAction H).smul ⟨g,hg⟩ φ = φ
      funext i
      change g * φ i * g⁻¹ = φ i
      have hi := Subgroup.mem_centralizer_iff.mp hgc (φ i) ⟨i, rfl⟩
      rw [← hi]
      group
  have hz0 : Nat.card Z ≤ z := by
    rw [Nat.card_congr (Z.equivMapOfInjective H.subtype Subtype.val_injective).toEquiv, hm]
    exact hz
  calc Nat.card H = Nat.card (MulAction.orbit ↥H φ) * Nat.card (MulAction.stabilizer ↥H φ) := hmul.symm
    _ ≤ (Nat.card (MulAut.conj : (ggAutomizer K Bs) →* MulAut (ggAutomizer K Bs)).range * d) * z := Nat.mul_le_mul horbit hz0

theorem ggNbr_card_stabilizer_le_of_commutant {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hcardK : p ^ 3 ≤ Nat.card ↥(Bs ⊓ K)) (hy : y ∈ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) (φ : Λ → MulAut ↥Bs)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hRC : GGReflConjSimple p (ggAutomizer K Bs) φ)
    (f : M.Group ≃* ↥(ggAutomizer K Bs))
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    {d z : ℕ} (hdiag : Nat.card {σ : Λ ≃ Λ // ∀ i j, M (σ i) (σ j) = M i j} ≤ d)
    (hz : Nat.card ↥(((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)) ⊓
        Subgroup.centralizer (Set.range φ)) ≤ z) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)) ≤
        Nat.card ↥(ggAutomizer K Bs) * d * z := by
  have h := ggNbr_card_stabilizer_le_inner_mul_commutant hH hcardK hy hM φ hrefl hRC f hf hdiag hz
  have hi : Nat.card (MulAut.conj : (ggAutomizer K Bs) →* MulAut (ggAutomizer K Bs)).range ≤
      Nat.card (ggAutomizer K Bs) := Nat.card_le_card_of_surjective _
    (MulAut.conj : (ggAutomizer K Bs) →* MulAut (ggAutomizer K Bs)).rangeRestrict_surjective
  exact h.trans (Nat.mul_le_mul_right z (Nat.mul_le_mul_right d hi))

theorem ggResCentBoundNbr_three_of_weylDatum {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hy : y ∈ Bs)
    (hcardK : 3 ^ 3 ≤ Nat.card ↥(Bs ⊓ K))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (φ : Λ → MulAut ↥Bs) (hrefl : ∀ i, GGIsReflection 3 (φ i))
    (hRC : GGReflConjSimple 3 (ggAutomizer K Bs) φ)
    (f : M.Group ≃* ↥(ggAutomizer K Bs))
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (h : Λ → V) (a : Λ → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod 3))
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - a i v • h i)
    (hF : Module.finrank (ZMod 3) (LinearMap.pi a).ker ≤ 2) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y,hy⟩ : Bs)) ≤
        (3 - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := by
  classical
  let H := (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
    MulAction.stabilizer (MulAut ↥Bs) (⟨y,hy⟩ : Bs)
  let Z := H ⊓ Subgroup.centralizer (Set.range φ)
  let yV := ι (Additive.ofMul (⟨y,hy⟩ : Bs))
  have hZ : Z ≤ ggAutomizer ⊤ Bs :=
    fun g hg => sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hg.1.1
  have hy1 : y ≠ 1 := (GGResHyp.data_K hH).2.1
  have hyV : yV ≠ 0 := by
    intro h0
    have h := ι.injective (h0.trans ι.map_zero.symm)
    exact hy1 (congrArg Subtype.val ((ofMul_eq_zero).mp h))
  have hyfix : ∀ i, φ i ⟨y,hy⟩ = ⟨y,hy⟩ := by
    intro i
    have hi : φ i ∈ ggAutomizer K Bs := (hf i) ▸ (f (M.simple i)).2
    exact ggAutomizer_fix_of_centralizes hy
      (fun k hk => (Subgroup.mem_centralizer_iff.mp (GGResHyp.data_K hH).1 k hk).symm) hi
  have hay : ∀ i, a i yV = 0 := by
    intro i
    have hfV : ggLin (p := 3) ι (φ i) yV = yV := by
      rw [ggLin_apply_ofMul,hyfix]
    rw [hlin] at hfV
    have hhi : h i ≠ 0 := by
      intro h0
      have h2 := hpair i i
      rw [h0,map_zero,hC.1] at h2
      exact (zmod_two_ne_zero (p := 3) (by decide)) h2.symm
    exact (smul_eq_zero.mp (sub_eq_self.mp hfV)).resolve_right hhi
  have hGy : ∀ g : Z, ggLin (p := 3) ι g.1 yV = yV := by
    intro g
    rw [ggLin_apply_ofMul]
    have hfix : g.1 ⟨y,hy⟩ = ⟨y,hy⟩ := MulAction.mem_stabilizer_iff.mp g.2.1.2
    rw [hfix]
  have hcomm : ∀ g : Z, ∀ i v, ggLin (p := 3) ι g.1 (v - a i v • h i) =
      ggLin (p := 3) ι g.1 v - a i (ggLin (p := 3) ι g.1 v) • h i := by
    intro g i v
    have he := (Subgroup.mem_centralizer_iff.mp g.2.2 (φ i) ⟨i,rfl⟩).symm
    calc ggLin (p := 3) ι g.1 (v - a i v • h i) =
        ggLin (p := 3) ι g.1 (ggLin (p := 3) ι (φ i) v) := by rw [hlin]
      _ = ggLin (p := 3) ι (g.1 * φ i) v := by rw [map_mul,LinearEquiv.mul_apply]
      _ = ggLin (p := 3) ι (φ i * g.1) v := by rw [he]
      _ = ggLin (p := 3) ι (φ i) (ggLin (p := 3) ι g.1 v) := by rw [map_mul,LinearEquiv.mul_apply]
      _ = _ := hlin _ _
  by_cases hD4 : ∃ e : Fin 4 ≃ Λ, M = (ggCoxeterMatrixD 4).reindex e
  · obtain ⟨e,he⟩ := hD4
    have hz : Nat.card Z ≤ 4 := by
      have hz0 := card_weyl_commutant_full_rank_le_square (by decide : 3 ≠ 2)
        hH.2.2.2.1 ι Z hZ hM hC h a hpair hcomm yV hyV hay hGy hF
        (ggIntCartan_rank_eq_card_of_typeD4 (by decide) hC e he)
      simpa using hz0
    have hi := card_inner_le_half_of_d4 f e he
    have hbound := ggNbr_card_stabilizer_le_inner_mul_commutant hH hcardK hy hM φ hrefl hRC f hf
      (GGIsWeylMatrix.card_autPerm_le_six hM) hz
    calc Nat.card H ≤ Nat.card (MulAut.conj : (ggAutomizer K Bs) →* MulAut (ggAutomizer K Bs)).range * 6 * 4 := hbound
      _ = (3 - 1) * 6 * Nat.card (ggAutomizer K Bs) := by rw [← hi];ring
  · have hz : Nat.card Z ≤ 6 := card_weyl_commutant_three_le_six hH.2.2.2.1 ι Z hZ
      hM hC h a hpair hcomm yV hyV hay hGy hF
    have hbound := ggNbr_card_stabilizer_le_of_commutant hH hcardK hy hM φ hrefl hRC f hf
      (GGIsWeylMatrix.card_autPerm_le_two hM hD4) hz
    simpa only [Nat.reduceSub] using hbound.trans_eq (by ring)

private theorem ggResCentBoundNbr_of_weylDatum_small_commutant {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hcardK : p ^ 3 ≤ Nat.card ↥(Bs ⊓ K))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (φ : Λ → MulAut ↥Bs) (hrefl : ∀ i, GGIsReflection p (φ i))
    (hRC : GGReflConjSimple p (ggAutomizer K Bs) φ)
    (f : M.Group ≃* ↥(ggAutomizer K Bs))
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (h : Λ → V) (a : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod p))
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - a i v • h i)
    (hF : Module.finrank (ZMod p) (LinearMap.pi a).ker ≤ 2)
    (hcase : Nat.Coprime (p - 1) (2 * Module.finrank (ZMod p) V - 3) ∨
      p = 5 ∨ Matrix.rank (C.map (Int.castRingHom (ZMod p))) = Fintype.card Λ ∨
      Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p)
      ↥(Submodule.span (ZMod p) (Set.range h) ⊔
        Submodule.span (ZMod p) {ι (Additive.ofMul (⟨y,hy⟩ : Bs))}) + 1 ∨
      ι (Additive.ofMul (⟨y,hy⟩ : Bs)) ∈ Submodule.span (ZMod p) (Set.range h))
    (hdet : ∀ g ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, (ggLin (p := p) ι g).det ^ 2 = 1) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y,hy⟩ : Bs)) ≤
        (p - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := by
  classical
  let H := (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
    MulAction.stabilizer (MulAut ↥Bs) (⟨y,hy⟩ : Bs)
  let Z := H ⊓ Subgroup.centralizer (Set.range φ)
  let yV := ι (Additive.ofMul (⟨y,hy⟩ : Bs))
  have hZ : Z ≤ ggAutomizer ⊤ Bs :=
    fun g hg => sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hg.1.1
  have hy1 : y ≠ 1 := (GGResHyp.data_K hH).2.1
  have hyV : yV ≠ 0 := by
    intro h0
    have h := ι.injective (h0.trans ι.map_zero.symm)
    exact hy1 (congrArg Subtype.val ((ofMul_eq_zero).mp h))
  have hyfix : ∀ i, φ i ⟨y,hy⟩ = ⟨y,hy⟩ := by
    intro i
    have hi : φ i ∈ ggAutomizer K Bs := (hf i) ▸ (f (M.simple i)).2
    exact ggAutomizer_fix_of_centralizes hy
      (fun k hk => (Subgroup.mem_centralizer_iff.mp (GGResHyp.data_K hH).1 k hk).symm) hi
  have hay : ∀ i, a i yV = 0 := by
    intro i
    have hfV : ggLin (p := p) ι (φ i) yV = yV := by
      rw [ggLin_apply_ofMul,hyfix]
    rw [hlin] at hfV
    have hhi : h i ≠ 0 := by
      intro h0
      have h2 := hpair i i
      rw [h0,map_zero,hC.1] at h2
      exact (zmod_two_ne_zero (p := p) hp2) (by simpa using h2.symm)
    exact (smul_eq_zero.mp (sub_eq_self.mp hfV)).resolve_right hhi
  have hGy : ∀ g : Z, ggLin (p := p) ι g.1 yV = yV := by
    intro g
    rw [ggLin_apply_ofMul]
    have hfix : g.1 ⟨y,hy⟩ = ⟨y,hy⟩ := MulAction.mem_stabilizer_iff.mp g.2.1.2
    rw [hfix]
  have hcomm : ∀ g : Z, ∀ i v, ggLin (p := p) ι g.1 (v - a i v • h i) =
      ggLin (p := p) ι g.1 v - a i (ggLin (p := p) ι g.1 v) • h i := by
    intro g i v
    have he := (Subgroup.mem_centralizer_iff.mp g.2.2 (φ i) ⟨i,rfl⟩).symm
    calc ggLin (p := p) ι g.1 (v - a i v • h i) =
        ggLin (p := p) ι g.1 (ggLin (p := p) ι (φ i) v) := by rw [hlin]
      _ = ggLin (p := p) ι (g.1 * φ i) v := by rw [map_mul,LinearEquiv.mul_apply]
      _ = ggLin (p := p) ι (φ i * g.1) v := by rw [he]
      _ = ggLin (p := p) ι (φ i) (ggLin (p := p) ι g.1 v) := by rw [map_mul,LinearEquiv.mul_apply]
      _ = _ := hlin _ _
  by_cases hD4 : ∃ e : Fin 4 ≃ Λ, M = (ggCoxeterMatrixD 4).reindex e
  · obtain ⟨e,he⟩ := hD4
    have hz : Nat.card Z ≤ 2 * (p - 1) := card_weyl_commutant_full_rank_sign_le hp2
      hH.2.2.2.1 ι Z hZ hM hC h a hpair hcomm yV hyV hay hGy hF
      (ggIntCartan_rank_eq_card_of_typeD4 hp2 hC e he)
      (fun g => hdet g.1 g.2.1.1)
    have hi := card_inner_le_half_of_d4 f e he
    have hb := ggNbr_card_stabilizer_le_inner_mul_commutant hH hcardK hy hM φ hrefl hRC f hf
      (GGIsWeylMatrix.card_autPerm_le_six hM) hz
    exact hb.trans_eq (by rw [← hi]; ring)
  · have hz : Nat.card Z ≤ 2 * p := by
      rcases hcase with hcop | hp5 | hfull | hdim | hyU
      · exact card_weyl_commutant_coprime_sign_le hH.2.2.2.1 ι Z hZ
          hM hC h a hpair hcomm yV hyV hay hGy hF (fun g => hdet g.1 g.2.1.1) hp2 hcop
      · subst p
        exact card_weyl_commutant_five_sign_le_ten hH.2.2.2.1 ι Z hZ
          hM hC h a hpair hcomm yV hyV hay hGy hF (fun g => hdet g.1 g.2.1.1)
      · have hb := card_weyl_commutant_full_rank_sign_le hp2 hH.2.2.2.1 ι Z hZ
          hM hC h a hpair hcomm yV hyV hay hGy hF hfull (fun g => hdet g.1 g.2.1.1)
        exact hb.trans (Nat.mul_le_mul_left 2 (Nat.sub_le p 1))
      · have hb := card_weyl_commutant_coroot_line_sign_le hp2 hH.2.2.2.1 ι Z hZ
          hM hC h a hpair hcomm yV hGy hdim (fun g => hdet g.1 g.2.1.1)
        exact hb.trans (Nat.mul_le_mul_left 2 (Nat.sub_le p 1))
      · exact card_weyl_commutant_axis_in_coroot_sign_le hp2 hH.2.2.2.1 ι Z hZ
          hM hC h a hpair hcomm yV hyV hay hGy hF hyU (fun g => hdet g.1 g.2.1.1)
    have hb := ggNbr_card_stabilizer_le_of_commutant hH hcardK hy hM φ hrefl hRC f hf
      (GGIsWeylMatrix.card_autPerm_le_two hM hD4) hz
    have hnum : (Nat.card (ggAutomizer K Bs) * 2) * (2 * p) ≤
        (p-1) * 6 * Nat.card (ggAutomizer K Bs) := by
      have hp3 : 3 ≤ p := by
        have hp := (Fact.out : p.Prime).two_le
        omega
      have hnum : 4 * p ≤ 6 * (p - 1) := by omega
      nlinarith
    exact hb.trans hnum

theorem ggResCentBoundNbr_three_of_weylDatum_rank {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hy : y ∈ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (φ : Λ → MulAut ↥Bs) (hrefl : ∀ i, GGIsReflection 3 (φ i))
    (f : M.Group ≃* ↥(ggAutomizer K Bs))
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hcl : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (h : Λ → V) (a : Λ → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod 3))
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - a i v • h i)
    (hF : Module.finrank (ZMod 3) (LinearMap.pi a).ker ≤ 2)
    (h3 : 3 ≤ Fintype.card Λ) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y,hy⟩ : Bs)) ≤
        (3 - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := by
  have : Nonempty Λ := Fintype.card_pos_iff.mp (by omega)
  have hKcard : 3 ^ 3 ≤ Nat.card ↥(Bs ⊓ K) := ggNbr_card_inf_of_weyl_rank_three (by decide)
    hH hM hC ι φ h a (fun i => (hf i) ▸ (f (M.simple i)).2) hpair hlin h3
  have hRC := ggReflConjSimple_of_weylMatrix (by decide : 3 ≠ 2) hM h3 hC ι φ h a hpair hlin hcl
  exact ggResCentBoundNbr_three_of_weylDatum hH hy hKcard hM hC φ hrefl hRC f hf
    ι h a hpair hlin hF

theorem ggResCentBoundNbr_three_of_weylDatum_fixed {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hy : y ∈ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (φ : Λ → MulAut ↥Bs) (hrefl : ∀ i, GGIsReflection 3 (φ i))
    (f : M.Group ≃* ↥(ggAutomizer K Bs))
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hcl : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (h : Λ → V) (a : Λ → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod 3))
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - a i v • h i)
    (hfix : ∀ b : Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G))
    (h3 : 3 ≤ Fintype.card Λ) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y,hy⟩ : Bs)) ≤
        (3 - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := by
  classical
  have : Finite V := Finite.of_equiv (Additive Bs) ι.toEquiv
  let F := (LinearMap.pi a).ker
  let f0 : F → ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := fun v =>
    ⟨(Additive.toMul (ι.symm v.1) : Bs), by
      refine ⟨(Additive.toMul (ι.symm v.1) : Bs).2, ?_⟩
      apply hfix
      intro ψ hψ
      have hzero : ∀ i, a i v.1 = 0 := by
        intro i
        exact congrFun (LinearMap.mem_ker.mp v.2) i
      have hφ : ∀ i, φ i (Additive.toMul (ι.symm v.1)) = Additive.toMul (ι.symm v.1) := by
        intro i
        apply ι.injective
        change ι (Additive.ofMul (φ i (Additive.toMul (ι.symm v.1)))) = _
        rw [← ggLin_apply_ofMul (p := 3),hlin,ofMul_toMul,ι.apply_symm_apply,hzero,zero_smul,sub_zero]
        exact (ι.apply_symm_apply v.1).symm
      rw [hcl] at hψ
      exact ggFixed_of_mem_closure φ _ hφ ψ hψ⟩
  have hinj : Function.Injective f0 := by
    intro v w hvw
    have h := congrArg Subtype.val hvw
    have hh : (Additive.toMul (ι.symm v.1) : Bs) = Additive.toMul (ι.symm w.1) := Subtype.ext h
    exact Subtype.ext (ι.symm.injective (Additive.toMul.injective hh))
  have hcard : Nat.card F ≤ 3^2 := (Nat.card_le_card_of_injective _ hinj).trans
    (card_bstar_inf_centralizer_le hH.1 hH.2.2.2.2.1)
  have hF : Module.finrank (ZMod 3) F ≤ 2 := by
    have h := FiniteField.pow_finrank_eq_natCard 3 F
    rw [← h] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hcard
  exact ggResCentBoundNbr_three_of_weylDatum_rank hH hy hM hC φ hrefl f hf hcl
    ι h a hpair hlin hF h3

theorem ggResCentBoundNbr_three_of_torData {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hy : y ∈ Bs)
    {m N : ℕ} {M : CoxeterMatrix (Fin N)} {C : Matrix (Fin N) (Fin N) ℤ}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) (hm : Odd m) (hpm : 3 ∣ m)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hTor : GGTorusTorData m N C M ↥K (ggGamma K hN).range) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y,hy⟩ : Bs)) ≤
        (3 - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := by
  classical
  have hBs : IsElemAbelian 3 Bs := hH.1.tableB_facts.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  obtain ⟨w,hw⟩ := hTor
  have h3 : 3 ≤ N := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp
    ((pow_three_le_card_range_ggGamma_bstar hH.1 hH.2.2.2.2.1 hN).trans
      (ggTD_card_range_le_pow hm hpm hBs hS hN w hw))
  obtain ⟨V,hVadd,hVmod,hι⟩ := exists_ggLinData (p := 3) (G := G) (Bs := Bs) hBs
  let : AddCommGroup V := hVadd
  let : Module (ZMod 3) V := hVmod
  obtain ⟨ι⟩ := hι
  have : Finite V := Finite.of_equiv (Additive Bs) ι.toEquiv
  have : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  obtain ⟨hnk,hbk,a,hlin,hpair,-,hsep⟩ := ggTD_linearData hm hpm hBs hS hN w hw V ι
  obtain ⟨f,hf⟩ := ggTD_weyl hN hw (by decide : 3 ≠ 2) hBs hnk
  have hcl := ggTD_closure hN hw (by decide : 3 ≠ 2) hBs hnk
  let φ : Fin N → MulAut Bs := fun i => ggTDρB K Bs (ggTDnH w hnk i)
  let h : Fin N → V := fun i => ι (Additive.ofMul (⟨_,hbk i⟩ : Bs))
  have h2 : ∀ i, a i (h i) = 2 := by
    intro i
    rw [hpair i i,hC.1 i]
    norm_num
  have hrefl : ∀ i, GGIsReflection 3 (φ i) := fun i =>
    ggIsReflection_of_eq_reflection (by decide) ι (h2 i)
      (ggLin_eq_reflection ι (h2 i) (hlin i))
  have hfix : ∀ b : Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G) := by
    intro b hb
    have hz : ∀ i, a i (ι (Additive.ofMul b)) = 0 := by
      intro i
      have hmem : φ i ∈ ggAutomizer K Bs := by
        change ggTDρB K Bs (ggTDnH w hnk i) ∈ _
        rw [← hf i]
        exact (f (M.simple i)).2
      have hφ : φ i b = b := hb _ hmem
      have he : ggLin (p := 3) ι (φ i) (ι (Additive.ofMul b)) = ι (Additive.ofMul b) := by
        rw [ggLin_apply_ofMul,hφ]
      rw [hlin] at he
      have hhi : h i ≠ 0 := by
        intro hi
        have htwo : a i (h i) = (2 : ZMod 3) := h2 i
        rw [hi,map_zero] at htwo
        exact (zmod_two_ne_zero (p := 3) (by decide)) htwo.symm
      exact (smul_eq_zero.mp (sub_eq_self.mp he)).resolve_right hhi
    apply (ggGamma_eq_one_iff K hN b).mp
    simpa only [ι.symm_apply_apply,toMul_ofMul] using hsep _ hz
  exact ggResCentBoundNbr_three_of_weylDatum_fixed hH hy hM hC φ hrefl f hf hcl
    ι h a hpair hlin hfix (by simpa using h3)

theorem ggResCentBoundNbr_of_weylDatum_line {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (φ : Λ → MulAut ↥Bs) (hrefl : ∀ i, GGIsReflection p (φ i))
    (f : M.Group ≃* ↥(ggAutomizer K Bs))
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hcl : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (h : Λ → V) (a : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod p))
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - a i v • h i)
    (hker : ∀ v, (∀ i, a i v = 0) →
      v ∈ Submodule.span (ZMod p) {ι (Additive.ofMul (⟨y,hy⟩ : Bs))}) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y,hy⟩ : Bs)) ≤
        (p - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := by
  classical
  let H := (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
    MulAction.stabilizer (MulAut ↥Bs) (⟨y,hy⟩ : Bs)
  let Z := H ⊓ Subgroup.centralizer (Set.range φ)
  have hy1 : y ≠ 1 := (GGResHyp.data_K hH).2.1
  let Z0 : Subgroup H := (Subgroup.centralizer (Set.range φ)).comap H.subtype
  have hZeq : Z0.map H.subtype = Z := by
    ext g
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.2, hk⟩
    · rintro ⟨hg, hcentral⟩
      exact ⟨⟨g, hg⟩, hcentral, rfl⟩
  have hZtop : H ≤ ggAutomizer ⊤ Bs :=
    fun g hg => sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hg.1
  have hZstab : H ≤ MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs) := inf_le_right
  have hVfin : Finite V := Finite.of_equiv (Additive Bs) ι.toEquiv
  let : Finite V := hVfin
  have hcard : p ^ 4 ≤ Nat.card V := by
    have he : Nat.card V = Nat.card Bs := (Nat.card_congr ι.toEquiv).symm.trans (Nat.card_congr Additive.toMul)
    rw [he]
    exact hH.1.tableB_facts.2.2.2.2
  have hfin4 : 4 ≤ Module.finrank (ZMod p) V := by
    rw [← FiniteField.pow_finrank_eq_natCard p V] at hcard
    exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hcard
  have hdim := ggWeylDatum_finrank_le a (ι (Additive.ofMul (⟨y, hy⟩ : Bs))) hker
  have h3 : 3 ≤ Fintype.card Λ := by omega
  have : Nonempty Λ := Fintype.card_pos_iff.mp (by omega)
  have hcardK := ggNbr_card_inf_of_weyl_rank_three hp2 hH hM hC ι φ h a
    (fun i => (hf i) ▸ (f (M.simple i)).2) hpair hlin h3
  have hRC := ggReflConjSimple_of_weylMatrix hp2 hM h3 hC ι φ h a hpair hlin hcl
  have hZcomm : ∀ g : Z0, ∀ i, (g.1.1 : MulAut Bs) * φ i = φ i * g.1.1 := by
    intro g i
    exact (Subgroup.mem_centralizer_iff.mp g.2 (φ i) ⟨i,rfl⟩).symm
  have hZcard := ggResCent_ker_card hp2 hH.1.tableB_facts.2.1 hH.2.2.2.1 hy hy1
    hM hC hpair hlin hker (inferInstance : Nonempty Λ) hfin4 hZtop hZstab hZcomm
  have hz : Nat.card Z ≤ p - 1 := by
    rw [← hZeq,← Nat.card_congr (Z0.equivMapOfInjective H.subtype Subtype.val_injective).toEquiv]
    exact hZcard
  have hb := ggNbr_card_stabilizer_le_of_commutant hH hcardK hy hM φ hrefl hRC f hf
    (GGIsWeylMatrix.card_autPerm_le_six hM) hz
  exact hb.trans_eq (by ring)

theorem bstar_eq_of_split_linear_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hLab : GGHasLabel ⟨.A, r, f⟩ (K ⧸ Subgroup.center K))
    (hΛ : LargeEvenInLambda2 ⟨.A, r, f⟩) : Bs = B := by
  obtain ⟨F,hField,hFinite,hChar,hN,φ,hF,hφs,hker,hdiag⟩ :=
    exists_diagonal_cover_of_large_linear_K hRig hH hr hpq hLab hΛ
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  let ψ : Matrix.SpecialLinearGroup (Fin (r + 1)) F →* G := K.subtype.comp φ
  have hψker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (r + 1)) F) := by
    intro g hg
    have hφ : φ g = 1 := K.subtype_injective (MonoidHom.mem_ker.mp hg)
    exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_le_center (r+1) F (hker g hφ)
  have hψdiag : ∀ b ∈ Bs, GGActsDiag ψ b := by
    intro b hb
    obtain ⟨t,ht⟩ := hdiag (ggGamma K hN ⟨b,hb⟩) ⟨⟨b,hb⟩,rfl⟩
    obtain ⟨E,hE,haE⟩ := ht
    let u : Fin (r+1) → Fˣ := fun k => Units.mk0 (t k)
      (TypeANbrDvd.ActsDiag.ne_zero ⟨E,hE,haE⟩ k)
    have hEu : E = ggDiagUnit u := by
      apply Units.ext
      rw [hE]
      rfl
    refine ⟨u,fun s => ?_⟩
    have hact := congrArg K.subtype (haE s)
    change (((ggGamma K hN ⟨b,hb⟩) (φ s)) : G) =
      ((φ (ComponentClassification.CatalogueBHigherLinearAction.slConjugation (r+1) F E s)) : G) at hact
    rw [ggGamma_coe] at hact
    change b * ψ s * b⁻¹ = ψ (ggDiagConj u s)
    rw [show b * ψ s * b⁻¹ = ((φ
      (ComponentClassification.CatalogueBHigherLinearAction.slConjugation (r+1) F E s)) : G) from hact,hEu]
    rfl
  exact hH.1.bstar_eq_of_linear_diagonal hψker (by omega) hψdiag

theorem centralizer_line_of_split_linear_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hLab : GGHasLabel ⟨.A, r, f⟩ (K ⧸ Subgroup.center K))
    (hΛ : LargeEvenInLambda2 ⟨.A, r, f⟩) :
    Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
  rw [bstar_eq_of_split_linear_K hRig hH hr hpq hLab hΛ]
  exact inf_centralizer_eq_zpowers_of_sHat hH.2.2.2.2.1.1

theorem ggResCentBoundNbr_of_xDatum_line {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hDatum : GGResXDatum p Bs K)
    (hfix : ∀ b : Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) →
      (b : G) ∈ Subgroup.zpowers y) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y,hy⟩ : Bs)) ≤
        (p - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := by
  obtain ⟨Λ,hΛf,hΛd,M,C,V,hVadd,hVmod,ι,φ,h,a,hM,hC,hlin,hrefl,hpair,⟨f,hf⟩,hcl⟩ := hDatum
  let : Fintype Λ := hΛf
  let : DecidableEq Λ := hΛd
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  have : Finite V := Finite.of_equiv (Additive Bs) ι.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hker := ggWeylDatum_rootKernel_le_line_of_fix hlin hy (by
    intro b hb
    apply hfix b
    rw [hcl]
    exact ggFixed_of_mem_closure φ b hb)
  exact ggResCentBoundNbr_of_weylDatum_line hp2 hH hy hM hC φ hrefl f hf hcl
    ι h a hpair hlin hker

theorem ggResCentBoundNbr_of_torData_line {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    {m N : ℕ} {M : CoxeterMatrix (Fin N)} {C : Matrix (Fin N) (Fin N) ℤ}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) (hm : Odd m) (hpm : p ∣ m)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hTor : GGTorusTorData m N C M ↥K (ggGamma K hN).range)
    (hCen : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y,hy⟩ : Bs)) ≤
        (p - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := by
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hDatum := ggResXDatum_of_torData hp2 hm hpm hM hC hBs hS hN hTor
  exact ggResCentBoundNbr_of_xDatum_line hp2 hH hy hDatum (by
    intro b hb
    exact hCen ⟨b.2, ggTD_fix_mem_centralizer hm hpm hBs hS hN hTor b hb⟩)

theorem ggResCentBoundNbr_of_tbTor_line
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hK : GGInnerDiagOnLabel GGTBTorCov p Bs K)
    (hCen : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y,hy⟩ : Bs)) ≤
        (p - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := by
  obtain ⟨m,N,C,M,hN,hm,hpm,hM,hC,hTor⟩ :=
    l05nPlP4_core_K (ggTBTorWRows_of_all hT) hLift hH hK
  exact ggResCentBoundNbr_of_torData_line hH.1.1.2.2.2.2.2.1.2.1 hH hy hM hC hm hpm hN hTor hCen

private theorem ggResCentBoundNbr_of_weylDatum_small_commutant_fixed
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (φ : Λ → MulAut Bs) (hrefl : ∀ i, GGIsReflection p (φ i))
    (f : M.Group ≃* ggAutomizer K Bs)
    (hf : ∀ i, (f (M.simple i) : MulAut Bs) = φ i)
    (hcl : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ι : Additive Bs ≃+ V) (h : Λ → V) (a : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod p))
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - a i v • h i)
    (hfix : ∀ b : Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G))
    (h3 : 3 ≤ Fintype.card Λ)
    (hcase : Nat.Coprime (p - 1) (2 * Module.finrank (ZMod p) V - 3) ∨
      p = 5 ∨ Matrix.rank (C.map (Int.castRingHom (ZMod p))) = Fintype.card Λ ∨
      Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p)
        ↥(Submodule.span (ZMod p) (Set.range h) ⊔
          Submodule.span (ZMod p) {ι (Additive.ofMul (⟨y,hy⟩ : Bs))}) + 1 ∨
      ι (Additive.ofMul (⟨y,hy⟩ : Bs)) ∈ Submodule.span (ZMod p) (Set.range h))
    (hdet : ∀ g ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, (ggLin (p := p) ι g).det ^ 2 = 1) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (p-1) * 6 * Nat.card (ggAutomizer K Bs) := by
  classical
  have : Nonempty Λ := Fintype.card_pos_iff.mp (by omega)
  have : Finite V := Finite.of_equiv (Additive Bs) ι.toEquiv
  let F := (LinearMap.pi a).ker
  let f0 : F → ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := fun v =>
    ⟨(Additive.toMul (ι.symm v.1) : Bs), by
      refine ⟨(Additive.toMul (ι.symm v.1) : Bs).2, ?_⟩
      apply hfix
      intro ψ hψ
      have hzero : ∀ i, a i v.1 = 0 := by
        intro i
        exact congrFun (LinearMap.mem_ker.mp v.2) i
      have hφ : ∀ i, φ i (Additive.toMul (ι.symm v.1)) = Additive.toMul (ι.symm v.1) := by
        intro i
        apply ι.injective
        change ι (Additive.ofMul (φ i (Additive.toMul (ι.symm v.1)))) = _
        rw [← ggLin_apply_ofMul (p := p),hlin,ofMul_toMul,ι.apply_symm_apply,hzero,zero_smul,sub_zero]
        exact (ι.apply_symm_apply v.1).symm
      rw [hcl] at hψ
      exact ggFixed_of_mem_closure φ _ hφ ψ hψ⟩
  have hinj : Function.Injective f0 := by
    intro v w hvw
    have h := congrArg Subtype.val hvw
    have hh : (Additive.toMul (ι.symm v.1) : Bs) = Additive.toMul (ι.symm w.1) := Subtype.ext h
    exact Subtype.ext (ι.symm.injective (Additive.toMul.injective hh))
  have hcard : Nat.card F ≤ p^2 := (Nat.card_le_card_of_injective _ hinj).trans
    (card_bstar_inf_centralizer_le hH.1 hH.2.2.2.2.1)
  have hF : Module.finrank (ZMod p) F ≤ 2 := by
    rw [← FiniteField.pow_finrank_eq_natCard p F] at hcard
    exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hcard
  have hcardK := ggNbr_card_inf_of_weyl_rank_three hp2 hH hM hC ι φ h a
    (fun i => (hf i) ▸ (f (M.simple i)).2) hpair hlin h3
  have hRC := ggReflConjSimple_of_weylMatrix hp2 hM h3 hC ι φ h a hpair hlin hcl
  exact ggResCentBoundNbr_of_weylDatum_small_commutant hp2 hH hy hcardK hM hC φ hrefl hRC
    f hf ι h a hpair hlin hF hcase hdet

theorem ggResCentBoundNbr_of_weylDatum_coroot_cases_fixed
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (φ : Λ → MulAut Bs) (hrefl : ∀ i, GGIsReflection p (φ i))
    (f : M.Group ≃* ggAutomizer K Bs)
    (hf : ∀ i, (f (M.simple i) : MulAut Bs) = φ i)
    (hcl : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ι : Additive Bs ≃+ V) (h : Λ → V) (a : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod p))
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - a i v • h i)
    (hfix : ∀ b : Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G))
    (h3 : 3 ≤ Fintype.card Λ)
    (hcase : Matrix.rank (C.map (Int.castRingHom (ZMod p))) = Fintype.card Λ ∨
      Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p)
        ↥(Submodule.span (ZMod p) (Set.range h) ⊔
          Submodule.span (ZMod p) {ι (Additive.ofMul (⟨y,hy⟩ : Bs))}) + 1 ∨
      ι (Additive.ofMul (⟨y,hy⟩ : Bs)) ∈ Submodule.span (ZMod p) (Set.range h))
    (hdet : ∀ g ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, (ggLin (p := p) ι g).det ^ 2 = 1) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (p-1) * 6 * Nat.card (ggAutomizer K Bs) := by
  exact ggResCentBoundNbr_of_weylDatum_small_commutant_fixed hp2 hH hy hM hC φ hrefl
    f hf hcl ι h a hpair hlin hfix h3 (Or.inr (Or.inr hcase)) hdet

theorem ggResCentBoundNbr_of_weylDatum_full_rank_fixed
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (φ : Λ → MulAut Bs) (hrefl : ∀ i, GGIsReflection p (φ i))
    (f : M.Group ≃* ggAutomizer K Bs)
    (hf : ∀ i, (f (M.simple i) : MulAut Bs) = φ i)
    (hcl : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ι : Additive Bs ≃+ V) (h : Λ → V) (a : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod p))
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - a i v • h i)
    (hfix : ∀ b : Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G))
    (h3 : 3 ≤ Fintype.card Λ)
    (hfull : Matrix.rank (C.map (Int.castRingHom (ZMod p))) = Fintype.card Λ)
    (hdet : ∀ g ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, (ggLin (p := p) ι g).det ^ 2 = 1) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (p-1) * 6 * Nat.card (ggAutomizer K Bs) := by
  exact ggResCentBoundNbr_of_weylDatum_coroot_cases_fixed hp2 hH hy hM hC φ hrefl
    f hf hcl ι h a hpair hlin hfix h3 (Or.inl hfull) hdet

theorem ggResCentBoundNbr_of_torData_nonsingular
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    {m N : ℕ} {M : CoxeterMatrix (Fin N)} {C : Matrix (Fin N) (Fin N) ℤ}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) (hm : Odd m) (hpm : p ∣ m)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hTor : GGTorusTorData m N C M K (ggGamma K hN).range)
    (hdetC : ¬ (p : ℤ) ∣ C.det) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (p-1) * 6 * Nat.card (ggAutomizer K Bs) := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  obtain ⟨w,hw⟩ := hTor
  have h3 : 3 ≤ N := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    ((pow_three_le_card_range_ggGamma_bstar hH.1 hH.2.2.2.2.1 hN).trans
      (ggTD_card_range_le_pow hm hpm hBs hS hN w hw))
  obtain ⟨V,hVadd,hVmod,hι⟩ := exists_ggLinData (p := p) (G := G) (Bs := Bs) hBs
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  obtain ⟨ι⟩ := hι
  have : Finite V := Finite.of_equiv (Additive Bs) ι.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  obtain ⟨hnk,hbk,a,hlin,hpair,-,hsep⟩ := ggTD_linearData hm hpm hBs hS hN w hw V ι
  obtain ⟨f,hf⟩ := ggTD_weyl hN hw hp2 hBs hnk
  have hcl := ggTD_closure hN hw hp2 hBs hnk
  let φ : Fin N → MulAut Bs := fun i => ggTDρB K Bs (ggTDnH w hnk i)
  let h : Fin N → V := fun i => ι (Additive.ofMul (⟨_,hbk i⟩ : Bs))
  have h2 : ∀ i, a i (h i) = 2 := by intro i;rw [hpair i i,hC.1 i];norm_num
  have hrefl : ∀ i, GGIsReflection p (φ i) := fun i =>
    ggIsReflection_of_eq_reflection hp2 ι (h2 i) (ggLin_eq_reflection ι (h2 i) (hlin i))
  have hfix := ggTD_fix_mem_centralizer hm hpm hBs hS hN ⟨w,hw⟩
  have hfull : Matrix.rank (C.map (Int.castRingHom (ZMod p))) = Fintype.card (Fin N) := by
    let A := C.map (Int.castRingHom (ZMod p))
    have hk : A.mulVecLin.ker = ⊥ := by
      ext c
      simp only [LinearMap.mem_ker,Submodule.mem_bot]
      constructor
      · intro hc
        exact ggCartan_ker_zero_of_not_dvd_det C hdetC c (by
          intro j
          have hj := congrFun hc j
          simpa [A,Matrix.mulVec,dotProduct] using hj)
      · rintro rfl
        simp
    have hr := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [hk] at hr
    change Module.finrank (ZMod p) A.mulVecLin.range = Fintype.card (Fin N)
    simpa using hr
  exact ggResCentBoundNbr_of_weylDatum_full_rank_fixed hp2 hH hy hM hC φ hrefl f hf hcl
    ι h a hpair hlin hfix (by simpa using h3) hfull
    (fun g hg => hH.join_det_sq_eq_one_of_dichotomy hX hTCJ hRig ι hg)

private theorem ggResCentBoundNbr_of_torData_small_commutant
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    {m N : ℕ} {M : CoxeterMatrix (Fin N)} {C : Matrix (Fin N) (Fin N) ℤ}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) (hm : Odd m) (hpm : p ∣ m)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hTor : GGTorusTorData m N C M K (ggGamma K hN).range)
    (hcase : Nat.Coprime (p - 1) (2 * Nat.log p (Nat.card Bs) - 3) ∨
      p = 5 ∨ Nat.card Bs ≤ p * Nat.card
        ↥((ggBstarComm K Bs).map Bs.subtype ⊔ Subgroup.zpowers y) ∨
      y ∈ (ggBstarComm K Bs).map Bs.subtype) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (p-1) * 6 * Nat.card (ggAutomizer K Bs) := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  obtain ⟨w,hw⟩ := hTor
  have h3 : 3 ≤ N := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    ((pow_three_le_card_range_ggGamma_bstar hH.1 hH.2.2.2.2.1 hN).trans
      (ggTD_card_range_le_pow hm hpm hBs hS hN w hw))
  obtain ⟨V,hVadd,hVmod,hι⟩ := exists_ggLinData (p := p) (G := G) (Bs := Bs) hBs
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  obtain ⟨ι⟩ := hι
  have : Finite V := Finite.of_equiv (Additive Bs) ι.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  obtain ⟨hnk,hbk,a,hlin,hpair,-,hsep⟩ := ggTD_linearData hm hpm hBs hS hN w hw V ι
  obtain ⟨f,hf⟩ := ggTD_weyl hN hw hp2 hBs hnk
  have hcl := ggTD_closure hN hw hp2 hBs hnk
  let φ : Fin N → MulAut Bs := fun i => ggTDρB K Bs (ggTDnH w hnk i)
  let h : Fin N → V := fun i => ι (Additive.ofMul (⟨_,hbk i⟩ : Bs))
  have h2 : ∀ i, a i (h i) = 2 := by intro i;rw [hpair i i,hC.1 i];norm_num
  have hrefl : ∀ i, GGIsReflection p (φ i) := fun i =>
    ggIsReflection_of_eq_reflection hp2 ι (h2 i) (ggLin_eq_reflection ι (h2 i) (hlin i))
  have hfix := ggTD_fix_mem_centralizer hm hpm hBs hS hN ⟨w,hw⟩
  have hdimBs : Nat.log p (Nat.card Bs) = Module.finrank (ZMod p) V := by
    rw [card_eq_of_ggLin ι,← FiniteField.pow_finrank_eq_natCard p V,
      Nat.log_pow (Fact.out : p.Prime).one_lt]
  have hc : Nat.Coprime (p - 1) (2 * Module.finrank (ZMod p) V - 3) ∨
      p = 5 ∨ Matrix.rank (C.map (Int.castRingHom (ZMod p))) = Fintype.card (Fin N) ∨
      Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p)
        ↥(Submodule.span (ZMod p) (Set.range h) ⊔
          Submodule.span (ZMod p) {ι (Additive.ofMul (⟨y,hy⟩ : Bs))}) + 1 ∨
      ι (Additive.ofMul (⟨y,hy⟩ : Bs)) ∈ Submodule.span (ZMod p) (Set.range h) := by
    rcases hcase with hcop | hp5 | hcard | hyComm
    · exact Or.inl (by rwa [hdimBs] at hcop)
    · exact Or.inr (Or.inl hp5)
    · right; right; right; left
      let U := Submodule.span (ZMod p) (Set.range h) ⊔
        Submodule.span (ZMod p) {ι (Additive.ofMul (⟨y,hy⟩ : Bs))}
      have hle := ggSpanSub_coroot_axis_le ι hlin hrefl hcl (⟨y,hy⟩ : Bs)
      have hineq : Nat.card V ≤ p * Nat.card U := by
        rw [← card_eq_of_ggLin ι]
        exact hcard.trans (Nat.mul_le_mul_left p ((Subgroup.card_le_of_le hle).trans_eq
          (card_ggSpanSub ι U)))
      rw [← FiniteField.pow_finrank_eq_natCard p V,
        ← FiniteField.pow_finrank_eq_natCard p U,← pow_succ'] at hineq
      exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hineq
    · right; right; right; right
      obtain ⟨c,hc,hcy⟩ := hyComm
      have hceq : c = (⟨y,hy⟩ : Bs) := Subtype.ext hcy
      rw [hceq] at hc
      exact ggBstarComm_le_span hlin hcl hc
  exact ggResCentBoundNbr_of_weylDatum_small_commutant_fixed hp2 hH hy hM hC φ hrefl f hf hcl
    ι h a hpair hlin hfix (by simpa using h3) hc
    (fun g hg => hH.join_det_sq_eq_one_of_dichotomy hX hTCJ hRig ι hg)

theorem ggResCentBoundNbr_of_torData_coroot_cases
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    {m N : ℕ} {M : CoxeterMatrix (Fin N)} {C : Matrix (Fin N) (Fin N) ℤ}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) (hm : Odd m) (hpm : p ∣ m)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hTor : GGTorusTorData m N C M K (ggGamma K hN).range)
    (hcase : Nat.card Bs ≤ p * Nat.card
        ↥((ggBstarComm K Bs).map Bs.subtype ⊔ Subgroup.zpowers y) ∨
      y ∈ (ggBstarComm K Bs).map Bs.subtype) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (p-1) * 6 * Nat.card (ggAutomizer K Bs) := by
  exact ggResCentBoundNbr_of_torData_small_commutant hX hTCJ hRig hH hy
    hM hC hm hpm hN hTor (Or.inr (Or.inr hcase))

theorem ggResCentBoundNbr_of_tbTor_nonsingular
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hK : GGInnerDiagOnLabel GGTBTorNonsingularCov p Bs K) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (p-1) * 6 * Nat.card (ggAutomizer K Bs) := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨lab,r,m,N,C,M,R,hR,θ,I,hN,hperf,hlab,hrow,hdet,hBsI,hLift,hT,-⟩ :=
    l05nPlQ_marking_with (ggTBTorWRows_of_all hT) hLift hp2
      (fun _ _ _ C _ => ¬ (p : ℤ) ∣ C.det) hK
  have hTB := ggTorusTBGroup_of_nbr hH.1 hH.2.2.2.2.1 hperf θ hN hBsI hLift
  have hTor := hT K (ggQuotHom θ) (ggGamma K hN).range hTB
  obtain ⟨hm,hpm,hM,hC⟩ := l05nPlP1_row_facts Fact.out hp2 hlab hrow
  exact ggResCentBoundNbr_of_torData_nonsingular hX hTCJ hRig hH hy hM hC hm hpm hN hTor hdet

theorem ggResCentBoundNbr_of_tbTor_coroot_cases
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hK : GGInnerDiagOnLabel GGTBTorCov p Bs K)
    (hcase : Nat.card Bs ≤ p * Nat.card
        ↥((ggBstarComm K Bs).map Bs.subtype ⊔ Subgroup.zpowers y) ∨
      y ∈ (ggBstarComm K Bs).map Bs.subtype) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (p-1) * 6 * Nat.card (ggAutomizer K Bs) := by
  obtain ⟨m,N,C,M,hN,hm,hpm,hM,hC,hTor⟩ :=
    l05nPlP4_core_K (ggTBTorWRows_of_all hT) hLift hH hK
  exact ggResCentBoundNbr_of_torData_coroot_cases hX hTCJ hRig hH hy hM hC hm hpm hN hTor hcase

theorem ggResCentBoundNbr_five_of_tbTor
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] [Fact (Nat.Prime 5)]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 5 B Bs x L D J y K) (hy : y ∈ Bs)
    (hK : GGInnerDiagOnLabel GGTBTorCov 5 Bs K) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (5-1) * 6 * Nat.card (ggAutomizer K Bs) := by
  obtain ⟨m,N,C,M,hN,hm,hpm,hM,hC,hTor⟩ :=
    l05nPlP4_core_K (ggTBTorWRows_of_all hT) hLift hH hK
  exact ggResCentBoundNbr_of_torData_small_commutant hX hTCJ hRig hH hy
    hM hC hm hpm hN hTor (Or.inr (Or.inl rfl))

theorem ggResCentBoundNbr_of_tbTor_coprime
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hK : GGInnerDiagOnLabel GGTBTorCov p Bs K)
    (hcop : Nat.Coprime (p - 1) (2 * Nat.log p (Nat.card Bs) - 3)) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (p-1) * 6 * Nat.card (ggAutomizer K Bs) := by
  obtain ⟨m,N,C,M,hN,hm,hpm,hM,hC,hTor⟩ :=
    l05nPlP4_core_K (ggTBTorWRows_of_all hT) hLift hH hK
  exact ggResCentBoundNbr_of_torData_small_commutant hX hTCJ hRig hH hy
    hM hC hm hpm hN hTor (Or.inl hcop)

theorem ggResCentBoundNbr_three_of_tbTor
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K) (hy : y ∈ Bs)
    (hK : GGInnerDiagOnLabel GGTBTorCov 3 Bs K) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y,hy⟩ : Bs)) ≤
        (3 - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := by
  obtain ⟨m,N,C,M,hN,hm,hpm,hM,hC,hTor⟩ :=
    l05nPlP4_core_K (ggTBTorWRows_of_all hT) hLift hH hK
  exact ggResCentBoundNbr_three_of_torData hH hy hM hC hm hpm hN hTor

theorem ggResCentBoundNbr_of_tbTor_split_linear
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hK : GGInnerDiagOnLabel GGTBTorSplitLinearCov p Bs K) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (p-1) * 6 * Nat.card (ggAutomizer K Bs) := by
  obtain ⟨lab,hlab,hhas,R,hR,I,F,θ,hcov,hN,hact⟩ := largeEvenMarking_exists_hasLabel hK
  obtain ⟨hTor,htag,hr,hp⟩ := hcov
  have hcen : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
    obtain ⟨t,r,f⟩ := lab
    simp only at htag hr hp
    subst htag
    exact centralizer_line_of_split_linear_K hRig hH hr hp hhas hlab
  have hKTor : GGInnerDiagOnLabel GGTBTorCov p Bs K := by
    obtain ⟨hperf,lab,hlab,hraw⟩ := hK
    exact ⟨hperf,lab,hlab,largeEvenRawDatum_mono (fun R _ I F => by
      rintro ⟨hs,hna,θ,⟨hcov,hN,hact⟩⟩
      exact ⟨hs,hna,θ,hcov.1,hN,hact⟩) hraw⟩
  exact ggResCentBoundNbr_of_tbTor_line hT hLift hH hy hKTor hcen.le

theorem ggResCentBoundNbr_three_of_unitary_six
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hy : y ∈ Bs)
    (hK : GGInnerDiagOnLabel GGNbrInner937U63Label 3 Bs K) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (3-1) * 6 * Nat.card (ggAutomizer K Bs) := by
  obtain ⟨lab,hΛ,hhas,R,hR,I,F,θ,hcov,hN,hact⟩ := largeEvenMarking_exists_hasLabel hK
  obtain ⟨⟨htw,hr,hpq,hpd⟩,hr5,hp3⟩ := hcov
  obtain ⟨f,hN,hf,hpm,hTor⟩ := ggTwA5Three_torDataAt hRig hLB hPJ hH
    (Or.inr ⟨rfl,rfl⟩) rfl hΛ hhas ⟨htw,hr5,hpq⟩
  have hm : Odd (2 ^ f + 1) := by
    obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    rw [pow_succ]
    exact ⟨2 ^ g,by omega⟩
  have hM : GGIsWeylMatrix (CoxeterMatrix.A 5) := by
    refine Or.inl ⟨5,Equiv.refl _,by norm_num,Or.inl ?_⟩
    apply CoxeterMatrix.ext
    ext i j
    rw [CoxeterMatrix.reindex_apply]
    simp
  exact ggResCentBoundNbr_three_of_torData hH hy hM (ggIntCartan_A 5) hm hpm hN hTor

theorem centralizer_line_of_original_unitary_L
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hpq : p ∣ 2 ^ f + 1)
    (hLab : GGHasLabel ⟨.twA,r,f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA,r,f⟩) :
    Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
  classical
  by_cases hEq : Bs = B
  · rw [hEq]
    exact inf_centralizer_eq_zpowers_of_sHat hH.2.2.2.2.1.1
  have hlt : B < Bs := lt_of_le_of_ne hH.1.2.1.1 (Ne.symm hEq)
  have hf : 2 ≤ f := by
    have hf1 : 1 ≤ f := hΛ.1
    by_contra hn
    have hfeq : f = 1 := by omega
    have hthree : p ∣ 3 := by simpa [hfeq] using hpq
    exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp hthree)
  have hCover : ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (φ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f F (r+1)) →* L),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin (r+1) → F, LineU.ActsDiagU φ a t := by
    by_cases hpd : p ∣ r+1
    · have hr5 : r ≠ 5 := by
        intro heq
        have hp6 : p ∣ 6 := by simpa [heq] using hpd
        have hp23 := (Fact.out : p.Prime).dvd_mul.mp (show p ∣ 2 * 3 from hp6)
        rcases hp23 with hp2 | hp3'
        · exact hH.1.1.2.2.2.2.2.1.2.1
            ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hp2)
        · exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp hp3')
      exact exists_diagonal_cover_of_large_unitary_L hRig hH hr hr5 hpq hpd hLab hΛ
    · exact exists_diagonal_cover_of_large_unitary_L_coprime hRig hH hr (Or.inr (by omega))
        hpq hpd hLab hΛ
  obtain ⟨F,hField,hFinite,hChar,hN,φ,hF,hM,hdiag⟩ := hCover
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hCJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D :=
    hH.centralizer_J_le_D_of_unitary hM hdiag hf (by omega) hpq hlt
  have hpJ : p ∣ Nat.card J := hPJ G p B x L D J hH.1.1 hH.1.2.2
  have hJK : J ≤ K := le_of_ggNbr hLB hH.1.1 hH.1.2.2 hpJ hH.2.2.2.2.1
  exact hH.2.2.2.2.1.bstar_inf_centralizer_eq_zpowers hH.1 hCJ hJK

theorem centralizer_line_of_unitary_L_marking
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel GGTableBUnitaryLiftLabel p Bs L) :
    Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
  classical
  obtain ⟨lab,hΛ,hhas,R,hR,I,F,θ,hcov,hN,hact⟩ := largeEvenMarking_exists_hasLabel hL
  obtain ⟨htype,hpq⟩ := hcov
  have hf : 2 ≤ lab.n := by
    have hf1 : 1 ≤ lab.n := hΛ.1
    by_contra hn
    have heq : lab.n = 1 := by omega
    have hthree : p ∣ 3 := by simpa [heq] using hpq
    exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp hthree)
  by_cases hpd : p ∣ lab.rank+1
  · have htw : lab.tag = .twA := by
      rcases htype with h | ⟨h,hr⟩
      · exact h
      · exfalso
        have hp4 : p ∣ 2 ^ 2 := by simpa [hr] using hpd
        exact hH.1.1.2.2.2.2.2.1.2.1
          ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
            ((Fact.out : p.Prime).dvd_of_dvd_pow hp4))
    have hp5 : 5 ≤ p := by
      have hp := (Fact.out : p.Prime).two_le
      have hp2 := hH.1.1.2.2.2.2.2.1.2.1
      have hp4 : p ≠ 4 := by intro h; have hh := (Fact.out : p.Prime); rw [h] at hh; norm_num at hh
      omega
    have hr4 : 4 ≤ lab.rank := by have hpR := Nat.le_of_dvd (by omega : 0 < lab.rank+1) hpd; omega
    obtain ⟨tag,r,f⟩ := lab
    simp only at htw hr4 hpq hhas hΛ
    subst htw
    exact centralizer_line_of_original_unitary_L hRig hLB hPJ hp3 hH hr4 hpq hhas hΛ
  · have hmark : LargeEvenMarking L (fun lab R _ I F θ =>
        GGStdSubSmallUnitaryLabel p lab ∧ LargeEvenSplit p lab ∧
          B ≤ Subgroup.normalizer (L : Set G) ∧
          ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' : L => (l' : G) = b⁻¹*l*b) φ) := by
      refine largeEvenMarking_mono (fun lab' R _ I F θ' hP => ?_)
        (ggInnerDiagOn_relabel hRig hH.2.2.1.1 hΛ hhas)
      obtain ⟨heq,hN',hact'⟩ := hP
      subst lab'
      have hsplit : LargeEvenSplit p lab := by
        rcases htype with htw | ⟨htw,hr⟩
        · exact Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted,htw],by simp [htw],hpq⟩)
        · exact Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted,htw],by simp [htw],hpq⟩)
      exact ⟨⟨⟨htype,hpq⟩,hpd,Or.inl hf⟩,hsplit,hH.1.2.1.1.trans hN',
        fun b hb => hact' b (hH.1.2.1.1 hb)⟩
    have hCJ := (GGStdSubFixedJOn_unitary G p B Bs x L D J hH.1 hmark).1
    have hpJ : p ∣ Nat.card J := hPJ G p B x L D J hH.1.1 hH.1.2.2
    have hJK : J ≤ K := le_of_ggNbr hLB hH.1.1 hH.1.2.2 hpJ hH.2.2.2.2.1
    exact hH.2.2.2.2.1.bstar_inf_centralizer_eq_zpowers hH.1 hCJ.le hJK

theorem centralizer_line_of_fixed_J_sectors
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLab
      (fun p lab => (GGTypeASplitLabel p lab ∨
        ((lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1)) ∨
        GGStdSubSmallUnitaryLabel p lab) p Bs L) :
    Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
  have hmark : LargeEvenMarking L (fun lab R _ I F θ =>
      ((GGTypeASplitLabel p lab ∨
        ((lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1)) ∨
        GGStdSubSmallUnitaryLabel p lab) ∧ LargeEvenSplit p lab ∧
        B ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' : L => (l' : G)=b⁻¹*l*b) φ) := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hL
    obtain ⟨hS,hSplit,hN,hact⟩ := hP
    exact ⟨hS,hSplit,hH.1.2.1.1.trans hN,fun b hb => hact b (hH.1.2.1.1 hb)⟩
  have hCJ := (GGStdSubFixedJOn_sectors G p B Bs x L D J hH.1 hmark).1
  have hpJ : p ∣ Nat.card J := hPJ G p B x L D J hH.1.1 hH.1.2.2
  have hJK : J ≤ K := le_of_ggNbr hLB hH.1.1 hH.1.2.2 hpJ hH.2.2.2.2.1
  exact hH.2.2.2.2.1.bstar_inf_centralizer_eq_zpowers hH.1 hCJ.le hJK

theorem ggResCentBoundNbr_of_tbTor_unitary_L
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hK : GGInnerDiagOnLabel GGTBTorCov p Bs K)
    (hL : GGInnerDiagOnLabel GGTableBUnitaryLiftLabel p Bs L) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (p-1) * 6 * Nat.card (ggAutomizer K Bs) := by
  exact ggResCentBoundNbr_of_tbTor_line hT hLift hH hy hK
    (centralizer_line_of_unitary_L_marking hRig hLB hPJ hp3 hH hL).le

theorem ggResCentBoundNbr_of_tbTor_fixed_J_sectors
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hK : GGInnerDiagOnLabel GGTBTorCov p Bs K)
    (hL : GGInnerDiagOnLab
      (fun p lab => (GGTypeASplitLabel p lab ∨
        ((lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1)) ∨
        GGStdSubSmallUnitaryLabel p lab) p Bs L) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (p-1) * 6 * Nat.card (ggAutomizer K Bs) := by
  exact ggResCentBoundNbr_of_tbTor_line hT hLift hH hy hK
    (centralizer_line_of_fixed_J_sectors hLB hPJ hH hL).le

theorem ggResCentBoundNbr_three_of_F4
    (hX : GGResXDichotomyInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hy : y ∈ Bs)
    (hK : GGInnerDiagOnLabel GGF4ThreeLabel 3 Bs K) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (3-1) * 6 * Nat.card (ggAutomizer K Bs) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR : ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
      3 ^ 4 ≤ Nat.card (ggGamma K hN).range := fun hN =>
    ggF4Three_rank_of_marking
      (ggF4ThreeSCTransvInput_of_cube ggF4ThreeSCCubeInput_holds)
      hH.1 hH.2.2.2.1 hK hN
  have hcard := card_eq_of_F4Three_marking hH.1 hK hR
  have hMark : LargeEvenMarking K (fun lab _ _ I _ θ =>
      lab.tag = .F4 ∧ Bs ≤ Subgroup.normalizer (K : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ
        (fun l l' : K => (l' : G) = b⁻¹*l*b) φ) :=
    largeEvenMarking_mono (fun lab R _ I F θ hP => ⟨hP.1.1,hP.2⟩) hK
  obtain ⟨hord,_,hfix⟩ := ggF4NbrAutReflKGInput_holds G 3 Bs K
    Nat.prime_three (by decide) hH.1.2.1.2.1 hH.1.2.1.2.2.2 hMark hcard
  have hD : GGResXDatum 3 Bs K := by
    rcases (hX G 3 B Bs x L D J y K hH).2 with hD | hseven
    · exact hD
    · obtain ⟨labJ,labK,hΛJ,hΛK,hJ,hK',hrow⟩ := hseven
      have h37 : 3 = 7 := hrow.1
      omega
  obtain ⟨Λ,hΛf,hΛd,M,C,V,hVadd,hVmod,ι,φ,h,a,hM,hC,hlin,hrefl,hpair,⟨f,hf⟩,hcl⟩ := hD
  letI : Finite V := Finite.of_equiv (Additive Bs) ι.toEquiv
  letI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have h3 : 3 ≤ Fintype.card Λ := by
    by_contra hn
    have h12 := ggWeylTypeData_card_le_twelve_of_rank_le_two
      (ggWeylTypeData_of_isWeylMatrix hM) (by omega)
    have hfcard : Nat.card M.Group = Nat.card (ggAutomizer K Bs) := Nat.card_congr f.toEquiv
    rw [hfcard] at h12
    norm_num at hord
    omega
  exact ggResCentBoundNbr_three_of_weylDatum_fixed hH hy hM hC φ hrefl
    f hf hcl ι h a hpair hlin hfix h3

theorem GGResHyp.fix_mem_centralizer_three_of_twE6
    (hRk : GGTwE6ThreeNbrRankInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel GGTableBTwE6ThreeLabel 3 Bs K) :
    ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G) := by
  have hMark := largeEvenMarking_and_labelAll
    (S := fun lab => GGTableBTwE6ThreeLabel 3 lab)
    (P' := fun R _ I _ => GGE6ThreeModelSCr R I)
    (fun lab hΛ hbad =>
      (largeEvenLabelAll_twE6Three_of hΛ hbad
        (fun F _ _ n hn hF h3 => E6ThreeModel.e6ThreeModel_holds.2 F n hn hF h3)).mono
        (fun _ _ _ _ hP => hP.2))
    (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨hKperf,lab,hΛ,hraw⟩ := hMark
  obtain ⟨R,hR,I,F,hRs,hRn,θ,⟨hbad,hN,hact⟩,hMk⟩ := largeEvenRawDatum_exists hraw
  have hSC := hH.1.2.1.2.2.2
  have hBs := hH.1.tableB_facts.2.1
  have h5 : 3 ^ 5 ≤ Nat.card (ggGamma K hN).range :=
    hRk G 3 B Bs x L D J hH.1 rfl y K hH.2.2.2.2.1
      (largeEvenMarking_mono (fun lab R _ I F θ hP =>
        ⟨hP.1,largeEvenSplit_of_twE6BadLabel hP.1,hP.2⟩) hK)
      hN (ggTorusSelfCent_ggGamma hN hSC)
  have hAT := ggTorusTBGroup_of_nbr_card hH.1 (by norm_num : 3 ≤ 5)
    hH.2.2.2.2.1 hKperf θ hN (fun b hb => ggLAut_mem_of_induces K θ hN hact hb) h5
  obtain ⟨hψ,hker,hperf,hA,hAI,hr,-,hsc⟩ := hAT
  obtain ⟨Φ,T,w,hD⟩ := (hMk K (ggQuotHom θ) hψ hker hperf
    (ggGamma K hN).range hA hAI hr hsc).exists_data
  apply fix_mem_centralizer_of_pointwise_noFix Nat.prime_three hBs hSC θ hN hact
  intro a ha hfixed
  refine hD.eq_one_of_forall_conj_eq ha fun i => ?_
  refine hfixed (w i) fun a' ha' => ?_
  exact ⟨(hD.coboundary i a' ha').2,
    fun b' hb' => hD.fixed b' hb' _ (hD.coboundary i a' ha').1⟩

theorem ggResCentBoundNbr_three_of_twE6
    (hX : GGResXDichotomyInput) (hRk : GGTwE6ThreeNbrRankInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hy : y ∈ Bs)
    (hK : GGInnerDiagOnLabel GGTableBTwE6ThreeLabel 3 Bs K) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (3-1) * 6 * Nat.card (ggAutomizer K Bs) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMark := largeEvenMarking_and_labelAll
    (S := fun lab => GGTableBTwE6ThreeLabel 3 lab)
    (P' := fun R _ I _ => GGE6ThreeModelSCr R I)
    (fun lab hΛ hbad =>
      (largeEvenLabelAll_twE6Three_of hΛ hbad
        (fun F _ _ n hn hF h3 => E6ThreeModel.e6ThreeModel_holds.2 F n hn hF h3)).mono
        (fun _ _ _ _ hP => hP.2))
    (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨hKperf,lab,hΛ,hraw⟩ := hMark
  obtain ⟨R,hR,I,F,hRs,hRn,θ,⟨hbad,hN,hact⟩,hMk⟩ := largeEvenRawDatum_exists hraw
  have hKlab : GGInnerDiagOnLab GGTwE6BadLabel 3 Bs K :=
    largeEvenMarking_mono (fun lab R _ I F θ hP =>
      ⟨hP.1,largeEvenSplit_of_twE6BadLabel hP.1,hP.2⟩) hK
  have hSC := hH.1.2.1.2.2.2
  have h5 : 3 ^ 5 ≤ Nat.card (ggGamma K hN).range :=
    hRk G 3 B Bs x L D J hH.1 rfl y K hH.2.2.2.2.1 hKlab hN
      (ggTorusSelfCent_ggGamma hN hSC)
  have hfix := hH.fix_mem_centralizer_three_of_twE6 hRk hK
  have hDat : GGResXDatum 3 Bs K := by
    rcases (hX G 3 B Bs x L D J y K hH).2 with hDat | hseven
    · exact hDat
    · obtain ⟨labJ,labK,hΛJ,hΛK,hJ,hK',hrow⟩ := hseven
      have : 3 = 7 := hrow.1
      omega
  obtain ⟨Λ,hΛf,hΛd,M,C,V,hVadd,hVmod,ι,φ,h,a,hM,hC,hlin,hrefl,hpair,⟨f,hf⟩,hcl⟩ := hDat
  letI : Finite V := Finite.of_equiv (Additive Bs) ι.toEquiv
  letI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hker3 : Module.finrank (ZMod 3) (LinearMap.pi a).ker ≤ 3 :=
    ggResJ_rootKernel_finrank_le_three ι φ h a hlin hrefl hcl hfix
      ((card_bstar_inf_centralizer_le hH.1 hH.2.2.2.2.1).trans (by norm_num : 3^2 ≤ 3^3))
  obtain ⟨_,j,hCcard,hj,-⟩ := exists_card_bstar_inf_centralizer hH.1 hH.2.2.2.2.1
  have hC3 : 3 ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := by
    rw [hCcard]
    exact le_trans (by norm_num : 3 ≤ 3^1) (Nat.pow_le_pow_right (by norm_num) hj)
  have hBs6 : 3^6 ≤ Nat.card Bs := by
    have hh := NbrU63.card_range_ggGamma_mul_card_inf hN
    rw [← hh, show 3^6 = 3^5 * 3 by norm_num]
    exact Nat.mul_le_mul h5 hC3
  have hdim : 6 ≤ Module.finrank (ZMod 3) V := by
    have hcardV : Nat.card Bs = Nat.card V := Nat.card_congr (Additive.ofMul.trans ι.toEquiv)
    rw [hcardV, ← FiniteField.pow_finrank_eq_natCard 3 V] at hBs6
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hBs6
  have h3 : 3 ≤ Fintype.card Λ := by
    have hEq := (LinearMap.pi a).finrank_range_add_finrank_ker
    have hle : Module.finrank (ZMod 3) (LinearMap.pi a).range ≤ Fintype.card Λ := by
      simpa only [Module.finrank_pi] using Submodule.finrank_le (LinearMap.pi a).range
    omega
  exact ggResCentBoundNbr_three_of_weylDatum_fixed hH hy hM hC φ hrefl
    f hf hcl ι h a hpair hlin hfix h3

@[expose] def GGTorusNoFixSC (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ∀ a ∈ A, (∀ n : L', GGTorusWeylElt p A n →
        MulAut.conj n * a * (MulAut.conj n)⁻¹ = a) → a = 1

theorem ggTorusNoFixSC_of_scWeylIrred {p r : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} (hp : p.Prime) (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (h : GGSCWeylIrred p r R) : GGTorusNoFixSC p r R I := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  have hcpL := hcp L' ψ hψ hker hperf
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
    have hφp : φ ^ p = 1 := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ r
      rw [hk, hA.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ := hIp φ hφI hφp
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨n, hn, hnp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL hgp
    have hfix : ∀ a ∈ A, a n = n := by
      intro a ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have heE : e ∈ E := show Λ e ∈ A from ha
      refine eq_of_lift_pow_eq_one hp hker hcpL ?_ ?_ hnp
      · rw [hΛmap, hn, ← hg e heE, mul_inv_cancel_right]
      · rw [← map_pow, hnp, map_one]
    have h1 := hsc n hfix hnp
    rw [← hΛn, hn] at h1
    exact h1
  have hirr : GGWeylIrred E :=
    h E hEab (by rw [hcardE]; exact hr) (by rw [hcardE]; exact h3) hscE
  have hnorm_of : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ψ n ∈ Subgroup.normalizer (E : Set R) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro e
    have h1 := hn (Λ e)
    rw [← hΛn, ← map_inv, ← map_mul, ← map_mul] at h1
    exact h1
  have hnorm_to : ∀ n : L', ψ n ∈ Subgroup.normalizer (E : Set R) →
      MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro a
    constructor
    · intro ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have h1 := (hn e).mp ha
      rw [← hΛn, ← map_inv, ← map_mul, ← map_mul]
      exact h1
    · intro ha
      obtain ⟨e₁, he₁⟩ := hAΛ _ ha
      have he₁E : e₁ ∈ E := by
        show Λ e₁ ∈ A
        rw [he₁]
        exact ha
      have h2 : (ψ n)⁻¹ * e₁ * ψ n ∈ E := by
        refine (hn _).mpr ?_
        rw [show ψ n * ((ψ n)⁻¹ * e₁ * ψ n) * (ψ n)⁻¹ = e₁ by group]
        exact he₁E
      have h3' : a = Λ ((ψ n)⁻¹ * e₁ * ψ n) := by
        rw [map_mul, map_mul, map_inv, he₁, hΛn]
        group
      rw [h3']
      exact h2
  have hWeyl : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      GGTorusWeylElt p A n := by
    intro n hn a ha
    obtain ⟨e, rfl⟩ := hAΛ a ha
    have heE : e ∈ E := ha
    have hn' := hnorm_of n hn
    have he'E : ψ n * e * (ψ n)⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hn' e).mp heE
    obtain ⟨x, hx, hxp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (g := e) (hEab.2 e heE)
    have hlx : Λ e = MulAut.conj x := hΛeq hx
    have hy : ψ (n * x * n⁻¹) = ψ n * e * (ψ n)⁻¹ := by rw [map_mul, map_mul, map_inv, hx]
    have hyp : (n * x * n⁻¹) ^ p = 1 := by rw [conj_pow, hxp, mul_one, mul_inv_cancel]
    have hcomm : x * (n * x * n⁻¹) = (n * x * n⁻¹) * x :=
      commute_of_lift_pow_eq_one hp hker hcpL
        (by rw [hy, hx]; exact TableB.IsElemAbelian.comm hEab heE he'E) hyp
    have hform : n * (Λ e n)⁻¹ = (n * x * n⁻¹) * x⁻¹ := by
      rw [hlx, MulAut.conj_apply]
      group
    refine ⟨?_, fun a' ha' => ?_⟩
    · have hc : Commute (n * x * n⁻¹) x⁻¹ :=
        (show Commute x (n * x * n⁻¹) from hcomm).symm.inv_right
      rw [hform, hc.mul_pow, hyp, inv_pow, hxp, inv_one, mul_one]
    · obtain ⟨e'', rfl⟩ := hAΛ a' ha'
      have he''E : e'' ∈ E := ha'
      obtain ⟨z, hz, hzp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (g := e'')
        (hEab.2 e'' he''E)
      have hzx : z * x = x * z :=
        commute_of_lift_pow_eq_one hp hker hcpL
          (by rw [hz, hx]; exact TableB.IsElemAbelian.comm hEab he''E heE) hxp
      have hzy : z * (n * x * n⁻¹) = (n * x * n⁻¹) * z :=
        commute_of_lift_pow_eq_one hp hker hcpL
          (by rw [hz, hy]; exact TableB.IsElemAbelian.comm hEab he''E he'E) hyp
      have hcy : Commute z (n * x * n⁻¹) := hzy
      have hcx : Commute z x⁻¹ := (show Commute z x from hzx).inv_right
      rw [hform, hΛeq hz, MulAut.conj_apply, (hcy.mul_right hcx).eq, mul_inv_cancel_right]
  intro a0 ha0 hfixed
  obtain ⟨e,he⟩ := hAΛ a0 ha0
  have heE : e ∈ E := by
    change Λ e ∈ A
    rw [he]
    exact ha0
  have hLineE : Subgroup.zpowers e ≤ E := Subgroup.zpowers_le.mpr heE
  have hLineInv : ∀ g ∈ Subgroup.normalizer (E : Set R),
      ∀ t ∈ Subgroup.zpowers e, g * t * g⁻¹ ∈ Subgroup.zpowers e := by
    intro g hg t ht
    obtain ⟨n,rfl⟩ := hψ g
    have hGe : ψ n * e * (ψ n)⁻¹ = e := by
      apply hΛinj
      rw [map_mul,map_mul,map_inv,hΛn,he]
      exact hfixed n (hWeyl n (hnorm_to n hg))
    have hcomm : Commute (ψ n) e := by
      change ψ n * e = e * ψ n
      calc ψ n * e = (ψ n * e * (ψ n)⁻¹) * ψ n := by group
        _ = e * ψ n := by rw [hGe]
    obtain ⟨z,rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    rw [(hcomm.zpow_right z).eq,mul_assoc,mul_inv_cancel,mul_one]
    exact Subgroup.mem_zpowers_iff.mpr ⟨z,rfl⟩
  rcases hirr (Subgroup.zpowers e) hLineE hLineInv with hbot | htop
  · have he1 : e = 1 := by
      have := Subgroup.mem_zpowers e
      rw [hbot] at this
      exact Subgroup.mem_bot.mp this
    rw [← he,he1,map_one]
  · have hsmall : Nat.card E ≤ p := by
      rw [← htop,Nat.card_zpowers]
      exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hEab.2 e heE))
    rw [hcardE] at hsmall
    have hbig : p < p ^ 3 := by
      calc p = p ^ 1 := by simp
        _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega

theorem card_range_ggGamma_le_pow_of_reflections
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs K : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive Bs ≃+ V) (φ : Λ → MulAut Bs)
    (h : Λ → V) (a : Λ → Module.Dual (ZMod p) V)
    (hDiag : ∀ i, a i (h i) = 2)
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - a i v • h i)
    (hcl : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hfix : ∀ b : Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G)) :
    Nat.card (ggGamma K hN).range ≤ p ^ Fintype.card Λ := by
  classical
  letI : Finite V := Finite.of_equiv (Additive Bs) ι.toEquiv
  let F := (LinearMap.pi a).ker
  let f0 : F → ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := fun v =>
    ⟨(Additive.toMul (ι.symm v.1) : Bs), by
      refine ⟨(Additive.toMul (ι.symm v.1) : Bs).2, ?_⟩
      apply hfix
      intro ψ hψ
      have hzero : ∀ i, a i v.1 = 0 := by
        intro i
        exact congrFun (LinearMap.mem_ker.mp v.2) i
      have hφ : ∀ i, φ i (Additive.toMul (ι.symm v.1)) = Additive.toMul (ι.symm v.1) := by
        intro i
        apply ι.injective
        change ι (Additive.ofMul (φ i (Additive.toMul (ι.symm v.1)))) = _
        rw [← ggLin_apply_ofMul (p := p),hlin,ofMul_toMul,ι.apply_symm_apply,hzero,zero_smul,sub_zero]
        exact (ι.apply_symm_apply v.1).symm
      rw [hcl] at hψ
      exact ggFixed_of_mem_closure φ _ hφ ψ hψ⟩
  have hinj : Function.Injective f0 := by
    intro v w hvw
    have h := congrArg Subtype.val hvw
    have hh : (Additive.toMul (ι.symm v.1) : Bs) = Additive.toMul (ι.symm w.1) := Subtype.ext h
    exact Subtype.ext (ι.symm.injective (Additive.toMul.injective hh))

  have hsurj : Function.Surjective f0 := by
    intro b
    let u : Bs := ⟨b.1,b.2.1⟩
    let v : V := ι (Additive.ofMul u)
    have hh : ∀ i, h i ≠ 0 := by
      intro i hi
      have h2 := hDiag i
      rw [hi,map_zero] at h2
      exact (zmod_two_ne_zero hp2) h2.symm
    have ha0 : ∀ i, a i v = 0 := by
      intro i
      have hφmem : φ i ∈ ggAutomizer K Bs := by
        rw [hcl]
        exact Subgroup.subset_closure ⟨i,rfl⟩
      have hφfix : φ i u = u := ggAutomizer_fix_of_centralizes u.2
        (fun k hk => (Subgroup.mem_centralizer_iff.mp b.2.2 k hk).symm) hφmem
      have hVfix : ggLin (p := p) ι (φ i) v = v := by
        dsimp [v]
        rw [ggLin_apply_ofMul,hφfix]
      rw [hlin] at hVfix
      exact (smul_eq_zero.mp (sub_eq_self.mp hVfix)).resolve_right (hh i)
    refine ⟨⟨v,LinearMap.mem_ker.mpr (funext ha0)⟩,?_⟩
    apply Subtype.ext
    change ((Additive.toMul (ι.symm (ι (Additive.ofMul u))) : Bs) : G) = b.1
    rw [ι.symm_apply_apply]
    rfl
  have hcardF : Nat.card F = Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) :=
    Nat.card_congr (Equiv.ofBijective f0 ⟨hinj,hsurj⟩)
  have hkcard : Nat.card (LinearMap.pi a).toAddMonoidHom.ker = Nat.card F := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun v => ?_)
    change ((LinearMap.pi a) v = 0) ↔ ((LinearMap.pi a) v = 0)
    rfl
  have hrcard : Nat.card (LinearMap.pi a).toAddMonoidHom.range =
      Nat.card (LinearMap.pi a).range := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun v => ?_)
    change (∃ w, (LinearMap.pi a) w = v) ↔ (∃ w, (LinearMap.pi a) w = v)
    rfl
  have hv : Nat.card V = Nat.card (LinearMap.pi a).range * Nat.card F := by
    have hc0 := AddSubgroup.card_ker_mul_card_range (LinearMap.pi a).toAddMonoidHom
    rw [hkcard,hrcard] at hc0
    simpa only [mul_comm] using hc0.symm
  have hb : Nat.card Bs = Nat.card V := Nat.card_congr (Additive.ofMul.trans ι.toEquiv)
  have hc := NbrU63.card_range_ggGamma_mul_card_inf hN
  have heq : Nat.card (ggGamma K hN).range = Nat.card (LinearMap.pi a).range := by
    apply Nat.mul_right_cancel (Nat.card_pos : 0 < Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)))
    rw [hc,hb,hv,hcardF]
  rw [heq]
  have hzcard : Fintype.card (ZMod p) = p := by
    rw [← Nat.card_eq_fintype_card,Nat.card_zmod]
  exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans_eq (by
    rw [Nat.card_eq_fintype_card,Fintype.card_fun,hzcard])

theorem noFixSC_linearNs_model {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K - 1) (hd : 5 ≤ d) :
    GGTorusNoFixSC p 0 (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) := by
  have hpK0 : (p : K) ≠ 0 := fun h =>
    hp2 (((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      ((CharP.cast_eq_zero_iff K 2 p).mp h)).symm)
  set e := TypeA.recipeEquiv d K with he
  refine ggTorusNoFixSC_of_scWeylIrred hp
    (center_eq_bot_of_mulEquiv_of_center_eq_bot e.symm (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot
      (by omega)))
    (fun φ hφ hφp => NbrInnerMore.ggOutdiagPrime_linear hp hpK (by omega) φ hφ hφp)
    (ggCenterPrime_of_mulEquiv e (ggCenterPrime_projectiveSL hp hpK hd))
    (ggSCWeylIrred_of_mulEquiv e (ggSCWeylIrred_projectiveSL hp hpK0 hpK (by omega)))

theorem largeEvenLabelAll_noFixSC_linearNs {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGTableBNbrInnerLinearNsLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusNoFixSC p 0 R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hp2, hq⟩ := h
  dsimp only at ht hl hp2 hq
  subst ht
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := NbrInnerMore.charP_two_of_card_pow hn hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ',
    noFixSC_linearNs_model (d := l + 1) hp hp2 (by rwa [hK]) (by omega)⟩

theorem GGResHyp.fix_mem_centralizer_three_of_linearNs
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel GGTableBNbrInnerLinearNsLabel 3 Bs K) :
    ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G) := by
  classical
  have hMark := largeEvenMarking_and_labelAll
    (S := fun lab => GGTableBNbrInnerLinearNsLabel 3 lab)
    (P' := fun R _ I _ => GGTorusNoFixSC 3 0 R I)
    (fun lab hΛ hns => largeEvenLabelAll_noFixSC_linearNs Nat.prime_three hΛ hns)
    (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨hKperf,lab,hΛ,hraw⟩ := hMark
  obtain ⟨R,hR,I,F,hRs,hRn,θ,⟨hlabel,hN,hact⟩,hMk⟩ := largeEvenRawDatum_exists hraw
  have hSC := hH.1.2.1.2.2.2
  have hBs := hH.1.tableB_facts.2.1
  have hpow : 3^3 ≤ Nat.card (ggGamma K hN).range :=
    pow_three_le_card_range_ggGamma_bstar hH.1 hH.2.2.2.2.1 hN
  have hAT := ggTorusTBGroup_of_nbr_card hH.1 (by norm_num : 3 ≤ 3)
    hH.2.2.2.2.1 hKperf θ hN (fun b hb => ggLAut_mem_of_induces K θ hN hact hb) hpow
  obtain ⟨hψ,hker,hperf,hA,hAI,hr,-,hsc⟩ := hAT
  have h0 : 3^0 ≤ Nat.card (ggGamma K hN).range := by
    rw [pow_zero]
    exact Nat.succ_le_of_lt (Nat.card_pos : 0 < Nat.card (ggGamma K hN).range)
  exact fix_mem_centralizer_of_pointwise_noFix Nat.prime_three hBs hSC θ hN hact
    (hMk K (ggQuotHom θ) hψ hker hperf (ggGamma K hN).range hA hAI h0 hpow hsc)

theorem ggResCentBoundNbr_three_of_linearNs
    (hX : GGResXDichotomyInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hy : y ∈ Bs)
    (hK : GGInnerDiagOnLabel GGTableBNbrInnerLinearNsLabel 3 Bs K) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (3-1) * 6 * Nat.card (ggAutomizer K Bs) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMark := largeEvenMarking_and_labelAll
    (S := fun lab => GGTableBNbrInnerLinearNsLabel 3 lab)
    (P' := fun R _ I _ => GGTorusNoFixSC 3 0 R I)
    (fun lab hΛ hns => largeEvenLabelAll_noFixSC_linearNs Nat.prime_three hΛ hns)
    (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨hKperf,lab,hΛ,hraw⟩ := hMark
  obtain ⟨R,hR,I,F,hRs,hRn,θ,⟨hlabel,hN,hact⟩,hMk⟩ := largeEvenRawDatum_exists hraw
  have hpow : 3^3 ≤ Nat.card (ggGamma K hN).range :=
    pow_three_le_card_range_ggGamma_bstar hH.1 hH.2.2.2.2.1 hN
  have hfix := hH.fix_mem_centralizer_three_of_linearNs hK
  have hDat : GGResXDatum 3 Bs K := by
    rcases (hX G 3 B Bs x L D J y K hH).2 with hDat | hseven
    · exact hDat
    · obtain ⟨labJ,labK,hΛJ,hΛK,hJ,hK',hrow⟩ := hseven
      have : 3 = 7 := hrow.1
      omega
  obtain ⟨Λ,hΛf,hΛd,M,C,V,hVadd,hVmod,ι,φ,h,a,hM,hC,hlin,hrefl,hpair,⟨f,hf⟩,hcl⟩ := hDat
  letI : Finite V := Finite.of_equiv (Additive Bs) ι.toEquiv
  letI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hDiag : ∀ i, a i (h i) = 2 := by
    intro i
    rw [hpair,hC.1]
    norm_num
  have hrank := card_range_ggGamma_le_pow_of_reflections (by decide : 3 ≠ 2)
    hN ι φ h a hDiag hlin hcl hfix
  have h3 : 3 ≤ Fintype.card Λ :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hpow.trans hrank)
  exact ggResCentBoundNbr_three_of_weylDatum_fixed hH hy hM hC φ hrefl
    f hf hcl ι h a hpair hlin hfix h3

theorem GGResHyp.fix_mem_centralizer_three_of_E6_two
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel GGE6TwoThreeLabel 3 Bs K) :
    ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G) := by
  classical
  have hMark := largeEvenMarking_and_labelAll
    (S := fun lab => GGE6TwoThreeLabel 3 lab)
    (P' := fun R _ I _ => ∃ r, GGTorusLift 3 r R ∧ GGTorusNoFix 3 r R I)
    (fun lab hΛ hlabel => (largeEvenLabelAll_torusIrred_e6TwoThree hlabel).mono
      (fun R _ I F hP => by
        obtain ⟨r,hLift,hIrred⟩ := hP
        exact ⟨r,hLift,ggTorusNoFix_of_irred (by norm_num : 1 < 3) hIrred⟩))
    (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨hKperf,lab,hΛ,hraw⟩ := hMark
  obtain ⟨R,hR,I,F,hRs,hRn,θ,⟨hlabel,hN,hact⟩,r,hLift,hNF⟩ := largeEvenRawDatum_exists hraw
  have hBs := hH.1.tableB_facts.2.1
  have hSC := hH.1.2.1.2.2.2
  have hΓr := pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hH.2.2.2.2.1 hKperf θ hN hLift
  have hΓ3 := pow_three_le_card_range_ggGamma_bstar hH.1 hH.2.2.2.2.1 hN
  exact FrameRoute.fix_mem_centralizer_of_noFix Nat.prime_three hBs hSC
    hKperf θ hN hact hΓr hΓ3 hNF

theorem ggResCentBoundNbr_three_of_E6_two
    (hX : GGResXDichotomyInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hy : y ∈ Bs)
    (hK : GGInnerDiagOnLabel GGE6TwoThreeLabel 3 Bs K) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (3-1) * 6 * Nat.card (ggAutomizer K Bs) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMark := largeEvenMarking_and_labelAll
    (S := fun lab => GGE6TwoThreeLabel 3 lab)
    (P' := fun R _ I _ => ∃ r, GGTorusLift 3 r R ∧ GGTorusNoFix 3 r R I)
    (fun lab hΛ hlabel => (largeEvenLabelAll_torusIrred_e6TwoThree hlabel).mono
      (fun R _ I F hP => by
        obtain ⟨r,hLift,hIrred⟩ := hP
        exact ⟨r,hLift,ggTorusNoFix_of_irred (by norm_num : 1 < 3) hIrred⟩))
    (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨hKperf,lab,hΛ,hraw⟩ := hMark
  obtain ⟨R,hR,I,F,hRs,hRn,θ,⟨hlabel,hN,hact⟩,r,hLift,hNF⟩ := largeEvenRawDatum_exists hraw
  have hΓ3 := pow_three_le_card_range_ggGamma_bstar hH.1 hH.2.2.2.2.1 hN
  have hfix := hH.fix_mem_centralizer_three_of_E6_two hK
  have hDat : GGResXDatum 3 Bs K := by
    rcases (hX G 3 B Bs x L D J y K hH).2 with hDat | hseven
    · exact hDat
    · obtain ⟨labJ,labK,hΛJ,hΛK,hJ,hK',hrow⟩ := hseven
      have : 3 = 7 := hrow.1
      omega
  obtain ⟨Λ,hΛf,hΛd,M,C,V,hVadd,hVmod,ι,φ,h,a,hM,hC,hlin,hrefl,hpair,⟨f,hf⟩,hcl⟩ := hDat
  letI : Finite V := Finite.of_equiv (Additive Bs) ι.toEquiv
  letI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hDiag : ∀ i, a i (h i) = 2 := by
    intro i
    rw [hpair,hC.1]
    norm_num
  have hrank := card_range_ggGamma_le_pow_of_reflections (by decide : 3 ≠ 2)
    hN ι φ h a hDiag hlin hcl hfix
  have h3 : 3 ≤ Fintype.card Λ :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hΓ3.trans hrank)
  have hb := ggResCentBoundNbr_three_of_weylDatum_fixed hH hy hM hC φ hrefl
    f hf hcl ι h a hpair hlin hfix h3
  exact hb

theorem largeEvenLabelAll_noFixSC_twE6_sub
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twE6) (hd : 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusLift 3 4 R ∧ GGTorusNoFixSC 3 4 R I := by
  have h3 : ¬ 3 ∣ 2 ^ lab.n + 1 := by
    intro h
    have h2 := Nat.dvd_sub h hd
    have hp : 0 < 2 ^ lab.n := Nat.two_pow_pos lab.n
    have he : 2 ^ lab.n + 1 - (2 ^ lab.n - 1) = 2 := by omega
    rw [he] at h2
    exact absurd (Nat.le_of_dvd (by norm_num : 0 < 2) h2) (by norm_num)
  exact TwE6Delta.labelAll ht fun F _ _ hF =>
    ⟨ggTorusLift_twE6Dvd hΛ.1 hF Nat.prime_three (by decide) hd,
      ggTorusNoFixSC_of_scWeylIrred Nat.prime_three (TwE6Delta.center_recipeR_eq_bot hΛ.1 hF)
        (fun φ hφ _ => TwE6Delta.recipeI_subset_inn_of_not_dvd hΛ.1 hF h3 hφ)
        (TwE6Delta.ggCenterPrime_three_twE6 hΛ.1 hF h3)
        (Irred937.ggNbrKGTwE6ThreeSubSCWeylIrred_holds F lab.n hΛ.1 hF hd)⟩

theorem GGResHyp.fix_mem_centralizer_three_of_twE6_sub
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs K) :
    ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G) := by
  classical
  have hMark := largeEvenMarking_and_labelAll
    (S := fun lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1)
    (P' := fun R _ I _ => GGTorusLift 3 4 R ∧ GGTorusNoFixSC 3 4 R I)
    (fun lab hΛ hP => largeEvenLabelAll_noFixSC_twE6_sub hΛ hP.1 hP.2)
    (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨hKperf,lab,hΛ,hraw⟩ := hMark
  obtain ⟨R,hR,I,F,hRs,hRn,θ,⟨hlabel,hN,hact⟩,hLift,hMk⟩ := largeEvenRawDatum_exists hraw
  have hSC := hH.1.2.1.2.2.2
  have hBs := hH.1.tableB_facts.2.1
  have hΓ4 := pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hH.2.2.2.2.1 hKperf θ hN hLift
  have hΓ3 := pow_three_le_card_range_ggGamma_bstar hH.1 hH.2.2.2.2.1 hN
  have hAT := ggTorusTBGroup_of_nbr_card hH.1 (by norm_num : 3 ≤ 4)
    hH.2.2.2.2.1 hKperf θ hN (fun b hb => ggLAut_mem_of_induces K θ hN hact hb) hΓ4
  obtain ⟨hψ,hker,hperf,hA,hAI,hr,-,hsc⟩ := hAT
  exact fix_mem_centralizer_of_pointwise_noFix Nat.prime_three hBs hSC θ hN hact
    (hMk K (ggQuotHom θ) hψ hker hperf (ggGamma K hN).range hA hAI hΓ4 hΓ3 hsc)

theorem ggResCentBoundNbr_three_of_twE6_sub
    (hX : GGResXDichotomyInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hy : y ∈ Bs)
    (hK : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs K) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (3-1) * 6 * Nat.card (ggAutomizer K Bs) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMark := largeEvenMarking_and_labelAll
    (S := fun lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1)
    (P' := fun R _ I _ => GGTorusLift 3 4 R ∧ GGTorusNoFixSC 3 4 R I)
    (fun lab hΛ hP => largeEvenLabelAll_noFixSC_twE6_sub hΛ hP.1 hP.2)
    (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨hKperf,lab,hΛ,hraw⟩ := hMark
  obtain ⟨R,hR,I,F,hRs,hRn,θ,⟨hlabel,hN,hact⟩,hLift,hMk⟩ := largeEvenRawDatum_exists hraw
  have hΓ3 := pow_three_le_card_range_ggGamma_bstar hH.1 hH.2.2.2.2.1 hN
  have hfix := hH.fix_mem_centralizer_three_of_twE6_sub hK
  have hDat : GGResXDatum 3 Bs K := by
    rcases (hX G 3 B Bs x L D J y K hH).2 with hDat | hseven
    · exact hDat
    · obtain ⟨labJ,labK,hΛJ,hΛK,hJ,hK',hrow⟩ := hseven
      have : 3 = 7 := hrow.1
      omega
  obtain ⟨Λ,hΛf,hΛd,M,C,V,hVadd,hVmod,ι,φ,h,a,hM,hC,hlin,hrefl,hpair,⟨f,hf⟩,hcl⟩ := hDat
  letI : Finite V := Finite.of_equiv (Additive Bs) ι.toEquiv
  letI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hDiag : ∀ i, a i (h i) = 2 := by
    intro i
    rw [hpair,hC.1]
    norm_num
  have hrank := card_range_ggGamma_le_pow_of_reflections (by decide : 3 ≠ 2)
    hN ι φ h a hDiag hlin hcl hfix
  have h3 : 3 ≤ Fintype.card Λ :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hΓ3.trans hrank)
  exact ggResCentBoundNbr_three_of_weylDatum_fixed hH hy hM hC φ hrefl
    f hf hcl ι h a hpair hlin hfix h3

theorem GGResHyp.false_of_e6_two_seven
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp 7 B Bs x L D J y K)
    (hK : GGHasLabel ⟨.E6, 0, 1⟩ (K ⧸ Subgroup.center K)) : False := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hcfg := hH.1
  have hnb : GGNbr 7 B x D J y K := hH.2.2.2.2.1
  have hM : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.E6, 0, 1⟩) 7 Bs K :=
    ggInnerDiagOn_relabel ggLabelRigidInput_holds (hH.2.2.1.2 y K hnb)
      largeEvenInLambda2_e6 hK
  have hNLMark := largeEvenMarking_and_labelAll
    (S := fun lab => lab = ⟨.E6, 0, 1⟩)
    (P' := fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusNoLine 7 0 R I)
    (fun lab hΛ heq => by
      subst lab
      exact largeEvenLabelAll_noLine_e6_two_seven hΛ ⟨rfl, rfl⟩)
    (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hNLMark
  obtain ⟨R, _, I, F, hs, hna, θ, ⟨-, hN, hact⟩, hNL⟩ := largeEvenRawDatum_exists hraw
  have hzero : 7 ^ 0 ≤ Nat.card (ggGamma K hN).range := by
    rw [pow_zero]
    exact Nat.succ_le_of_lt (Nat.card_pos : 0 < Nat.card (ggGamma K hN).range)
  obtain ⟨w, hwK, hwC, hwx⟩ := ggNbrInnerWeyl_of_ggTorusNoLine hcfg hnb hperf θ hN
    (fun b hb => ggLAut_mem_of_induces K θ hN hact hb) hzero (hNL hs hna)
  have hnoref := ggSeven_e6Nbr_noReflection hcfg hH.2.2.1 hnb hK
  have hempty : {φ : MulAut Bs | φ ∈ ggAutomizer K Bs ∧ GGIsReflection 7 φ} = ∅ := by
    ext φ
    constructor
    · intro hφ
      exact (hnoref φ hφ.1 hφ.2).elim
    · intro hφ
      exact hφ.elim
  have hbot := hH.2.2.2.2.2.1
  unfold GGReflGenerated at hbot
  rw [hempty, Subgroup.closure_empty] at hbot
  have hwN : w ∈ Subgroup.normalizer (Bs : Set G) :=
    Subgroup.mem_normalizer_fintype fun b hb => hcfg.2.1.2.2.2 _ (hwC b hb) (by
      rw [conj_pow, hcfg.2.1.2.1.2 b hb, mul_one, mul_inv_cancel])
  have hwAut := ggConjAut_mem_ggAutomizer hwK hwN
  rw [hbot, Subgroup.mem_bot] at hwAut
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  have he : w * x * w⁻¹ = x := by
    simpa [ggConjAut_apply] using
      congrArg (fun φ : MulAut Bs => ((φ ⟨x, hxBs⟩ : Bs) : G)) hwAut
  apply hwx
  rw [he]
  exact Subgroup.mem_zpowers x

theorem ggSeven_K_absurd_of_noLine

    {G : Type} [Group G] [Finite G]
    (hRig : GGLabelRigidInput) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hp : p = 7)
    {labX : LargeEvenLabel} (hΛ : LargeEvenInLambda2 labX)
    (hX : GGHasLabel labX (K ⧸ Subgroup.center K)) (hSeven : GGSevenLabel labX) : False := by
  subst p
  have hcfg := hH.1
  have hnb : GGNbr 7 B x D J y K := hH.2.2.2.2.1
  have hHS := ggNbr_halfSplit_of_hyp hraw hiso hcfg hnb (hH.2.2.1.2 y K hnb)
  have hContra (labX : LargeEvenLabel) (hΛX : LargeEvenInLambda2 labX)
      (hHasX : GGHasLabel labX (K ⧸ Subgroup.center K)) (hn1 : labX.n = 1)
      (hEq : ∀ lab, LargeEvenInLambda2 lab → GGHasLabel lab (K ⧸ Subgroup.center K) →
        GGLabelIso lab labX → lab = labX)
      (hNe : labX ≠ ⟨.A, 8, 1⟩ ∧ labX ≠ ⟨.E6, 0, 1⟩) : False := by
    obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hHSlab⟩ := largeEvenMarking_exists_hasLabel hHS
    have heq := hEq lab hlab hhas (hRig lab labX _ hlab hΛX hhas hHasX)
    rcases largeEvenHalfSplit_dvd hlab hHSlab with hd | ⟨-, hex⟩
    · rw [heq, hn1] at hd
      norm_num at hd
    · rw [heq] at hex
      exact hex.elim hNe.1 hNe.2
  rcases hSeven with rfl | rfl | rfl | rfl | rfl
  · exact ggForkNbrSevenExcl'_of_notRefl hA8 G B Bs x L D J hcfg hH.2.1
      hH.2.2.1 hH.2.2.2.1 y K hnb hH.2.2.2.2.2.1 hX
  · refine hContra ⟨.A, 11, 1⟩ hΛ hX rfl (fun lab _ _ hIso =>
      ggTWR_iso_eq hIso (Or.inl rfl) (by norm_num)) ?_
    constructor <;> intro h
    · have := congrArg LargeEvenLabel.rank h
      norm_num at this
    · have := congrArg LargeEvenLabel.tag h
      cases this
  · exact hH.false_of_e6_two_seven hX
  · refine hContra ⟨.twE6, 0, 1⟩ hΛ hX rfl
      (fun lab _ _ hIso => eq_of_ggLabelIso_of_twE6 rfl hIso) ?_
    constructor <;> intro h <;> have ht := congrArg LargeEvenLabel.tag h <;> cases ht
  · refine hContra ⟨.E8, 0, 1⟩ hΛ hX rfl ?_ ?_
    · intro lab hlab hhas _
      exact eq_of_ggLabelIso_of_excTag (lab := ⟨.E8, 0, 1⟩) (lab' := lab)
        (Or.inr (Or.inr (Or.inl rfl))) (hRig ⟨.E8, 0, 1⟩ lab _ hΛ hlab hX hhas)
    · constructor <;> intro h <;> have ht := congrArg LargeEvenLabel.tag h <;> cases ht

theorem ggResCentBoundNbr_of_seven_marking

    (hRig : GGLabelRigidInput) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs) (hp7 : p = 7)
    (hK : GGInnerDiagOnLabel (fun _ lab => GGSevenLabel lab) p Bs K) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (p - 1) * 6 * Nat.card (ggAutomizer K Bs) := by
  obtain ⟨lab,hΛ,hHas,R,hR,I,F,θ,hSeven,-⟩ := largeEvenMarking_exists_hasLabel hK
  exact (ggSeven_K_absurd_of_noLine hRig hA8 hraw hiso hH hp7 hΛ hHas hSeven).elim

theorem GGResHyp.false_of_labelAll_card_lt
    {S : ℕ → LargeEvenLabel → Prop}
    (hLow : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 →
      LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
        ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I →
          IsElemAbelian p X → Nat.card X < p ^ 3))
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel S p Bs K) : False := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hMark := largeEvenMarking_and_labelAll
    (S := fun lab => S p lab)
    (P' := LargeEvenSimpleGuard fun R _ I _ =>
      ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I →
        IsElemAbelian p X → Nat.card X < p ^ 3)
    (fun lab hΛ hSel => hLow p lab (Fact.out : p.Prime) hp2 hΛ hSel)
    (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨hKperf,lab,hΛ,hraw⟩ := hMark
  obtain ⟨R,hR,I,F,hRs,hRn,θ,⟨hSel,hN,hact⟩,hBound⟩ := largeEvenRawDatum_exists hraw
  have hΓ3 := pow_three_le_card_range_ggGamma_bstar hH.1 hH.2.2.2.2.1 hN
  have hAT := ggTorusTBGroup_of_nbr_card hH.1 (by omega : 3 ≤ 3)
    hH.2.2.2.2.1 hKperf θ hN (fun b hb => ggLAut_mem_of_induces K θ hN hact hb) hΓ3
  obtain ⟨hψ,hker,hperf,hA,hAI,-,-,-⟩ := hAT
  have hAI' : ∀ a ∈ (ggGamma K hN).range, ∃ φ : MulAut R,
      ∀ l : K, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    intro a ha
    obtain ⟨φ,-,hφ⟩ := hAI a ha
    exact ⟨φ,hφ⟩
  have hcard := TypeA.card_inducedSub hψ hker hperf hAI'
  have hXI : ((TypeA.inducedSub (ggQuotHom θ) (ggGamma K hN).range :
      Subgroup (MulAut R)) : Set (MulAut R)) ⊆ I := by
    rintro φ ⟨a,ha,hφ⟩
    obtain ⟨φ',hφ'I,hφ'⟩ := hAI a ha
    rw [TypeA.induced_unique (ggQuotHom θ) hψ hφ hφ']
    exact hφ'I
  have hlt := hBound hRs hRn _ hXI (TypeA.isElemAbelian_inducedSub hψ hA)
  rw [hcard] at hlt
  exact (not_le.mpr hlt) hΓ3

theorem GGResHyp.false_of_small_neighbour
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel
      (fun p lab => GGTableBNbrInnerNineSmallLabel p lab ∨ lab.tag = .triD4 ∨ lab.tag = .twF4)
      p Bs K) : False := by
  refine hH.false_of_labelAll_card_lt (fun p lab hp hp2 hΛ hSel => ?_) hK
  rcases hSel with hSmall | ht | ht
  · rcases hSmall with h | h | h | h | h | h | h | h | ⟨ht,hl⟩
    · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hΛ (Or.inl h)).mono
        fun _ _ _ _ hB _ _ => hB
    · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hΛ (Or.inr (Or.inl h))).mono
        fun _ _ _ _ hB _ _ => hB
    · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hΛ (Or.inr (Or.inr (Or.inl h)))).mono
        fun _ _ _ _ hB _ _ => hB
    · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hΛ
        (Or.inr (Or.inr (Or.inr (Or.inl h))))).mono fun _ _ _ _ hB _ _ => hB
    · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hΛ
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))).mono fun _ _ _ _ hB _ _ => hB
    · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hΛ
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))).mono
        fun _ _ _ _ hB _ _ => hB
    · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hΛ
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))).mono
        fun _ _ _ _ hB _ _ => hB
    · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hΛ
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))).mono
        fun _ _ _ _ hB _ _ => hB
    · exact largeEvenLabelAll_card_lt_unitaryThree_all hp hp2 hΛ ht hl
  · exact (NbrInnerNine.largeEvenLabelAll_card_lt_triD4_all hp hp2 hΛ ht).mono
      fun _ _ _ _ hB _ _ => hB
  · exact (NbrInnerNine.largeEvenLabelAll_card_lt_twF4_all hp hp2 hΛ ht).mono
      fun _ _ _ _ hB _ _ => hB

theorem ggResCentBoundNbr_of_small_neighbour
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hK : GGInnerDiagOnLabel
      (fun p lab => GGTableBNbrInnerNineSmallLabel p lab ∨ lab.tag = .triD4 ∨ lab.tag = .twF4)
      p Bs K) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (p - 1) * 6 * Nat.card (ggAutomizer K Bs) :=
  (hH.false_of_small_neighbour hK).elim

theorem GGNoTransvection.fixes_of_inverts_commutator
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) (hRG : GGReflGenerated p (ggAutomizer K Bs))
    {g : MulAut Bs} (hg : g ∈ ggAutomizer ⊤ Bs)
    (hInv : ∀ u ∈ ggBstarComm K Bs, g u = u⁻¹)
    {x : Bs} (hgx : g x = x) : ∀ φ ∈ ggAutomizer K Bs, φ x = x := by
  classical
  obtain ⟨V,hVadd,hVmod,hι⟩ := exists_ggLinData (p := p) (G := G) (Bs := Bs) hBs
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  obtain ⟨ι⟩ := hι
  have : Finite V := Finite.of_equiv (Additive Bs) ι.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let A := (ggAutomizer ⊤ Bs).map (ggLin (p := p) ι)
  have hNTL : QTwoLin.TransvectionFree A := ggQ2P3P_transvectionFree ι hNT
  have hgA : ggLin (p := p) ι g ∈ A := Subgroup.mem_map_of_mem (ggLin (p := p) ι) hg
  have hdisp (φ : MulAut Bs) (hφ : φ ∈ ggAutomizer K Bs) (b : Bs) :
      φ b * b⁻¹ ∈ ggBstarComm K Bs := by
    rw [hBs.1.is_comm.comm (φ b) b⁻¹]
    exact Subgroup.subset_closure ⟨b,φ,hφ,rfl⟩
  have hneg (φ : MulAut Bs) (hφ : φ ∈ ggAutomizer K Bs) :
      ∀ v ∈ HardMathSupport.Kantor79.movedSpace (ggLin (p := p) ι φ),
        ggLin (p := p) ι g v = -v := by
    intro v hv
    obtain ⟨w,hw⟩ := HardMathSupport.Kantor79.mem_movedSpace_iff.mp hv
    let b : Bs := Additive.toMul (ι.symm w)
    have hb : ι (Additive.ofMul b) = w := by simp [b]
    have he := ggLin_apply_ofMul_sub (p := p) ι φ b
    rw [hb,hw] at he
    rw [he]
    exact (ggLin_inv_iff (p := p) ι g (φ b * b⁻¹)).mp (hInv _ (hdisp φ hφ b))
  have hcentRef (φ : MulAut Bs) (hφ : φ ∈ ggAutomizer K Bs)
      (hr : GGIsReflection p φ) : Commute g φ := by
    have hφA : ggLin (p := p) ι φ ∈ A :=
      Subgroup.mem_map_of_mem (ggLin (p := p) ι) (ggAutomizer_mono Bs le_top hφ)
    have hcA : ggLin (p := p) ι (g * φ * g⁻¹) ∈ A := by
      rw [map_mul,map_mul,map_inv]
      exact A.mul_mem (A.mul_mem hgA hφA) (A.inv_mem hgA)
    have hmr : HardMathSupport.Kantor79.movedSpace (ggLin (p := p) ι (g * φ * g⁻¹)) =
        HardMathSupport.Kantor79.movedSpace (ggLin (p := p) ι φ) := by
      rw [map_mul,map_mul,map_inv,ZS.movedSpace_conj]
      apply le_antisymm
      · rintro v ⟨w,hw,rfl⟩
        change ggLin (p := p) ι g w ∈ HardMathSupport.Kantor79.movedSpace (ggLin (p := p) ι φ)
        rw [hneg φ hφ w hw]
        exact Submodule.neg_mem _ hw
      · intro v hv
        refine ⟨-v,Submodule.neg_mem _ hv,?_⟩
        change ggLin (p := p) ι g (-v) = v
        rw [hneg φ hφ (-v) (Submodule.neg_mem _ hv),neg_neg]
    have hrL : ZS.IsRefl p (ggLin (p := p) ι φ) :=
      (ZS.isRefl_iff_ggLinRefl _).mpr ((ggRC_isReflection_iff_linRefl ι φ).mp hr)
    have hcL : ZS.IsRefl p (ggLin (p := p) ι (g * φ * g⁻¹)) :=
      (ZS.isRefl_iff_ggLinRefl _).mpr
        ((ggRC_isReflection_iff_linRefl ι _).mp (hr.conj' g))
    have he : g * φ * g⁻¹ = φ := ggLin_injective (p := p) ι
      (ZS.eq_of_movedSpace_eq hp2 hNTL hcA hφA hcL hrL hmr)
    exact mul_inv_eq_iff_eq_mul.mp he
  have hcent : ∀ φ ∈ ggAutomizer K Bs, Commute g φ := by
    intro φ hφ
    rw [hRG] at hφ
    refine Subgroup.closure_induction
      (p := fun φ _ => Commute g φ) (fun φ h => hcentRef φ h.1 h.2)
      (Commute.one_right g) (fun φ ψ _ _ hφ hψ => hφ.mul_right hψ)
      (fun φ _ hφ => hφ.inv_right) hφ
  intro φ hφ
  let d : Bs := φ x * x⁻¹
  have hd := hdisp φ hφ x
  have hcomm : g (φ x) = φ (g x) := by
    have he := congrArg (fun t : MulAut Bs => t x) (hcent φ hφ).eq
    simpa only [MulAut.mul_apply] using he
  have hgd : g d = d := by
    dsimp [d]
    rw [map_mul,map_inv,hcomm,hgx]
  have hfix := (ggLin_fix_iff (p := p) ι g d).mp hgd
  have hinv := (ggLin_inv_iff (p := p) ι g d).mp (hInv d hd)
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  have hz : (2 : ZMod p) • ι (Additive.ofMul d) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp (hfix.symm.trans hinv)
  have hv : ι (Additive.ofMul d) = 0 := (smul_eq_zero.mp hz).resolve_left h2
  have hd1 : d = 1 := by
    apply Additive.ofMul.injective
    apply ι.injective
    simpa using hv
  have he := congrArg (fun b : Bs => b * x) hd1
  simpa [d,mul_assoc] using he

theorem GGResHyp.false_of_tbTor_inverter
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel GGTBTorCov p Bs K)
    (n : G) (hn : n ∈ Subgroup.normalizer (Bs : Set G))
    (hnx : n * x * n⁻¹ = x)
    (hInv : ∀ u : Bs, u ∈ ggBstarComm K Bs → n * (u : G) * n⁻¹ = (u : G)⁻¹) :
    False := by
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hxD : x ∈ D := hH.1.2.2.1.2.2.2.1
  have hx : x ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hxD)
  let g := ggConjAut Bs hn
  have hg : g ∈ ggAutomizer ⊤ Bs := ggConjAut_mem_ggAutomizer (Subgroup.mem_top n) hn
  have hgx : g (⟨x,hx⟩ : Bs) = ⟨x,hx⟩ := Subtype.ext hnx
  have hginv : ∀ u ∈ ggBstarComm K Bs, g u = u⁻¹ := by
    intro u hu
    exact Subtype.ext (hInv u hu)
  have hfix := GGNoTransvection.fixes_of_inverts_commutator
    hH.1.1.2.2.2.2.2.1.2.1 hBs hH.2.2.2.1 hH.2.2.2.2.2.1 hg hginv hgx
  obtain ⟨m,N,C,M,hN,hm,hpm,hM,hC,hTor⟩ :=
    l05nPlP4_core_K (ggTBTorWRows_of_all hT) hLift hH hK
  have hSC := hH.1.2.1.2.2.2
  have hxC : x ∈ Subgroup.centralizer (K : Set G) :=
    ggTD_fix_mem_centralizer hm hpm hBs hSC hN hTor ⟨x,hx⟩ hfix
  apply hH.2.2.2.2.1.2.2.2
  have hz : Subgroup.zpowers x ≤ Subgroup.centralizer (K : Set G) :=
    Subgroup.zpowers_le.mpr hxC
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hz)]
  exact bot_le

theorem ggResCentBoundNbr_of_tbTor_rest
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5)
    (hK : GGInnerDiagOnLabel GGTBTorCov p Bs K)
    (hNs : ¬ GGInnerDiagOnLabel GGTBTorNonsingularCov p Bs K)
    (hSplit : ¬ GGInnerDiagOnLabel GGTBTorSplitLinearCov p Bs K)
    (hL : ¬ GGInnerDiagOnLabel GGTableBUnitaryLiftLabel p Bs L)
    (hSector : ¬ GGInnerDiagOnLab
      (fun p lab => (GGTypeASplitLabel p lab ∨
        ((lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1)) ∨
        GGStdSubSmallUnitaryLabel p lab) p Bs L)
    (hcard : ¬ Nat.card Bs ≤ p * Nat.card
      ↥((ggBstarComm K Bs).map Bs.subtype ⊔ Subgroup.zpowers y))
    (hyU : y ∉ (ggBstarComm K Bs).map Bs.subtype) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (p - 1) * 6 * Nat.card (ggAutomizer K Bs) := by
  obtain ⟨hEq,hEqSub,n,hnL,hnN,hnx,hnInv⟩ :=
    hH.exists_inverter_of_tbTor_rest hRig hLB hPJ hp3 hp5 hK hNs hSplit hL hSector hcard hyU
  apply False.elim
  refine hH.false_of_tbTor_inverter hT hLift hK n hnN hnx ?_
  intro u hu
  apply hnInv
  rw [← hEq]
  exact Subgroup.mem_map_of_mem Bs.subtype hu

theorem GGResHyp.false_of_classical_rank_vacuity
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel GGTableBNbrInnerNineClassicalLabel p Bs K) : False := by
  refine hH.false_of_labelAll_card_lt (fun p lab hp hp2 hΛ hSel => ?_) hK
  rcases hSel with ⟨hTag,hOrd⟩ | ⟨hTag,hOrd⟩ | ⟨hTag,hOrd⟩ | ⟨hTag,hr,hOrd⟩
  · exact (largeEvenLabelAll_card_lt_linear_of_ord hp hp2 hTag hOrd).mono
      fun _ _ _ _ hB _ _ => hB
  · exact largeEvenLabelAll_card_lt_unitary_of_ord hp hp2 hΛ hTag hOrd
  · exact (largeEvenLabelAll_card_lt_symplectic_of_ord hp hp2 hΛ hTag hOrd).mono
      fun _ _ _ _ hB _ _ => hB
  · exact largeEvenLabelAll_card_lt_orthogonal_of_ord hp hp2 hTag hr hOrd

theorem ggResCentBoundNbr_of_classical_rank_vacuity
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hK : GGInnerDiagOnLabel GGTableBNbrInnerNineClassicalLabel p Bs K) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut Bs) (⟨y,hy⟩ : Bs)) ≤
        (p - 1) * 6 * Nat.card (ggAutomizer K Bs) :=
  (hH.false_of_classical_rank_vacuity hK).elim

theorem ggResCentBoundNbrInput_of_rest
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hRk : GGTwE6ThreeNbrRankInput)
    (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hRest : GGResCentBoundNbrRestInput) : GGResCentBoundNbrInput := by
  intro G _ _ p B Bs x L D J y K hH _ hy
  classical
  by_cases hClassical : GGInnerDiagOnLabel GGTableBNbrInnerNineClassicalLabel p Bs K
  · exact ggResCentBoundNbr_of_classical_rank_vacuity hH hy hClassical
  by_cases hSmall : GGInnerDiagOnLabel
      (fun p lab => GGTableBNbrInnerNineSmallLabel p lab ∨ lab.tag = .triD4 ∨ lab.tag = .twF4)
      p Bs K
  · exact ggResCentBoundNbr_of_small_neighbour hH hy hSmall
  by_cases hSeven : p = 7 ∧
      GGInnerDiagOnLabel (fun _ lab => GGSevenLabel lab) p Bs K
  · exact ggResCentBoundNbr_of_seven_marking hRig hA8 hraw hiso
      hH hy hSeven.1 hSeven.2
  have hNoSeven : p = 7 →
      ¬ GGInnerDiagOnLabel (fun _ lab => GGSevenLabel lab) p Bs K := by
    intro hp7 hMark
    exact hSeven ⟨hp7,hMark⟩
  by_cases hE6Two : GGInnerDiagOnLabel GGE6TwoThreeLabel p Bs K
  · obtain ⟨lab,hΛ,hhas,R,hR,I,F,θ,hlabel,hN,hact⟩ := largeEvenMarking_exists_hasLabel hE6Two
    have hp3 : p = 3 := hlabel.2.2
    subst p
    exact ggResCentBoundNbr_three_of_E6_two hX hH hy hE6Two
  by_cases hTwE6Sub : p = 3 ∧
      GGInnerDiagOnLabel (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) p Bs K
  · obtain ⟨rfl,hMark⟩ := hTwE6Sub
    exact ggResCentBoundNbr_three_of_twE6_sub hX hH hy hMark
  have hNoTwE6Sub : p = 3 →
      ¬ GGInnerDiagOnLabel (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) p Bs K := by
    intro hp3 hMark
    exact hTwE6Sub ⟨hp3,hMark⟩
  by_cases hNS : p = 3 ∧ GGInnerDiagOnLabel GGTableBNbrInnerLinearNsLabel p Bs K
  · obtain ⟨rfl,hNS⟩ := hNS
    exact ggResCentBoundNbr_three_of_linearNs hX hH hy hNS
  have hNoNS : p = 3 → ¬ GGInnerDiagOnLabel GGTableBNbrInnerLinearNsLabel p Bs K := by
    intro hp3 hMark
    exact hNS ⟨hp3,hMark⟩
  by_cases hTwE6 : GGInnerDiagOnLabel GGTwE6BadLabel p Bs K
  · obtain ⟨lab,hΛ,hhas,R,hR,I,F,θ,hcov,hN,hact⟩ := largeEvenMarking_exists_hasLabel hTwE6
    have hp3 : p = 3 := hcov.2.1
    subst p
    exact ggResCentBoundNbr_three_of_twE6 hX hRk hH hy hTwE6
  by_cases hF4 : GGInnerDiagOnLabel GGF4ThreeLabel p Bs K
  · obtain ⟨lab,hΛ,hhas,R,hR,I,F,θ,hcov,hN,hact⟩ := largeEvenMarking_exists_hasLabel hF4
    have hp3 : p = 3 := hcov.2.1
    subst p
    exact ggResCentBoundNbr_three_of_F4 hX hH hy hF4
  by_cases hU6 : GGInnerDiagOnLabel GGNbrInner937U63Label p Bs K
  · obtain ⟨lab,hΛ,hhas,R,hR,I,F,θ,hcov,hN,hact⟩ := largeEvenMarking_exists_hasLabel hU6
    obtain ⟨-,hr5,rfl⟩ := hcov
    exact ggResCentBoundNbr_three_of_unitary_six hRig hLB hPJ hH hy hU6
  by_cases hSplit : GGInnerDiagOnLabel GGTBTorSplitLinearCov p Bs K
  · exact ggResCentBoundNbr_of_tbTor_split_linear hT hLift hRig hH hy hSplit
  · by_cases hK : GGInnerDiagOnLabel GGTBTorCov p Bs K
    · by_cases hp3 : p = 3
      · subst p
        exact ggResCentBoundNbr_three_of_tbTor hT hLift hH hy hK
      · by_cases hp5 : p = 5
        · subst p
          exact ggResCentBoundNbr_five_of_tbTor hT hLift hX hTCJ hRig hH hy hK
        · by_cases hL : GGInnerDiagOnLabel GGTableBUnitaryLiftLabel p Bs L
          · exact ggResCentBoundNbr_of_tbTor_unitary_L hT hLift hRig hLB hPJ hp3 hH hy hK hL
          · by_cases hSector : GGInnerDiagOnLab
                (fun p lab => (GGTypeASplitLabel p lab ∨
                  ((lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1)) ∨
                  GGStdSubSmallUnitaryLabel p lab) p Bs L
            · exact ggResCentBoundNbr_of_tbTor_fixed_J_sectors hT hLift hLB hPJ hH hy hK hSector
            · by_cases hcop : Nat.Coprime (p - 1) (2 * Nat.log p (Nat.card Bs) - 3)
              · exact ggResCentBoundNbr_of_tbTor_coprime hT hLift hX hTCJ hRig hH hy hK hcop
              · by_cases hCen : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y
                · exact ggResCentBoundNbr_of_tbTor_line hT hLift hH hy hK hCen
                · by_cases hNs : GGInnerDiagOnLabel GGTBTorNonsingularCov p Bs K
                  · exact ggResCentBoundNbr_of_tbTor_nonsingular hT hLift hX hTCJ hRig hH hy hNs
                  · by_cases hdim : Nat.card Bs ≤ p * Nat.card
                        ↥((ggBstarComm K Bs).map Bs.subtype ⊔ Subgroup.zpowers y)
                    · exact ggResCentBoundNbr_of_tbTor_coroot_cases hT hLift hX hTCJ hRig hH hy hK
                        (Or.inl hdim)
                    · by_cases hyComm : y ∈ (ggBstarComm K Bs).map Bs.subtype
                      · exact ggResCentBoundNbr_of_tbTor_coroot_cases hT hLift hX hTCJ hRig hH hy hK
                          (Or.inr hyComm)
                      · exact ggResCentBoundNbr_of_tbTor_rest hT hLift hRig hLB hPJ hH hy
                          hp3 hp5 hK hNs hSplit hL hSector hdim hyComm
    · exact hRest G p B Bs x L D J y K hH hy hK hU6 hF4 hTwE6 hNoNS
        hE6Two hNoTwE6Sub hNoSeven hSmall hClassical

private theorem GGResHyp.false_of_rowRes_cases
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {lab : LargeEvenLabel}
    (hH : GGResHyp p B Bs x L D J y K) (hRes : GGTBWeylRowRes p lab)
    (hΛ : LargeEvenInLambda2 lab)
    (hUse : ∀ S : ℕ → LargeEvenLabel → Prop, S p lab → GGInnerDiagOnLabel S p Bs K)
    (hU6 : ¬ GGInnerDiagOnLabel GGNbrInner937U63Label p Bs K)
    (hF4 : ¬ GGInnerDiagOnLabel GGF4ThreeLabel p Bs K)
    (hTwE6 : ¬ GGInnerDiagOnLabel GGTwE6BadLabel p Bs K)
    (hNS : p = 3 → ¬ GGInnerDiagOnLabel GGTableBNbrInnerLinearNsLabel p Bs K)
    (hE6 : ¬ GGInnerDiagOnLabel GGE6TwoThreeLabel p Bs K)
    (hTwSub : p = 3 → ¬ GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) p Bs K) : False := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  by_cases hU : lab.tag = .twA ∧ lab.rank = 5 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1
  · apply hU6
    apply hUse GGNbrInner937U63Label
    refine ⟨⟨hU.1, by omega, ?_, ?_⟩, hU.2.1, hU.2.2.1⟩
    · simpa [hU.2.2.1] using hU.2.2.2
    · rw [hU.2.2.1, hU.2.1]; norm_num
  · by_cases hS : GGTBResSmallLabel p lab
    · exact ggTBWeylRowResRest_small_false_nbr hH.1 hnb
        (hUse (fun p lab => GGTBWeylRowResRest p lab ∧ GGTBResSmallLabel p lab)
          ⟨⟨hRes, hU⟩, hS⟩)
    · have hRest2 : GGTBWeylRowResRest2 p lab := ⟨⟨hRes, hU⟩, hS⟩
      rcases ggTBWeylRowResRest2_cases Fact.out hp2 hΛ hRest2 with hA | hF | hE | hT | hBad
      · apply hNS hA.2.2.2
        apply hUse GGTableBNbrInnerLinearNsLabel
        refine ⟨hA.1, by omega, hp2, ?_⟩
        rw [hA.2.2.1, hA.2.2.2]
        norm_num
      · exact hF4 (hUse GGF4ThreeLabel hF)
      · exact hE6 (hUse GGE6TwoThreeLabel hE)
      · exact hTwSub hT.2.1
          (hUse (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) ⟨hT.1, hT.2.2⟩)
      · exact hTwE6 (hUse GGTwE6BadLabel hBad)

private theorem GGResHyp.not_innerDiag_rowRes_of_rest
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU6 : ¬ GGInnerDiagOnLabel GGNbrInner937U63Label p Bs K)
    (hF4 : ¬ GGInnerDiagOnLabel GGF4ThreeLabel p Bs K)
    (hTwE6 : ¬ GGInnerDiagOnLabel GGTwE6BadLabel p Bs K)
    (hNS : p = 3 → ¬ GGInnerDiagOnLabel GGTableBNbrInnerLinearNsLabel p Bs K)
    (hE6 : ¬ GGInnerDiagOnLabel GGE6TwoThreeLabel p Bs K)
    (hTwSub : p = 3 → ¬ GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) p Bs K) :
    ¬ GGInnerDiagOnLabel GGTBWeylRowRes p Bs K := by
  intro hMark
  obtain ⟨hperf, lab, hΛ, hRaw⟩ := hMark
  obtain ⟨R, hR, I, F, hRs, hRn, θ, hData⟩ := largeEvenRawDatum_exists hRaw
  have hUse : ∀ S : ℕ → LargeEvenLabel → Prop, S p lab →
      GGInnerDiagOnLabel S p Bs K := by
    intro S hSel
    refine ⟨hperf, lab, hΛ, largeEvenRawDatum_mono (fun R _ I F hQ => ?_) hRaw⟩
    obtain ⟨hs, hna, θ, hθ⟩ := hQ
    exact ⟨hs, hna, θ, ⟨hSel, hθ.2⟩⟩
  exact GGResHyp.false_of_rowRes_cases hH hData.1 hΛ hUse hU6 hF4 hTwE6 hNS hE6 hTwSub

theorem GGResHyp.false_of_nbr_rest_known
    (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hTor : ¬ GGInnerDiagOnLabel GGTBTorCov p Bs K)
    (hU6 : ¬ GGInnerDiagOnLabel GGNbrInner937U63Label p Bs K)
    (hF4 : ¬ GGInnerDiagOnLabel GGF4ThreeLabel p Bs K)
    (hTwE6 : ¬ GGInnerDiagOnLabel GGTwE6BadLabel p Bs K)
    (hNS : p = 3 → ¬ GGInnerDiagOnLabel GGTableBNbrInnerLinearNsLabel p Bs K)
    (hE6 : ¬ GGInnerDiagOnLabel GGE6TwoThreeLabel p Bs K)
    (hTwSub : p = 3 → ¬ GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) p Bs K)
    (hSeven : p = 7 → ¬ GGInnerDiagOnLabel
      (fun _ lab => lab = ⟨.A,8,1⟩ ∨ lab = ⟨.A,11,1⟩ ∨ lab = ⟨.E6,0,1⟩ ∨
        lab = ⟨.twE6,0,1⟩ ∨ lab = ⟨.E8,0,1⟩) p Bs K) : False := by
  have hNoRes := GGResHyp.not_innerDiag_rowRes_of_rest hH hU6 hF4 hTwE6 hNS hE6 hTwSub
  have hNoCov : ¬ GGInnerDiagOnLabel
      (fun p lab => GGTBTorCov p lab ∨ GGTBWeylRowRes p lab) p Bs K :=
    fun hMark => hMark.elim_or.elim hTor hNoRes
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hRow := (ggResXRest_of_known hRig hraw hiso hTCJ hI3
    G p B Bs x L D J y K hH).2 hNoCov
  obtain ⟨labJ, labK, hΛJ, hΛK, hJ, hK, hSevenRow⟩ := hRow
  exact hSeven hSevenRow.1 (largeEvenMarking_mono
    (fun lab' R _ I F θ hP => ⟨(by rw [hP.1]; exact hSevenRow.2), hP.2⟩)
    (ggInnerDiagOn_relabel hRig (hH.2.2.1.2 y K hnb) hΛK hK))

theorem ggResCentBoundNbrRestInput_of_known
    (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput)
    :
    GGResCentBoundNbrRestInput := by
  intro G _ _ p B Bs x L D J y K hH _ _ hTor hU6 hF4 hTwE6 hNS hE6 hTwSub hSeven _ _
  exact (GGResHyp.false_of_nbr_rest_known hRig hraw hiso hTCJ hI3
    hH hTor hU6 hF4 hTwE6 hNS hE6 hTwSub hSeven).elim

theorem ggResCentBoundNbrInput_of_known
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hRk : GGTwE6ThreeNbrRankInput)
    (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    : GGResCentBoundNbrInput  := by
  exact ggResCentBoundNbrInput_of_rest hT hLift hX hTCJ hRig hLB hPJ hRk hA8 hraw hiso
    (ggResCentBoundNbrRestInput_of_known hRig hraw hiso hTCJ
      (ggNbrSubcomponentInput_of_lBalance hLB hPJ))

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGResidualWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGNSJoinOutWeakPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanCharTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGPhanCentralQuotient
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanLocal
public import CFSG.LocalAnalysis.StandardType.GGNSJoinByType
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanUnitaryAnyA
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEData
import CFSG.LocalAnalysis.StandardType.GGWeylNoEichlerBCDAux
import CFSG.LocalAnalysis.StandardType.PhanELiftQuasi
import CFSG.LocalAnalysis.StandardType.GGOrthFrameConcl
import CFSG.LocalAnalysis.StandardType.GGOrthModelInputsHold
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneWeyl
import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryGen
import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryRk1
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanTransfer
import CFSG.GroupTheory.QuasisimpleCentralSection
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan

section Defs

@[expose] def GGExcPhanPayloadOf (n : ℕ) (N : CoxeterMatrix (Fin n)) (t : StatedLieTag) (p : ℕ)
    {G : Type} [Group G] (Bs X : Subgroup G) : Prop :=
  ∃ f : ℕ, 4 ≤ 2 ^ f ∧ IsCentralQuotientOf (lieUniversal t 0 2 f Nat.prime_two) ↥X ∧
    ∃ s : Fin n → MulAut ↥Bs, (∀ i, s i ∈ ggAutomizer X Bs ∧ GGIsReflection p (s i)) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = (2 ^ f) ^ 2 ∧
        (∀ i, Nonempty (Su F 2 f 2 ≃* ggRankOneIn X Bs (s i))) ∧
        (∀ i j, i ≠ j → N.M i j = 2 →
          ∀ a ∈ ggRankOneIn X Bs (s i), ∀ b ∈ ggRankOneIn X Bs (s j), a * b = b * a) ∧
        (∀ i j, N.M i j = 3 → ∃ W : Subgroup G,
          UnitaryBlockStandardPair F 2 f W (ggRankOneIn X Bs (s i)) (ggRankOneIn X Bs (s j)))

@[expose] def GGExcPhanPayload (p : ℕ) {G : Type} [Group G] (Bs X : Subgroup G) : Prop :=
  GGExcPhanPayloadOf 6 CoxeterMatrix.E₆ .twistedE6 p Bs X ∨
    GGExcPhanPayloadOf 7 CoxeterMatrix.E₇ .E7 p Bs X ∨
    GGExcPhanPayloadOf 8 CoxeterMatrix.E₈ .E8 p Bs X

@[expose] def GGResidualGenFrame (p : ℕ) {G : Type} [Group G] (Bs X : Subgroup G) : Prop :=
  (∃ Φ : OrthTorus.OrthWeakFrame p Bs X, Φ.Recognized) ∨ GGExcPhanPayload p Bs X

@[expose] def ggRowP_ResGenRest (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ggRowP_ETwE6 p lab ∨ ggRowP_EE7 p lab ∨ ggRowP_EE8 p lab ∨
    (lab.n = 1 ∧ ((ggRowP_ESU p lab ∧ (lab.rank = 3 ∨ lab.rank = 5)) ∨ ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab))

@[expose] def ggRowP_ResGenExc (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ggRowP_ETwE6 p lab ∨ ggRowP_EE7 p lab ∨ ggRowP_EE8 p lab

@[expose] def ggRowP_ResGenRestTwo (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.n = 1 ∧ ((ggRowP_ESU p lab ∧ (lab.rank = 3 ∨ lab.rank = 5)) ∨ ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab)

@[expose] def ggRowP_ResGenExcFrame : ℕ → LargeEvenLabel → Prop :=
  fun _ _ => False

@[expose] def GGGenResidualFrameInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ¬ GGIsWeylMatrixA M →
        ∀ X : Subgroup G, (X = L ∨ (X ∈ 𝒦 ∧ ¬ NSJoin.NSTypeD M) ∨ (T M ∧ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X)) →
          ¬ GGSplitLie p X → ¬ GGMemberUnitary p Bs X →
          (¬ NSJoin.NSTypeD M → GGInnerDiagOnLabel ggRowP_ResGenExcFrame p Bs X) →
          (NSJoin.NSTypeD M → X ≠ L) →
          GGResidualGenFrame p Bs X ∨ GGGenConcl M Bs X L 𝒦 e

end Defs

theorem ggRowP_ResGenRest_iff {p : ℕ} {lab : LargeEvenLabel} :
    ggRowP_ResGenRest p lab ↔ ggRowP_ResGenExc p lab ∨ ggRowP_ResGenRestTwo p lab := by
  unfold ggRowP_ResGenRest ggRowP_ResGenExc ggRowP_ResGenRestTwo
  tauto

theorem eq_of_isCentralQuotientOf_of_le {U : LieUniversal} (hU : CFSG.IsQuasisimple U.K) {G : Type} [Group G]
    [Finite G] {X Y : Subgroup G} (hYX : Y ≤ X) (hX : IsCentralQuotientOf U ↥X)
    (hY : IsCentralQuotientOf U ↥Y) : Y = X := by
  obtain ⟨θX, hθXs, hθXk⟩ := hX
  obtain ⟨θY, hθYs, hθYk⟩ := hY
  have hXq : CFSG.IsQuasisimple ↥X := CFSG.LocalCores.isQuasisimple_of_surjective hU θX hθXs hθXk
  have hYq : CFSG.IsQuasisimple ↥Y := CFSG.LocalCores.isQuasisimple_of_surjective hU θY hθYs hθYk
  have equivOf : ∀ {Q : Type} [Group Q] (θ : U.K →* Q), Function.Surjective θ →
      θ.ker ≤ Subgroup.center U.K →
      Nonempty (U.K ⧸ Subgroup.center U.K ≃* Q ⧸ Subgroup.center Q) := by
    intro Q _ θ hs hk
    have hc : Subgroup.center U.K = ((QuotientGroup.mk' (Subgroup.center Q)).comp θ).ker := by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
        CFSG.LocalCores.comap_center_eq_of_perfect hU.1 θ hs hk]
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hs))⟩
  obtain ⟨eX⟩ := equivOf θX hθXs hθXk
  obtain ⟨eY⟩ := equivOf θY hθYs hθYk
  have htop := (CFSG.GroupTheory.eq_top_and_exists_central_surjection_of_quasisimple_section ↥Y ↥X hYq hXq
    (eY.symm.trans eX) (Y.subgroupOf X) (Subgroup.subgroupOfEquivOfLe hYX).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hYX).surjective).1
  exact le_antisymm hYX (Subgroup.subgroupOf_eq_top.mp htop)

section Proofs

theorem GGExcPhanPayloadOf.le_iSup_rankOne {n : ℕ} {N : CoxeterMatrix (Fin n)} {t : StatedLieTag}
    (hPhan : ∀ (F : Type) [Field F] [Finite F] (f : ℕ) [CharP F 2], Nat.card F = (2 ^ f) ^ 2 → 4 ≤ 2 ^ f →
      ∀ {Y : Type} [Group Y] (U : Fin n → Subgroup Y) (W : Fin n → Fin n → Subgroup Y),
        WeakPhanSL F 2 f N U W → IsCentralQuotientOf (lieUniversal t 0 2 f Nat.prime_two) Y)
    (hQ : ∀ f : ℕ, 4 ≤ 2 ^ f → CFSG.IsQuasisimple (lieUniversal t 0 2 f Nat.prime_two).K)
    {p : ℕ} {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (h : GGExcPhanPayloadOf n N t p Bs X) :
    X ≤ ⨆ r : MulAut ↥Bs, ⨆ (_ : r ∈ ggAutomizer X Bs), ⨆ (_ : GGIsReflection p r),
      ggRankOneIn X Bs r := by
  obtain ⟨f, hq, hXc, s, hs, F, hFf, hFfin, hFc, hF, hiso, hcomm, hpair⟩ := h
  letI : Field F := hFf
  letI : Finite F := hFfin
  haveI : CharP F 2 := hFc
  have hW := ggWeakPhanSL_subgroupOf (H := ⨆ i, ggRankOneIn X Bs (s i)) (Equiv.refl (Fin n))
    (ggBCDE_reindex_refl N).symm hq F hF (fun i => ggRankOneIn X Bs (s i)) hiso hcomm hpair rfl
  have hYc : IsCentralQuotientOf (lieUniversal t 0 2 f Nat.prime_two) ↥(⨆ i, ggRankOneIn X Bs (s i)) :=
    hPhan F f hF hq _ _ hW
  have hYX : ⨆ i, ggRankOneIn X Bs (s i) ≤ X := iSup_le fun i => ggRankOneIn_le X Bs (s i)
  refine (eq_of_isCentralQuotientOf_of_le (hQ f hq) hYX hXc hYc).symm.le.trans (iSup_le fun i => ?_)
  exact (le_iSup (fun (_ : GGIsReflection p (s i)) => ggRankOneIn X Bs (s i)) (hs i).2).trans
    ((le_iSup (fun (_ : s i ∈ ggAutomizer X Bs) =>
        ⨆ (_ : GGIsReflection p (s i)), ggRankOneIn X Bs (s i)) (hs i).1).trans
      (le_iSup (fun r => ⨆ (_ : r ∈ ggAutomizer X Bs), ⨆ (_ : GGIsReflection p r),
        ggRankOneIn X Bs r) (s i)))

theorem GGExcPhanPayload.le_iSup_rankOne
    (hPE : PhanEInput2) {p : ℕ} {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (h : GGExcPhanPayload p Bs X) :
    X ≤ ⨆ r : MulAut ↥Bs, ⨆ (_ : r ∈ ggAutomizer X Bs), ⨆ (_ : GGIsReflection p r),
      ggRankOneIn X Bs r := by
  have hf1 : ∀ f : ℕ, 4 ≤ 2 ^ f → 1 ≤ f := by
    intro f hq
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · subst h0; norm_num at hq
    · exact h0
  rcases h with h6 | h7 | h8
  · refine h6.le_iSup_rankOne ?_ (fun f hq => PhanE.isQuasisimple_lieUniversal_twistedE6 f (hf1 f hq))
    intro F _ _ f _ hF hq
    exact (hPE F f hF hq).1
  · refine h7.le_iSup_rankOne ?_ (fun f _ => PhanE.isQuasisimple_lieUniversal_E7 f)
    intro F _ _ f _ hF hq
    exact (hPE F f hF hq).2.1
  · refine h8.le_iSup_rankOne ?_ (fun f _ => PhanE.isQuasisimple_lieUniversal_E8 f)
    intro F _ _ f _ hF hq
    exact (hPE F f hF hq).2.2

theorem GGResidualGenFrame.le_iSup_rankOne
    (hD : PhanDInput2) (hPE : PhanEInput2) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {G : Type} [Group G]
    [Finite G] {Bs X : Subgroup G} (h : GGResidualGenFrame p Bs X) :
    X ≤ ⨆ r : MulAut ↥Bs, ⨆ (_ : r ∈ ggAutomizer X Bs), ⨆ (_ : GGIsReflection p r),
      ggRankOneIn X Bs r := by
  rcases h with ⟨Φ, hΦ⟩ | hE
  · exact Φ.le_iSup_rankOne hp2 hD OrthTorus.orthRankOneModelInput_holds OrthTorus.orthPairModelInput_holds
      OrthTorus.orthGenModelInput_holds hΦ
  · exact hE.le_iSup_rankOne hPE

theorem ggGenConcl_of_le_iSup_isReflection {p : ℕ} {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {X : Subgroup G} (hXA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (h : X ≤ ⨆ r : MulAut ↥Bs, ⨆ (_ : r ∈ ggAutomizer X Bs), ⨆ (_ : GGIsReflection p r),
      ggRankOneIn X Bs r) :
    GGGenConcl M Bs X L 𝒦 e := by
  unfold GGGenConcl
  apply le_antisymm
  · refine h.trans (iSup_le fun r => iSup_le fun hrA => iSup_le fun hrR => ?_)
    have hrC : r ∈ ggCoxRefl M e :=
      ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3 (hXA hrA) hrR
    exact le_iSup₂_of_le (f := fun r (_ : r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer X Bs ∧ r ∈ ggCoxRefl M e}) =>
      ggRankOneIn X Bs r) r ⟨hrA, hrC⟩ le_rfl
  · exact iSup₂_le fun r _ => ggRankOneIn_le X Bs r

end Proofs

end CFSG.StandardType

end

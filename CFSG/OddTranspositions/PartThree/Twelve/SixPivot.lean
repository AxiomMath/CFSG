module

public import CFSG.OddTranspositions.PartThree.Twelve.Minimal
public import CFSG.OddTranspositions.PartThree.OddTranspClosure
public import CFSG.OddTranspositions.PartThree.Twelve.Three
public import CFSG.OddTranspositions.PartFour.Fourteen.SpCommonPerp
public import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockSp
import CFSG.OddTranspositions.PartThree.Twelve.Five
import CFSG.OddTranspositions.PartThree.Nine.Setup
import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLayer
import CFSG.LieType.SteinbergBRMulEquivCores
import CFSG.OddTranspositions.WidthSylow
import CFSG.OddTranspositions.TheoremTwo.Assembly
import CFSG.OddTranspositions.SixNine
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeSwap
import CFSG.LocalAnalysis.EvenSporadicStandard.SolvableRadical
import CFSG.Quasithin.Background.E1TwoAbs
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Hom
import CFSG.OddTranspositions.PartFour.Fourteen.SpShapeRigid
import CFSG.OddTranspositions.PartFour.Fourteen.ShapeTransport
import CFSG.OddTranspositions.PartThree.Twelve.FourOrth
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.ClassicalInvolution.WeakCT.StandardPair
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwap
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizePieces
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
import CFSG.OddTranspositions.O4PairTenWidth
import CFSG.OddTranspositions.Width

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem mem_Halpha_of_mem_commSet (hC : HypothesisC D) (hα : hC.alpha = {hC.d}) {x : G}
    (hx : x ∈ commSet D hC.d) : x ∈ Halpha D hC.alpha :=
  Subgroup.subset_closure ((Nine.DalphaStar_eq_commSet hC hα).symm ▸ hx)

theorem mem_DstarH_of_mem_commSet (hC : HypothesisC D) (hα : hC.alpha = {hC.d}) {x : G}
    (hx : x ∈ commSet D hC.d) :
    (⟨x, mem_Halpha_of_mem_commSet hC hα hx⟩ : Halpha D hC.alpha) ∈ DstarH hC :=
  (mem_DstarH_iff hC).mpr ((Nine.DalphaStar_eq_commSet hC hα).symm ▸ hx)

abbrev commonPerpH (hC : HypothesisC D) (x y : G) : Set (Halpha D hC.alpha) :=
  {z | (z : G) ∈ commSet D x ∩ commSet D y ∩ commSet D hC.d}

theorem image_commonPerpH (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y) :
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) '' commonPerpH hC x y =
      {z | IsConj s z ∧
        Commute z (QuotientGroup.mk' _ ⟨x, mem_Halpha_of_mem_commSet hC hα hx⟩) ∧
        Commute z (QuotientGroup.mk' _ ⟨y, mem_Halpha_of_mem_commSet hC hα hy⟩)} := by
  obtain ⟨d₀, hd₀⟩ := imageClass_isClass hC
  have hcls : ∀ z, z ∈ imageClass hC ↔ IsConj s z := by
    intro z
    rw [hd₀] at hs ⊢
    exact ⟨fun hz => (isConj_comm.mp hs).trans hz, fun hz => (show IsConj d₀ s from hs).trans hz⟩
  set xH : Halpha D hC.alpha := ⟨x, mem_Halpha_of_mem_commSet hC hα hx⟩
  set yH : Halpha D hC.alpha := ⟨y, mem_Halpha_of_mem_commSet hC hα hy⟩
  have hxs : xH ∈ DstarH hC := mem_DstarH_of_mem_commSet hC hα hx
  have hys : yH ∈ DstarH hC := mem_DstarH_of_mem_commSet hC hα hy
  ext z
  constructor
  · rintro ⟨w, ⟨⟨hwx, hwy⟩, hwd⟩, rfl⟩
    have hwH : w ∈ DstarH hC :=
      (mem_DstarH_iff hC).mpr ((Nine.DalphaStar_eq_commSet hC hα).symm ▸ hwd)
    refine ⟨(hcls _).mp ⟨w, hwH, rfl⟩, ?_, ?_⟩
    · exact (show Commute w xH from Subtype.ext hwx.2.1.eq).map _
    · exact (show Commute w yH from Subtype.ext hwy.2.1.eq).map _
  · rintro ⟨hz, hzx, hzy⟩
    obtain ⟨w, hw, rfl⟩ := (hcls z).mpr hz
    have hwx : Commute w xH := commute_of_commute_mk_of_le_center hC hMZ hw hxs hzx
    have hwy : Commute w yH := commute_of_commute_mk_of_le_center hC hMZ hw hys hzy
    have hwG : (w : G) ∈ commSet D hC.d := by
      rw [← Nine.DalphaStar_eq_commSet hC hα]
      exact (mem_DstarH_iff hC).mp hw
    have hwxG : Commute (w : G) x := congrArg Subtype.val hwx.eq
    have hwyG : Commute (w : G) y := congrArg Subtype.val hwy.eq
    refine ⟨w, ⟨⟨⟨hwG.1, hwxG, fun h => hxy ?_⟩, ⟨hwG.1, hwyG, fun h => hxy ?_⟩⟩, hwG⟩, rfl⟩
    · rw [← h]
      exact hwyG
    · rw [← h]
      exact hwxG.symm

theorem map_closure_commonPerpH (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y) :
    (Subgroup.closure (commonPerpH hC x y)).map
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) =
      Subgroup.closure {z | IsConj s z ∧
        Commute z (QuotientGroup.mk' _ ⟨x, mem_Halpha_of_mem_commSet hC hα hx⟩) ∧
        Commute z (QuotientGroup.mk' _ ⟨y, mem_Halpha_of_mem_commSet hC hα hy⟩)} := by
  rw [MonoidHom.map_closure, image_commonPerpH hC hMZ hα hs hx hy hxy]

theorem not_commute_mk_of_mem_commSet (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d}) {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d)
    (hxy : ¬ Commute x y) :
    ¬ Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        ⟨x, mem_Halpha_of_mem_commSet hC hα hx⟩)
      (QuotientGroup.mk' _ ⟨y, mem_Halpha_of_mem_commSet hC hα hy⟩) := fun h =>
  hxy (congrArg Subtype.val (commute_of_commute_mk_of_le_center hC hMZ
    (mem_DstarH_of_mem_commSet hC hα hx) (mem_DstarH_of_mem_commSet hC hα hy) h).eq)

abbrev hypLineGroup (D : Set G) (x y : G) : Subgroup G :=
  Subgroup.closure (commSet D x ∩ commSet D y)

theorem setup_quotient_solvableRadical {X : Type} [Group X] [Finite X] {E : Set X}
    (hS : Setup X E) (hns : ¬ Group.IsSolvable X) :
    Setup (X ⧸ CFSG.solvableRadical X) (QuotientGroup.mk' (CFSG.solvableRadical X) '' E) := by
  refine hS.map _ (QuotientGroup.mk'_surjective _) fun e he h1 => hns ?_
  have he' : e ∈ CFSG.solvableRadical X := (QuotientGroup.eq_one_iff e).mp h1
  rcases hS.subset_or_disjoint (CFSG.solvableRadical X) with hsub | hdisj
  · have htop := hS.eq_top_of_subset _ hsub
    have hRs : Group.IsSolvable (CFSG.solvableRadical X) :=
      CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
    rw [htop] at hRs
    exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup X).subtype)
      (fun g => ⟨⟨g, trivial⟩, rfl⟩)
  · exact absurd he' (hdisj e he)

theorem not_disconnected_image {X : Type} [Group X] [Finite X] {E : Set X} {Y : Type} [Group Y]
    (φ : X →* Y) (h : ¬ CFSG.Timmesfeld.Connectivity.Disconnected E) :
    ¬ CFSG.Timmesfeld.Connectivity.Disconnected (φ '' E) := by
  rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hab⟩
  exact hab (OddLocal.reach_map φ (reach_of_not_disconnected h ha hb))

theorem eq_commSet_of_isMaxOrbit {X : Type} [Group X] {E D : Set X} {d : X}
    (hN : CFSG.Timmesfeld.Connectivity.IsNormalSet D)
    (htrans : ∀ e ∈ commSet D d, ∀ e' ∈ commSet D d,
      ∃ g ∈ Subgroup.closure (commSet D d), g * e * g⁻¹ = e')
    (hE : IsMaxOrbit D d E) : E = commSet D d := by
  obtain ⟨e, he, rfl, -⟩ := hE
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hgd : Commute g d := by
      have hle : Subgroup.closure (commSet D d) ≤ Subgroup.centralizer {d} := by
        rw [Subgroup.closure_le]
        intro z hz
        exact Subgroup.mem_centralizer_singleton_iff.mpr hz.2.1.eq
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
    refine ⟨hN g e he.1, ?_, fun h => he.2.2 ?_⟩
    · have h1 : Commute (g * e * g⁻¹) (g * d * g⁻¹) := he.2.1.conj g
      rwa [hgd.eq, mul_inv_cancel_right] at h1
    · have h2 : g * e * g⁻¹ = g * d * g⁻¹ := by rw [h, hgd.eq, mul_inv_cancel_right]
      simpa using h2
  · intro hf
    obtain ⟨g, hg, hge⟩ := htrans e he f hf
    exact ⟨g, hg, hge.symm⟩

theorem not_isSolvable_of_isSymplecticTransvection {X : Type} [Group X] {s : X} {m f : ℕ}
    (hf : 2 ≤ f) (h : IsSymplecticTransvection X m f s) : ¬ Group.IsSolvable X := by
  obtain ⟨k, hmk, F, hF, hFin, hcard, e, hr⟩ := h
  have h4 : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Group.IsPerfect (CFSG.Open.StatedSp k F) :=
    CFSG.ClassicalInvolution.Models.SymplecticPairs.isPerfect_statedSp_of_four_le h4
  have : Nontrivial (CFSG.Open.StatedSp k F) := by
    refine ⟨⟨e (QuotientGroup.mk s), 1, fun h1 => ?_⟩⟩
    rw [h1] at hr
    simp [IsSymplecticTransvectionIn] at hr
  have hns : ¬ Group.IsSolvable (CFSG.Open.StatedSp k F) :=
    CFSG.LieType.SteinbergBR.not_isSolvable_of_isPerfect
  intro hX
  exact hns (Group.isSolvable_of_surjective
    (f := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)))

theorem isConj_of_mem_imageClass (hC : HypothesisC D)
    {s z : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs : s ∈ imageClass hC) (hz : z ∈ imageClass hC) : IsConj s z := by
  obtain ⟨d₀, hd₀⟩ := imageClass_isClass hC
  rw [hd₀] at hs hz
  exact (isConj_comm.mp hs).trans hz

theorem not_isSolvable_closure_of_subset (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y)
    {Ω : Set G} (hΔΩ : commSet D x ∩ commSet D y ∩ commSet D hC.d ⊆ Ω) :
    ¬ Group.IsSolvable (Subgroup.closure Ω) := by
  obtain ⟨t, ht, -, -, -, hSpK, -, -⟩ := isSymplecticTransvection_closure_commonCommute
    (center_Hbar_eq_bot hC) hn hSp
    (isConj_of_mem_imageClass hC hs ⟨_, mem_DstarH_of_mem_commSet hC hα hx, rfl⟩)
    (isConj_of_mem_imageClass hC hs ⟨_, mem_DstarH_of_mem_commSet hC hα hy, rfl⟩)
    (not_commute_mk_of_mem_commSet hC hMZ hα hx hy hxy)
  have hKbar := not_isSolvable_of_isSymplecticTransvection hf hSpK
  intro hL
  apply hKbar
  rw [← map_closure_commonPerpH hC hMZ hα hs hx hy hxy]
  have hle : Subgroup.closure (commonPerpH hC x y) ≤
      (Subgroup.closure Ω).comap (Halpha D hC.alpha).subtype := by
    rw [Subgroup.closure_le]
    intro z hz
    exact Subgroup.subset_closure (hΔΩ hz)
  let φ : Subgroup.closure (commonPerpH hC x y) →* Subgroup.closure Ω :=
    ((Halpha D hC.alpha).subtype.comp (Subgroup.closure (commonPerpH hC x y)).subtype).codRestrict
      _ fun k => hle k.2
  have hφ : Function.Injective φ := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : Subgroup.closure Ω => (z : G)) h
  have : Group.IsSolvable (Subgroup.closure (commonPerpH hC x y)) :=
    Group.isSolvable_of_isSolvable_injective hφ
  exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective _ _)

theorem exists_not_commute_of_setup {X : Type} [Group X] {E : Set X} (hS : Setup X E)
    (hns : ¬ Group.IsSolvable X) : ∀ a ∈ E, ∃ b ∈ E, ¬ Commute a b := by
  intro a ha
  by_contra h
  push Not at h
  apply hns
  have hcen : a ∈ Subgroup.center X := by
    have hle : (⊤ : Subgroup X) ≤ Subgroup.centralizer {a} := by
      rw [← hS.gen, Subgroup.closure_le]
      intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mpr (h b hb).eq.symm
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))
  have hEa : E ⊆ {a} := by
    intro b hb
    obtain ⟨c, rfl⟩ := isConj_iff.mp (hS.isConj ha hb)
    rw [Set.mem_singleton_iff, Subgroup.mem_center_iff.mp hcen c, mul_inv_cancel_right]
  have htop : Subgroup.closure ({a} : Set X) = ⊤ :=
    top_le_iff.mp (hS.gen ▸ Subgroup.closure_mono hEa)
  have hcomm : ∀ g h : X, g * h = h * g := by
    intro g h
    have hg : g ∈ Subgroup.closure ({a} : Set X) := htop ▸ Subgroup.mem_top g
    have hh : h ∈ Subgroup.closure ({a} : Set X) := htop ▸ Subgroup.mem_top h
    rw [← Subgroup.zpowers_eq_closure] at hg hh
    obtain ⟨i, rfl⟩ := hg
    obtain ⟨j, rfl⟩ := hh
    rw [← zpow_add, ← zpow_add, add_comm]
  exact Group.isSolvable_of_comm hcomm

abbrev deltaIn (Ω D : Set G) (x y d : G) : Set (Subgroup.closure Ω) :=
  {z | (z : G) ∈ commSet D x ∩ commSet D y ∩ commSet D d}

omit [Finite G] in
theorem commSet_image_inClosure (hD : IsOddTransp D) {Ω : Set G} {x y d : G}
    (hΩ : Ω ⊆ commSet D x ∩ commSet D y) (hdΩ : d ∈ Ω)
    (hΔΩ : commSet D x ∩ commSet D y ∩ commSet D d ⊆ Ω)
    (hcen : CFSG.solvableRadical (Subgroup.closure Ω) ≤ Subgroup.center (Subgroup.closure Ω))
    (hnc : ∀ a ∈ inClosure Ω, ∃ b ∈ inClosure Ω, ¬ Commute a b) :
    commSet (QuotientGroup.mk' (CFSG.solvableRadical (Subgroup.closure Ω)) '' inClosure Ω)
        (QuotientGroup.mk' _ ⟨d, Subgroup.subset_closure hdΩ⟩) =
      QuotientGroup.mk' (CFSG.solvableRadical (Subgroup.closure Ω)) '' deltaIn Ω D x y d := by
  set dL : Subgroup.closure Ω := ⟨d, Subgroup.subset_closure hdΩ⟩ with hdLdef
  have hE := isOddTransp_inClosure hD fun z hz => (hΩ hz).1.1
  have hinj := injOn_mk_of_le_center hE hcen hnc
  have hdL : dL ∈ inClosure Ω := hdΩ
  ext z
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hwc, hwne⟩
    have hc : Commute w dL := commute_of_commute_mk_of_le_center' hE hcen hw hdL hwc
    refine ⟨w, ⟨hΩ hw, (hΩ hw).1.1, congrArg Subtype.val hc.eq, fun h => hwne ?_⟩, rfl⟩
    have hwd : w = dL := Subtype.ext h
    rw [hwd]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨w, hΔΩ hw, rfl⟩, ?_, fun h => ?_⟩
    · exact (show Commute w dL from Subtype.ext hw.2.2.1.eq).map _
    · exact hw.2.2.2 (congrArg Subtype.val (hinj (hΔΩ hw) hdL h))

omit [Finite G] in
theorem exists_mem_closure_deltaIn_of_mem_closure_commonPerpH (hC : HypothesisC D)
    (hα : hC.alpha = {hC.d}) {x y : G} {Ω : Set G}
    (hΔΩ : commSet D x ∩ commSet D y ∩ commSet D hC.d ⊆ Ω) {g₀ : Halpha D hC.alpha}
    (hg : g₀ ∈ Subgroup.closure (commonPerpH hC x y)) :
    ∃ g ∈ Subgroup.closure (deltaIn Ω D x y hC.d), (g : G) = g₀ := by
  have h1 : (Subgroup.closure (commonPerpH hC x y)).map (Halpha D hC.alpha).subtype =
      Subgroup.closure (commSet D x ∩ commSet D y ∩ commSet D hC.d) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z, mem_Halpha_of_mem_commSet hC hα hz.2⟩, hz, rfl⟩
  have h2 : (Subgroup.closure (deltaIn Ω D x y hC.d)).map (Subgroup.closure Ω).subtype =
      Subgroup.closure (commSet D x ∩ commSet D y ∩ commSet D hC.d) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z, Subgroup.subset_closure (hΔΩ hz)⟩, hz, rfl⟩
  have hmem : (g₀ : G) ∈ (Subgroup.closure (deltaIn Ω D x y hC.d)).map
      (Subgroup.closure Ω).subtype := by
    rw [h2, ← h1]
    exact ⟨g₀, hg, rfl⟩
  obtain ⟨g, hg', hgeq⟩ := hmem
  exact ⟨g, hg', hgeq⟩

theorem exists_conj_deltaIn (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y)
    {Ω : Set G} (hΔΩ : commSet D x ∩ commSet D y ∩ commSet D hC.d ⊆ Ω)
    {δ δ' : Subgroup.closure Ω} (hδ : δ ∈ deltaIn Ω D x y hC.d)
    (hδ' : δ' ∈ deltaIn Ω D x y hC.d) :
    ∃ g ∈ Subgroup.closure (deltaIn Ω D x y hC.d), g * δ * g⁻¹ = δ' := by
  have hZ := center_Hbar_eq_bot hC
  obtain ⟨t, ht, -, -, -, -, hcl, -⟩ := isSymplecticTransvection_closure_commonCommute hZ hn hSp
    (isConj_of_mem_imageClass hC hs ⟨_, mem_DstarH_of_mem_commSet hC hα hx, rfl⟩)
    (isConj_of_mem_imageClass hC hs ⟨_, mem_DstarH_of_mem_commSet hC hα hy, rfl⟩)
    (not_commute_mk_of_mem_commSet hC hMZ hα hx hy hxy)
  have hne := (subset_rootBlock_and_ne_of_isSymplecticTransvection (imageClass_isClass hC) hZ hs
    hSp).2
  have hinj := injOn_mk_DstarH_of_rootBlock_ne hC hMZ hs hne
  let δH : Halpha D hC.alpha := ⟨δ, mem_Halpha_of_mem_commSet hC hα hδ.2⟩
  let δH' : Halpha D hC.alpha := ⟨δ', mem_Halpha_of_mem_commSet hC hα hδ'.2⟩
  have hδH : δH ∈ commonPerpH hC x y := hδ
  have hδH' : δH' ∈ commonPerpH hC x y := hδ'
  have himg := image_commonPerpH hC hMZ hα hs hx hy hxy
  have hm1 : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) δH ∈
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) '' commonPerpH hC x y :=
    ⟨δH, hδH, rfl⟩
  have hm2 : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) δH' ∈
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) '' commonPerpH hC x y :=
    ⟨δH', hδH', rfl⟩
  rw [himg] at hm1 hm2
  have h1 := (hcl _).mp hm1
  have h2 := (hcl _).mp hm2
  obtain ⟨g₁, hg₁, he₁⟩ := h1
  obtain ⟨g₂, hg₂, he₂⟩ := h2
  have hgbar : g₂ * g₁⁻¹ ∈ Subgroup.closure {z | IsConj s z ∧
      Commute z (QuotientGroup.mk' _ ⟨x, mem_Halpha_of_mem_commSet hC hα hx⟩) ∧
      Commute z (QuotientGroup.mk' _ ⟨y, mem_Halpha_of_mem_commSet hC hα hy⟩)} :=
    Subgroup.mul_mem _ hg₂ (Subgroup.inv_mem _ hg₁)
  rw [← map_closure_commonPerpH hC hMZ hα hs hx hy hxy] at hgbar
  obtain ⟨g₀, hg₀, hg₀e⟩ := hgbar
  have hconj : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (g₀ * δH * g₀⁻¹) =
      QuotientGroup.mk' _ δH' := by
    rw [map_mul, map_mul, map_inv, hg₀e, ← he₁, ← he₂]
    group
  have hδs : δH ∈ DstarH hC := mem_DstarH_of_mem_commSet hC hα hδ.2
  have hδs' : δH' ∈ DstarH hC := mem_DstarH_of_mem_commSet hC hα hδ'.2
  have heq : g₀ * δH * g₀⁻¹ = δH' := hinj (DstarH_conj_mem hC hδs) hδs' hconj
  obtain ⟨g, hg, hgeq⟩ := exists_mem_closure_deltaIn_of_mem_closure_commonPerpH hC hα hΔΩ hg₀
  refine ⟨g, hg, Subtype.ext ?_⟩
  have := congrArg Subtype.val heq
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this ⊢
  rw [hgeq]
  exact this

theorem rad_quotient_solvableRadical {X : Type} [Group X] [Finite X] :
    ∀ N : Subgroup (X ⧸ CFSG.solvableRadical X), N.Normal → Group.IsSolvable N → N = ⊥ :=
  fun N hN hNs => by
    have h := CFSG.Timmesfeld.Bridge.OddTransp.le_solvableRadical hN hNs
    rw [CFSG.SignalizerFunctorTheorem.Nonsolvable.solvableRadical_quotient] at h
    exact le_bot_iff.mp h

omit [Finite G] in
theorem d_mem_commSet_inter (hC : HypothesisC D) {x y : G} (hx : x ∈ commSet D hC.d)
    (hy : y ∈ commSet D hC.d) : hC.d ∈ commSet D x ∩ commSet D y :=
  ⟨⟨hC.hd, hx.2.1.symm, fun h => hx.2.2 h.symm⟩, ⟨hC.hd, hy.2.1.symm, fun h => hy.2.2 h.symm⟩⟩

theorem exists_hypothesisC_inClosure (hD : IsOddTransp D) {Ω : Set G} (hΩD : Ω ⊆ D) {d : G}
    (hdΩ : d ∈ Ω) (hcls : ∃ t : Subgroup.closure Ω, inClosure Ω = {g | IsConj t g})
    (hconn : ¬ CFSG.Timmesfeld.Connectivity.Disconnected (inClosure Ω))
    (hns : ¬ Group.IsSolvable (Subgroup.closure Ω)) :
    ∃ hCL : HypothesisC
        (QuotientGroup.mk' (CFSG.solvableRadical (Subgroup.closure Ω)) '' inClosure Ω),
      hCL.d = QuotientGroup.mk' _ ⟨d, Subgroup.subset_closure hdΩ⟩ := by
  have hS := setup_inClosure hD hΩD hcls
  have hSq := setup_quotient_solvableRadical hS hns
  have hconnq := not_disconnected_image
    (QuotientGroup.mk' (CFSG.solvableRadical (Subgroup.closure Ω))) hconn
  obtain ⟨hC₀⟩ := nonempty_hypothesisC hSq hconnq rad_quotient_solvableRadical
  exact exists_hypothesisC_d hC₀ ⟨_, hdΩ, rfl⟩

abbrev barSet (Ω : Set G) :
    Set (Subgroup.closure Ω ⧸ CFSG.solvableRadical (Subgroup.closure Ω)) :=
  QuotientGroup.mk' (CFSG.solvableRadical (Subgroup.closure Ω)) '' inClosure Ω

theorem DalphaStar_barSet_eq (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y)
    {Ω : Set G} (hΩ : Ω ⊆ commSet D x ∩ commSet D y) (hdΩ : hC.d ∈ Ω)
    (hΔΩ : commSet D x ∩ commSet D y ∩ commSet D hC.d ⊆ Ω)
    (hcen : CFSG.solvableRadical (Subgroup.closure Ω) ≤ Subgroup.center (Subgroup.closure Ω))
    (hS : Setup (Subgroup.closure Ω) (inClosure Ω))
    (hns : ¬ Group.IsSolvable (Subgroup.closure Ω))
    (hCL : HypothesisC (barSet Ω))
    (hd : hCL.d = QuotientGroup.mk' _ ⟨hC.d, Subgroup.subset_closure hdΩ⟩) :
    DalphaStar (barSet Ω) hCL.alpha =
      QuotientGroup.mk' (CFSG.solvableRadical (Subgroup.closure Ω)) '' deltaIn Ω D x y hC.d := by
  have hnc := exists_not_commute_of_setup hS hns
  have hcomm := commSet_image_inClosure hC.setup.oddT hΩ hdΩ hΔΩ hcen hnc
  rw [hCL.DalphaStar_alpha]
  have hE := hCL.hE
  rw [hd] at hE
  rw [eq_commSet_of_isMaxOrbit hCL.setup.normal ?_ hE, hcomm]
  intro e he e' he'
  rw [hcomm] at he he'
  obtain ⟨δ, hδ, rfl⟩ := he
  obtain ⟨δ', hδ', rfl⟩ := he'
  obtain ⟨g, hg, hgeq⟩ := exists_conj_deltaIn hC hMZ hα hs hn hSp hx hy hxy hΔΩ hδ hδ'
  refine ⟨QuotientGroup.mk' _ g, ?_, ?_⟩
  · rw [hcomm, ← MonoidHom.map_closure]
    exact ⟨g, hg, rfl⟩
  · rw [← hgeq, map_mul, map_mul, map_inv]

abbrev tripleGroup (D : Set G) (x y d : G) : Subgroup G :=
  Subgroup.closure (commSet D x ∩ commSet D y ∩ commSet D d)

omit [Finite G] in
theorem tripleGroup_le_closure {Ω : Set G} {x y d : G}
    (hΔΩ : commSet D x ∩ commSet D y ∩ commSet D d ⊆ Ω) :
    tripleGroup D x y d ≤ Subgroup.closure Ω :=
  Subgroup.closure_mono hΔΩ

omit [Finite G] in
theorem tripleGroup_le_Halpha (hC : HypothesisC D) (hα : hC.alpha = {hC.d}) (x y : G) :
    tripleGroup D x y hC.d ≤ Halpha D hC.alpha := by
  rw [Subgroup.closure_le]
  intro z hz
  exact mem_Halpha_of_mem_commSet hC hα hz.2

omit [Finite G] in
theorem closure_deltaIn_eq {Ω : Set G} {x y d : G}
    (hΔΩ : commSet D x ∩ commSet D y ∩ commSet D d ⊆ Ω) :
    Subgroup.closure (deltaIn Ω D x y d) =
      (tripleGroup D x y d).subgroupOf (Subgroup.closure Ω) := by
  apply Subgroup.map_injective (Subgroup.closure Ω).subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (tripleGroup_le_closure hΔΩ), MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hz
    exact ⟨⟨z, Subgroup.subset_closure (hΔΩ hz)⟩, hz, rfl⟩

omit [Finite G] in
theorem closure_commonPerpH_eq (hC : HypothesisC D) (hα : hC.alpha = {hC.d}) (x y : G) :
    Subgroup.closure (commonPerpH hC x y) =
      (tripleGroup D x y hC.d).subgroupOf (Halpha D hC.alpha) := by
  apply Subgroup.map_injective (Halpha D hC.alpha).subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (tripleGroup_le_Halpha hC hα x y), MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hz
    exact ⟨⟨z, mem_Halpha_of_mem_commSet hC hα hz.2⟩, hz, rfl⟩

omit [Finite G] in
theorem range_mk_comp_inclusion_closure {Ω : Set G} {x y d : G}
    (hΔΩ : commSet D x ∩ commSet D y ∩ commSet D d ⊆ Ω) :
    ((QuotientGroup.mk' (CFSG.solvableRadical (Subgroup.closure Ω))).comp
        (Subgroup.inclusion (tripleGroup_le_closure hΔΩ))).range =
      (Subgroup.closure (deltaIn Ω D x y d)).map
        (QuotientGroup.mk' (CFSG.solvableRadical (Subgroup.closure Ω))) := by
  rw [MonoidHom.range_comp, Subgroup.inclusion_range, closure_deltaIn_eq hΔΩ]

omit [Finite G] in
theorem range_mk_comp_inclusion_H (hC : HypothesisC D) (hα : hC.alpha = {hC.d}) (x y : G) :
    ((QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))).comp
        (Subgroup.inclusion (tripleGroup_le_Halpha hC hα x y))).range =
      (Subgroup.closure (commonPerpH hC x y)).map
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) := by
  rw [MonoidHom.range_comp, Subgroup.inclusion_range, closure_commonPerpH_eq hC hα]

theorem isSolvable_ker_mk_comp {K Y : Type} [Group K] [Group Y] (ι : K →* Y)
    (hι : Function.Injective ι) (N : Subgroup Y) [N.Normal] (hN : Group.IsSolvable N) :
    Group.IsSolvable ((QuotientGroup.mk' N).comp ι).ker := by
  let j : ((QuotientGroup.mk' N).comp ι).ker →* N :=
    { toFun := fun k => ⟨ι k, by
        have := k.2
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at this
        exact this⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hj : Function.Injective j := fun a b h => Subtype.ext (hι (congrArg Subtype.val h))
  exact Group.isSolvable_of_isSolvable_injective hj

theorem solvableRadical_eq_bot_of_isSymplecticTransvection {X : Type} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) {s : X} {m f : ℕ} (hm : 2 ≤ m) (hf : 2 ≤ f)
    (h : IsSymplecticTransvection X m f s) : CFSG.solvableRadical X = ⊥ := by
  have hns := not_isSolvable_of_isSymplecticTransvection hf h
  obtain ⟨k, hmk, F, hF, hFin, hcard, e, -⟩ := h
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hcard])
  have h4 : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have := CFSG.SeitzReduction.SymplecticPilot.isSimpleGroup_statedSp_of_four_le (n := k) h4
    (by omega)
  let eX : X ≃* CFSG.Open.StatedSp k F :=
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm).trans e
  have : IsSimpleGroup X := MulEquiv.isSimpleGroup eX
  refine CFSG.solvableRadical_eq_bot_of_isSimpleGroup X ?_
  by_contra hab
  push Not at hab
  exact hns (Group.isSolvable_of_comm hab)

theorem exists_surjective_of_range_eq {K Y : Type} [Group K] [Group Y] (ψ : K →* Y)
    {S : Subgroup Y} (h : ψ.range = S) :
    ∃ ψ' : K →* S, Function.Surjective ψ' ∧ ψ'.ker = ψ.ker ∧ ∀ k, (ψ' k : Y) = ψ k := by
  subst h
  exact ⟨ψ.rangeRestrict, ψ.rangeRestrict_surjective, ψ.ker_rangeRestrict, fun _ => rfl⟩

theorem exists_mulEquiv_of_surjective {K A B : Type} [Group K] [Group A] [Group B] [Finite K]
    {φ : K →* A} {χ : K →* B} (hφ : Function.Surjective φ) (hφk : Group.IsSolvable φ.ker)
    (hχ : Function.Surjective χ) (hχk : Group.IsSolvable χ.ker)
    (hB : CFSG.solvableRadical B = ⊥) :
    ∃ Ψ : B ≃* A ⧸ CFSG.solvableRadical A, ∀ k, Ψ (χ k) = QuotientGroup.mk' _ (φ k) := by
  have : Finite A := Finite.of_surjective φ hφ
  have : Finite B := Finite.of_surjective χ hχ
  obtain ⟨ψ₁, h₁⟩ := CFSG.Quasithin.E1.exists_quotRadEquiv φ hφ hφk
  obtain ⟨ψ₂, h₂⟩ := CFSG.Quasithin.E1.exists_quotRadEquiv χ hχ hχk
  let e : B ⧸ CFSG.solvableRadical B ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hB).trans QuotientGroup.quotientBot
  refine ⟨e.symm.trans (ψ₂.symm.trans ψ₁), fun k => ?_⟩
  have h3 : e.symm (χ k) = QuotientGroup.mk' _ (χ k) := (MulEquiv.symm_apply_eq _).mpr rfl
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h3, ← h₂, MulEquiv.symm_apply_apply, h₁]

theorem ker_mk_comp_le_center {K Y : Type} [Group K] [Group Y] (ι : K →* Y)
    (hι : Function.Injective ι) (N : Subgroup Y) [N.Normal] (hN : N ≤ Subgroup.center Y) :
    ((QuotientGroup.mk' N).comp ι).ker ≤ Subgroup.center K := by
  intro k hk
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hk
  rw [Subgroup.mem_center_iff]
  intro g
  apply hι
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.mp (hN hk) (ι g)

theorem solvableRadical_le_ker {K B : Type} [Group K] [Group B] [Finite K] {χ : K →* B}
    (hχ : Function.Surjective χ) (hB : CFSG.solvableRadical B = ⊥) :
    CFSG.solvableRadical K ≤ χ.ker := by
  have h := CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.map_solvableRadical_le hχ
  rwa [hB, le_bot_iff, Subgroup.map_eq_bot_iff] at h

theorem solvableRadical_le_center_of_surjective {K A : Type} [Group K] [Group A] [Finite K]
    {φ : K →* A} (hφ : Function.Surjective φ) (hφk : Group.IsSolvable φ.ker)
    (hK : CFSG.solvableRadical K ≤ Subgroup.center K) :
    CFSG.solvableRadical A ≤ Subgroup.center A := by
  rw [← CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.map_solvableRadical hφ hφk]
  exact (Subgroup.map_mono hK).trans (Subgroup.map_center_le_center hφ)

theorem hypothesisE_barSet (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y)
    {Ω : Set G} (hΩ : Ω ⊆ commSet D x ∩ commSet D y) (hdΩ : hC.d ∈ Ω)
    (hΔΩ : commSet D x ∩ commSet D y ∩ commSet D hC.d ⊆ Ω)
    (hcen : CFSG.solvableRadical (Subgroup.closure Ω) ≤ Subgroup.center (Subgroup.closure Ω))
    (hS : Setup (Subgroup.closure Ω) (inClosure Ω))
    (hns : ¬ Group.IsSolvable (Subgroup.closure Ω))
    (hCL : HypothesisC (barSet Ω))
    (hd : hCL.d = QuotientGroup.mk' _ ⟨hC.d, Subgroup.subset_closure hdΩ⟩) :
    (∃ s' ∈ imageClass hCL, IsSymplecticTransvection
      (Halpha (barSet Ω) hCL.alpha ⧸
        CFSG.solvableRadical (Halpha (barSet Ω) hCL.alpha)) (n - 2) f s') ∧
    CFSG.solvableRadical (Halpha (barSet Ω) hCL.alpha) ≤
      Subgroup.center (Halpha (barSet Ω) hCL.alpha) := by
  classical
  have hDal := DalphaStar_barSet_eq hC hMZ hα hs hn hSp hx hy hxy hΩ hdΩ hΔΩ hcen hS hns hCL hd
  have hHL : ((QuotientGroup.mk' (CFSG.solvableRadical (Subgroup.closure Ω))).comp
      (Subgroup.inclusion (tripleGroup_le_closure hΔΩ))).range = Halpha (barSet Ω) hCL.alpha := by
    rw [range_mk_comp_inclusion_closure hΔΩ, MonoidHom.map_closure]
    show _ = Subgroup.closure (DalphaStar _ hCL.alpha)
    rw [hDal]
  obtain ⟨t, ht, hts, htu, htw, hSpK, -, hcenK⟩ := isSymplecticTransvection_closure_commonCommute
    (center_Hbar_eq_bot hC) hn hSp
    (isConj_of_mem_imageClass hC hs ⟨_, mem_DstarH_of_mem_commSet hC hα hx, rfl⟩)
    (isConj_of_mem_imageClass hC hs ⟨_, mem_DstarH_of_mem_commSet hC hα hy, rfl⟩)
    (not_commute_mk_of_mem_commSet hC hMZ hα hx hy hxy)
  have hKbar : ((QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))).comp
      (Subgroup.inclusion (tripleGroup_le_Halpha hC hα x y))).range =
      Subgroup.closure {z | IsConj s z ∧
        Commute z (QuotientGroup.mk' _ ⟨x, mem_Halpha_of_mem_commSet hC hα hx⟩) ∧
        Commute z (QuotientGroup.mk' _ ⟨y, mem_Halpha_of_mem_commSet hC hα hy⟩)} := by
    rw [range_mk_comp_inclusion_H hC hα, map_closure_commonPerpH hC hMZ hα hs hx hy hxy]
  obtain ⟨φ, hφs, hφk, hφa⟩ := exists_surjective_of_range_eq _ hHL
  obtain ⟨χ, hχs, hχk, hχa⟩ := exists_surjective_of_range_eq _ hKbar
  have hφks : Group.IsSolvable φ.ker := by
    rw [hφk]
    exact isSolvable_ker_mk_comp _ (Subgroup.inclusion_injective _) _
      CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have hχks : Group.IsSolvable χ.ker := by
    rw [hχk]
    exact isSolvable_ker_mk_comp _ (Subgroup.inclusion_injective _) _
      CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have hKZ := solvableRadical_eq_bot_of_isSymplecticTransvection hcenK (by omega) hf hSpK
  obtain ⟨Ψ, hΨ⟩ := exists_mulEquiv_of_surjective hφs hφks hχs hχks hKZ
  refine ⟨⟨Ψ ⟨t, ht⟩, ?_, isSymplecticTransvection_map Ψ hSpK⟩, ?_⟩
  · have hmem : t ∈ QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) ''
        commonPerpH hC x y := by
      rw [image_commonPerpH hC hMZ hα hs hx hy hxy]
      exact ⟨hts, htu, htw⟩
    obtain ⟨w, hw, hwt⟩ := hmem
    let k₀ : tripleGroup D x y hC.d := ⟨(w : G), Subgroup.subset_closure hw⟩
    have hχk₀ : χ k₀ = ⟨t, ht⟩ := Subtype.ext (by rw [hχa]; exact hwt)
    rw [← hχk₀, hΨ]
    refine ⟨φ k₀, ?_, rfl⟩
    rw [mem_DstarH_iff, hφa]
    show _ ∈ DalphaStar (barSet Ω) hCL.alpha
    rw [hDal]
    exact ⟨Subgroup.inclusion (tripleGroup_le_closure hΔΩ) k₀, hw, rfl⟩
  · have hKc : CFSG.solvableRadical (tripleGroup D x y hC.d) ≤
        Subgroup.center (tripleGroup D x y hC.d) := by
      refine (solvableRadical_le_ker hχs hKZ).trans ?_
      rw [hχk]
      exact ker_mk_comp_le_center _ (Subgroup.inclusion_injective _) _ hMZ
    exact solvableRadical_le_center_of_surjective hφs hφks hKc

omit [Finite G] in
theorem closure_le_centralizer {Ω : Set G} {x y : G} (hΩ : Ω ⊆ commSet D x ∩ commSet D y) :
    Subgroup.closure Ω ≤ Subgroup.centralizer {x} := by
  rw [Subgroup.closure_le]
  intro z hz
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hΩ hz).1.2.1.eq

theorem card_quotient_closure_lt {Ω : Set G} {x y : G} (hΩ : Ω ⊆ commSet D x ∩ commSet D y)
    (hxy : ¬ Commute x y) :
    Nat.card (Subgroup.closure Ω ⧸ CFSG.solvableRadical (Subgroup.closure Ω)) < Nat.card G := by
  have hyc : y ∉ Subgroup.centralizer {x} := fun h =>
    hxy (show Commute y x from Subgroup.mem_centralizer_singleton_iff.mp h).symm
  have hlt : Subgroup.closure Ω < ⊤ :=
    lt_of_le_of_lt (closure_le_centralizer hΩ)
      (lt_top_iff_ne_top.mpr fun h => hyc (by rw [h]; exact Subgroup.mem_top y))
  calc Nat.card (Subgroup.closure Ω ⧸ CFSG.solvableRadical (Subgroup.closure Ω))
      ≤ Nat.card (Subgroup.closure Ω) := Nat.le_of_dvd Nat.card_pos
        (Subgroup.card_quotient_dvd_card _)
    _ < Nat.card (⊤ : Subgroup G) := Subgroup.card_lt_of_lt hlt
    _ = Nat.card G := Subgroup.card_top

theorem exists_isOrthReflection_barSet (hIH : Theorem4Below (Nat.card G))
    (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y)
    {Ω : Set G} (hΩ : Ω ⊆ commSet D x ∩ commSet D y) (hdΩ : hC.d ∈ Ω)
    (hΔΩ : commSet D x ∩ commSet D y ∩ commSet D hC.d ⊆ Ω)
    (hcen : CFSG.solvableRadical (Subgroup.closure Ω) ≤ Subgroup.center (Subgroup.closure Ω))
    (hS : Setup (Subgroup.closure Ω) (inClosure Ω))
    (hns : ¬ Group.IsSolvable (Subgroup.closure Ω))
    (hCL : HypothesisC (barSet Ω))
    (hd : hCL.d = QuotientGroup.mk' _ ⟨hC.d, Subgroup.subset_closure hdΩ⟩) :
    ∃ t ∈ barSet Ω, IsOrthReflection
      (Subgroup.closure Ω ⧸ CFSG.solvableRadical (Subgroup.closure Ω)) n f t := by
  obtain ⟨⟨s', hs', hSp'⟩, hMZL⟩ :=
    hypothesisE_barSet hC hMZ hα hs hn hf hSp hx hy hxy hΩ hdΩ hΔΩ hcen hS hns hCL hd
  have hZL := center_Hbar_eq_bot hCL
  have hE : HypothesisE hCL := Or.inl ⟨s', hs', n - 2, f, by omega, hf, Or.inl hSp'⟩
  have hO4 : ¬ ∃ s₀ ∈ imageClass hCL, ∃ f₀ : ℕ, 2 ≤ f₀ ∧ IsOrthReflection
      (Halpha (barSet Ω) hCL.alpha ⧸
        CFSG.solvableRadical (Halpha (barSet Ω) hCL.alpha)) 4 f₀ s₀ := by
    rintro ⟨s₀, -, f₀, -, h₀⟩
    refine notMem_commutator_of_isOrthReflection hZL h₀ ?_
    rw [(isPerfect_of_isSymplecticTransvection hZL hf hSp').commutator_eq_top]
    exact Subgroup.mem_top s₀
  have hcls := imageClass_isClass hCL
  rcases hIH _ _ hCL (card_quotient_closure_lt hΩ hxy) rad_quotient_solvableRadical hE hMZL
      hO4 with ⟨s₁, -, m, f₁, hm, hf₁, hSp₁, t, ht, hO⟩ | ⟨k, ε, π, hk, h5, -⟩ |
      ⟨f₂, n₂, -, hn₂, ⟨e⟩, -⟩
  · obtain ⟨rfl, rfl⟩ := isSymplecticTransvection_rigid hf₁ hf hm (by omega) hSp₁ hSp'
    refine ⟨t, ht, ?_⟩
    have h2 : n - 2 + 2 = n := by omega
    rwa [h2] at hO
  · exact absurd h5 (not_isFiveReflectionModel_of_isSymplecticTransvection hcls hZL hs' hf hSp' hk)
  · exact absurd ⟨e⟩
      (not_nonempty_mulEquiv_l2Wreath_of_isSymplecticTransvection hZL hf hSp' (by omega))

theorem isOrthReflection_of_centerQuotient {X Y : Type} [Group X] [Group Y]
    (ε : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y) {s : X} {s' : Y}
    (hε : ε (QuotientGroup.mk s) = QuotientGroup.mk s') {m f : ℕ}
    (h : IsOrthReflection Y m f s') : IsOrthReflection X m f s := by
  rcases h with ⟨k, hk, hmk, F, hF, hFin, hcard, e', hr⟩ |
      ⟨k, hk, hmk, F, hF, hFin, hcard, b, c, hbc, e', hr⟩
  · refine Or.inl ⟨k, hk, hmk, F, hF, hFin, hcard, ε.trans e', ?_⟩
    rwa [MulEquiv.trans_apply, hε]
  · refine Or.inr ⟨k, hk, hmk, F, hF, hFin, hcard, b, c, hbc, ε.trans e', ?_⟩
    rwa [MulEquiv.trans_apply, hε]

theorem isOrthReflection_of_quotient_solvableRadical {X : Type} [Group X] [Finite X]
    (hcen : CFSG.solvableRadical X ≤ Subgroup.center X) {t : X} {m f : ℕ}
    (h : IsOrthReflection (X ⧸ CFSG.solvableRadical X) m f (QuotientGroup.mk t)) :
    IsOrthReflection X m f t := by
  have hNZ : CFSG.solvableRadical X = Subgroup.center X :=
    le_antisymm hcen (CFSG.OddTranspositions.center_le_solvableRadical X)
  have hZ : Subgroup.center (X ⧸ CFSG.solvableRadical X) = ⊥ := by
    have h1 := CFSG.OddTranspositions.center_le_solvableRadical (X ⧸ CFSG.solvableRadical X)
    rwa [CFSG.SignalizerFunctorTheorem.Nonsolvable.solvableRadical_quotient, le_bot_iff] at h1
  refine isOrthReflection_of_centerQuotient ((QuotientGroup.quotientMulEquivOfEq hNZ.symm).trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm) ?_ h
  rw [MulEquiv.trans_apply, MulEquiv.symm_apply_eq]
  rfl

theorem isOrthReflection_closure_of_pivot (hIH : Theorem4Below (Nat.card G))
    (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y)
    {Ω : Set G} (hΩ : Ω ⊆ commSet D x ∩ commSet D y) (hdΩ : hC.d ∈ Ω)
    (hΔΩ : commSet D x ∩ commSet D y ∩ commSet D hC.d ⊆ Ω)
    (hcls : ∃ t : Subgroup.closure Ω, inClosure Ω = {g | IsConj t g})
    (hconn : ¬ CFSG.Timmesfeld.Connectivity.Disconnected (inClosure Ω))
    (hcen : CFSG.solvableRadical (Subgroup.closure Ω) ≤ Subgroup.center (Subgroup.closure Ω)) :
    ∃ t, ∃ ht : t ∈ Ω,
      IsOrthReflection (Subgroup.closure Ω) n f ⟨t, Subgroup.subset_closure ht⟩ := by
  have hΩD : Ω ⊆ D := fun z hz => (hΩ hz).1.1
  have hS := setup_inClosure hC.setup.oddT hΩD hcls
  have hns := not_isSolvable_closure_of_subset hC hMZ hα hs hn hf hSp hx hy hxy hΔΩ
  obtain ⟨hCL, hd⟩ := exists_hypothesisC_inClosure hC.setup.oddT hΩD hdΩ hcls hconn hns
  obtain ⟨_, ⟨t, ht, rfl⟩, hO⟩ := exists_isOrthReflection_barSet hIH hC hMZ hα hs hn hf hSp hx hy
    hxy hΩ hdΩ hΔΩ hcen hS hns hCL hd
  exact ⟨(t : G), ht, isOrthReflection_of_quotient_solvableRadical hcen hO⟩

end CFSG.OddTranspositions.PartThree

end

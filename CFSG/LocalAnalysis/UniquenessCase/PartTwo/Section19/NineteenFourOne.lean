module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourAt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.VZeroSmall17
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.MSubBasic
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1A5
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatSporW
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
public import CFSG.GroupTheory.SteinbergCBFTFactorization
public import CFSG.Holt.General.Basic
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Main
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedA7
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpLeaf
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpReduce
public import CFSG.LocalAnalysis.ComponentClassification.TBLitIntrinsicTypes
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.LocalAnalysis.StronglyEmbedded.PSubgroups
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.NineThreeSylData
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveFourteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSixteen
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22q
public import CFSG.LocalAnalysis.UniquenessCase.UC6K47d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S9
public import CFSG.LocalAnalysis.WeakClosure81.EightThreeA
public import CFSG.LocalAnalysis.WeakClosure81.SevenFiveTwo
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.W19Min
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E2TwoProofDefs
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11SecBNPCaseS
public import CFSG.Quasithin.Vol2.Ch11SecBTCIso
public import CFSG.Quasithin.Vol2.Ch11StatementsE
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.SignalizerFunctorTheorem.Glauberman.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.HeldB.AllFixed
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s19c_inf_ne_bot_of_mQuot_le_two {V U : Subgroup G} (hV : IsPGroup 2 V)
    (hm : 4 < mSub V) (h : E3.mQuot V U ≤ 2) : V ⊓ U ≠ ⊥ := by
  intro hbot
  have hcardV : Nat.card ↥V = 2 ^ mSub V := card_eq_two_pow_mSub hV
  have hmul := E3.card_eq_two_pow_mul hV (inf_le_left : V ⊓ U ≤ V)
  have hmq : E3.mQuot V (V ⊓ U) = E3.mQuot V U := by
    rw [E3.mQuot, E3.mQuot, inf_comm, Subgroup.inf_relIndex_right]
  rw [hmq] at hmul
  have hpow : 2 ^ E3.mQuot V U ≤ 4 := by
    calc 2 ^ E3.mQuot V U ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h
      _ = 4 := by norm_num
  have hbig : 32 ≤ Nat.card ↥V := by
    rw [hcardV]
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ mSub V := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h8 : 8 ≤ Nat.card ↥(V ⊓ U) := by
    by_contra hlt
    have hle : Nat.card ↥(V ⊓ U) ≤ 7 := by omega
    have hle' : 2 ^ E3.mQuot V U * Nat.card ↥(V ⊓ U) ≤ 4 * 7 :=
      Nat.mul_le_mul hpow hle
    omega
  rw [hbot, Subgroup.card_bot] at h8
  omega

theorem mQuot_ne_two_19 (h71 : W3Lem71 G) (D : Data G)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (h2 : R19_2At D V₀ V p L K h) (h3 : R19_3At D V₀ V p L K h) {g : G} (hgM : g ∉ D.M)
    (hU : V₀ ⊓ conjSubgroup D.M g ≠ ⊥) (hV : ¬ V₀ ≤ conjSubgroup D.M g)
    (hVg : ¬ conjSubgroup V₀ g ≤ D.M) : E3.mQuot V₀ (conjSubgroup D.M g) ≠ 2 := by
  classical
  by_contra hmq2
  have hV0ne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.hyp.big
  have hV0elem : IsElemAbelian 2 V₀ := h.hyp.hyp125.pairFacts.elemAbelian₀
  have hV0p : IsPGroup 2 V₀ := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hV0elem
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V₀ := S17.hyp125_isTI h.hyp.hyp125 hV0ne
  have hInCalV : InCalV D.M V₀ := S17.hyp125_inCalV h.hyp.hyp125 hV0ne
  have hN : normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hInCalV
  have hV0card : 2 < Nat.card V₀ := by
    rw [card_eq_two_pow_mSub hV0p]
    calc 2 = 2 ^ 1 := by norm_num
      _ < 2 ^ mSub V₀ := Nat.pow_lt_pow_right (by norm_num) h.hyp.big
  have hHyp7 : Hyp7 V₀ := ⟨hV0elem, hV0card, hTI⟩
  have hgN : g ∉ normalizer (V₀ : Set G) := by
    rw [hN]
    exact hgM
  have hNormConj : Subgroup.normalizer (conjSubgroup V₀ g : Set G) =
      conjSubgroup D.M g := by
    rw [← E3.conjSubgroup_normalizer V₀ g, hN]
  let X : Subgroup G := V₀ ⊔ conjSubgroup V₀ g
  have hV0X : V₀ ≤ X := le_sup_left
  let U : Subgroup G := V₀ ⊓ Subgroup.normalizer (conjSubgroup V₀ g : Set G)
  let B : Subgroup G := conjSubgroup V₀ g ⊓ Subgroup.normalizer (V₀ : Set G)
  have hmqU : E3.mQuot V₀ U = 2 := by
    change E3.mQuot V₀ (V₀ ⊓ Subgroup.normalizer (conjSubgroup V₀ g : Set G)) = 2
    rw [hNormConj, inf_comm, E3.mQuot, Subgroup.inf_relIndex_right]
    exact hmq2
  have hmqU' : E3.mQuot V₀ (V₀ ⊓ Subgroup.normalizer (conjSubgroup V₀ g : Set G)) = 2 :=
    hmqU
  have hUbot : U ≠ ⊥ := by
    change V₀ ⊓ Subgroup.normalizer (conjSubgroup V₀ g : Set G) ≠ ⊥
    rw [hNormConj]
    exact hU
  have hUle : U ≤ conjSubgroup D.M g := by
    change V₀ ⊓ Subgroup.normalizer (conjSubgroup V₀ g : Set G) ≤ conjSubgroup D.M g
    rw [hNormConj]
    exact inf_le_right
  have hUneA : U ≠ V₀ := fun hEq => hV (hEq ▸ hUle)
  have hcomm : ⁅V₀, conjSubgroup V₀ g⁆ ≠ ⊥ := by
    intro hbot
    apply hV
    have hle : V₀ ≤ Subgroup.normalizer (conjSubgroup V₀ g : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot).trans
        (Subgroup.centralizer_le_normalizer _)
    rwa [hNormConj] at hle
  obtain ⟨hO2X, hUBbot, hcommUB, hshape, -, -⟩ :=
    h71 V₀ g hHyp7 hgN hUbot hUneA hcomm
  have hO2X' : pCoreOf 2 X = U ⊔ B := hO2X
  have hUBbot' : U ⊓ B = ⊥ := hUBbot
  have hcommUB' : ⁅U, B⁆ = ⊥ := hcommUB
  obtain ⟨Z, instZ, φ, hφsurj, hφker, hP⟩ := hshape
  have hZA5 : Nonempty (Z ≃* alternatingGroup (Fin 5)) := by
    rcases hP with ⟨n, hL2, hn⟩ | ⟨n, hSz, hn⟩ | ⟨m, hodd, ⟨eD⟩, hn⟩
    · have hn2 : n = 2 := by rw [← hn]; exact hmqU'
      rw [hn2] at hL2
      exact CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model Z hL2
    · have hn2 : n = 2 := by rw [← hn]; exact hmqU'
      rw [hn2] at hSz
      exfalso
      have hSuz : CFSG.Blueprint.SuzukiModel Z 2 2 := by
        have h' := hSz
        unfold CFSG.LocalAnalysis.UniquenessCase.UC22.IsSz CFSG.Blueprint.LieModel at h'
        rcases h' with ⟨hcl, -⟩ | ⟨-, hch, -⟩ | ⟨-, hrt, -⟩ | ⟨-, -, hS⟩
        · exact absurd hcl (by decide)
        · exact absurd hch (by decide)
        · exact absurd hrt (by decide)
        · exact hS
      obtain ⟨-, a, ha, K, hK, hKf, hf, hcard, -⟩ := hSuz
      omega
    · omega
  obtain ⟨eZA⟩ := hZA5
  let q : ↥X →* alternatingGroup (Fin 5) := eZA.toMonoidHom.comp φ
  have hqsurj : Function.Surjective q := eZA.surjective.comp hφsurj
  have hqkerO2 : q.ker = (pCoreOf 2 X).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, hφker, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hUA : U ≤ V₀ := inf_le_left
  have hUBle : B ≤ conjSubgroup V₀ g := inf_le_left
  have hBleN : B ≤ Subgroup.normalizer (V₀ : Set G) := inf_le_right
  have hcomm_el : ∀ u ∈ U, ∀ b ∈ B, u * b = b * u := by
    intro u hu b hb
    have hc := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommUB') hu
    exact ((Subgroup.mem_centralizer_iff.mp hc) b hb).symm
  have hdisj : V₀ ⊓ conjSubgroup V₀ g = ⊥ := by
    have hTIy : V₀ ⊓ conjSubgroup V₀ g = ⊥ ∨ V₀ ⊓ conjSubgroup V₀ g = V₀ := by
      have heq : CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ V₀ = conjSubgroup V₀ g := rfl
      have h' := hTI g⁻¹
      rwa [heq] at h'
    rcases hTIy with hbot | htop
    · exact hbot
    · exfalso
      have hAle : V₀ ≤ conjSubgroup V₀ g := by
        have hle : V₀ ⊓ conjSubgroup V₀ g ≤ conjSubgroup V₀ g := inf_le_right
        rwa [htop] at hle
      have hAeq : V₀ = conjSubgroup V₀ g :=
        Subgroup.eq_of_le_of_card_ge hAle (by rw [E3.card_conjSubgroup])
      exact hgN (conjSubgroup_eq_iff_mem_normalizer.mp hAeq.symm)
  have hABbot : V₀ ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxV, hxB⟩ := Subgroup.mem_inf.mp hx
    have hxAg : x ∈ conjSubgroup V₀ g := hxB.1
    have hxU : x ∈ U := by
      change x ∈ V₀ ⊓ Subgroup.normalizer (conjSubgroup V₀ g : Set G)
      exact Subgroup.mem_inf.mpr ⟨hxV, Subgroup.le_normalizer hxAg⟩
    have hxUB : x ∈ U ⊓ B := Subgroup.mem_inf.mpr ⟨hxU, hxB⟩
    rwa [hUBbot', Subgroup.mem_bot] at hxUB
  have hAinter : V₀ ⊓ pCoreOf 2 X = U := by
    rw [hO2X']
    refine le_antisymm ?_ (le_inf hUA le_sup_left)
    intro x hx
    obtain ⟨hxV, hxUB⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨u, huU, b, hbB, rfl⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm_el hxUB
    have hbV : b ∈ V₀ := by
      have hb_eq : b = u⁻¹ * (u * b) := by group
      rw [hb_eq]
      exact V₀.mul_mem (V₀.inv_mem (hUA huU)) hxV
    have hbBot : b ∈ V₀ ⊓ conjSubgroup V₀ g := ⟨hbV, hUBle hbB⟩
    rw [hdisj, Subgroup.mem_bot] at hbBot
    subst hbBot
    simpa using huU
  have hcardAB : Nat.card ↥(V₀ ⊔ B) = Nat.card ↥V₀ * Nat.card ↥B := by
    have h' := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
      (A := B) (B := V₀) hBleN
    rw [sup_comm, inf_comm, hABbot, Subgroup.card_bot, mul_one,
      mul_comm (Nat.card ↥B) (Nat.card ↥V₀)] at h'
    exact h'
  have hAO2card : Nat.card ↥(V₀ ⊔ pCoreOf 2 X) = Nat.card ↥V₀ * Nat.card ↥B := by
    rw [hO2X', ← sup_assoc, sup_eq_left.mpr hUA]
    exact hcardAB
  have hBne : B ≠ conjSubgroup V₀ g := by
    intro hBeq
    apply hVg
    rw [← hBeq]
    exact inf_le_right.trans (le_of_eq hN)
  have hBlt : B < conjSubgroup V₀ g := lt_of_le_of_ne hUBle hBne
  have hBltcard : Nat.card ↥B < Nat.card ↥V₀ := by
    have h' := Subgroup.card_lt_of_lt hBlt
    rwa [E3.card_conjSubgroup] at h'
  let fA : ↥V₀ →* ↥(alternatingGroup (Fin 5)) := q.comp (Subgroup.inclusion hV0X)
  have hfAker : fA.ker = U.subgroupOf V₀ := by
    ext a
    change q (Subgroup.inclusion hV0X a) = 1 ↔ (a : G) ∈ U
    constructor
    · intro hq1
      have hq : (a : G) ∈ pCoreOf 2 X := by
        have hmem : Subgroup.inclusion hV0X a ∈ q.ker := hq1
        rw [hqkerO2, Subgroup.mem_subgroupOf] at hmem
        exact hmem
      rw [← hAinter]
      exact ⟨a.2, hq⟩
    · intro hUa
      have hq : (a : G) ∈ pCoreOf 2 X := by
        have hUleO2 : U ≤ pCoreOf 2 X := by
          rw [← hAinter]
          exact inf_le_right
        exact hUleO2 hUa
      have hmem : Subgroup.inclusion hV0X a ∈ q.ker := by
        rw [hqkerO2, Subgroup.mem_subgroupOf]
        exact hq
      exact hmem
  let P : Subgroup ↥(alternatingGroup (Fin 5)) := (V₀.subgroupOf X).map q
  have hfArange : fA.range = P := by
    show (q.comp (Subgroup.inclusion hV0X)).range = P
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, by apply Subtype.ext; rfl⟩
  have hcardker : Nat.card ↥(fA.ker) = Nat.card ↥U := by
    rw [hfAker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUA).toEquiv
  have hcardrange : Nat.card ↥(fA.range) = Nat.card ↥P := by
    rw [hfArange]
  have hcardV1 : Nat.card ↥V₀ = 4 * Nat.card ↥U := by
    have h' := E3.card_eq_two_pow_mul hV0p hUA
    rw [hmqU] at h'
    norm_num at h'
    exact h'
  have hcardV2 : Nat.card ↥V₀ = Nat.card ↥U * Nat.card ↥P := by
    have h' := CFSG.ABGLocalTools.card_eq_card_ker_mul_of_surjective
      (f := fA.rangeRestrict) fA.rangeRestrict_surjective
    rw [MonoidHom.ker_rangeRestrict, hcardker, hcardrange] at h'
    exact h'
  have hPcard : Nat.card ↥P = 4 := by
    have h1 : 4 * Nat.card ↥U = Nat.card ↥P * Nat.card ↥U := by
      rw [mul_comm (Nat.card ↥P) (Nat.card ↥U), ← hcardV2, hcardV1]
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).symm
  obtain ⟨z, hzN, hzord⟩ := CFSG.Quasithin.H13.A5Syl.exists_orderOf_three P hPcard
  obtain ⟨y, hyq⟩ := hqsurj z
  have hzN_inv : z⁻¹ ∈ Subgroup.normalizer (P : Set ↥(alternatingGroup (Fin 5))) :=
    Subgroup.inv_mem _ hzN
  have hAy_le : conjSubgroup V₀ y ≤ V₀ ⊔ pCoreOf 2 X := by
    intro w hw
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hw
    have haX : a ∈ X := hV0X ha
    let ax : ↥X := ⟨a, haX⟩
    have hax : ax ∈ V₀.subgroupOf X := Subgroup.mem_subgroupOf.mpr ha
    have hqa : q ax ∈ P := Subgroup.mem_map_of_mem q hax
    have hzn : z⁻¹ * q ax * z ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hzN_inv (q ax)).mp hqa
    obtain ⟨a', haX', ha'q⟩ := Subgroup.mem_map.mp hzn
    have ha'V : (a' : G) ∈ V₀ := Subgroup.mem_subgroupOf.mp haX'
    have hyconj_mem : (y : G)⁻¹ * a * (y : G) ∈ X :=
      X.mul_mem (X.mul_mem (X.inv_mem y.2) haX) y.2
    let yconj : ↥X := ⟨(y : G)⁻¹ * a * (y : G), hyconj_mem⟩
    have hyconj : q yconj = z⁻¹ * q ax * z := by
      have hyx : yconj = (y : ↥X)⁻¹ * ax * (y : ↥X) := Subtype.ext rfl
      rw [hyx, map_mul, map_mul, map_inv, hyq]
    have hprod1 : q (yconj * (Subgroup.inclusion hV0X
        ⟨(a' : G), ha'V⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv]
      change q yconj * (q ⟨(a' : G), hV0X ha'V⟩)⁻¹ = 1
      have ha'q' : q ⟨(a' : G), hV0X ha'V⟩ = z⁻¹ * q ax * z := ha'q
      rw [hyconj, ha'q', mul_inv_cancel]
    have hk : ((y : G)⁻¹ * a * (y : G)) * (a' : G)⁻¹ ∈ pCoreOf 2 X := by
      have hmem : yconj * (Subgroup.inclusion hV0X
          ⟨(a' : G), ha'V⟩)⁻¹ ∈ q.ker := hprod1
      rw [hqkerO2, Subgroup.mem_subgroupOf] at hmem
      exact hmem
    change (MulAut.conj (y : G)⁻¹) a ∈ V₀ ⊔ pCoreOf 2 X
    have heq : (MulAut.conj (y : G)⁻¹) a =
        (((MulAut.conj (y : G)⁻¹) a) * (a' : G)⁻¹) * (a' : G) := by
      simp only [MulAut.conj_apply, inv_inv]
      group
    rw [heq]
    have hk' : (MulAut.conj (y : G)⁻¹) a * (a' : G)⁻¹ ∈ pCoreOf 2 X := by
      simpa only [MulAut.conj_apply, inv_inv] using hk
    exact (V₀ ⊔ pCoreOf 2 X).mul_mem
      ((le_sup_right : pCoreOf 2 X ≤ V₀ ⊔ pCoreOf 2 X) hk')
      ((le_sup_left : V₀ ≤ V₀ ⊔ pCoreOf 2 X) ha'V)
  have hprod_sub : ((V₀ : Set G) * (conjSubgroup V₀ y : Set G)) ⊆
      ((V₀ ⊔ pCoreOf 2 X : Subgroup G) : Set G) := by
    rintro x ⟨a, ha, c, hc, rfl⟩
    exact (V₀ ⊔ pCoreOf 2 X).mul_mem
      ((le_sup_left : V₀ ≤ V₀ ⊔ pCoreOf 2 X) ha) (hAy_le hc)
  have hprod_card_le : Nat.card ↥((V₀ : Set G) * (conjSubgroup V₀ y : Set G)) ≤
      Nat.card ↥(V₀ ⊔ pCoreOf 2 X) := by
    simpa only [SetLike.coe_sort_coe] using
      Nat.card_mono (Set.toFinite ((V₀ ⊔ pCoreOf 2 X : Subgroup G) : Set G)) hprod_sub
  have hprod_formula :=
    CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf V₀ (conjSubgroup V₀ y)
  have hAyeq : Nat.card (conjSubgroup V₀ y) = Nat.card V₀ := E3.card_conjSubgroup V₀ y
  rw [hAyeq] at hprod_formula
  have hAle : Nat.card V₀ ≤ Nat.card B * Nat.card ↥(V₀ ⊓ conjSubgroup V₀ y) := by
    have h1 : Nat.card V₀ * Nat.card V₀ ≤
        Nat.card ↥(V₀ ⊔ pCoreOf 2 X) * Nat.card ↥(V₀ ⊓ conjSubgroup V₀ y) := by
      rw [← hprod_formula]
      exact Nat.mul_le_mul_right _ hprod_card_le
    rw [hAO2card] at h1
    have h2 : Nat.card V₀ * Nat.card V₀ ≤
        Nat.card V₀ * (Nat.card B * Nat.card ↥(V₀ ⊓ conjSubgroup V₀ y)) := by
      calc Nat.card V₀ * Nat.card V₀
          ≤ (Nat.card V₀ * Nat.card B) * Nat.card ↥(V₀ ⊓ conjSubgroup V₀ y) := h1
        _ = Nat.card V₀ * (Nat.card B * Nat.card ↥(V₀ ⊓ conjSubgroup V₀ y)) := by
              rw [mul_assoc]
    exact Nat.le_of_mul_le_mul_left h2 Nat.card_pos
  have hInter_gt_one : 1 < Nat.card ↥(V₀ ⊓ conjSubgroup V₀ y) := by
    by_contra h'
    have hle1 : Nat.card ↥(V₀ ⊓ conjSubgroup V₀ y) ≤ 1 := by omega
    have hmulB : Nat.card B * Nat.card ↥(V₀ ⊓ conjSubgroup V₀ y) ≤ Nat.card B * 1 :=
      Nat.mul_le_mul_left _ hle1
    have hBlt' : Nat.card B < Nat.card V₀ := hBltcard
    omega
  have hInter_ne_bot : V₀ ⊓ conjSubgroup V₀ y ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hInter_gt_one
    omega
  have hTIy : V₀ ⊓ conjSubgroup V₀ y = ⊥ ∨ V₀ ⊓ conjSubgroup V₀ y = V₀ := by
    have heq : CFSG.CGT.Timmesfeld75.conjSubgroup (y : G)⁻¹ V₀ = conjSubgroup V₀ y := rfl
    have h' := hTI (y : G)⁻¹
    rwa [heq] at h'
  have hAyeqA : conjSubgroup V₀ y = V₀ := by
    rcases hTIy with hbot | htop
    · exact absurd hbot hInter_ne_bot
    · have hAle' : V₀ ≤ conjSubgroup V₀ y := by
        have hle : V₀ ⊓ conjSubgroup V₀ y ≤ conjSubgroup V₀ y := inf_le_right
        rwa [htop] at hle
      exact (Subgroup.eq_of_le_of_card_ge hAle' (by rw [E3.card_conjSubgroup])).symm
  have hyN : (y : G) ∈ Subgroup.normalizer (V₀ : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp hAyeqA
  have hyM : (y : G) ∈ D.M := by
    rw [← hN]
    exact hyN
  have h3ord : 3 ∣ orderOf y := by
    have hz3 : orderOf (q y) = 3 := by rw [hyq]; exact hzord
    have hdvd : orderOf (q y) ∣ orderOf y :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, pow_orderOf_eq_one, map_one])
    rwa [hz3] at hdvd
  let y' : ↥X := y ^ (orderOf y / 3)
  have hy'ordX : orderOf y' = 3 := by
    show orderOf (y ^ (orderOf y / 3)) = 3
    exact orderOf_pow_orderOf_div (orderOf_pos y).ne' h3ord
  have hy'ordG : orderOf (y' : G) = 3 := by
    rw [Subgroup.orderOf_coe, hy'ordX]
  have hy'M : (y' : G) ∈ D.M := by
    have hpow : (y' : G) = (y : G) ^ (orderOf y / 3) := by simp [y']
    rw [hpow]
    exact D.M.pow_mem hyM _
  have hy'Opp : (y' : G) ∈ Opp 3 D.M := by
    rw [Opp]
    exact Subgroup.subset_closure ⟨hy'M, ⟨1, by rw [pow_one]; exact hy'ordG⟩⟩
  have h2' : Opp 3 D.M = L ⊔ K := h2
  have h3' : ⁅L ⊔ K, V₀⁆ = ⊥ := h3
  have hy'LK : (y' : G) ∈ L ⊔ K := by
    rw [h2'] at hy'Opp
    exact hy'Opp
  have hy'C : (y' : G) ∈ centralizer (V₀ : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3') hy'LK
  have hnotle : ¬ V₀ ≤ U := fun hle => hUneA (le_antisymm hUA hle)
  obtain ⟨v, hvV₀, hvU⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hvX : v ∈ X := hV0X hvV₀
  let vX : ↥X := ⟨v, hvX⟩
  have hvq_ne : q vX ≠ 1 := by
    intro hq1
    have hq : (v : G) ∈ pCoreOf 2 X := by
      have hmem : vX ∈ q.ker := hq1
      rw [hqkerO2, Subgroup.mem_subgroupOf] at hmem
      exact hmem
    have hvU' : v ∈ U := by
      rw [← hAinter]
      exact Subgroup.mem_inf.mpr ⟨hvV₀, hq⟩
    exact hvU hvU'
  have hvq2 : orderOf (q vX) = 2 := by
    have hpow : (q vX) ^ 2 = 1 := by
      rw [← map_pow, show vX ^ 2 = 1 by
        apply Subtype.ext
        simpa [vX] using hV0elem.2 v hvV₀, map_one]
    exact orderOf_eq_prime (p := 2) (hp := ⟨Nat.prime_two⟩) hpow hvq_ne
  have hy'q_ne : q y' ≠ 1 := by
    intro hq1
    have hker : (y' : G) ∈ pCoreOf 2 X := by
      have hmem : y' ∈ q.ker := hq1
      rw [hqkerO2, Subgroup.mem_subgroupOf] at hmem
      exact hmem
    have h2grp : IsPGroup 2 ↥(pCoreOf 2 X) :=
      IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) X.subtype
    have h3dvd : 3 ∣ Nat.card ↥(pCoreOf 2 X) := by
      have h' := Subgroup.orderOf_dvd_natCard (pCoreOf 2 X) hker
      rwa [hy'ordG] at h'
    obtain ⟨n, hn⟩ := h2grp ⟨(y' : G), hker⟩
    have hdvd : orderOf (⟨(y' : G), hker⟩ : ↥(pCoreOf 2 X)) ∣ 2 ^ n :=
      orderOf_dvd_of_pow_eq_one hn
    have hdvd' : orderOf (y' : G) ∣ 2 ^ n := by
      have h1 : orderOf (⟨(y' : G), hker⟩ : ↥(pCoreOf 2 X)) = orderOf (y' : G) :=
        (Subgroup.orderOf_coe (⟨(y' : G), hker⟩ : ↥(pCoreOf 2 X))).symm
      rwa [h1] at hdvd
    rw [hy'ordG] at hdvd'
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd'
    norm_num at h32
  have hy'q3 : orderOf (q y') = 3 := by
    have hpow : (q y') ^ 3 = 1 := by
      rw [← map_pow, show y' ^ 3 = 1 by rw [← hy'ordX, pow_orderOf_eq_one], map_one]
    exact orderOf_eq_prime (p := 3) (hp := ⟨Nat.prime_three⟩) hpow hy'q_ne
  have hy'v : (y' : G) * v = v * (y' : G) := by
    have h' := Subgroup.mem_centralizer_iff.mp hy'C v hvV₀
    exact h'.symm
  have hcommq : Commute (q y') (q vX) := by
    show q y' * q vX = q vX * q y'
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hy'v
  have h6 : orderOf (q y' * q vX) = 6 := by
    have hcop : (orderOf (q y')).Coprime (orderOf (q vX)) := by
      rw [hy'q3, hvq2]
      decide
    have h' := Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcommq hcop
    rwa [hy'q3, hvq2] at h'
  exact CFSG.ComponentClassification.SolMax.FiveCat.Spor.alt_five_orderOf_ne_six _ h6

theorem inCalO_one_of_inCalO_two_19 (h71 : W3Lem71 G)
    (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (h2 : R19_2At D V₀ V p L K h) (h3 : R19_3At D V₀ V p L K h) (hm : 4 < mSub V₀) {g : G}
    (hg : InCalO 2 D.M ⊥ V₀ g) : InCalO 1 D.M ⊥ V₀ g := by
  obtain ⟨hF2, hD2⟩ := hg
  obtain ⟨hVg, hmq2, -⟩ := hF2
  obtain ⟨hV, hmqD2, -⟩ := hD2
  have hV0ne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.hyp.big
  have hV0elem : IsElemAbelian 2 V₀ := h.hyp.hyp125.pairFacts.elemAbelian₀
  have hV0p : IsPGroup 2 V₀ := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hV0elem
  have hInCalV : InCalV D.M V₀ := S17.hyp125_inCalV h.hyp.hyp125 hV0ne
  have hN : normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hInCalV
  have hgM : g ∉ D.M := by
    intro hgD
    apply hVg
    have hge : g ∈ Subgroup.normalizer (V₀ : Set G) := by rwa [hN]
    rw [conjSubgroup_eq_iff_mem_normalizer.mpr hge]
    exact hInCalV.2.1
  have hU : V₀ ⊓ conjSubgroup D.M g ≠ ⊥ :=
    s19c_inf_ne_bot_of_mQuot_le_two hV0p hm hmq2
  have hmq1 : E3.mQuot V₀ (conjSubgroup D.M g) ≤ 1 := by
    have hne := mQuot_ne_two_19 h71 D h h2 h3 hgM hU hV hVg
    omega
  have hgM' : g⁻¹ ∉ D.M := by
    intro hginv
    exact hgM (by simpa using D.M.inv_mem hginv)
  have hmeq : E3.mQuot (conjSubgroup V₀ g) D.M =
      E3.mQuot V₀ (conjSubgroup D.M g⁻¹) := by
    have h' := E3.mQuot_conjSubgroup V₀ (conjSubgroup D.M g⁻¹) g
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h'
    exact h'
  have hmqD2' : E3.mQuot V₀ (conjSubgroup D.M g⁻¹) ≤ 2 := by
    rw [← hmeq]
    exact hmqD2
  have hU' : V₀ ⊓ conjSubgroup D.M g⁻¹ ≠ ⊥ :=
    s19c_inf_ne_bot_of_mQuot_le_two hV0p hm hmqD2'
  have hV' : ¬ V₀ ≤ conjSubgroup D.M g⁻¹ := by
    intro hle
    exact hVg (by simpa using
      (E3.le_conjSubgroup_iff_inv_le (A := V₀) (B := D.M) (g⁻¹)).1 hle)
  have hVg' : ¬ conjSubgroup V₀ g⁻¹ ≤ D.M := by
    intro hle
    exact hV (by simpa using
      (E3.conjSubgroup_le_iff_le_inv (A := V₀) (B := D.M) (g⁻¹)).1 hle)
  have hmqD1 : E3.mQuot (conjSubgroup V₀ g) D.M ≤ 1 := by
    rw [hmeq]
    have hne := mQuot_ne_two_19 h71 D h h2 h3 hgM' hU' hV' hVg'
    omega
  exact ⟨⟨hVg, hmq1, by simp⟩, ⟨hV, hmqD1, by simp⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

module

public import CFSG.GroupTheory.CoprimeCentralizerTransport
public import CFSG.GroupTheory.PRankLeOfSylowLe
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AInner
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8
public import CFSG.LieType.Automorphisms.SteinbergBLCompleteIndexTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviSmall
public import CFSG.Quasithin.SteinbergBIEvenLinearThreeThreeSylowAction
public import CFSG.RankThree.PartOne.F106.ZeroStar
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsTwin
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanKFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPFF2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH7
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPQ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPQ3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPR
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
public import CFSG.GroupTheory.CentralizerQuotientCard
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderE6Order
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOuterSylowGlue
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldRoot
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneHilbertNinety
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlanePureFieldMatrix
public import CFSG.LocalAnalysis.GL83PartI.I_7_13
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Extremal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Common
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.StrongMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma32
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviGeneric
public import CFSG.LocalAnalysis.RankThreeUC.Section12.Context
public import CFSG.Quasithin.Background.C1PackC129Case
public import CFSG.Quasithin.Background.G25Seven
public import CFSG.Quasithin.EmptyFaithful.R3cBlocks
public import CFSG.Quasithin.EmptyFaithful.S14113bMain
public import CFSG.Quasithin.EmptyFaithful.S146zMComp
public import CFSG.Quasithin.EmptyFaithful.S146zQLists
public import CFSG.Quasithin.EmptyFaithful.SBc15R3G
public import CFSG.Quasithin.EmptyFaithful.SBc16SComp
public import CFSG.Quasithin.EmptyFaithful.SBc16SWr
public import CFSG.Quasithin.EmptyFaithful.SBc17Out5L
public import CFSG.Quasithin.H13.L32NThm1443
public import CFSG.Quasithin.SteinbergBICommonNormalizerTools
public import CFSG.Quasithin.SteinbergBITwoThreeSL2
public import CFSG.Quasithin.SteinbergOuterPrimeControl
public import CFSG.RankThree.PartOne.KF.F128Count
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartTwo.Sec16.Item1621StepsProofPara
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldExc
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem rank_three_le
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M) :
    CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3 := by
  have hNP : Subgroup.normalizer (P : Set G) ≤ D.M :=
    normalizer_sylow_le_M_of_onan c hON hP hNZ
  have hPtop : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ :=
    isSylowOf_top_of_normalizer_le hP hNP
  have h := CFSG.pRank_le_of_isSylowOf_le Nat.prime_three hPtop.le hPtop hP.le
  rwa [c.pRank_three_M] at h

theorem centerDescend_of_inner {A : Type*} [Group A] (β : MulAut A) {t : A}
    (ht : MulAut.conj t = β) :
    CFSG.RankThree.PartTwo.KFacts.centerDescend A β =
      MulAut.conj ((QuotientGroup.mk t : A ⧸ Subgroup.center A)) := by
  rw [← ht, CFSG.HardMathSupport.Solomon.Coordinator.centerDescend_conj]

theorem centerDescend_inner_data {A : Type*} [Group A] (β : MulAut A) {t : A}
    (ht : MulAut.conj t = β) :
    ∃ v : A ⧸ Subgroup.center A,
      CFSG.RankThree.PartTwo.KFacts.centerDescend A β = MulAut.conj v :=
  ⟨QuotientGroup.mk t, centerDescend_of_inner β ht⟩

theorem conj_injective_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hB : Function.Injective (MulAut.conj : B →* MulAut B)) :
    Function.Injective (MulAut.conj : A →* MulAut A) := by
  intro a a' h
  apply e.injective
  apply hB
  rw [← CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj e a,
    ← CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj e a', h]

theorem conj_injective_J0 {J : Subgroup G} (e : J0 J ≃* CFSG.Blueprint.NativeSporadic.J2)
    (hconjJ2 : Function.Injective
      (MulAut.conj : CFSG.Blueprint.NativeSporadic.J2 →* MulAut _)) :
    Function.Injective (MulAut.conj : J0 J →* MulAut (J0 J)) :=
  conj_injective_of_mulEquiv (A := J0 J) (B := CFSG.Blueprint.NativeSporadic.J2) e hconjJ2

theorem orderOf_eq_seven_of_conj {A : Type*} [Group A]
    (hconjA : Function.Injective (MulAut.conj : A →* MulAut A))
    {β : MulAut A} {u : A} (hu : MulAut.conj u = β)
    (hβ7 : β ^ 7 = 1) (hβne : β ≠ 1) : orderOf u = 7 := by
  rw [← orderOf_injective (MulAut.conj : A →* MulAut A) hconjA u, hu]
  exact orderOf_eq_prime hβ7 hβne

theorem orderOf_eq_three_of_conj {A : Type*} [Group A]
    (hconjA : Function.Injective (MulAut.conj : A →* MulAut A))
    {β : MulAut A} {u : A} (hu : MulAut.conj u = β)
    (hβ3 : β ^ 3 = 1) (hβne : β ≠ 1) : orderOf u = 3 := by
  rw [← orderOf_injective (MulAut.conj : A →* MulAut A) hconjA u, hu]
  exact orderOf_eq_prime hβ3 hβne

theorem commute_of_conj {A : Type*} [Group A]
    (hconjA : Function.Injective (MulAut.conj : A →* MulAut A))
    {βy βz : MulAut A} {u v : A} (hβcomm : βy * βz = βz * βy)
    (hu : MulAut.conj u = βy) (hv : MulAut.conj v = βz) : u * v = v * u := by
  apply hconjA
  rw [map_mul, map_mul, hu, hv]
  exact hβcomm

theorem order21_of_commuting {A : Type*} [Group A] {u v : A}
    (hord_u : orderOf u = 7) (hord_v : orderOf v = 3) (hcomm_uv : u * v = v * u) :
    orderOf (u * v) = 21 := by
  have hcop : Nat.Coprime (orderOf u) (orderOf v) := by
    rw [hord_u, hord_v]; norm_num
  rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcomm_uv hcop, hord_u, hord_v]

theorem j2_order21_J0 {J : Subgroup G}
    (e : J0 J ≃* CFSG.Blueprint.NativeSporadic.J2) {u v : J0 J}
    (hord_u : orderOf u = 7) (hord_v : orderOf v = 3) (hcomm_uv : u * v = v * u)
    (hK9o : K9J2Order) : False := by
  have hord_uv : orderOf (u * v) = 21 := order21_of_commuting hord_u hord_v hcomm_uv
  have hval : orderOf (e (u * v)) = 21 := by
    rw [MulEquiv.orderOf_eq e (u * v), hord_uv]
  exact hK9o (e (u * v)) hval

theorem inner_of_pow_seven_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hB : ∀ σ : MulAut B, σ ^ 7 = 1 →
      σ ∈ (MulAut.conj : B →* MulAut B).range) :
    ∀ σ : MulAut A, σ ^ 7 = 1 →
      σ ∈ (MulAut.conj : A →* MulAut A).range := by
  intro σ hσ
  have hσ' : (MulAut.congr e σ) ^ 7 = 1 := by
    rw [← map_pow, hσ, map_one]
  obtain ⟨b, hb⟩ := hB (MulAut.congr e σ) hσ'
  refine ⟨e.symm b, ?_⟩
  apply (MulAut.congr e).injective
  rw [CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj, MulEquiv.apply_symm_apply, hb]

theorem exists_noncentral_three_of_thetaComponent {C : Type} [Group C] [Finite C]
    {L : Subgroup C} (hL : L ∈ CFSG.RankThree.thetaComponents 3 C)
    (h3L : 3 ∣ Nat.card L) :
    ∃ x ∈ L, x ^ 3 = 1 ∧ ∃ k ∈ L,
      ⁅x, k⁆ ∉ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 C := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let θC : Subgroup C := CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 C
  let θL : Subgroup ↥L := CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 ↥L
  have hθL : ¬ 3 ∣ Nat.card θL :=
    (CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
      (H := ↥L) Nat.prime_three).2.2.1
  have hQq : CFSG.Open.IsQuasisimple (↥L ⧸ θL) :=
    (CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := ↥L ⧸ θL)).mp hL.2.2
  have h3Q : 3 ∣ Nat.card (↥L ⧸ θL) := by
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup θL
    rw [hcard] at h3L
    exact (Nat.Prime.dvd_mul Nat.prime_three).mp h3L |>.resolve_right hθL
  obtain ⟨xbar, hxbar_ord, hxbar_nc⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
      hQq Nat.prime_three (by norm_num) h3Q
  obtain ⟨x0, hx0⟩ := QuotientGroup.mk'_surjective θL xbar
  have hxbar_top : (QuotientGroup.mk' θL x0) ∈
      (⊤ : Subgroup ↥L).map (QuotientGroup.mk' θL) :=
    Subgroup.mem_map.mpr ⟨x0, Subgroup.mem_top x0, rfl⟩
  obtain ⟨x, hx, hx_ord, hx_mk⟩ :=
    CFSG.GroupTheory.CoprimeTransport.exists_mem_orderOf_eq_prime_mk_eq
      (p := 3) (G := ↥L) (N := θL) (C := ⊤) hθL (hx0 ▸ hxbar_top) hxbar_ord
  have hx3 : x ^ 3 = 1 := by rw [← hx_ord]; exact pow_orderOf_eq_one x
  have hnc : ∃ y : ↥L ⧸ θL, y * xbar ≠ xbar * y := by
    by_contra h
    apply hxbar_nc
    rw [Subgroup.mem_center_iff]
    intro y
    by_contra hy
    exact h ⟨y, hy⟩
  obtain ⟨ybar, hybar⟩ := hnc
  obtain ⟨k, hk_mk⟩ := QuotientGroup.mk'_surjective θL ybar
  have hcomm : ⁅x, k⁆ ∉ θL := by
    intro hmem
    have h1 : QuotientGroup.mk' θL ⁅x, k⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
    rw [map_commutatorElement, hx_mk, hk_mk, commutatorElement_eq_one_iff_mul_comm] at h1
    exact hybar h1.symm
  have hsub : (θC).subgroupOf L = θL := by
    simpa [θC, θL] using
      (CFSG.RankThree.aschbacherSolvableCore_eq_subgroupOf (p := 3) Nat.prime_three
        (H := C) (L := L) hL.2.1).symm
  refine ⟨x, x.2, ?_, k, k.2, ?_⟩
  · simpa using congrArg (fun z : ↥L => (z : C)) hx3
  · intro hmem
    apply hcomm
    have hmem' : L.subtype ⁅x, k⁆ ∈ θC := by
      rwa [map_commutatorElement L.subtype x k]
    have hmemL : ⁅x, k⁆ ∈ θC.subgroupOf L := hmem'
    rwa [hsub] at hmemL

theorem four_conj_ne_of_not_mem_normalizer {J : Subgroup G} {y : G} (hy7 : orderOf y = 7)
    (hyN : y ∉ Subgroup.normalizer (J : Set G)) :
    ∀ i j : Fin 4, i ≠ j →
      J.map (MulAut.conj (y ^ (i : ℕ))).toMonoidHom ≠
        J.map (MulAut.conj (y ^ (j : ℕ))).toMonoidHom := by
  have main : ∀ {i j : Fin 4}, (i : ℕ) < (j : ℕ) →
      J.map (MulAut.conj (y ^ (i : ℕ))).toMonoidHom =
        J.map (MulAut.conj (y ^ (j : ℕ))).toMonoidHom → False := by
    intro i j hlt heq
    set d : ℕ := (j : ℕ) - (i : ℕ) with hd
    have hdpos : 0 < d := by omega
    have hdlt : d < 7 := by
      have hi : (i : ℕ) ≤ 3 := by omega
      have hj : (j : ℕ) ≤ 3 := by omega
      omega
    have hdvd : ¬ 7 ∣ d := by
      intro h
      have := Nat.le_of_dvd hdpos h
      omega
    have hcop : d.Coprime 7 :=
      ((Nat.prime_seven.coprime_iff_not_dvd).mpr hdvd).symm
    have hcop' : d.gcd (orderOf y) = 1 := by
      rw [hy7]
      exact hcop.gcd_eq_one
    have hpow : y ^ (j : ℕ) = y ^ d * y ^ (i : ℕ) := by
      rw [show (j : ℕ) = d + (i : ℕ) by omega, pow_add]
    have hj : (j : ℕ) = d + (i : ℕ) := by omega
    have hcomp : (MulAut.conj (y ^ (i : ℕ))).toMonoidHom.comp
        (MulAut.conj (y ^ d)).toMonoidHom =
        (MulAut.conj (y ^ (j : ℕ))).toMonoidHom := by
      rw [hj]
      ext z
      change y ^ (i : ℕ) * (y ^ d * z * (y ^ d)⁻¹) * (y ^ (i : ℕ))⁻¹ =
        y ^ (d + (i : ℕ)) * z * (y ^ (d + (i : ℕ)))⁻¹
      rw [pow_add]
      group
    have heq' : (J.map (MulAut.conj (y ^ d)).toMonoidHom).map
        (MulAut.conj (y ^ (i : ℕ))).toMonoidHom =
        J.map (MulAut.conj (y ^ (i : ℕ))).toMonoidHom := by
      rw [Subgroup.map_map, hcomp]
      exact heq.symm
    have hmap : J.map (MulAut.conj (y ^ d)).toMonoidHom = J := by
      apply Subgroup.map_injective (f := (MulAut.conj (y ^ (i : ℕ))).toMonoidHom)
        (MulAut.conj (y ^ (i : ℕ))).injective
      exact heq'
    have hmem : y ^ d ∈ Subgroup.normalizer (J : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
    have hy_mem : y ∈ Subgroup.zpowers (y ^ d) := mem_zpowers_pow_iff.mpr hcop'
    exact hyN (Subgroup.zpowers_le.mpr hmem hy_mem)
  intro i j hij heq
  have hval : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hval with hlt | hlt
  · exact main hlt heq
  · exact main hlt heq.symm

theorem seven_normalizes_thetaComp
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (haL : a ∈ P ⊓ c.L) (ha3 : orderOf a = 3) (haZ : a ∉ zSub P c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : 3 ∣ Nat.card J)
    {y : G} (hyM : y ∈ D.M) (hy7 : orderOf y = 7)
    (hycent : ∀ q ∈ P ⊓ c.L, y * q = q * y) :
    y ∈ Subgroup.normalizer (J : Set G) := by
  classical
  have hrankG : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3 := rank_three_le c hON hP hNZ
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  have hrankC : CFSG.Open.pRank 3 (⊤ : Subgroup C) ≤ 3 :=
    (CFSG.SectionRank.pRank_top_le_of_injective (p := 3) Nat.prime_three.one_lt C.subtype
      C.subtype_injective).trans hrankG
  have hyC : y ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact hycent a haL
  have hypowC : ∀ n : ℕ, y ^ n ∈ C := fun n => C.pow_mem hyC n
  obtain ⟨L₀, hL₀, hL₀map⟩ := hJ
  have hcardL₀ : Nat.card L₀ = Nat.card J := by
    rw [← hL₀map]
    exact (Subgroup.card_map_of_injective C.subtype_injective).symm
  have h3L₀ : 3 ∣ Nat.card L₀ := by
    rw [hcardL₀]
    exact h3
  by_contra hyN
  let φ : Fin 4 → MulAut C := fun i =>
    MulAut.conj (⟨y ^ (i : ℕ), hypowC (i : ℕ)⟩ : C)
  let Y : Fin 4 → Subgroup C := fun i => L₀.map (φ i).toMonoidHom
  have hY_mem : ∀ i, Y i ∈ CFSG.RankThree.thetaComponents 3 C := fun i =>
    CFSG.RankThree.map_mulEquiv_mem_thetaComponents Nat.prime_three (φ i) hL₀
  have hYcard : ∀ i, Nat.card (Y i) = Nat.card L₀ := fun i =>
    Subgroup.card_map_of_injective (φ i).injective
  have h3Y : ∀ i, 3 ∣ Nat.card (Y i) := fun i => by
    rw [hYcard i]; exact h3L₀
  have hYmap : ∀ i, (Y i).map C.subtype =
      J.map (MulAut.conj (y ^ (i : ℕ))).toMonoidHom := by
    intro i
    have hcomp : C.subtype.comp
        (MulAut.conj (⟨y ^ (i : ℕ), hypowC (i : ℕ)⟩ : C)).toMonoidHom =
        (MulAut.conj (y ^ (i : ℕ))).toMonoidHom.comp C.subtype := by
      ext z
      rfl
    rw [show Y i = L₀.map (MulAut.conj (⟨y ^ (i : ℕ), hypowC (i : ℕ)⟩ : C)).toMonoidHom
      from rfl]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, show L₀.map C.subtype = J from hL₀map]
  have hYdist : ∀ i j : Fin 4, i ≠ j → Y i ≠ Y j := by
    intro i j hij hEq
    apply four_conj_ne_of_not_mem_normalizer (J := J) hy7 hyN i j hij
    rw [← hYmap i, ← hYmap j, hEq]
  choose x hxY hx3 k hkY hxk using fun i =>
    exists_noncentral_three_of_thetaComponent (hY_mem i) (h3Y i)
  have h4 := CFSG.RankThree.PartTwo.Sec15.four_le_pRank_of_thetaComponents
    (H := C) Y hY_mem hYdist x k hxY hkY hx3 hxk
  omega

theorem three_normalizes_thetaComp
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (haL : a ∈ P ⊓ c.L) (ha3 : orderOf a = 3) (haZ : a ∉ zSub P c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : 3 ∣ Nat.card J)
    {u : G} (huC : u ∈ Subgroup.centralizer ({a} : Set G))
    (hu3 : ∃ k : ℕ, orderOf u = 3 ^ k) :
    u ∈ Subgroup.normalizer (J : Set G) := by
  classical
  have hrankG : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3 := rank_three_le c hON hP hNZ
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  have hrankC : CFSG.Open.pRank 3 (⊤ : Subgroup C) ≤ 3 :=
    (CFSG.SectionRank.pRank_top_le_of_injective (p := 3) Nat.prime_three.one_lt C.subtype
      C.subtype_injective).trans hrankG
  obtain ⟨L₀, hL₀, hL₀map⟩ := hJ
  have haC : a ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
  have hzo : orderOf (⟨a, haC⟩ : C) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact ha3
  have hz_center : (⟨a, haC⟩ : C) ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp g.2
  have hcardL : Nat.card L₀ = Nat.card J := by
    rw [← hL₀map]
    exact (Subgroup.card_map_of_injective C.subtype_injective).symm
  have h3L : 3 ∣ Nat.card L₀ := by
    rw [hcardL]; exact h3
  have hu3' : ∃ k : ℕ, orderOf (⟨u, huC⟩ : C) = 3 ^ k := by
    obtain ⟨k, hk⟩ := hu3
    exact ⟨k, by rw [Subgroup.orderOf_mk]; exact hk⟩
  have huN := pElement_normalizes_thetaComponent_of_pRank_three
    (H := C) Nat.prime_three (by norm_num) hz_center hzo hL₀ h3L hu3' hrankC
  have huNm : L₀.map (MulAut.conj (⟨u, huC⟩ : C)).toMonoidHom = L₀ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp huN
  have hcomp : ((MulAut.conj u).toMonoidHom).comp C.subtype =
      C.subtype.comp ((MulAut.conj (⟨u, huC⟩ : C)).toMonoidHom) := by
    ext c
    rfl
  have h1 : J.map (MulAut.conj u).toMonoidHom =
      (L₀.map (MulAut.conj (⟨u, huC⟩ : C)).toMonoidHom).map C.subtype := by
    rw [← hL₀map, Subgroup.map_map, Subgroup.map_map, hcomp]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change J.map (MulAut.conj u).toMonoidHom = J
  rw [h1, huNm, show L₀.map C.subtype = J from hL₀map]

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

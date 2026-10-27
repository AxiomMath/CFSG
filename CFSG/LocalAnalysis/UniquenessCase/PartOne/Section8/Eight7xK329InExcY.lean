module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329Data
public import CFSG.Adapters.LieModelSimple
public import CFSG.Holt.PointHullTwoGroupBasic
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.GH74.Orders.LieType
import CFSG.RankThree.PartOne.KF.R9Levi
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeCore
import CFSG.GH74.GLS.IVK.Proofs2.Ivk41R
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux.Centralizers
import CFSG.RankThree.PartTwo.Sec12.Hering129CFamG2
import CFSG.RankThree.PartTwo.Sec12.Hering129LFix
import CFSG.RankThree.PartTwo.Sec12.Hering129KRes
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSec31TwoAux
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxAll
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrder504
import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel classicalTags)

open CFSG.Blueprint.Chevalley

private theorem k329inyg2_map_centralizer {A B : Type*} [Group A] [Group B] (e : A ≃* B) (z : A) :
    (Subgroup.centralizer ({z} : Set A)).map (e : A →* B) =
      Subgroup.centralizer ({e z} : Set B) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap]
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc e x * e z = e (x * z) := (map_mul e x z).symm
      _ = e (z * x) := by rw [hx]
      _ = e z * e x := map_mul e z x
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    refine Subgroup.mem_map.mpr ⟨e.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hx

private theorem k329inyg2_isPerfect_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hX : Group.IsPerfect X) : Group.IsPerfect Y := by
  rw [Group.isPerfect_def] at hX ⊢
  rw [_root_.commutator_def] at hX ⊢
  rw [← Subgroup.map_top_of_surjective (e : X →* Y) e.surjective, ← Subgroup.map_commutator, hX]

private theorem k329inyg2_absorb {G : Type*} [Group G] {C Q Y : Subgroup G}
    (hQC : Q ≤ C) (hYQ : Y ≤ Q) (hYne : Y ≠ ⊥) (hQ : CFSG.Open.IsQuasisimple ↥Q)
    (hYperf : Group.IsPerfect ↥Y) (hsub : CFSG.Open.IsSubnormal Y C) : Y = Q := by
  have hsubQ : CFSG.Open.IsSubnormal Y Q := by
    have h := CFSG.Open.IsSubnormal.inf_of_le hsub hQC
    rwa [inf_eq_left.mpr hYQ] at h
  have hmath : (Y.subgroupOf Q).IsSubnormal :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hYQ).mp hsubQ
  have htop : CFSG.Open.IsSubnormal (Y.subgroupOf Q) ⊤ :=
    CFSG.Open.IsSubnormal.of_mathlib hmath
  have hperf' : Group.IsPerfect ↥(Y.subgroupOf Q) :=
    k329inyg2_isPerfect_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYQ).symm hYperf
  rcases @CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top
      ↥Q _ hQ (Y.subgroupOf Q) htop hperf' with hbot | htop'
  · exfalso
    apply hYne
    rw [eq_bot_iff]
    intro y hy
    have hy' : (⟨y, hYQ hy⟩ : ↥Q) ∈ Y.subgroupOf Q := hy
    rw [hbot, Subgroup.mem_bot] at hy'
    exact congrArg Subtype.val hy'
  · apply le_antisymm hYQ
    intro q hq
    have hq' : (⟨q, hq⟩ : ↥Q) ∈ Y.subgroupOf Q := by
      rw [htop']
      trivial
    exact hq'

private theorem k329inyg2_center_eq_bot_of_card {G : Type*} [Group G] [IsSimpleGroup G]
    (hcard : Nat.card G = 504) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    have hcomm : IsMulCommutative G :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b)) a⟩⟩
    have hp := (@Group.is_simple_iff_prime_card G _ hcomm).mp (inferInstance : IsSimpleGroup G)
    rw [hcard] at hp
    exact (by norm_num : ¬ (504 : ℕ).Prime) hp

private theorem k329inyg2_class
    {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    {w : adjointGroup .G2 K} (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (Yw : Subgroup (adjointGroup .G2 K))
    (hYw : CFSG.Open.IsComponentOf Yw
      (Subgroup.centralizer ({w} : Set (adjointGroup .G2 K))))
    (hYw8 : LieModel ↥Yw .PSL 2 2 3)
    (hwclass : w ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ShortSL2 K ∨
      w ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2LongSL2 K) :
    Nat.card K = 8 := by
  have hYws : IsSimpleGroup ↥Yw :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hYw8
  have hcardYw : Nat.card ↥Yw = 504 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_eight
      (CFSG.Blueprint.LieModel.statedClassicalModel hYw8 (by decide))
  have hcenterY : Subgroup.center ↥Yw = ⊥ :=
    @k329inyg2_center_eq_bot_of_card ↥Yw _ hYws hcardYw
  have hperf : Group.IsPerfect ↥Yw := Group.isPerfect_def.mpr hYw.2.2.1
  have hYne : Yw ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot Yw).mp
      (CFSG.ComponentClassification.Quasisimple.nontrivial hYw.2.2)
  have hYwC : Yw ≤ Subgroup.centralizer ({w} : Set (adjointGroup .G2 K)) := hYw.1
  have hYwSub : CFSG.Open.IsSubnormal Yw
      (Subgroup.centralizer ({w} : Set (adjointGroup .G2 K))) := hYw.2.1
  rcases hwclass with hwS | hwM
  ·
    obtain ⟨N, hNC, hcomm, hNq, x, hxN, hxcen, hx1, -⟩ :=
      CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof.g2ThreeACent_holds K hK3 hK4 w hwS hw3 hw1
    have hNOC : CFSG.Open.IsQuasisimple ↥N :=
      (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥N).2.2.1.mp hNq
    have hYleN : Yw ≤ N := by
      have h1 : Yw ≤ ⁅Subgroup.centralizer ({w} : Set (adjointGroup .G2 K)),
          Subgroup.centralizer ({w} : Set (adjointGroup .G2 K))⁆ :=
        CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux.le_commutator_of_isPerfect
          hperf hYwC
      have h2 : ⁅Subgroup.centralizer ({w} : Set (adjointGroup .G2 K)),
          Subgroup.centralizer ({w} : Set (adjointGroup .G2 K))⁆ ≤ N := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        rw [commutatorElement_def]
        exact hcomm a ha b hb
      exact h1.trans h2
    have hYeqN : Yw = N := k329inyg2_absorb hNC hYleN hYne hNOC hperf hYwSub
    have hxY : x ∈ Yw := hYeqN.symm ▸ hxN
    have hxcenter : (⟨x, hxY⟩ : ↥Yw) ∈ Subgroup.center ↥Yw := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hxcen y.1 (hYeqN ▸ y.2)).symm
    rw [hcenterY, Subgroup.mem_bot] at hxcenter
    exact absurd (congrArg Subtype.val hxcenter) hx1
  ·
    obtain ⟨hcomm, -⟩ :=
      CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ThreeBCent_holds K hK3 hK4 w hwM hw3 hw1
    let S₀ : Subgroup (adjointGroup .G2 K) :=
      CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ShortSL2 K
    have hS₀C : S₀ ≤ Subgroup.centralizer ({w} : Set (adjointGroup .G2 K)) := by
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2Short_commute_g2Long hs hwM
    have hS₀q : CFSG.Open.IsQuasisimple ↥S₀ :=
      (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥S₀).2.2.1.mp
        (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.isQuasisimple_g2ShortSL2 (K := K) hK4)
    have hYleS : Yw ≤ S₀ := by
      have h1 : Yw ≤ ⁅Subgroup.centralizer ({w} : Set (adjointGroup .G2 K)),
          Subgroup.centralizer ({w} : Set (adjointGroup .G2 K))⁆ :=
        CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux.le_commutator_of_isPerfect
          hperf hYwC
      have h2 : ⁅Subgroup.centralizer ({w} : Set (adjointGroup .G2 K)),
          Subgroup.centralizer ({w} : Set (adjointGroup .G2 K))⁆ ≤ S₀ := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        rw [commutatorElement_def]
        exact hcomm a ha b hb
      exact h1.trans h2
    have hYeqS : Yw = S₀ := k329inyg2_absorb hS₀C hYleS hYne hS₀q hperf hYwSub
    obtain ⟨eSK⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2
      (K := K)
    have hformula : Nat.card ↥S₀ = Nat.card K * (Nat.card K ^ 2 - 1) := by
      change Nat.card ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ShortSL2 K) =
        Nat.card K * (Nat.card K ^ 2 - 1)
      rw [← Nat.card_congr eSK.toEquiv, CFSG.GorensteinWalter.sl2_card_formula K]
    have hcardS : Nat.card ↥S₀ = Nat.card ↥Yw := by rw [hYeqS]
    have hqeq : Nat.card K * (Nat.card K ^ 2 - 1) = 504 := by
      rw [← hformula, hcardS]
      exact hcardYw
    set q : ℕ := Nat.card K with hqdef
    have hq : q * (q ^ 2 - 1) = 504 := by rw [hqdef]; exact hqeq
    have hq4 : 4 ≤ q := by rw [hqdef]; exact hK4
    have hqle : q ≤ 8 := by
      by_contra h
      have h9 : 9 ≤ q := by omega
      have hq2 : 80 ≤ q ^ 2 - 1 := by
        have h81 : 9 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h9 2
        omega
      have h720 : 720 ≤ q * (q ^ 2 - 1) := by
        calc 720 = 9 * 80 := by norm_num
          _ ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul h9 hq2
      omega
    interval_cases q <;> norm_num at hq
    norm_num

private theorem k329inyg2_main
    (S : Type) [Group S] [Finite S] (r e : ℕ) (hr : r ≠ 3) (z : S) (hz : orderOf z = 3)
    (Y : Subgroup S)
    (hY : CFSG.Open.IsComponentOf Y (Subgroup.centralizer ({z} : Set S)))
    (hY8 : LieModel ↥Y .PSL 2 2 3)
    (K : Type) [instK : Field K] [instF : Finite K]
    (hAdm : CFSG.Open.StatedLieAdmissible CFSG.Open.StatedLieTag.G2 0 r e)
    (hKcard : Nat.card K = r ^ e)
    (eK : S ≃* CFSG.Blueprint.AdjointQuotient CFSG.Blueprint.Chevalley.Tag.G2 K) :
    r ^ e = 8 := by
  have hrp : r.Prime := hAdm.1
  have h3le : 3 ≤ r ^ e := hAdm.2.2.2
  have hne3 : r ^ e ≠ 3 := by
    intro heq
    have he : e ≠ 0 := by
      rintro rfl
      rw [pow_zero] at heq
      omega
    have hdvd : r ∣ 3 := heq ▸ dvd_pow_self r (n := e) he
    exact hr ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_three).mp hdvd)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    omega
  have hK3 : ringChar K ≠ 3 :=
    letI : CharP K r := CFSG.GH74.GLS.IVK.Proofs2.Ivk41R.charP_of_natCard_eq_pow hrp hKcard
    (by rw [ringChar.eq K r]; exact hr)
  have hZ : Subgroup.center ↥(adjointGroup .G2 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (K := K)
  let φ : S ≃* ↥(adjointGroup .G2 K) :=
    eK.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  let C : Subgroup S := Subgroup.centralizer ({z} : Set S)
  have hmapC : C.map (φ : S →* ↥(adjointGroup .G2 K)) =
      Subgroup.centralizer ({φ z} : Set ↥(adjointGroup .G2 K)) :=
    k329inyg2_map_centralizer φ z
  have hY₀ : CFSG.Open.IsComponentOf (Y.map (φ : S →* ↥(adjointGroup .G2 K)))
      (Subgroup.centralizer ({φ z} : Set ↥(adjointGroup .G2 K))) := by
    rw [← hmapC]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map φ hY
  have hz3 : z ^ 3 = 1 :=
    (orderOf_dvd_iff_pow_eq_one).mp (by simp [hz])
  have hz1 : z ≠ 1 := by
    intro h
    have h1 : orderOf z = 1 := orderOf_eq_one_iff.mpr h
    omega
  have hz₀3 : (φ z) ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have hz₀1 : φ z ≠ 1 := fun h => hz1 (φ.injective (by rw [h, map_one]))
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof.g2ThreeConjSL2_holds
      K hK3 hK4 (φ z) hz₀3 hz₀1
  let w : ↥(adjointGroup .G2 K) := g * (φ z) * g⁻¹
  let α : ↥(adjointGroup .G2 K) ≃* ↥(adjointGroup .G2 K) := MulAut.conj g
  let Yw : Subgroup ↥(adjointGroup .G2 K) :=
    (Y.map (φ : S →* ↥(adjointGroup .G2 K))).map
      (α : ↥(adjointGroup .G2 K) →* ↥(adjointGroup .G2 K))
  have hCw : (Subgroup.centralizer ({φ z} : Set ↥(adjointGroup .G2 K))).map
      (α : ↥(adjointGroup .G2 K) →* ↥(adjointGroup .G2 K)) =
      Subgroup.centralizer ({w} : Set ↥(adjointGroup .G2 K)) := by
    rw [k329inyg2_map_centralizer α (φ z)]
    simp only [w, α, MulAut.conj_apply]
  have hYw : CFSG.Open.IsComponentOf Yw
      (Subgroup.centralizer ({w} : Set ↥(adjointGroup .G2 K))) := by
    rw [← hCw]
    simpa only [Yw] using CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map α hY₀
  have hYw8 : LieModel ↥Yw .PSL 2 2 3 := by
    have h1 : LieModel ↥(Y.map (φ : S →* ↥(adjointGroup .G2 K))) .PSL 2 2 3 :=
      CFSG.Blueprint.LieModel.of_mulEquiv
        (Y.equivMapOfInjective (φ : S →* ↥(adjointGroup .G2 K)) φ.injective) hY8
    simpa only [Yw] using CFSG.Blueprint.LieModel.of_mulEquiv
      ((Y.map (φ : S →* ↥(adjointGroup .G2 K))).equivMapOfInjective
        (α : ↥(adjointGroup .G2 K) →* ↥(adjointGroup .G2 K)) α.injective) h1
  have hw3 : w ^ 3 = 1 := by
    dsimp only [w]
    rw [conj_pow, hz₀3]
    group
  have hw1 : w ≠ 1 := by
    intro h
    apply hz₀1
    calc φ z = g⁻¹ * w * g := by simp only [w]; group
      _ = g⁻¹ * 1 * g := by rw [h]
      _ = 1 := by group
  have hwclass : w ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ShortSL2 K ∨
      w ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2LongSL2 K := hg
  have hK8 : Nat.card K = 8 :=
    k329inyg2_class hK3 hK4 hw3 hw1 Yw hYw hYw8 hwclass
  rw [← hKcard]
  exact hK8

theorem k329in_excY_G2
    (S : Type) [Group S] [Finite S] (hS : IsSimpleGroup S) (n r e : ℕ)
    (hL : LieModel S .G2 n r e) (hr : r ≠ 3) (z : S) (hz : orderOf z = 3) (Y : Subgroup S)
    (hY : CFSG.Open.IsComponentOf Y (Subgroup.centralizer ({z} : Set S)))
    (hY8 : LieModel ↥Y .PSL 2 2 3) : r ^ e = 8 := by
  have hce := hL.chevalleyExceptionalModel
    (by decide : CFSG.Open.StatedLieTag.G2 ∈ CFSG.Blueprint.chevalleyExceptionalTags)
  obtain ⟨hAdm, K, hKf, hKfin, hKcard, ⟨eK⟩⟩ := hce
  have _hS := hS
  exact k329inyg2_main S r e hr z hz Y hY hY8 K (instK := hKf) (instF := hKfin)
    hAdm hKcard eK

private theorem k329inyd4e_absorption {S : Type} [Group S] {Q C Y : Subgroup S}
    (hQC : Q ≤ C) (hQ : CFSG.IsQuasisimple ↥Q) (hYQ : Y ≤ Q) (hY1 : Nontrivial ↥Y)
    (hYp : Group.IsPerfect ↥Y) (hYs : CFSG.Open.IsSubnormal Y C) : Y = Q := by
  have hsub : CFSG.Open.IsSubnormal Y Q := by
    have h := CFSG.Open.IsSubnormal.inf_of_le hYs hQC
    rwa [inf_eq_left.mpr hYQ] at h
  have hsm : (Y.subgroupOf Q).IsSubnormal :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hYQ).1 hsub
  exact CFSG.RankThree.PartTwo.Sec4.Res429.eq_of_le_of_isSubnormal_of_isQuasisimple
    hYQ hQ hYp hY1 hsm

theorem k329in_excY_trialityD4_even
    (S : Type) [Group S] [Finite S] (hS : IsSimpleGroup S)
    (n r e : ℕ) (hL : LieModel S .trialityD4 n r e) (hr2 : r = 2) (z : S) (hz : orderOf z = 3)
    (Y : Subgroup S) (hY : CFSG.Open.IsComponentOf Y (Subgroup.centralizer ({z} : Set S)))
    (hY8 : LieModel ↥Y .PSL 2 2 3) : r ^ e = 2 := by
  subst r
  have _hS : IsSimpleGroup S := hS
  by_cases he1 : e = 1
  · subst e
    norm_num
  · exfalso
    have he2 : 2 ≤ e := by
      have h1 : 1 ≤ e := (hL.admissible).2.1
      omega
    have hYs : IsSimpleGroup ↥Y :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hY8
    have hcard : Nat.card ↥Y = 504 :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_eight
        (CFSG.Blueprint.LieModel.statedClassicalModel hY8 (by decide))
    have hnc : ∃ a b : ↥Y, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      have hcomm : IsMulCommutative ↥Y := IsMulCommutative.of_comm fun a b => hcon a b
      have hp := (@Group.is_simple_iff_prime_card ↥Y _ hcomm).mp hYs
      rw [hcard] at hp
      exact (by norm_num : ¬ (504 : ℕ).Prime) hp
    have hcenter : Subgroup.center ↥Y = ⊥ :=
      @CFSG.ComponentClassification.Helpers.center_eq_bot ↥Y _ hYs hnc
    have hYperf : Group.IsPerfect ↥Y := Group.isPerfect_def.mpr hY.2.2.1
    have hYnt : Nontrivial ↥Y := hYs.toNontrivial
    obtain ⟨q, hqcard, hqp, hIs⟩ :=
      CFSG.RankThree.PartTwo.Sec12.Hering129C.isG2D4_of_chevalley_D4
        (hL.chevalleyExceptionalModel (by decide))
    have hq4 : 4 ≤ q.card := by
      rw [hqcard]
      have h : (2 : ℕ) ^ 2 ≤ 2 ^ e :=
        Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega)
      simpa using h
    have hp3 : q.p ≠ 3 := by rw [hqp]; norm_num
    have hzAB : CFSG.RankThree.PartTwo.Sec12.IsThreeA z q.card ∨
        CFSG.RankThree.PartTwo.Sec12.IsThreeB z (q.card ^ 3) :=
      (CFSG.RankThree.PartTwo.Sec12.Hering129L.ks129ThreeLocalFix_holds S q 3 hIs hq4 hp3
        (fun _ => hqp)).1 z hz
    let R : Subgroup S := CFSG.RankThree.PartTwo.Sec12.resCent (⊤ : Subgroup S) z
    have hRle : R ≤ Subgroup.centralizer ({z} : Set S) :=
      (CFSG.RankThree.PartTwo.Sec12.resCent_le (⊤ : Subgroup S) z).trans inf_le_right
    have hYleR : Y ≤ R :=
      CFSG.RankThree.PartTwo.Sec12.le_inSubgroup_perfectResidual_of_isPerfect
        (X := ⊤ ⊓ Subgroup.centralizer ({z} : Set S)) (P := Y) (le_inf le_top hY.1) hYperf
    have hsub : (Y.subgroupOf R).IsSubnormal :=
      (CFSG.Open.IsSubnormal.iff_subgroupOf hYleR).1 (by
        have h := CFSG.Open.IsSubnormal.inf_of_le hY.2.1 hRle
        rwa [inf_eq_left.mpr hYleR] at h)
    have absorb : CFSG.IsQuasisimple ↥R → Y = R := fun hQ =>
      k329inyd4e_absorption hRle hQ hYleR hYnt hYperf hY.2.1
    rcases hzAB with hA | hB
    · have hJ : CFSG.IsQuasisimple ↥R :=
        CFSG.RankThree.PartTwo.Sec12.Hering129KRes.isQuasisimple_of_isSLThreePiAt
          hA.2.2 (by omega)
      have hYR : Y = R := absorb hJ
      have hzR : z ∈ R := hA.2.1
      have hzY : z ∈ Y := hYR.symm ▸ hzR
      have hzcent : (⟨z, hzY⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        simpa using (Subgroup.mem_centralizer_singleton_iff.mp (hY.1 g.2))
      rw [hcenter] at hzcent
      have hz1 : z = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp hzcent)
      rw [hz1, orderOf_one] at hz
      omega
    · obtain ⟨F, hField, hFintype, hFcard, ⟨eiso⟩⟩ := hB.2
      have hFval : Nat.card F = 2 ^ (3 * e) := by
        rw [Nat.card_eq_fintype_card, hFcard, hqcard, ← pow_mul, Nat.mul_comm e 3]
      have h4F : 4 ≤ Nat.card F := by
        rw [hFval]
        have h : (2 : ℕ) ^ 2 ≤ 2 ^ (3 * e) :=
          Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega)
        simpa using h
      have hJ : CFSG.IsQuasisimple ↥R :=
        (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.isQuasisimple_special_linear_two h4F).of_mulEquiv
          eiso
      have hYR : Y = R := absorb hJ
      have hcardR : Nat.card ↥R = 504 := hYR ▸ hcard
      have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
          Nat.card F * (Nat.card F ^ 2 - 1) :=
        (CFSG.Open.StatedAPI.card_statedSL 2 F).symm.trans
          (CFSG.Open.StatedAPI.card_statedSL_two F)
      have h2 : Nat.card ↥R = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
        Nat.card_congr eiso.toEquiv
      have heq : Nat.card F * (Nat.card F ^ 2 - 1) = 504 := by
        rw [← hSL, ← h2]
        exact hcardR
      have ht64 : 64 ≤ 2 ^ (3 * e) := by
        have h : (2 : ℕ) ^ 6 ≤ 2 ^ (3 * e) :=
          Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega)
        simpa using h
      have hsq : 64 ≤ (2 ^ (3 * e)) ^ 2 := by
        rw [pow_two]
        exact le_trans (by norm_num : 64 ≤ 64 * 64) (Nat.mul_le_mul ht64 ht64)
      have hprod : 64 * 63 ≤ 2 ^ (3 * e) * ((2 ^ (3 * e)) ^ 2 - 1) :=
        Nat.mul_le_mul ht64 (by omega)
      have hlt : (504 : ℕ) < 2 ^ (3 * e) * ((2 ^ (3 * e)) ^ 2 - 1) := by omega
      rw [hFval] at heq
      omega

private theorem k329inyd4o_trialityD4_bridge
    (S : Type) [Group S] [Finite S] (n r e : ℕ)
    (hL : LieModel S .trialityD4 n r e) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      q.p = r ∧ q.exponent = e ∧
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie
        ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩).Group) := by
  obtain ⟨hrp, he1, -⟩ := hL.admissible
  let q : TauCeti.PrimePower := ⟨r, e, hrp, by omega⟩
  have hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid :=
    TauCeti.LieTypeIndex.valid_trialityD4 q
  refine ⟨q, hv, rfl, rfl, ?_⟩
  have hce : CFSG.Blueprint.ChevalleyExceptionalModel S .trialityD4 r e :=
    hL.chevalleyExceptionalModel (by decide)
  obtain ⟨K, hKfield, hKfin, hK, σ, hσ, hφ⟩ := hce.2
  have hqcard : q.card = r ^ e := by rw [TauCeti.PrimePower.card_def]
  have hK' : Nat.card K = q.card ^ 3 := by
    rw [hK, hqcard]
    rfl
  have hσ' : ∀ x : K, σ x = x ^ q.card := by
    intro x
    rw [hqcard]
    exact hσ x
  have he : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩).Group := by
    letI : Field K := hKfield
    letI : Finite K := hKfin
    exact hφ.some.trans
      ((CFSG.TauCetiBridge.Even.chevalleyBridgesAll).trialityD4 q hv K hK' σ hσ').some
  exact ⟨he⟩

private theorem k329inyd4o_lieOrderFormula_ne_504 (d : TauCeti.LieTypeIndex) (hd : d.Valid)
    (h2 : d.characteristic ≠ 2) :
    CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d ≠ 504 := by
  intro h
  obtain ⟨q, rfl, hq8⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.I1416Rows.Order504.lieOrderFormula_eq_504 hd h
  have hqp : q.p = 2 := by
    have hdvd : q.p ∣ 8 := by
      rw [← hq8, TauCeti.PrimePower.card_def]
      exact dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1
      (q.prime_p.dvd_of_dvd_pow (m := 2) (n := 3) (by simpa using hdvd))
  exact h2 (by simp [TauCeti.LieTypeIndex.characteristic_A, hqp])

theorem k329in_excY_trialityD4_odd
    (S : Type) [Group S] [Finite S] (hS : IsSimpleGroup S)
    (n r e : ℕ) (hL : LieModel S .trialityD4 n r e) (hr : r ≠ 3) (hr2 : r ≠ 2) (z : S)
    (hz : orderOf z = 3) (Y : Subgroup S)
    (hY : CFSG.Open.IsComponentOf Y (Subgroup.centralizer ({z} : Set S)))
    (hY8 : LieModel ↥Y .PSL 2 2 3) : False := by
  obtain ⟨hrp, he1, -⟩ := hL.admissible
  have hYs : IsSimpleGroup ↥Y :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hY8
  have hYcard : Nat.card ↥Y = 504 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_eight
      (CFSG.Blueprint.LieModel.statedClassicalModel hY8 (by decide))
  have hncY : ∃ a b : ↥Y, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcomm : IsMulCommutative ↥Y := IsMulCommutative.of_comm fun a b => hcon a b
    have hp := (@Group.is_simple_iff_prime_card ↥Y _ hcomm).mp hYs
    rw [hYcard] at hp
    exact (by norm_num : ¬ (504 : ℕ).Prime) hp
  have hcenterY : Subgroup.center ↥Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Y) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hncY
      have ha : a ∈ Subgroup.center ↥Y := by rw [h]; trivial
      exact hab ((Subgroup.mem_center_iff.mp ha b).symm)
  obtain ⟨q, hv, hqp, hqe, ⟨e₀⟩⟩ := k329inyd4o_trialityD4_bridge S n r e hL
  let d : TauCeti.LieTypeIndex := TauCeti.LieTypeIndex.trialityD4 q
  let β : MulAut S := MulAut.conj z
  have hβmem : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived S := by
    have hβinner : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner S := ⟨z, rfl⟩
    exact CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived S hβinner
  have hz3 : z ^ 3 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hz]
  have hβ3 : β ^ 3 = 1 := by
    change (MulAut.conj z : MulAut S) ^ 3 = 1
    rw [← map_pow (MulAut.conj : S →* MulAut S) z 3, hz3, map_one]
  have hβ1 : β ≠ 1 := by
    intro hβ
    have hβ' : MulAut.conj z = 1 := hβ
    have hzcenter : z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx : (MulAut.conj z) x = x := by simp [hβ']
      rw [MulAut.conj_apply] at hx
      exact (mul_inv_eq_iff_eq_mul.mp hx).symm
    have hcenterS : Subgroup.center S = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hncY
        have hab' : (a : S) * (b : S) ≠ (b : S) * (a : S) := by
          intro h'
          exact hab (Subtype.ext (by simpa using h'))
        have ha : (a : S) ∈ Subgroup.center S := by rw [h]; trivial
        exact hab' ((Subgroup.mem_center_iff.mp ha b).symm)
    have hz1 : z = 1 := by
      have hzbot : z ∈ (⊥ : Subgroup S) := hcenterS ▸ hzcenter
      simpa using hzbot
    exact absurd hz (by rw [hz1, orderOf_one]; norm_num)
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β =
      Subgroup.centralizer ({z} : Set S) := by
    ext x
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, Subgroup.mem_centralizer_iff]
    constructor
    · intro h y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have h' : (MulAut.conj z) x = x := by simpa [β] using h
      rw [MulAut.conj_apply] at h'
      exact mul_inv_eq_iff_eq_mul.mp h'
    · intro h
      have hz' : z * x = x * z := h z (Set.mem_singleton z)
      simpa [β, MulAut.conj_apply] using (mul_inv_eq_iff_eq_mul.mpr hz')
  have hY' : CFSG.Open.IsComponentOf Y
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) := by
    rw [hfix]
    exact hY
  have hdchar : d.characteristic = r := by
    change (TauCeti.LieTypeIndex.trialityD4 q).characteristic = r
    rw [TauCeti.LieTypeIndex.characteristic_trialityD4, hqp]
  have hpc : 3 ≠ d.characteristic := by
    rw [hdchar]
    exact fun h => hr h.symm
  have hcomp : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.CompIdxAt 3 d
      (TauCeti.CFSGIndex.lie ⟨d, hv⟩).Group :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.lieCompIdx_all ⟨d, hv⟩ 3 Nat.prime_three
      (by norm_num) hpc trivial
  have hcompS : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.CompIdxAt 3 d S :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.compIdxAt_of_mulEquiv e₀.symm hcomp
  obtain ⟨i, ⟨eY⟩, hrel⟩ := hcompS β hβmem hβ3 hβ1 Y hY'
  have hquotcard : Nat.card (↥Y ⧸ Subgroup.center ↥Y) = 504 := by
    rw [hcenterY]
    rw [show Nat.card (↥Y ⧸ (⊥ : Subgroup ↥Y)) = Nat.card ↥Y from
      Nat.card_congr QuotientGroup.quotientBot.toEquiv]
    exact hYcard
  cases i with
  | cyclic p hp => exact hrel.elim
  | sporadic name => exact hrel.elim
  | alternating m hm =>
    change CFSG.LocalAnalysis.GLTheoremA.KD264Lie.compRelC d
      (TauCeti.CFSGIndex.alternating m hm) at hrel
    rcases hrel with ⟨hm5, -⟩ | ⟨hm6, -⟩ | ⟨hm8, -⟩
    · subst hm5
      have halt : Nat.card (alternatingGroup (Fin 5)) = 504 := by
        rw [← Nat.card_congr eY.toEquiv, hquotcard]
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at halt
      norm_num at halt
    · subst hm6
      have halt : Nat.card (alternatingGroup (Fin 6)) = 504 := by
        rw [← Nat.card_congr eY.toEquiv, hquotcard]
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at halt
      norm_num at halt
    · subst hm8
      have halt : Nat.card (alternatingGroup (Fin 8)) = 504 := by
        rw [← Nat.card_congr eY.toEquiv, hquotcard]
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at halt
      norm_num at halt
  | lie e' =>
    have hcard_lie : Nat.card (↥Y ⧸ Subgroup.center ↥Y) =
        CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula e'.1 := by
      have hLB : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge :=
        CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
      exact hLB e' (↥Y ⧸ Subgroup.center ↥Y) ⟨eY⟩
    have h504 : CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula e'.1 = 504 :=
      hcard_lie.symm.trans hquotcard
    change CFSG.LocalAnalysis.GLTheoremA.KD264Lie.compRel d e'.1 at hrel
    have hr5 : 5 ≤ r := hrp.five_le_of_ne_two_of_ne_three hr2 hr
    have hfs5 : 5 ≤ CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d := by
      change 5 ≤ q.card
      rw [TauCeti.PrimePower.card_def]
      calc 5 ≤ q.p := by rw [hqp]; exact hr5
        _ = q.p ^ 1 := (pow_one _).symm
        _ ≤ q.p ^ q.exponent := Nat.pow_le_pow_right (by omega) (by have := q.exponent_pos; omega)
    have hfs2 : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d ≠ 2 := by omega
    have hfs3 : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d ≠ 3 := by omega
    have hchar : e'.1.characteristic = d.characteristic := by
      rcases hrel with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hfs2
      · exact absurd h hfs3
    have hchar2 : e'.1.characteristic ≠ 2 := by
      rw [hchar, hdchar]
      exact hr2
    exact (k329inyd4o_lieOrderFormula_ne_504 e'.1 e'.2 hchar2) h504

theorem k329in_excY_trialityD4
    (S : Type) [Group S] [Finite S] (hS : IsSimpleGroup S)
    (n r e : ℕ) (hL : LieModel S .trialityD4 n r e) (hr : r ≠ 3) (z : S) (hz : orderOf z = 3)
    (Y : Subgroup S) (hY : CFSG.Open.IsComponentOf Y (Subgroup.centralizer ({z} : Set S)))
    (hY8 : LieModel ↥Y .PSL 2 2 3) : r ^ e = 2 := by
  by_cases hr2 : r = 2
  · exact k329in_excY_trialityD4_even S hS n r e hL hr2 z hz Y hY hY8
  · exact (k329in_excY_trialityD4_odd S hS n r e hL hr hr2 z hz Y hY hY8).elim

theorem k329in_excY_twistedF4
    (S : Type) [Group S] [Finite S] (hS : IsSimpleGroup S)
    (n r e : ℕ) (hL : LieModel S .twistedF4 n r e) (hr : r ≠ 3) (z : S) (hz : orderOf z = 3)
    (Y : Subgroup S) (hY : CFSG.Open.IsComponentOf Y (Subgroup.centralizer ({z} : Set S)))
    (hY8 : LieModel ↥Y .PSL 2 2 3) : False := by
  have _hS := hS
  have _hr := hr
  obtain ⟨-, hRT⟩ := hL.reeTitsModel (by decide)
  obtain ⟨_, a, ha, _, K, hKfield, hKfin, hKchar, hKcard, ⟨φ⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hRT
  let _ : Field K := hKfield
  let _ : Finite K := hKfin
  let _ : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := hKchar
  let Γ := CFSG.LieType.Ree.ReeTag.F4.reeGamma K a
  set C : Subgroup S := Subgroup.centralizer ({z} : Set S) with hCdef
  have hzφ : orderOf (φ z) = 3 := by rw [MulEquiv.orderOf_eq, hz]
  obtain ⟨e₂⟩ := CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU
    a K hKcard (φ z) hzφ
  have hCmap : C.map φ.toMonoidHom = Subgroup.centralizer ({φ z} : Set Γ) := by
    rw [hCdef]
    exact CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.map_centralizer_singleton φ z
  let e₁ : C ≃* Subgroup.centralizer ({φ z} : Set Γ) :=
    (Subgroup.equivMapOfInjective C φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr hCmap)
  let F := GaloisField 2 (2 * (2 * a + 1))
  let H := CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 (2 * a + 1) F 3
  let e : C ≃* H := e₁.trans e₂
  have hFcard : Nat.card F = 2 ^ (2 * (2 * a + 1)) := by
    dsimp only [F]
    rw [GaloisField.card (p := 2) (n := 2 * (2 * a + 1)) (by omega)]
  have hFcard2 : Nat.card F = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [hFcard, ← pow_mul]
    congr 1
    ring
  have hUFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (2 * a + 1) F :=
    ⟨Nat.prime_two, by omega, hFcard⟩
  have hSU : CFSG.IsQuasisimple ↥H :=
    (CFSG.RankThree.PartOne.KFU.isQuasisimple_unitarySU_three hUFD (by omega)).1
  have hcentSU : Nat.card (Subgroup.center ↥H) = 3 := by
    dsimp only [H]
    exact CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.card_center_statedSU_three
      (⟨a, by ring⟩ : Odd (2 * a + 1)) (by omega) hFcard2
  have hcentC : Nat.card (Subgroup.center ↥C) = 3 := by
    have hmap : Subgroup.map e.toMonoidHom (Subgroup.center ↥C) = Subgroup.center ↥H :=
      Subgroup.map_center_eq e
    rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hmap]
    exact hcentSU
  have hSUopen : CFSG.Open.IsQuasisimple ↥H :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mp hSU
  have hQ : CFSG.Open.IsQuasisimple ↥C := CFSG.Open.IsQuasisimple.of_mulEquiv e hSUopen
  have hYs : IsSimpleGroup ↥Y :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hY8
  have hcard : Nat.card ↥Y = 504 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_eight
      (CFSG.Blueprint.LieModel.statedClassicalModel hY8 (by decide))
  have hnc : ∃ a b : ↥Y, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcomm : IsMulCommutative ↥Y := IsMulCommutative.of_comm fun a b => hcon a b
    have hp := (@Group.is_simple_iff_prime_card ↥Y _ hcomm).mp hYs
    rw [hcard] at hp
    exact (by norm_num : ¬ (504 : ℕ).Prime) hp
  have hYperf : Group.IsPerfect ↥Y := ⟨hY.2.2.1⟩
  have hYcenter : Subgroup.center ↥Y = ⊥ :=
    CFSG.ComponentClassification.Helpers.center_eq_bot ↥Y hnc
  have hYne : Y ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥Y = 1 := by rw [hbot]; exact Subgroup.card_bot
    omega
  have hYC : Y = C :=
    k329inyg2_absorb (C := C) (Q := C) (Y := Y) le_rfl hY.1 hYne hQ hYperf hY.2.1
  rw [hYC] at hYcenter
  rw [hYcenter, Subgroup.card_bot] at hcentC
  omega

theorem k329exc_zdatum_component (S : Type) [Group S] (z : S) (hz : K329ZDatum S z) :
    orderOf z = 3 ∧ ∃ Y : Subgroup S,
      CFSG.Open.IsComponentOf Y (Subgroup.centralizer ({z} : Set S)) ∧
        LieModel ↥Y .PSL 2 2 3 := by
  obtain ⟨hz3, M, Y, hMC, hMn, -, hYM, hYn, hY⟩ := hz
  have hYs : IsSimpleGroup ↥Y :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hY
  have hcard : Nat.card ↥Y = 504 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_eight
      (CFSG.Blueprint.LieModel.statedClassicalModel hY (by decide))
  have hnc : ∃ a b : ↥Y, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcomm : IsMulCommutative ↥Y := IsMulCommutative.of_comm fun a b => hcon a b
    have hp := (@Group.is_simple_iff_prime_card ↥Y _ hcomm).mp hYs
    rw [hcard] at hp
    exact (by norm_num : ¬ (504 : ℕ).Prime) hp
  refine ⟨hz3, Y, ⟨hYM.trans hMC, ?_, CFSG.Holt.PointHull.isQuasisimple_of_isSimpleGroup hnc⟩, hY⟩
  exact .step hYM hYn (.step hMC hMn (.refl _))

theorem k329exc_suzuki_not_three_dvd (S : Type) [Group S]
    (n r e : ℕ) (hL : LieModel S .twistedB2 n r e) : ¬ 3 ∣ Nat.card S := by
  rcases hL with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · obtain ⟨-, a, -, hfa, hcard⟩ := CFSG.GH74.card_of_suzukiModel h
    have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    rw [hcard, hfa]
    generalize 2 ^ (2 * a + 1) = q at hq
    unfold CFSG.Open.ordSuzuki
    intro hd
    have h1 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hd with hd | hd
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hd with hd | hd <;> omega
    · omega

theorem k329ExceptionalYStatement_holds
    : k329ExceptionalYStatement := by
  intro S _ _ hS t n r e ht htH hL hr z hz
  obtain ⟨hz3, Y, hYc, hY8⟩ := k329exc_zdatum_component S z hz
  cases t with
  | PSL => exact absurd (by simp [classicalTags]) ht
  | PSU => exact absurd (by simp [classicalTags]) ht
  | PSp => exact absurd (by simp [classicalTags]) ht
  | POmegaOdd => exact absurd (by simp [classicalTags]) ht
  | POmegaPlus => exact absurd (by simp [classicalTags]) ht
  | POmegaMinus => exact absurd (by simp [classicalTags]) ht
  | G2 => exact Or.inl ⟨rfl, k329in_excY_G2 S hS n r e hL hr z hz3 Y hYc hY8⟩
  | F4 => exact absurd (by simp [k329HeavyTags]) htH
  | E6 => exact absurd (by simp [k329HeavyTags]) htH
  | E7 => exact absurd (by simp [k329HeavyTags]) htH
  | E8 => exact absurd (by simp [k329HeavyTags]) htH
  | twistedE6 => exact absurd (by simp [k329HeavyTags]) htH
  | trialityD4 =>
    exact Or.inr (Or.inl ⟨rfl, k329in_excY_trialityD4 S hS n r e hL hr z hz3 Y hYc hY8⟩)
  | twistedB2 =>
    exact absurd (hz3 ▸ orderOf_dvd_natCard z) (k329exc_suzuki_not_three_dvd S n r e hL)
  | twistedG2 =>
    obtain ⟨-, -, -, h3, -⟩ := hL.admissible
    exact absurd h3 hr
  | twistedF4 => exact (k329in_excY_twistedF4 S hS n r e hL hr z hz3 Y hYc hY8).elim
  | Tits => exact Or.inr (Or.inr rfl)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

module

public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Quasithin.Background.D2Thirteen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PSubgroupInfNormalNilpotentLePCore

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

section Abstract

theorem exists_isComponentOf_not_le_centralizer {Q : Type} [Group Q] [Finite Q]
    {A : Subgroup Q} (hA2 : IsPGroup 2 ↥A) (hO2 : CFSG.pCore 2 Q = ⊥) (hAne : A ≠ ⊥)
    (hF : ∀ p : (Nat.card Q).primeFactors, CFSG.pCore (p : ℕ) Q ≤
      Subgroup.centralizer (A : Set Q)) :
    ∃ E : Subgroup Q, CFSG.GorensteinWalter.IsComponentOf E ⊤ ∧
      ¬ A ≤ Subgroup.centralizer (E : Set Q) := by
  classical
  by_contra hall
  push Not at hall
  have hFeq : CFSG.fittingSubgroupOf (⊤ : Subgroup Q) = CFSG.fittingSubgroup Q :=
    CFSG.Adapters.fittingSubgroupOf_top_eq_foundations Q
  have hFeqGW : CFSG.GorensteinWalter.fittingSubgroupOf (⊤ : Subgroup Q) = CFSG.fittingSubgroup Q :=
    hFeq
  have hFA : CFSG.fittingSubgroup Q ≤ Subgroup.centralizer (A : Set Q) := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    exact iSup_le hF
  have hEA : CFSG.GorensteinWalter.componentLayerOf (⊤ : Subgroup Q) ≤
      Subgroup.centralizer (A : Set Q) :=
    sSup_le fun E hE => Subgroup.le_centralizer_iff.mp (hall E hE)
  have hXA : CFSG.GorensteinWalter.generalizedFittingSubgroupOf (⊤ : Subgroup Q) ≤
      Subgroup.centralizer (A : Set Q) := by
    unfold CFSG.GorensteinWalter.generalizedFittingSubgroupOf
    rw [hFeqGW]
    exact sup_le hFA hEA
  have hAC := Subgroup.le_centralizer_iff.mpr hXA
  have hAX := hAC.trans CFSG.Adapters.centralizer_generalizedFittingSubgroupOf_top_le
  have hAF : A ≤ CFSG.fittingSubgroup Q := by
    rw [← hFeqGW]
    exact (le_inf hAC hAX).trans
      CFSG.GorensteinWalter.centralizer_generalizedFitting_intersection_le_fittingSubgroupOf
  have hAO := (le_inf le_rfl hAF).trans
    (CFSG.GorensteinWalter.pSubgroup_inf_normal_nilpotent_le_pCore A (CFSG.fittingSubgroup Q) 2
      Nat.prime_two hA2 CFSG.fittingSubgroup_normal CFSG.fittingSubgroup_nilpotent)
  rw [hO2, le_bot_iff] at hAO
  exact hAne hAO

variable {G : Type*} [Group G]

theorem mem_cComp_of_isQuasisimple_of_isSubnormal {K X : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥K) (hK : IsSubnormal K X) : K ∈ cComp X := by
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hq.1
  refine ⟨?_, hperf, hK, ?_⟩
  · intro hb
    have := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot K).mp this hb
  · intro K' hlt hne hperf' hsub
    have hKX : K ≤ X := A3.subnormal_le hK
    have hsubK : IsSubnormal K' K := A3.subnormal_of_le_of_le hsub hlt.le hKX
    obtain ⟨P, hPK, hPn, hK'P⟩ := A3.subnormal_exists_normal_of_lt hsubK hlt
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hPn with h1 | h1
    · exact absurd (Subgroup.subgroupOf_eq_top.mp h1) (not_le_of_gt hPK)
    · apply hne
      rw [← hperf', Subgroup.commutator_eq_bot_iff_le_centralizer.mpr]
      intro x hx
      have hxP : x ∈ P := hK'P hx
      have hxc := Subgroup.mem_center_iff.mp
        (h1 (show (⟨x, hPK.le hxP⟩ : ↥K) ∈ P.subgroupOf K from hxP))
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      exact congrArg Subtype.val (hxc ⟨y, hlt.le hy⟩)

theorem isQuasisimple_of_gw {Q : Type*} [Group Q] (h : CFSG.GorensteinWalter.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨hnt, hcomm, hs⟩ := h
  refine ⟨Group.isPerfect_def.mpr hcomm, hs, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [← QuotientGroup.ker_mk' (Subgroup.center Q), _root_.commutator_def,
      ← Subgroup.map_eq_bot_iff, Subgroup.map_commutator, eq_bot_iff]
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, -, b, -, rfl⟩ := hy
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hab a b
    | one => exact Subgroup.one_mem _
    | mul x y _ _ hx hy => exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => exact Subgroup.inv_mem _ hx
  rw [hcomm] at hle
  have htriv : ∀ q : Q ⧸ Subgroup.center Q, q = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [QuotientGroup.eq_one_iff]
    exact hle trivial
  obtain ⟨a, b, hne⟩ := hs.exists_pair_ne
  exact hne ((htriv a).trans (htriv b).symm)

section Offender

variable {W : Type} [CommGroup W] [Finite W]

theorem pCoreOf_le_centralizer_of_mem_QhatStar (hW : ∀ w : W, w ^ 2 = 1)
    {X C A : Subgroup (MulAut W)} {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r < 2)
    (hA : A ∈ QhatStar X) (hCX : C ≤ X) (hXC : X ≤ Subgroup.normalizer (C : Set (MulAut W)))
    (hO2 : pCoreOf 2 X = ⊥) (h3 : ¬ 3 ∣ Nat.card C) {p : ℕ} (hp : p.Prime)
    (hpC : p ∣ Nat.card C) : pCoreOf p C ≤ Subgroup.centralizer (A : Set (MulAut W)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hle : pCoreOf p C ≤ pCoreOf p X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p ((pCoreOf_le p C).trans hCX)
      (hXC.trans (normalizer_le_normalizer_pCoreOf p C)) (pCoreOf_isPGroup p C)
  by_cases hp2 : p = 2
  · subst hp2
    rw [hO2] at hle
    exact hle.trans bot_le
  · have hbot : ⁅pCoreOf p X, A⁆ = ⊥ := by
      by_contra hne
      obtain ⟨h35, h5, -⟩ := D2_13 hW hr hA hp2 rfl hne
      rcases h35 with rfl | rfl
      · exact h3 hpC
      · have e := (h5 rfl).1
        rw [e] at hr2
        exact lt_irrefl _ hr2
    exact hle.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)

theorem exists_cComp_of_mem_QhatStar (hW : ∀ w : W, w ^ 2 = 1)
    {X C A : Subgroup (MulAut W)} {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r < 2)
    (hA : A ∈ QhatStar X) (hCX : C ≤ X) (hXC : X ≤ Subgroup.normalizer (C : Set (MulAut W)))
    (hO2 : pCoreOf 2 X = ⊥) (h3 : ¬ 3 ∣ Nat.card C) (hAC : A ≤ C) :
    ∃ L : Subgroup (MulAut W), L ≤ C ∧ L ∈ cComp X ∧ CFSG.IsQuasisimple ↥L ∧
      ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  have hA2p : IsPGroup 2 ↥A := hA2.2.2.isPGroup
  set A' := A.subgroupOf C with hA'
  have hA'2 : IsPGroup 2 ↥A' := hA2p.of_equiv (Subgroup.subgroupOfEquivOfLe hAC).symm
  have hA'ne : A' ≠ ⊥ := by
    intro hb
    apply hA2.ne_bot
    rw [eq_bot_iff]
    intro a ha
    have : (⟨a, hAC ha⟩ : ↥C) ∈ A' := ha
    rw [hb, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  have hCp2 : pCoreOf 2 C ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 C).trans hCX)
      (hXC.trans (normalizer_le_normalizer_pCoreOf 2 C)) (pCoreOf_isPGroup 2 C)
  have hO2C : CFSG.pCore 2 ↥C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxC : (x : MulAut W) ∈ pCoreOf 2 C := ⟨x, by assumption, rfl⟩
    have := hCp2 hxC
    rw [hO2, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Subtype.ext this
  have hF : ∀ p : (Nat.card ↥C).primeFactors, CFSG.pCore (p : ℕ) ↥C ≤
      Subgroup.centralizer (A' : Set ↥C) := by
    intro p x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hxC : (x : MulAut W) ∈ pCoreOf (p : ℕ) C := ⟨x, by assumption, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.mp
      (pCoreOf_le_centralizer_of_mem_QhatStar hW hr hr2 hA hCX hXC hO2 h3
        (Nat.prime_of_mem_primeFactors p.2) (Nat.dvd_of_mem_primeFactors p.2) hxC)
      a (Subgroup.mem_subgroupOf.mp ha)
    exact Subtype.ext hc
  obtain ⟨E, hE, hEA⟩ := exists_isComponentOf_not_le_centralizer hA'2 hO2C hA'ne hF
  obtain ⟨-, hEsub, hEq⟩ := hE
  set Lc := E.map C.subtype with hLcdef
  have hLcC : Lc ≤ C := by rw [hLcdef]; exact Subgroup.map_subtype_le E
  have hLq : CFSG.IsQuasisimple ↥Lc :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (E.equivMapOfInjective C.subtype C.subtype_injective)
      (isQuasisimple_of_gw hEq)
  have hEsub' : E.IsSubnormal :=
    Subgroup.IsSubnormal.trans le_top hEsub Subgroup.IsSubnormal.top
  have hLsubC : IsSubnormal Lc C := by
    rw [CFSG.Quasithin.isSubnormal_iff_subgroupOf hLcC, hLcdef]
    show ((E.map C.subtype).comap C.subtype).IsSubnormal
    rw [Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    exact hEsub'
  have hCsub : IsSubnormal C X :=
    A3.subnormal_of_normal hCX ((Subgroup.normal_subgroupOf_iff_le_normalizer hCX).mpr hXC)
  refine ⟨Lc, hLcC, mem_cComp_of_isQuasisimple_of_isSubnormal hLq
    (A3.subnormal_trans hLsubC hCsub), hLq, fun hAL => hEA ?_⟩
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have h1 := Subgroup.mem_centralizer_iff.mp (hAL (Subgroup.mem_subgroupOf.mp ha)) _
    ⟨e, he, rfl⟩
  exact Subtype.ext h1

end Offender

end Abstract

end CFSG.Quasithin.H13

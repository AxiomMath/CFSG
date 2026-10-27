module

public import CFSG.RankThree.PartOne.Q1327.Datum
public import CFSG.RankThree.PartOne.N143.Inspect613
import CFSG.RankThree.PartOne.N143.CaseB1Theta
public import CFSG.RankThree.PartOne.N143.Weyl613List

public section

namespace CFSG.RankThree.PartOne.Q1327

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320
  CFSG.RankThree.PartOne.K1327
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f r : ℕ} {R : Subgroup G} {s s' zs : MulAut E}

structure SDatum (p : ℕ) (E : Subgroup G) (R : Subgroup G) (s : MulAut E) (f : ℕ) (a : G)
    (N A₀ S : Subgroup G) : Prop where
  a_mem : a ∈ E
  a_ne : a ≠ 1
  N_le : N ≤ Subgroup.centralizer (({a} : Set G) ∪ (R : Set G))
  N_mem : N.subgroupOf (Subgroup.centralizer (({a} : Set G) ∪ (R : Set G))) ∈
    thetaComponents p ↥(Subgroup.centralizer (({a} : Set G) ∪ (R : Set G)))
  K_le : kZero p E s ≤ N
  N_model : StatedClassicalModel (↥N ⧸ aschbacherSolvableCore p ↥N) .PSU 3 2 f
  A₀_le : A₀ ≤ E
  A₀_elem : IsElementaryAbelian p ↥A₀
  A₀_card : Nat.card A₀ = p ^ 2
  S_le : S ≤ pElementSubgroup p (Subgroup.centralizer (R : Set G))
  S_ne : S ≠ ⊥
  S_two : IsPGroup 2 ↥S
  A₀_norm : A₀ ≤ Subgroup.normalizer (S : Set G)
  comm : ⁅S, A₀⁆ = S

omit [Finite G] in
theorem centralizer_union_eq (a : G) (R : Subgroup G) :
    Subgroup.centralizer (({a} : Set G) ∪ (R : Set G)) =
      Subgroup.centralizer (R : Set G) ⊓ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_union, Set.mem_singleton_iff,
    SetLike.mem_coe]
  constructor
  · intro hx
    refine ⟨fun h hh => hx h (Or.inr hh), fun h hh => ?_⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (show Commute a x from hx a (Or.inl rfl)) i).eq
  · rintro ⟨h1, h2⟩ h (rfl | hh)
    · exact h2 _ (Subgroup.mem_zpowers _)
    · exact h1 h hh

theorem N_le_Jc (hS : SchreierFor InCatalog) (H : Hyp G p A c L E f r R s s' zs) {Jc : Subgroup G}
    (hJ : JcData p E c R s Jc) {a : G} {N : Subgroup G} (haE : a ∈ E)
    (hN : N ≤ Subgroup.centralizer (({a} : Set G) ∪ (R : Set G)))
    (hNθ : N.subgroupOf (Subgroup.centralizer (({a} : Set G) ∪ (R : Set G))) ∈
      thetaComponents p ↥(Subgroup.centralizer (({a} : Set G) ∪ (R : Set G))))
    (hKN : kZero p E s ≤ N) : N ≤ Jc := by
  have h := H.h12
  have hp := h.prime
  have hMne := centralizer_R_ne_top H
  have hKM : ∀ H' : Subgroup G, H' ≤ Subgroup.centralizer (R : Set G) → CFSG.IsKGroup ↥H' :=
    fun H' hH' => h.setup.2.2.1 H' (ne_top_of_le_ne_top hMne hH')
  have hD : Subgroup.zpowers a ≤ Subgroup.centralizer (R : Set G) :=
    Subgroup.zpowers_le.mpr (E_le_centralizer_R H haE)
  have hDel : IsElementaryAbelian p ↥(Subgroup.zpowers a) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (Sec12Three.pow_eq_one_of_mem_E h haE)
  rw [centralizer_union_eq] at hN hNθ
  obtain ⟨J', hJ'θ, hNJ'⟩ := exists_thetaComponent_ge hp h.three_lt hS hKM h.evenRank_eq.le
    (Nat.card ↥(Subgroup.zpowers a)) (Subgroup.zpowers a) hD rfl hDel N hN hNθ
  obtain ⟨-, hKt, -, hKtM⟩ := class_facts H (Or.inl rfl) (mem_clsOf_self p E s)
  obtain ⟨hP0, hPperf⟩ := subgroupOf_ne_bot_perfect hKtM (KFAt.toLiftAt hKt).1
  have hKJc : (kZero p E s).subgroupOf (Subgroup.centralizer (R : Set G)) ≤
      Jc.subgroupOf (Subgroup.centralizer (R : Set G)) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hJ.K_le s (mem_clsOf_self p E s) (Subgroup.mem_subgroupOf.mp hx))
  have hKJ' : (kZero p E s).subgroupOf (Subgroup.centralizer (R : Set G)) ≤ J' := fun x hx =>
    hNJ' (Subgroup.mem_subgroupOf.mpr (hKN (Subgroup.mem_subgroupOf.mp hx)))
  have heq := theta_component_eq_of_perfect_le hp hJ'θ hJ.mem hP0 hPperf hKJ' hKJc
  intro x hx
  have hxM : x ∈ Subgroup.centralizer (R : Set G) := (hN hx).1
  have hxJ' : (⟨x, hxM⟩ : ↥(Subgroup.centralizer (R : Set G))) ∈ J' :=
    hNJ' (Subgroup.mem_subgroupOf.mpr hx)
  rw [heq] at hxJ'
  exact Subgroup.mem_subgroupOf.mp hxJ'

theorem listEven_Jc (hS : SchreierFor InCatalog) (hSLB : N143.SectionListBound)
    (hI613 : N143.Item613ListIdx) (H : Hyp G p A c L E f r R s s' zs) {Jc : Subgroup G}
    (hJ : JcData p E c R s Jc) (hθ : aschbacherSolvableCore p ↥Jc = Subgroup.center ↥Jc)
    (hp7 : 7 ≤ p) {A₀ S : Subgroup G} (hA₀E : A₀ ≤ E) (hA₀el : IsElementaryAbelian p ↥A₀)
    (hA₀card : Nat.card A₀ = p ^ 2) (hSJc : S ≤ Jc) (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 ↥S)
    (hA₀S : A₀ ≤ Subgroup.normalizer (S : Set G)) (hSA₀ : ⁅S, A₀⁆ = S) :
    N143.ListEvenItem (↥Jc ⧸ Subgroup.center ↥Jc) := by
  have h := H.h12
  have hp := h.prime
  have hK : CFSG.IsKGroup ↥(Subgroup.centralizer (R : Set G)) :=
    h.setup.2.2.1 _ (centralizer_R_ne_top H)
  have he : CFSG.Assembly.evenRank ↥(Subgroup.centralizer (R : Set G)) ≤ 3 :=
    (CFSG.RankThree.PartOne.Sec9A.evenRank_subgroup_le _).trans h.evenRank_eq.le
  have hA₀M : A₀ ≤ Subgroup.centralizer (R : Set G) := hA₀E.trans (E_le_centralizer_R H)
  have hSM : S ≤ Subgroup.centralizer (R : Set G) := hSJc.trans hJ.le_M
  have hA₀L : A₀.subgroupOf (Subgroup.centralizer (R : Set G)) ≤
      Jc.subgroupOf (Subgroup.centralizer (R : Set G)) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hJ.E_le (hA₀E (Subgroup.mem_subgroupOf.mp hx)))
  have hSL : S.subgroupOf (Subgroup.centralizer (R : Set G)) ≤
      Jc.subgroupOf (Subgroup.centralizer (R : Set G)) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hSJc (Subgroup.mem_subgroupOf.mp hx))
  have : Fact p.Prime := ⟨hp⟩
  have hel : IsElementaryAbelian p ↥(A₀.subgroupOf (Subgroup.centralizer (R : Set G))) := by
    have := hA₀el
    exact IsElementaryAbelian.subgroupOf hA₀M
  have hcard : p ^ 2 ≤ Nat.card ↥(A₀.subgroupOf (Subgroup.centralizer (R : Set G))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀M).toEquiv, hA₀card]
  let e1 := Subgroup.subgroupOfEquivOfLe hJ.le_M
  have hmap := aschbacherSolvableCore_map_mulEquiv hp e1
  have hnot : ¬ (S.subgroupOf (Subgroup.centralizer (R : Set G))).subgroupOf
      (Jc.subgroupOf (Subgroup.centralizer (R : Set G))) ≤
      aschbacherSolvableCore p ↥(Jc.subgroupOf (Subgroup.centralizer (R : Set G))) := by
    intro hle
    apply hS1
    have hcen : ∀ x ∈ S, ∀ j ∈ Jc, x * j = j * x := by
      intro x hx j hj
      have hy : (⟨⟨x, hSM hx⟩, Subgroup.mem_subgroupOf.mpr (hSJc hx)⟩ :
          ↥(Jc.subgroupOf (Subgroup.centralizer (R : Set G)))) ∈
          aschbacherSolvableCore p ↥(Jc.subgroupOf (Subgroup.centralizer (R : Set G))) :=
        hle (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hx))
      have hy' : e1 ⟨⟨x, hSM hx⟩, Subgroup.mem_subgroupOf.mpr (hSJc hx)⟩ ∈
          aschbacherSolvableCore p ↥Jc := by
        rw [← hmap]
        exact ⟨_, hy, rfl⟩
      rw [hθ] at hy'
      have := Subgroup.mem_center_iff.mp hy' ⟨j, hj⟩
      exact (congrArg Subtype.val this).symm
    rw [← hSA₀, eq_bot_iff, Subgroup.commutator_le]
    intro x hx a ha
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_commute.mpr (hcen x hx a (hJ.E_le (hA₀E ha)))
  have h613 := N143.item613With_listEven hSLB hI613 hS ↥(Subgroup.centralizer (R : Set G)) hK he p
    hp hp7 (Jc.subgroupOf (Subgroup.centralizer (R : Set G))) hJ.mem
    (A₀.subgroupOf (Subgroup.centralizer (R : Set G))) hel hcard hA₀L
    ⟨S.subgroupOf (Subgroup.centralizer (R : Set G)), N143.subgroupOf_ne_bot hSM hS1,
      N143.isPGroup_subgroupOf hSM hS2, hSL, hnot, N143.normalizer_subgroupOf_of_le hA₀S,
      (N143.commutator_subgroupOf hSM hA₀M).trans (by rw [hSA₀])⟩
  have hLK : CFSG.IsKGroup ↥(Jc.subgroupOf (Subgroup.centralizer (R : Set G))) :=
    N143.isKGroup_subgroup hK _
  have hLe : CFSG.Assembly.evenRank ↥(Jc.subgroupOf (Subgroup.centralizer (R : Set G))) ≤ 3 :=
    (CFSG.RankThree.PartOne.Sec9A.evenRank_subgroup_le _).trans he
  obtain ⟨hZ', -⟩ := N143.thetaQuotient_center_bot_and_list hSLB hLK hLe p hp hp7 hJ.mem.2.2
  let e2 := QuotientGroup.congr _ _ e1 hmap
  let e3 := QuotientGroup.quotientMulEquivOfEq hθ
  let e4 := (QuotientGroup.quotientMulEquivOfEq hZ').trans QuotientGroup.quotientBot
  exact N143.ListEvenItem.of_mulEquiv (e4.trans (e2.trans e3)) h613

theorem evenLie_Jc (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hTwo : TwoActionInputs)
    (hFull : K156.Full106Stmt) (hSLB : N143.SectionListBound) (hI613 : N143.Item613ListIdx)
    (hBridge : N143.EvenListBridge) (hP5 : KF1327P5) (H : Hyp G p A c L E f r R s s' zs)
    {Jc : Subgroup G} (hJ : JcData p E c R s Jc) {a : G} {N A₀ S : Subgroup G}
    (d : SDatum p E R s f a N A₀ S) :
    CFSG.Blueprint.EvenLieType (↥Jc ⧸ Subgroup.center ↥Jc) := by
  have h := H.h12
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  obtain ⟨hq, hθ⟩ := Jc_isQuasisimple hGA hS hRe hTwo hFull H hJ
  have hSJc : S ≤ Jc := S_le_Jc H hJ d.S_le d.A₀_le d.comm
  by_cases hp7 : 7 ≤ p
  · exact hBridge _ (listEven_Jc hS hSLB hI613 H hJ hθ hp7 d.A₀_le d.A₀_elem d.A₀_card hSJc d.S_ne
      d.S_two d.A₀_norm d.comm)
  · have hp5' : p = 5 := by
      have h56 : p = 5 ∨ p = 6 := by omega
      rcases h56 with h5 | h6
      · exact h5
      · exfalso
        rw [h6] at hp
        exact absurd hp (by norm_num)
    have hbase := t123Base_Jc hGA hS hRe hTwo hFull H hJ d.A₀_le d.A₀_elem d.A₀_card d.S_le d.S_ne
      d.S_two d.A₀_norm d.comm
    have hlist := list_Jc hSLB H hJ hq
    have hNJc := N_le_Jc hS H hJ d.a_mem d.N_le d.N_mem d.K_le
    subst hp5'
    exact hP5 G Jc A₀ E hbase hlist ⟨a, N, f, d.a_mem, d.a_ne,
      le_inf hNJc (d.N_le.trans (Subgroup.centralizer_le Set.subset_union_left)), H.hf2, H.hpf,
      d.N_model⟩

end CFSG.RankThree.PartOne.Q1327

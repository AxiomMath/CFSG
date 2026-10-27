module

public import CFSG.RankThree.PartOne.S12.Sec12A
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement Pointwise

section Auxiliary

variable {G : Type*} [Group G]

theorem thetaComponentsAt_eq_of_zpowers_eq (p : ℕ) {a b : G}
    (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    thetaComponentsAt p a = thetaComponentsAt p b := by
  have key : ∀ {x y : G}, x ∈ Subgroup.zpowers y → ∀ g : G,
      g ∈ Subgroup.centralizer ({y} : Set G) → g ∈ Subgroup.centralizer ({x} : Set G) := by
    intro x y hx g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    exact Commute.zpow_right hg k
  have hcent : Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({b} : Set G) := by
    ext g
    constructor
    · exact key (h ▸ Subgroup.mem_zpowers b) g
    · exact key (h.symm ▸ Subgroup.mem_zpowers a) g
  unfold thetaComponentsAt
  rw [hcent]

theorem le_of_isPerfect_of_forall_mul_central {L J : Subgroup G} (hL : Group.IsPerfect L)
    (hdec : ∀ l ∈ L, ∃ m ∈ L ⊓ J, ∃ z : G, (∀ x ∈ L, z * x = x * z) ∧ m * z = l) : L ≤ J := by
  have hcomm : ⁅L, L⁆ ≤ L ⊓ J := by
    rw [Subgroup.commutator_le]
    intro l₁ hl₁ l₂ hl₂
    obtain ⟨m₁, hm₁, z₁, hz₁, rfl⟩ := hdec l₁ hl₁
    obtain ⟨m₂, hm₂, z₂, hz₂, rfl⟩ := hdec l₂ hl₂
    have h1 : ⁅z₁, m₂ * z₂⁆ = 1 := Commute.commutator_eq (hz₁ _ hl₂)
    have h2 : ⁅m₁, z₂⁆ = 1 := Commute.commutator_eq (hz₂ m₁ hm₁.1 : Commute z₂ m₁).symm
    have hEq : ⁅m₁ * z₁, m₂ * z₂⁆ = ⁅m₁, m₂⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, h1, commutatorElement_mul_right_eq_mul_conj, h2]
      group
    rw [hEq]
    exact Subgroup.commutator_le_self _ (Subgroup.commutator_mem_commutator hm₁ hm₂)
  rw [Subgroup.isPerfect_iff.mp hL] at hcomm
  exact fun x hx => (hcomm hx).2

theorem commute_of_mem_theta_of_isQuasisimple [Finite G] {p : ℕ} (hp : p.Prime)
    {L : Subgroup G} (hLq : CFSG.IsQuasisimple L)
    {z : G} (hz : z ∈ inSubgroup (aschbacherSolvableCore p) L) {l : G} (hl : l ∈ L) :
    z * l = l * z := by
  obtain ⟨hθL, hnormal⟩ := theta_le_and_normal p L
  rcases quasisimple_normal_subgroups hLq hnormal with htop | hcen
  · exfalso
    have hLθ : L ≤ inSubgroup (aschbacherSolvableCore p) L :=
      Subgroup.subgroupOf_eq_top.mp htop
    have hθsol := (theta_solvable_and_not_dvd hp L).1
    have hLsol : Group.IsSolvable L :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLθ)
        (Subgroup.inclusion_injective hLθ)
    have hLperf := hLq.1
    have hLsimple := hLq.2.1
    have hLnt : Nontrivial L := (QuotientGroup.mk'_surjective (Subgroup.center L)).nontrivial
    exact Group.IsPerfect.not_isSolvable L hLsol
  · have hzc : (⟨z, hθL hz⟩ : L) ∈ Subgroup.center L := hcen (Subgroup.mem_subgroupOf.mpr hz)
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨l, hl⟩)).symm

theorem le_of_sectionTenRel_of_isQuasisimple [Finite G] {p : ℕ} (hp : p.Prime)
    {L J : Subgroup G} (hLq : CFSG.IsQuasisimple L) (hLJ : sectionTenRel p L J) : L ≤ J := by
  refine le_of_isPerfect_of_forall_mul_central hLq.1 fun l hl => ?_
  have hl' : l ∈ ((L ⊓ J : Subgroup G) : Set G) *
      ((inSubgroup (aschbacherSolvableCore p) L : Subgroup G) : Set G) := by
    rw [← sectionTenRel_iff.mp hLJ]
    exact hl
  obtain ⟨m, hm, z, hz, rfl⟩ := hl'
  exact ⟨m, hm, z, fun x hx => commute_of_mem_theta_of_isQuasisimple hp hLq hz hx, rfl⟩

end Auxiliary

theorem Sec12Hyp.mem_thetaCompZeroStarE
    (hSchreier : SchreierFor InCatalog) (hTwoAction : TwoActionInputs)
    (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple)
    {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E)
    (hCE : ∀ f ∈ E, (∀ l ∈ L, f * l = l * f) → f ∈ Subgroup.zpowers c) :
    L ∈ thetaCompZeroStarE p E := by
  have hp : p.Prime := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hAel : IsElementaryAbelian p A := h.A_elem
  have hEel : IsElementaryAbelian p E := h.E_elem
  have hLzs : L ∈ sectionTenZeroStar p A := h.L_mem.1.1
  have hLz : L ∈ sectionTenZero p A := (sectionTenZeroStar_subset p A).1 hLzs
  have hLq : CFSG.IsQuasisimple L := h106 hSchreier hTwoAction G p A h.setup L hLzs
  have hAadm : A ∈ admissibleTriples p E :=
    ⟨h.A_le_E, hAel, h.A_card, h.setup.2.2.2.2.2.2.2.2.1⟩
  refine ⟨⟨A, hAadm, hLz⟩, ⟨A, hAadm, hLz.1⟩, fun J hJ hLJ => ?_⟩
  obtain ⟨B, hB, hJB⟩ := hJ
  obtain ⟨f, hfB, hf1, hJf⟩ := mem_thetaComponentFamily_iff.mp hJB
  have hfE : f ∈ E := hB.1 hfB
  have hLJ' : L ≤ J := le_of_sectionTenRel_of_isQuasisimple hp hLq hLJ
  have hJC : J ≤ Subgroup.centralizer ({f} : Set G) := (mem_thetaComponentsAt_iff.mp hJf).1
  have hfc : f ∈ Subgroup.zpowers c := hCE f hfE fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hJC (hLJ' hl))).symm
  have hcord : orderOf c = p :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian c h.c_mem) h.c_ne_one
  have hford : orderOf f = p :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian f hfE) hf1
  have hzp : Subgroup.zpowers f = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hfc)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hford, hcord])
  have hJc : J ∈ thetaComponentsAt p c := thetaComponentsAt_eq_of_zpowers_eq p hzp ▸ hJf
  exact hLzs.2.2 J (mem_thetaComponentFamily_iff.mpr ⟨c, h.c_mem, h.c_ne_one, hJc⟩) hLJ

end CFSG.RankThree.PartOne

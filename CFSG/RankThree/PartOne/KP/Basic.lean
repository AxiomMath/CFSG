module

public import CFSG.RankThree.GroupTheory.SteinbergBMExceptionalComponentCentralization
public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Automorphisms
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Pointwise

theorem isElementaryAbelian_range_of_hom {H E : Type*} [Group H] [Group E] {p : ℕ}
    [IsElementaryAbelian p E] (α : E →* H) : IsElementaryAbelian p α.range := by
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨x, rfl⟩ := α.rangeRestrict_surjective a
    obtain ⟨y, rfl⟩ := α.rangeRestrict_surjective b
    rw [← map_mul, ← map_mul, (IsMulCommutative.is_comm (M := E)).comm x y]
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_
    obtain ⟨x, rfl⟩ := α.rangeRestrict_surjective y
    rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p E) x, map_one]

@[expose] def ElementaryRankAtMostOne (p : ℕ) (H : Type*) [Group H] : Prop :=
  ∀ A : Subgroup H, IsElementaryAbelian p A → Nat.card A ≤ p

namespace ElementaryRankAtMostOne

theorem of_isCyclic {H : Type*} [Group H] {p : ℕ} (hp : p.Prime)
    (hH : ∀ P : Subgroup H, IsPGroup p P → IsCyclic P) : ElementaryRankAtMostOne p H := by
  intro A hA
  have hcyc : IsCyclic A := hH A (IsElementaryAbelian.isPGroup p A)
  have hexp : Monoid.exponent A ∣ p := IsElementaryAbelian.exponent_dvd_p p A
  rw [IsCyclic.exponent_eq_card] at hexp
  exact Nat.le_of_dvd hp.pos hexp

theorem of_mulEquiv {T T' : Type*} [Group T] [Group T'] {p : ℕ} (e : T ≃* T')
    (h : ElementaryRankAtMostOne p (MulAut T')) : ElementaryRankAtMostOne p (MulAut T) := by
  intro A hA
  have hinj : Function.Injective ((MulAut.congr e).toMonoidHom.comp A.subtype) :=
    (MulAut.congr e).injective.comp Subtype.val_injective
  have hcard : Nat.card (A.map (MulAut.congr e).toMonoidHom) = Nat.card A :=
    card_map_of_injective_comp _ A hinj
  have hmap : IsElementaryAbelian p (A.map (MulAut.congr e).toMonoidHom) := by
    have := isElementaryAbelian_range_of_hom (p := p) ((MulAut.congr e).toMonoidHom.comp A.subtype)
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at this
  rw [← hcard]
  exact h _ hmap

theorem of_outer_card_lt {T : Type*} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    (hpT : ¬ p ∣ Nat.card T) (hout : Nat.card (Outer T) < p ^ 2) :
    ElementaryRankAtMostOne p (MulAut T) := by
  intro A hA
  have : Fact p.Prime := ⟨hp⟩
  have hAp : IsPGroup p A := IsElementaryAbelian.isPGroup p A
  have hinj := injective_comp_of_isPGroup (QuotientGroup.mk' (inner T))
    (by rw [QuotientGroup.ker_mk']; exact coprime_card_inner hp hpT) hAp
  have hcard : Nat.card (A.map (QuotientGroup.mk' (inner T))) = Nat.card A :=
    card_map_of_injective_comp _ A hinj
  have hle : Nat.card A ≤ Nat.card (Outer T) := by
    rw [← hcard]
    exact Subgroup.card_le_card_group _
  obtain ⟨k, hk⟩ := hAp.exists_card_eq
  by_contra hgt
  rw [not_le, hk] at hgt
  have hk2 : 2 ≤ k := by
    by_contra hk1
    have hk' : k < 2 := by omega
    interval_cases k
    · simp at hgt
      have := hp.one_lt
      omega
    · simp at hgt
  have : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
  omega

theorem of_not_dvd_outer {T : Type*} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    (hpT : ¬ p ∣ Nat.card T) (hpO : ¬ p ∣ Nat.card (Outer T)) :
    ElementaryRankAtMostOne p (MulAut T) := by
  intro A hA
  have : Fact p.Prime := ⟨hp⟩
  have hAp : IsPGroup p A := IsElementaryAbelian.isPGroup p A
  have hinj := injective_comp_of_isPGroup (QuotientGroup.mk' (inner T))
    (by rw [QuotientGroup.ker_mk']; exact coprime_card_inner hp hpT) hAp
  have hcard : Nat.card (A.map (QuotientGroup.mk' (inner T))) = Nat.card A :=
    card_map_of_injective_comp _ A hinj
  have hdvd : Nat.card A ∣ Nat.card (Outer T) := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk⟩ := hAp.exists_card_eq
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [hk, pow_zero]
    exact hp.one_lt.le
  · exact absurd ((dvd_pow_self p hk0.ne').trans (hk ▸ hdvd)) hpO

end ElementaryRankAtMostOne

theorem le_card_ker_of_elementaryRankAtMostOne {H : Type*} [Group H] {p : ℕ} (hp : p.Prime)
    (hH : ElementaryRankAtMostOne p H) {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian p E] (hE : Nat.card E = p ^ 2) (α : E →* H) :
    p ≤ Nat.card α.ker := by
  have hle : Nat.card α.range ≤ p := hH _ (isElementaryAbelian_range_of_hom α)
  have hsplit : Nat.card E = Nat.card α.range * Nat.card α.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv]
  refine le_of_not_gt fun hlt => ?_
  have h1 : Nat.card α.range * Nat.card α.ker < p * p :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hle) (Nat.mul_lt_mul_of_pos_left hlt hp.pos)
  rw [← hsplit, hE, sq] at h1
  exact lt_irrefl _ h1

theorem componentLocalCoreCentralizes_of_le_card {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElementaryAbelian p E)
    (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G}
    (hL : IsComponent L)
    (hXL : ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ≤
      normalizer (L : Set G))
    (hcard : p ≤ Nat.card (E ⊓ centralizer (L : Set G) : Subgroup G)) :
    ComponentLocalCoreCentralizes p E t L := by
  obtain ⟨hset, hX, hI, hW⟩ :=
    SteinbergBM.plane_core_product_centralizes_of_le_card hp hp2 hE hEcard ht ht1 hL hXL hcard
  exact ⟨hset, hW.trans (Subgroup.centralizer_le_normalizer _), hX, hI, hW⟩

theorem component_local_core_centralizes_of_rank_le_one {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElementaryAbelian p E)
    (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G}
    (hL : IsComponent L) (hEL : E ≤ normalizer (L : Set G))
    (hXL : ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ≤
      normalizer (L : Set G))
    (hrank : ElementaryRankAtMostOne p (MulAut (L ⧸ center L))) :
    p ≤ Nat.card (E ⊓ centralizer (L : Set G) : Subgroup G) ∧
      ComponentLocalCoreCentralizes p E t L := by
  have := hE
  have : Group.IsPerfect L := hL.1.1
  have hcard : p ≤ Nat.card (E ⊓ centralizer (L : Set G) : Subgroup G) := by
    have h := le_card_ker_of_elementaryRankAtMostOne hp hrank hEcard
      ((Finkelstein1977.automizer L).comp (inclusion hEL))
    rwa [SteinbergBM.card_ker_automizer_comp_inclusion hEL] at h
  exact ⟨hcard, componentLocalCoreCentralizes_of_le_card hp hp2 hE hEcard ht ht1 hL hXL hcard⟩

theorem le_centralizer_of_range_eq_bot {G : Type*} [Group G] {E L : Subgroup G}
    [Group.IsPerfect L] (hEL : E ≤ normalizer (L : Set G))
    (h : ((Finkelstein1977.automizer L).comp (inclusion hEL)).range = ⊥) :
    E ≤ centralizer (L : Set G) := by
  intro x hx
  have hmem : ((Finkelstein1977.automizer L).comp (inclusion hEL)) ⟨x, hx⟩ ∈
      ((Finkelstein1977.automizer L).comp (inclusion hEL)).range := ⟨⟨x, hx⟩, rfl⟩
  rw [h] at hmem
  have h1 : ((Finkelstein1977.automizer L).comp (inclusion hEL)) ⟨x, hx⟩ = 1 :=
    Subgroup.mem_bot.mp hmem
  exact (Finkelstein1977.automizer_eq_one_iff L (inclusion hEL ⟨x, hx⟩)).mp h1

end CFSG.RankThree.PartOne

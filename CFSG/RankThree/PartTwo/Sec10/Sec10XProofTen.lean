module

public import CFSG.RankThree.PartTwo.Sec10.Sec10XProofThirteen
public import CFSG.RankThree.PartTwo.Sec10.Sec10XProofSym

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)


@[expose] def Step1010U : Prop :=
  Sec4.Item4_5 →
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Sec10Std G A c L a R →
      sec10U L a ∈ fourGroupsMinus A ∧
        sec10U L a = inSubgroup (CFSG.pCore 2)
          (Subgroup.centralizer ((Subgroup.closure {c, a} : Subgroup G) : Set G)) ∧
        sec10U L a ∈
          maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2)

@[expose] def Step1010 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Sec10Std G A c L a R →
      sec10U L a ∈ fourGroupsMinus A ∧
        (sec10U L a ≤ inSubgroup (aschbacherSolvableCore 3)
            (Subgroup.centralizer ({a} : Set G)) ∨
          ∃ Y ∈ thetaComponentsAt 3 a, sec10U L a ≤ Y ∧
            (Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* projSL 2 (GaloisField 3 3)) ∨
              Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
              Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* CFSG.Blueprint.NativeSporadic.M12)) ∧
            ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (sec10U L a : Set G) ⊓
                Subgroup.centralizer ({a} : Set G)),
              Subgroup.closure ({c, a} : Set G)⁆ ≤
              inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)))

namespace Sec10XProof

section Transport


variable {G : Type} [Group G]

theorem mem_normalizer_of_mem_normalizer_subgroupOf {K H : Subgroup G} (hKH : K ≤ H) {x : H}
    (hx : x ∈ Subgroup.normalizer ((K.subgroupOf H : Subgroup H) : Set H)) :
    (x : G) ∈ Subgroup.normalizer (K : Set G) := by
  have := mem_normalizer_map_subtype hx
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKH] at this

theorem mem_normalizer_subgroupOf_of_mem_normalizer {K H : Subgroup G} {x : H}
    (hx : (x : G) ∈ Subgroup.normalizer (K : Set G)) :
    x ∈ Subgroup.normalizer ((K.subgroupOf H : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simpa using hx y

end Transport

section Std

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem pRank_centralizer_eq_three (h : Sec10Std G A c L a R) {H : Subgroup G} (hAH : A ≤ H) :
    CFSG.Open.pRank 3 (Subgroup.centralizer ((A.subgroupOf H : Subgroup H) : Set H)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply IsGreatest.csSup_eq
  refine ⟨⟨A.subgroupOf H, ?_, isElemAbelian_subgroupOf H h.mem_partTwoF.1, ?_⟩, ?_⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (h.comm (Subgroup.mem_subgroupOf.mp hy) (Subgroup.mem_subgroupOf.mp hx))
  · rw [card_subgroupOf_of_le hAH, h.card_eq]
    norm_num
  · rintro k ⟨E, hE, hEe, hEk⟩
    have hEA : E.map H.subtype ≤ A := by
      rintro _ ⟨x, hx, rfl⟩
      have hx3 : (x : G) ^ 3 = 1 := by simpa using congrArg Subtype.val (hEe.2 x hx)
      refine Sec15.mem_of_mem_partTwoF h.mem_partTwoF hx3 fun y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hE hx) ⟨y, hAH hy⟩
        (Subgroup.mem_subgroupOf.mpr hy))
    have hcard := Subgroup.card_le_of_le hEA
    rw [Subgroup.card_map_of_injective H.subtype_injective, hEk, h.card_eq] at hcard
    by_contra hk
    have h81 : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem closure_c_a_inf_sup (h : Sec10Std G A c L a R) {d : G} (hd3 : orderOf d = 3)
    (hA : A = Subgroup.closure {c, a, d}) :
    Subgroup.closure ({c, a} : Set G) ⊓ Subgroup.zpowers d = ⊥ ∧
      Subgroup.closure ({c, a} : Set G) ⊔ Subgroup.zpowers d = A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsup : Subgroup.closure ({c, a} : Set G) ⊔ Subgroup.zpowers d = A := by
    rw [hA, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  refine ⟨?_, hsup⟩
  have hB9 : Nat.card (Subgroup.closure ({c, a} : Set G)) = 9 := by
    rw [Set.pair_comm]
    exact card_closure_a_c h
  have hdvd : Nat.card (Subgroup.closure ({c, a} : Set G) ⊓ Subgroup.zpowers d :
      Subgroup G) ∣ 3 := by
    rw [← hd3, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le inf_le_right
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have hle : Subgroup.zpowers d ≤ Subgroup.closure ({c, a} : Set G) := by
      have heq := Subgroup.eq_of_le_of_card_ge (inf_le_right :
        Subgroup.closure ({c, a} : Set G) ⊓ Subgroup.zpowers d ≤ Subgroup.zpowers d)
        (by rw [h3, Nat.card_zpowers, hd3])
      rw [← heq]
      exact inf_le_left
    rw [sup_eq_left.mpr hle] at hsup
    have := h.card_eq
    rw [← hsup, hB9] at this
    norm_num at this

theorem rank3II_10_10 (h462 : Sec4.Item4_62) (h97 : Sec9.Item97) (h108 : Item108)
    (h : Sec10Std G A c L a R) (hU : sec10U L a ∈ fourGroupsMinus A)
    (hUeq : sec10U L a = inSubgroup (CFSG.pCore 2)
      (Subgroup.centralizer ((Subgroup.closure {c, a} : Subgroup G) : Set G))) :
    sec10U L a ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) ∨
      ∃ Y ∈ thetaComponentsAt 3 a, sec10U L a ≤ Y ∧
        (Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* projSL 2 (GaloisField 3 3)) ∨
          Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
          Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* CFSG.Blueprint.NativeSporadic.M12)) ∧
        ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (sec10U L a : Set G) ⊓
            Subgroup.centralizer ({a} : Set G)),
          Subgroup.closure ({c, a} : Set G)⁆ ≤
          inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hdL, hd3, hAcl⟩ := exists_inf_eq_zpowers h97 h.toHyp91
  have hdA := h.d_mem_A hdL
  set U := sec10U L a with hUdef
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  have hAC : A ≤ Ca := le_centralizer_of_mem h h.a_mem
  have haC : a ∈ Ca := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hsec4 : SectionFourHyp Ca := h.toTheoremFourHyp.sectionFourHyp
    (Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp h.a_ne_one)
  set A' := A.subgroupOf Ca with hA'
  have hA'map : A'.map Ca.subtype = A := by
    rw [hA', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAC]
  have hA'E : Late.IsE27 A' :=
    ⟨isElemAbelian_subgroupOf Ca h.mem_partTwoF.1, (card_subgroupOf_of_le hAC).trans h.card_eq⟩
  set a' : Ca := ⟨a, haC⟩ with ha'
  have ha'A : a' ∈ A' := Subgroup.mem_subgroupOf.mpr h.a_mem
  have ha'Z : a' ∈ Subgroup.center Ca := Subgroup.mem_center_iff.mpr fun y =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)
  have ha'1 : a' ≠ 1 := fun h1 => h.a_ne_one (congrArg Subtype.val h1)
  set B := Subgroup.closure ({c, a} : Set G) with hB
  have hBA : B ≤ A := by
    rw [hB, Set.pair_comm]
    exact closure_a_c_le h
  have hBC : B ≤ Ca := hBA.trans hAC
  set B' := B.subgroupOf Ca with hB'
  have hB'map : B'.map Ca.subtype = B := by
    rw [hB', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBC]
  have hB'A' : B' ≤ A' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hBA (Subgroup.mem_subgroupOf.mp hx))
  have hB'card : Nat.card B' = 9 := by
    rw [card_subgroupOf_of_le hBC, hB, Set.pair_comm]
    exact card_closure_a_c h
  have hUL : U ≤ L ⊓ Ca := Subgroup.map_subtype_le _
  have hUC : U ≤ Ca := hUL.trans inf_le_right
  set U' := U.subgroupOf Ca with hU'
  have hU'map : U'.map Ca.subtype = U := by
    rw [hU', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hUC]
  obtain ⟨⟨-, hUe, hU4⟩, hUA⟩ := hU
  have hU'K : IsKleinFour U' :=
    Sec6.isKleinFour_of_isElemAbelian (isElemAbelian_subgroupOf Ca hUe)
      ((card_subgroupOf_of_le hUC).trans hU4)
  have hU'A : ⁅U', A'⁆ = U' := by
    apply Subgroup.map_injective Ca.subtype_injective
    rw [Subgroup.map_commutator, hU'map, hA'map]
    exact hUA.symm
  have hCB : Subgroup.centralizer (B : Set G) ≤ Ca :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.subset_closure (by simp)))
  have hU'eq : U' = inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (B' : Set Ca)) := by
    apply Subgroup.map_injective Ca.subtype_injective
    rw [hU'map, hB', centralizer_subgroupOf hBC,
      GroupTheory.SteinbergBY.map_inSubgroup_pCore_of_injective 2 Ca.subtype Ca.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hCB]
    exact hUeq
  set D' := (Subgroup.zpowers d).subgroupOf Ca with hD'
  have hdC : d ∈ Ca := hAC hdA
  have hDC : Subgroup.zpowers d ≤ Ca := Subgroup.zpowers_le.mpr hdC
  have hD'map : D'.map Ca.subtype = Subgroup.zpowers d := by
    rw [hD', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hDC]
  have hD'A' : D' ≤ A' := fun x hx => Subgroup.mem_subgroupOf.mpr
    ((Subgroup.zpowers_le.mpr hdA) (Subgroup.mem_subgroupOf.mp hx))
  obtain ⟨hBDinf, hBDsup⟩ := closure_c_a_inf_sup h hd3 hAcl
  have hB'D' : B' ⊓ D' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxBD : (x : G) ∈ B ⊓ Subgroup.zpowers d :=
      ⟨Subgroup.mem_subgroupOf.mp hx.1, Subgroup.mem_subgroupOf.mp hx.2⟩
    rw [hBDinf, Subgroup.mem_bot] at hxBD
    exact Subgroup.mem_bot.mpr (Subtype.ext hxBD)
  have hB'D'sup : B' ⊔ D' = A' := by
    apply Subgroup.map_injective Ca.subtype_injective
    rw [Subgroup.map_sup, hB'map, hD'map, hA'map]
    exact hBDsup
  have hND : Subgroup.normalizer (A' : Set Ca) ≤ Subgroup.normalizer (D' : Set Ca) := by
    intro x hx
    exact mem_normalizer_subgroupOf_of_mem_normalizer
      (h108 G A c L a R h d hdL (mem_normalizer_of_mem_normalizer_subgroupOf hAC hx))
  rcases h462 Ca hsec4 A' hA'E a' ha'A ha'Z ha'1 B' hB'A' hB'card U' hU'K hU'A hU'eq D' hD'A'
      hB'D' hB'D'sup hND (pRank_centralizer_eq_three h hAC) with h1 | ⟨Y', hY', hUY', hiso, hcomm⟩
  · left
    rw [← hU'map]
    exact Subgroup.map_mono h1
  · right
    refine ⟨Y'.map Ca.subtype, ⟨Y', hY', rfl⟩, hU'map ▸ Subgroup.map_mono hUY', ?_, ?_⟩
    · set eY := Sec4.thetaQuotCongr (Y'.equivMapOfInjective Ca.subtype Ca.subtype_injective).symm
      rcases hiso with he | he | he
      · obtain ⟨e⟩ := he
        exact Or.inl ⟨eY.trans e⟩
      · obtain ⟨e⟩ := he
        exact Or.inr (Or.inl ⟨eY.trans e⟩)
      · obtain ⟨e⟩ := he
        exact Or.inr (Or.inr ⟨eY.trans e⟩)
    · have hmap := Subgroup.map_mono (f := Ca.subtype) hcomm
      rw [Subgroup.map_commutator, centralizer_subgroupOf hUC,
        GroupTheory.SteinbergBY.map_inSubgroup_pCore_of_injective 2 Ca.subtype Ca.subtype_injective,
        Subgroup.subgroupOf_map_subtype, hB'map] at hmap
      exact hmap

end Std

end Sec10XProof

theorem step1010_of (h462 : Sec4.Item4_62) (h45 : Sec4.Item4_5) (h97 : Sec9.Item97)
    (h107 : Item107) (hU : Step1010U) : Step1010 := by
  intro G _ _ A c L a R h
  obtain ⟨hU1, hUeq, -⟩ := hU h45 G A c L a R h
  exact ⟨hU1, Sec10XProof.rank3II_10_10 h462 h97
    (item108_of_item97 h107 (rank3II_10_3 h45 h97) h97) h hU1 hUeq⟩

end CFSG.RankThree.PartTwo.Sec10

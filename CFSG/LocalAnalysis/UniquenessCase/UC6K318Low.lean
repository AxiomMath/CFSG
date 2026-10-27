module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K318Step
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588D3
public import CFSG.RankThree.SubgroupLists.IrreducibleGL3
public import CFSG.RankThree.PartOne.KF.F1322OmegaSeven
public import CFSG.Quasithin.EmptyFaithful.A38c15IrrHess
public import CFSG.Quasithin.EmptyFaithful.A38c15IrrCyc
public import CFSG.Quasithin.EmptyFaithful.A38c15IrrMono
public import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.K318

open Subgroup CFSG.Open CFSG.RepresentationTheory CFSG.RankThree.SubgroupLists

theorem statedClassicalModel_psl_two {s : ℕ} [Fact s.Prime] (hs5 : 5 ≤ s) {G : Type} [Group G]
    (e : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s)) :
    StatedClassicalModel G .PSL 2 s 1 :=
  ⟨⟨Fact.out, le_rfl, le_rfl, by simp only [pow_one, ne_eq, Prod.mk.injEq, true_and]; omega,
      by simp only [pow_one, ne_eq, Prod.mk.injEq, true_and]; omega⟩,
    ZMod s, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one],
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod s))⟩⟩

theorem simple_card_of_psl_two {s : ℕ} [Fact s.Prime] (hs5 : 5 ≤ s) {G : Type} [Group G]
    (e : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s)) :
    IsSimpleGroup G ∧ Nat.card G = ordA 1 s := by
  have h := statedClassicalModel_psl_two hs5 e
  refine ⟨CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel h, ?_⟩
  have := CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical h
  rw [pow_one] at this
  exact this

theorem statedClassicalModel_sl_three (q : ℕ) [Fact q.Prime] :
    StatedClassicalModel (StatedProj (StatedSL 3 (ZMod q))) .PSL 3 q 1 :=
  ⟨⟨Fact.out, le_rfl, by norm_num, by simp, by simp⟩, ZMod q, inferInstance, inferInstance,
    by rw [Nat.card_zmod, pow_one], ⟨MulEquiv.refl _⟩⟩

section Normal

variable {G : Type} [Group G]

theorem eq_of_normal_not_isSolvable {P H : Subgroup G} [Finite P] [Group.IsPerfect P]
    (hHP : H ≤ P) (hnorm : ∀ g ∈ P, ∀ x ∈ H, g * x * g⁻¹ ∈ H) (R : Subgroup P) [R.Normal]
    (hRs : Group.IsSolvable R) (hs : IsSimpleGroup (P ⧸ R)) (hH : ¬ Group.IsSolvable H) :
    H = P := by
  haveI : (H.subgroupOf P).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g g.2 n hn⟩
  rcases le_or_eq_top_of_normal hRs hs (H.subgroupOf P) with h | h
  · exfalso
    apply hH
    haveI := hRs
    have h1 : Group.IsSolvable (H.subgroupOf P) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion h)
        (Subgroup.inclusion_injective h)
    haveI := h1
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hHP).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hHP).symm.injective
  · exact le_antisymm hHP (Subgroup.subgroupOf_eq_top.1 h)

end Normal

theorem not_isSolvable_of_isQuasisimple {H : Type*} [Group H] (h : CFSG.IsQuasisimple H) :
    ¬ Group.IsSolvable H := by
  obtain ⟨hperf, hs, -⟩ := h
  have : Nontrivial H := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : Nontrivial (H ⧸ center H) := IsSimpleGroup.toNontrivial
    obtain ⟨a, b, hab⟩ := this.exists_pair_ne
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (congrArg _ (Subsingleton.elim a b))
  exact Group.IsPerfect.not_isSolvable H

theorem card_quotient_le {P : Type*} [Group P] [Finite P] (R : Subgroup P) :
    Nat.card (P ⧸ R) ≤ Nat.card P := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup R]
  exact Nat.le_mul_of_pos_right _ Nat.card_pos

theorem list318_of_dim_two {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    {P : Subgroup (GL (Fin 2) (ZMod q))} [Group.IsPerfect P] (R : Subgroup P) [R.Normal]
    (hRs : Group.IsSolvable R) (hs : IsSimpleGroup (P ⧸ R)) (r : ℕ) :
    N588.List318 r (Nat.card (P ⧸ R)) := by
  have hP : P ≠ ⊥ := by
    intro hbot
    have : Subsingleton P := by
      rw [hbot]
      infer_instance
    exact not_comm_of_simple hs fun a b => Subsingleton.elim _ _
  obtain ⟨-, -, hqs, ⟨s, hsp, hs5, -, ⟨e⟩⟩, -, -⟩ :=
    CFSG.SectionRank.Ccomm.perfect_prime_linear_recognition hq2 P hP
  haveI : Fact s.Prime := ⟨hsp⟩
  have hR : R = center P := eq_of_simple_quotients hRs hs hqs.2
  have hn : Nat.card (P ⧸ R) = ordA 1 s := by
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hR).toEquiv]
    exact (simple_card_of_psl_two hs5 e).2
  exact Or.inl ⟨s, hsp, by omega, Or.inl hn⟩

theorem comm_of_dim_le_one {F : Type*} [Field F] {d : ℕ} (hd : d ≤ 1) (a b : GL (Fin d) F) :
    a * b = b * a := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd with rfl | rfl
  · exact Units.ext (Matrix.ext fun i => Fin.elim0 i)
  · exact CFSG.SectionRank.Ccomm.GL_one_comm a b

theorem card_GL_three_three : Nat.card (GL (Fin 3) (ZMod 3)) = 11232 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod, Fin.prod_univ_three]
  norm_num

theorem card_GL_three_two : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod, Fin.prod_univ_three]
  norm_num

theorem card_alt (n : ℕ) (hn : 2 ≤ n) : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem list318_of_dim_three
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hq5 : 5 ≤ q)
    {P : Subgroup (GL (Fin 3) (ZMod q))} [Group.IsPerfect P]
    (hirr : IsIrreducibleMatrixRep P.subtype) (R : Subgroup P) [R.Normal]
    (hRs : Group.IsSolvable R) (hs : IsSimpleGroup (P ⧸ R)) (r : ℕ) :
    N588.List318 r (Nat.card (P ⧸ R)) ∨ Nat.card (P ⧸ R) ≤ 1080 := by
  classical
  have hq : q.Prime := Fact.out
  have hnsolv : ¬ Group.IsSolvable P := not_isSolvable_of_simple hs
  rcases irreducible_gl3_reduction hirr with ⟨H, hHG, hnorm, hHirr, hcyc, -, -⟩ | hmono |
      ⟨-, H, hHG, hnorm, hHirr, hcard, hext⟩ | ⟨H, hHG, hnorm, hqs, hHirr, hscal, hdet, hZ⟩
  · exact absurd (CFSG.Quasithin.A38c15.isSolvable_of_cyclic_normal hHG hnorm hHirr hcyc) hnsolv
  · exact absurd (CFSG.Quasithin.A38c15.isSolvable_of_isTransitiveMonomial hmono) hnsolv
  · exact absurd (CFSG.Quasithin.A38c15.isSolvable_of_extraspecial27_normal hHG hnorm hHirr
      hcard hext) hnsolv
  have hHP : H = P :=
    eq_of_normal_not_isSolvable hHG hnorm R hRs hs (not_isSolvable_of_isQuasisimple hqs)
  have hle : Nat.card (P ⧸ R) ≤ Nat.card H := hHP ▸ card_quotient_le R
  rcases quasisimple_cases hq2 hHG hnorm hqs hHirr hscal hdet hZ with h | ⟨M, hMt, hMd, hM⟩ |
      ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨-, hZ3, ⟨e⟩, -⟩
  ·
    obtain rfl : P = StatedSL 3 (ZMod q) := hHP.symm.trans h
    have hm := statedClassicalModel_sl_three q
    have hRN : R = (StatedScalars (Fin 3) (ZMod q)).subgroupOf (StatedSL 3 (ZMod q)) :=
      eq_of_simple_quotients hRs hs (CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hm)
    left
    refine Or.inl ⟨q, hq, hq2, Or.inr ?_⟩
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hRN).toEquiv]
    have := CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hm
    rw [pow_one] at this
    exact this
  ·
    obtain ⟨e₁⟩ := CFSG.RankThree.PartOne.KF1322.nonempty_omegaGL_equiv_psl2 hq5 hMt hMd
    have e : P ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod q) :=
      (MulEquiv.subgroupCongr (hHP.symm.trans hM)).trans e₁
    obtain ⟨hPs, hPc⟩ := simple_card_of_psl_two hq5 e
    have hRb : R = ⊥ :=
      eq_of_simple_quotients hRs hs ((MulEquiv.isSimpleGroup_congr QuotientGroup.quotientBot).2 hPs)
    left
    refine Or.inl ⟨q, hq, hq2, Or.inl ?_⟩
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hRb).trans
      QuotientGroup.quotientBot).toEquiv, hPc]
  ·
    right
    rw [Nat.card_congr e.toEquiv, card_alt 5 (by norm_num)] at hle
    exact hle.trans (by decide)
  ·
    right
    rw [Nat.card_congr e.toEquiv, card_GL_three_two] at hle
    exact hle.trans (by norm_num)
  ·
    right
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center H), hZ3,
      Nat.card_congr e.toEquiv, card_alt 6 (by norm_num)] at hle
    exact hle.trans (by decide)

theorem false_of_dim_le_three
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {d : ℕ} (hd : d ≤ 3)
    {P : Subgroup (GL (Fin d) (ZMod q))} [Group.IsPerfect P]
    (hirr : IsIrreducibleMatrixRep P.subtype) (R : Subgroup P) [R.Normal]
    (hRs : Group.IsSolvable R) (hs : IsSimpleGroup (P ⧸ R)) {r : ℕ}
    (hbig : 1081 ≤ Nat.card (P ⧸ R)) (h5 : 5 ∣ Nat.card (P ⧸ R))
    (h318 : ¬ N588.List318 r (Nat.card (P ⧸ R))) : False := by
  have hq : q.Prime := Fact.out
  rcases (show d ≤ 1 ∨ d = 2 ∨ d = 3 by omega) with hd1 | rfl | rfl
  · exact not_comm_of_simple hs fun a b => Subtype.ext (comm_of_dim_le_one hd1 _ _)
  · exact h318 (list318_of_dim_two hq2 R hRs hs r)
  by_cases hq5 : 5 ≤ q
  · rcases list318_of_dim_three hq2 hq5 hirr R hRs hs r with h | h
    · exact h318 h
    · omega
  have hq3 : q = 3 := by
    have h2 := hq.two_le
    have h4 : q ≠ 4 := by
      rintro rfl
      norm_num at hq
    omega
  subst hq3
  have hdvd : Nat.card (P ⧸ R) ∣ 11232 := by
    rw [← card_GL_three_three]
    exact (R.index_dvd_card).trans (Subgroup.card_subgroup_dvd_card P)
  have := h5.trans hdvd
  norm_num at this

end CFSG.LocalAnalysis.UniquenessCase.UC6.K318

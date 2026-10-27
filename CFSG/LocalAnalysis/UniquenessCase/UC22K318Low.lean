module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K318Red
public import CFSG.LocalAnalysis.UniquenessCase.UC6K318Low
import TauCeti.RepresentationTheory.CharacterTable.Solvable

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K318

open Subgroup CFSG.Open CFSG.RepresentationTheory CFSG.RankThree.SubgroupLists
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC6.K318 (not_comm_of_simple not_isSolvable_of_simple
  eq_of_simple_quotients exists_range_quotient_equiv exists_lower_of_reducible
  statedClassicalModel_psl_two simple_card_of_psl_two statedClassicalModel_sl_three
  eq_of_normal_not_isSolvable not_isSolvable_of_isQuasisimple comm_of_dim_le_one card_alt)

theorem lieModel_of_dim_two {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    {P : Subgroup (GL (Fin 2) (ZMod q))} [Group.IsPerfect P] (R : Subgroup P) [R.Normal]
    (hRs : Group.IsSolvable R) (hs : IsSimpleGroup (P ⧸ R)) :
    ∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ (s = q ∨ s = 5) ∧ LieModel (P ⧸ R) .PSL 2 s 1 := by
  have hP : P ≠ ⊥ := by
    intro hbot
    have : Subsingleton P := by
      rw [hbot]
      infer_instance
    exact not_comm_of_simple hs fun a b => Subsingleton.elim _ _
  obtain ⟨-, -, hqs, ⟨s, hsp, hs5, hsq, ⟨e⟩⟩, -, -⟩ :=
    CFSG.SectionRank.Ccomm.perfect_prime_linear_recognition hq2 P hP
  haveI : Fact s.Prime := ⟨hsp⟩
  have hR : R = center P := eq_of_simple_quotients hRs hs hqs.2
  exact ⟨s, hsp, by omega, hsq, Or.inl ⟨by decide,
    statedClassicalModel_psl_two hs5 ((QuotientGroup.quotientMulEquivOfEq hR).trans e)⟩⟩

theorem classification_of_dim_three
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    {P : Subgroup (GL (Fin 3) (ZMod q))} [Group.IsPerfect P]
    (hirr : IsIrreducibleMatrixRep P.subtype) (R : Subgroup P) [R.Normal]
    (hRs : Group.IsSolvable R) (hs : IsSimpleGroup (P ⧸ R)) :
    (∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ (s = q ∨ s = 5 ∨ s = 7) ∧ LieModel (P ⧸ R) .PSL 2 s 1) ∨
      LieModel (P ⧸ R) .PSL 3 q 1 ∨
      (Nonempty (P ⧸ R ≃* alternatingGroup (Fin 6)) ∧ Nat.card R = 3) := by
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
  have hbot : IsSimpleGroup P → Nonempty (P ⧸ R ≃* P) := fun hPs =>
    ⟨(QuotientGroup.quotientMulEquivOfEq (eq_of_simple_quotients hRs hs
      ((MulEquiv.isSimpleGroup_congr QuotientGroup.quotientBot).2 hPs))).trans
      QuotientGroup.quotientBot⟩
  rcases quasisimple_cases hq2 hHG hnorm hqs hHirr hscal hdet hZ with h | ⟨M, hMt, hMd, hM⟩ |
      ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨-, hZ3, ⟨e⟩, -⟩
  ·
    obtain rfl : P = StatedSL 3 (ZMod q) := hHP.symm.trans h
    have hm := statedClassicalModel_sl_three q
    have hRN : R = (StatedScalars (Fin 3) (ZMod q)).subgroupOf (StatedSL 3 (ZMod q)) :=
      eq_of_simple_quotients hRs hs (CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hm)
    exact Or.inr (Or.inl (LieModel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hRN).symm
      (Or.inl ⟨by decide, hm⟩)))
  ·
    by_cases hq5 : 5 ≤ q
    · obtain ⟨e₁⟩ := CFSG.RankThree.PartOne.KF1322.nonempty_omegaGL_equiv_psl2 hq5 hMt hMd
      have e : P ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod q) :=
        (MulEquiv.subgroupCongr (hHP.symm.trans hM)).trans e₁
      obtain ⟨eR⟩ := hbot (simple_card_of_psl_two hq5 e).1
      exact Or.inl ⟨q, hq, hq2, Or.inl rfl, Or.inl ⟨by decide,
        statedClassicalModel_psl_two hq5 (eR.trans e)⟩⟩
    exfalso
    have hq3 : q = 3 := by
      have h2 := hq.two_le
      have h4 : q ≠ 4 := by
        rintro rfl
        norm_num at hq
      omega
    subst hq3
    have hdvd : Nat.card H ∣ 2 ^ 3 * 3 ^ 1 := by
      have h1 := Subgroup.card_dvd_of_le
        (hM.le.trans (CFSG.RankThree.PartOne.LIT.omegaGL_le_soGL M))
      have h24 : (3 : ℕ) * (3 ^ 2 - 1) = 2 ^ 3 * 3 ^ 1 := by norm_num
      rw [card_soGL_three hq2 hMt hMd, h24] at h1
      exact h1
    exact not_isSolvable_of_isQuasisimple hqs
      (TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_three hdvd)
  ·
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have eP : P ≃* alternatingGroup (Fin 5) := (MulEquiv.subgroupCongr hHP.symm).trans e
    obtain ⟨e₅⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
      (ZMod 5) (Or.inr (Nat.card_zmod 5))
    obtain ⟨eR⟩ := hbot ((MulEquiv.isSimpleGroup_congr eP).2 inferInstance)
    exact Or.inl ⟨5, by norm_num, by norm_num, Or.inr (Or.inl rfl), Or.inl ⟨by decide,
      statedClassicalModel_psl_two le_rfl ((eR.trans eP).trans (e₅.symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod 5)).symm))⟩⟩
  ·
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨e₇⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
    have eP : P ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
      ((MulEquiv.subgroupCongr hHP.symm).trans e).trans e₇
    obtain ⟨eR⟩ := hbot (simple_card_of_psl_two (by norm_num) eP).1
    exact Or.inl ⟨7, by norm_num, by norm_num, Or.inr (Or.inr rfl), Or.inl ⟨by decide,
      statedClassicalModel_psl_two (by norm_num) (eR.trans eP)⟩⟩
  ·
    subst hHP
    have hR := eq_of_simple_quotients hRs hs hqs.2.1
    refine Or.inr (Or.inr ⟨⟨(QuotientGroup.quotientMulEquivOfEq hR).trans e⟩, ?_⟩)
    rw [hR]
    exact hZ3

theorem ordA_one_ne_360 {s : ℕ} (hs : s.Prime) : ordA 1 s ≠ 360 := by
  intro h
  rcases hs.eq_two_or_odd' with rfl | hodd
  · rw [UC6.N588.ordA_one_eq] at h
    norm_num at h
  have h2 := UC6.N588.two_mul_ordA_one hodd
  rw [h] at h2
  have h9 : s = 9 := UC6.N588.eq_of_l2_eq hs.one_lt.le (by norm_num)
    (h2.symm.trans (by norm_num))
  rw [h9] at hs
  norm_num at hs

theorem ordA_two_ne_360 {q : ℕ} (hq : q.Prime) : ordA 2 q ≠ 360 := by
  intro h
  obtain ⟨hlo, hhi⟩ := UC6.N588.bounds_l3 h.symm
  rcases hq.eq_two_or_odd' with rfl | hodd
  · norm_num at hlo
  have h3 : 3 ≤ q := by
    have h2 := hq.two_le
    obtain ⟨k, rfl⟩ := hodd
    omega
  have h5 := (UC6.N588.monotone_l3 h3).trans hhi
  norm_num at h5

theorem not_alt_six_of_psl_two {S : Type} [Group S] {s : ℕ} (hs : s.Prime)
    (h : LieModel S .PSL 2 s 1) : ¬ Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨e⟩
  rcases h with ⟨-, hm⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
  · have hc := CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hm
    rw [pow_one, Nat.card_congr e.toEquiv, card_alt 6 (by norm_num)] at hc
    exact ordA_one_ne_360 hs (hc.symm.trans (by decide))
  all_goals omega

theorem not_alt_six_of_psl_three {S : Type} [Group S] {q : ℕ} (hq : q.Prime)
    (h : LieModel S .PSL 3 q 1) : ¬ Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨e⟩
  rcases h with ⟨-, hm⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
  · have hc := CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hm
    rw [pow_one, Nat.card_congr e.toEquiv, card_alt 6 (by norm_num)] at hc
    exact ordA_two_ne_360 hq (hc.symm.trans (by decide))
  all_goals omega

theorem k318_of_list {S : Type} [Group S] {q n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h : (∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ (s = q ∨ s = 5 ∨ s = 7) ∧ LieModel S .PSL 2 s 1) ∨
      LieModel S .PSL 3 q 1 ∨ (Nonempty (S ≃* alternatingGroup (Fin 6)) ∧ 3 ∣ n)) :
    ((∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (LieModel S .PSL 2 p 1 ∨ LieModel S .PSL 3 p 1)) ∨
        Nonempty (S ≃* alternatingGroup (Fin 6))) ∧
      (Nonempty (S ≃* alternatingGroup (Fin 6)) → 3 ∣ n) := by
  rcases h with ⟨s, hs, hs2, -, h⟩ | h | ⟨hA, h3⟩
  · exact ⟨Or.inl ⟨s, hs, hs2, Or.inl h⟩, fun hA => (not_alt_six_of_psl_two hs h hA).elim⟩
  · exact ⟨Or.inl ⟨q, hq, hq2, Or.inr h⟩, fun hA => (not_alt_six_of_psl_three hq h hA).elim⟩
  · exact ⟨Or.inr hA, fun _ => h3⟩

variable {L : Type} [Group L] [Finite L]

theorem classification_of_dim_le_three
    [Group.IsPerfect L] {X : Subgroup L} [X.Normal]
    (hXs : Group.IsSolvable X) (hs : IsSimpleGroup (L ⧸ X)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {d : ℕ} (hd : d ≤ 3) (φ : L →* GL (Fin d) (ZMod q)) (hφ : φ.ker ≤ X) :
    (∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ (s = q ∨ s = 5 ∨ s = 7) ∧ LieModel (L ⧸ X) .PSL 2 s 1) ∨
      LieModel (L ⧸ X) .PSL 3 q 1 ∨
      (Nonempty (L ⧸ X ≃* alternatingGroup (Fin 6)) ∧ 3 ∣ Nat.card X) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  by_cases hirr : IsIrreducibleMatrixRep φ
  · obtain ⟨hRn, ⟨e⟩⟩ := exists_range_quotient_equiv φ X hφ
    haveI : Group.IsPerfect φ.range := Group.IsPerfect.range φ
    have hRs : Group.IsSolvable (X.map φ.rangeRestrict) := by
      haveI := hXs
      exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective φ.rangeRestrict X)
    have hsP : IsSimpleGroup (φ.range ⧸ X.map φ.rangeRestrict) :=
      (MulEquiv.isSimpleGroup_congr e).2 hs
    have hirrP : IsIrreducibleMatrixRep φ.range.subtype := fun W hW =>
      hirr W fun g w hw => hW ⟨φ g, g, rfl⟩ w hw
    rcases (show d ≤ 1 ∨ d = 2 ∨ d = 3 by omega) with hd1 | rfl | rfl
    · exact absurd (fun a b => Subtype.ext (comm_of_dim_le_one hd1 _ _)) (not_comm_of_simple hsP)
    · obtain ⟨s, hsp, hs2, hsq, h⟩ := lieModel_of_dim_two hq2 _ hRs hsP
      exact Or.inl ⟨s, hsp, hs2, hsq.imp_right Or.inl, h.of_mulEquiv e⟩
    · rcases classification_of_dim_three hq2 hirrP _ hRs hsP with ⟨s, hsp, hs2, hsq, h⟩ | h |
          ⟨⟨e'⟩, h3⟩
      · exact Or.inl ⟨s, hsp, hs2, hsq, h.of_mulEquiv e⟩
      · exact Or.inr (Or.inl (h.of_mulEquiv e))
      · refine Or.inr (Or.inr ⟨⟨e.symm.trans e'⟩, ?_⟩)
        rw [← h3]
        exact Subgroup.card_map_dvd X _
  · simp only [IsIrreducibleMatrixRep, not_forall] at hirr
    obtain ⟨W, hW, hWne⟩ := hirr
    push Not at hWne
    obtain ⟨d', hd', ψ, hψ⟩ := exists_lower_of_reducible hXs hs φ hφ W hW hWne.1 hWne.2
    exact ih d' hd' (by omega) ψ hψ

theorem classification_or_irreducible_four
    [Group.IsPerfect L] (X : Subgroup L) [X.Normal]
    (hXs : Group.IsSolvable X) (hX2 : CFSG.Open.pCoreOf 2 X = ⊥)
    (hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q X ≤ 3)
    (hcent : centralizer (X : Set L) ≤ X) (hs : IsSimpleGroup (L ⧸ X)) :
    ∃ q : ℕ, ∃ _ : Fact q.Prime, q ≠ 2 ∧ q ∣ Nat.card X ∧
      (((∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ (s = q ∨ s = 5 ∨ s = 7) ∧ LieModel (L ⧸ X) .PSL 2 s 1) ∨
          LieModel (L ⧸ X) .PSL 3 q 1 ∨
          (Nonempty (L ⧸ X ≃* alternatingGroup (Fin 6)) ∧ 3 ∣ Nat.card X)) ∨
        ∃ φ : L →* GL (Fin 4) (ZMod q), φ.ker ≤ X ∧ IsIrreducibleMatrixRep φ ∧
          CriticalSection X q 4 φ) := by
  classical
  obtain ⟨q, hq, hq2, hqd, d, hd, φ, hφ, hcs⟩ := exists_criticalSection X hXs hX2 hrank hcent hs
  haveI : Fact q.Prime := ⟨hq⟩
  refine ⟨q, inferInstance, hq2, hqd, ?_⟩
  rcases (show d ≤ 3 ∨ d = 4 by omega) with hd3 | rfl
  · exact Or.inl (classification_of_dim_le_three hXs hs hq hq2 hd3 φ hφ)
  by_cases hirr : IsIrreducibleMatrixRep φ
  · exact Or.inr ⟨φ, hφ, hirr, hcs⟩
  simp only [IsIrreducibleMatrixRep, not_forall] at hirr
  obtain ⟨W, hW, hWne⟩ := hirr
  push Not at hWne
  obtain ⟨d', hd', ψ, hψ⟩ := exists_lower_of_reducible hXs hs φ hφ W hW hWne.1 hWne.2
  exact Or.inl (classification_of_dim_le_three hXs hs hq hq2 (by omega) ψ hψ)

end CFSG.LocalAnalysis.UniquenessCase.UC22.K318

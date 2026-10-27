module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KU3Census
import CFSG.GH74.Generic.BProg.B2.PumpupTableL2
import CFSG.GH74.Generic.S3.L3FRank
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512L3SD
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512WrSylow
import CFSG.GH74.GLS.IVK.Proofs2.Lemma44b
import CFSG.CGT.PushingUpLit.SolK.GenFour
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Small
import CFSG.LocalAnalysis.EvenBN.GMS.GoldschmidtTypeInvolution
import CFSG.LocalAnalysis.SeitzReduction.RankOneLinearData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem closure_card_succ_of_relIndex_le_two {G : Type*} [Group G] [Finite G]
    {A P : Subgroup G} (hAP : A ≤ P) (hidx : A.relIndex P ≤ 2) (s : Finset G)
    (hs : Subgroup.closure (s : Set G) = A) :
    ∃ t : Finset G, t.card ≤ s.card + 1 ∧ Subgroup.closure (t : Set G) = P := by
  classical
  by_cases hAP_eq : A = P
  · exact ⟨s, by omega, by rw [hs, hAP_eq]⟩
  · have hpos : 0 < A.relIndex P := by
      haveI : A.IsFiniteRelIndex P :=
        Subgroup.isFiniteRelIndex_iff_finiteIndex.2 (by infer_instance)
      exact Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
    have hidx2 : A.relIndex P = 2 := by
      have hne1 : A.relIndex P ≠ 1 := by
        intro h
        exact hAP_eq (hAP.antisymm (Subgroup.relIndex_eq_one.mp h))
      omega
    obtain ⟨a, haP, haA, hcover⟩ :=
      Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp hidx2
    have hle : Subgroup.closure (s : Set G) ≤
        Subgroup.closure ((insert a⁻¹ s : Finset G) : Set G) := by
      apply Subgroup.closure_mono
      intro x hx
      exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hx))
    refine ⟨insert a⁻¹ s, Finset.card_insert_le _ _, ?_⟩
    apply le_antisymm
    · refine (Subgroup.closure_le P).mpr ?_
      intro x hx
      rw [Finset.mem_coe, Finset.mem_insert] at hx
      rcases hx with hxa | hxs
      · rw [hxa]
        exact P.inv_mem haP
      · have hxA : x ∈ A := by
          rw [← hs]
          exact Subgroup.subset_closure (Finset.mem_coe.mpr hxs)
        exact hAP hxA
    · intro b hbP
      rcases hcover b hbP with hbA | hbA
      · have hbA' : b * a ∈ Subgroup.closure (s : Set G) := by rwa [hs]
        have hb : b = (b * a) * a⁻¹ := by group
        rw [hb]
        exact Subgroup.mul_mem _ (hle hbA') (Subgroup.subset_closure (by simp))
      · rw [← hs] at hbA
        exact hle hbA

private theorem sectionalTwoRankLE_wreathed_three (m : ℕ) :
    CFSG.GH74.SectionalTwoRankLE (CFSG.Open.WreathedTwoGroup m) 3 := by
  intro P _
  obtain ⟨A, hAP, hAcomm, hAidx⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.wreathedTwoGroup_exists_isCommutative_relIndex_le_two m P
  obtain ⟨s, hs_card, hs_clos⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.wreathedTwoGroup_isCommutative_closure_two m A hAcomm
  obtain ⟨t, ht_card, ht_clos⟩ :=
    closure_card_succ_of_relIndex_le_two hAP hAidx s hs_clos
  exact ⟨t, by omega, ht_clos⟩

private theorem sectionalTwoRankLE_three_of_lieModel_psl_three_wreathed {X : Type} [Group X]
    [Finite X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : CFSG.Blueprint.LieModel X .PSL 3 p f) (hq : p ^ f % 4 = 1) :
    CFSG.GH74.SectionalTwoRankLE X 3 := by
  obtain ⟨-, F, iF, hfin, hF, he⟩ := h.statedClassicalModel (by decide)
  have hf : 1 ≤ f := (CFSG.GH74.Generic.S3.lieModel_prime h).2
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 X))
  obtain ⟨m, -, hS⟩ := CFSG.GH74.GLS.IVK.Proofs2.Lemma44b.sylow_L3_wr hp hp2
    (Or.inl ⟨rfl, F, iF, hfin, hF, he⟩) hq (Nat.one_lt_pow (by omega) hp.one_lt) S
  refine CFSG.CGT.PushingUpLit.SolK.sectionalTwoRankLE_of_sylow S ?_
  exact CFSG.GH74.SectionalTwoRankLE.of_mulEquiv hS.some.symm (sectionalTwoRankLE_wreathed_three m)

private theorem sectionalTwoRankLE_three_of_lieModel_psu_three_wreathed {X : Type} [Group X]
    [Finite X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : CFSG.Blueprint.LieModel X .PSU 3 p f) (hq : p ^ f % 4 = 3) :
    CFSG.GH74.SectionalTwoRankLE X 3 := by
  obtain ⟨-, F, iF, hfin, hF, he⟩ := h.statedClassicalModel (by decide)
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 X))
  obtain ⟨m, -, hS⟩ := CFSG.GH74.GLS.IVK.Proofs2.Lemma44b.sylow_U3_wr hp hp2
    (Or.inr ⟨rfl, F, iF, hfin, hF, he⟩) hq S
  refine CFSG.CGT.PushingUpLit.SolK.sectionalTwoRankLE_of_sylow S ?_
  exact CFSG.GH74.SectionalTwoRankLE.of_mulEquiv hS.some.symm (sectionalTwoRankLE_wreathed_three m)

private theorem sectionalTwoRankLE_three_of_census {X : Type} [Group X] [Finite X]
    {r f : ℕ} (hr : r ≠ 2)
    (hcase : LieModel X .PSL 2 r f ∨ (r ^ f % 3 = 2 ∧ LieModel X .PSL 3 r f) ∨
      (r ^ f % 3 = 1 ∧ LieModel X .PSU 3 r f)) :
    CFSG.GH74.SectionalTwoRankLE X 3 := by
  rcases hcase with h2 | ⟨_, h3⟩ | ⟨_, hU⟩
  · exact CFSG.GH74.SectionalTwoRankLE.mono (by omega)
      (CFSG.GH74.Generic.BProg.B2.PumpupTableL2.sectionalTwoRankLE_two_of_psl2_model hr h2)
  · have hp := (CFSG.GH74.Generic.S3.lieModel_prime h3).1
    rcases CFSG.LocalAnalysis.WeakClosure81.pow_mod_four_eq_one_or_three hp hr with h1 | h3mod
    · exact sectionalTwoRankLE_three_of_lieModel_psl_three_wreathed hp hr h3 h1
    · have h2 := CFSG.LocalAnalysis.WeakClosure81.sectionalTwoRankLE_two_of_lieModel_psl_three
        hp hr h3 h3mod
      exact CFSG.GH74.SectionalTwoRankLE.mono (by omega) h2
  · have hp := (CFSG.GH74.Generic.S3.lieModel_prime hU).1
    rcases CFSG.LocalAnalysis.WeakClosure81.pow_mod_four_eq_one_or_three hp hr with h1 | h3mod
    · exact CFSG.GH74.SectionalTwoRankLE.mono (by omega)
        (CFSG.LocalAnalysis.WeakClosure81.sectionalTwoRankLE_two_of_lieModel_psu_three hp hr hU h1)
    · exact sectionalTwoRankLE_three_of_lieModel_psu_three_wreathed hp hr hU h3mod

private theorem false_of_sectionalTwoRankLE_three {X : Type} [Group X] [Finite X]
    {K : Subgroup X} {m : ℕ} (hX : CFSG.GH74.SectionalTwoRankLE X 3)
    (hm : 4 ≤ m) (hL2 : IsL2 (Bar2 K) m) : False := by
  obtain ⟨e⟩ := CFSG.SeitzReduction.RankOne.nonempty_mulEquiv_psl2_of_lieModel hL2
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 (Bar2 K)))
  have hm2 : 2 ≤ m := by omega
  obtain ⟨hQcard, hQsq⟩ := CFSG.LocalAnalysis.EvenBN.GMS.sylow_facts_of_psl2 hm2 e Q
  have hBar : CFSG.GH74.SectionalTwoRankLE (Bar2 K) 3 :=
    CFSG.GH74.SectionalTwoRankLE.quotient (CFSG.pCore 2 ↥K)
      (CFSG.GH74.SectionalTwoRankLE.subgroup K hX)
  have hA : ∀ a : ↥Q, a ^ 2 = 1 := by
    intro a
    apply Subtype.ext
    simpa [pow_two] using hQsq a.1 a.2
  have hcard : 2 ^ 3 < Nat.card ↥Q := by
    change 2 ^ 3 < Nat.card ↥(Q : Subgroup (Bar2 K))
    rw [hQcard]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  haveI : IsMulCommutative ↥Q := CFSG.BenderSuzuki.isMulCommutative_of_forall_sq_one hA
  letI : CommGroup ↥Q := IsMulCommutative.instCommGroup
  exact CFSG.LocalAnalysis.WeakClosure81.not_sectionalTwoRankLE_of_injective_of_sq_eq_one
    hA hcard (Q : Subgroup (Bar2 K)).subtype (Q : Subgroup (Bar2 K)).subtype_injective hBar

theorem kU3CensusOdd_holds : KU3CensusOdd := by
  intro X _ _ r f hr hcase K hK m hm hL2
  exact false_of_sectionalTwoRankLE_three (sectionalTwoRankLE_three_of_census hr hcase) hm hL2

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

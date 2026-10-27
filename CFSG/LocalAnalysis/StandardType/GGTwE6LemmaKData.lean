module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LemmaKCheck
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordSound
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.StandardType.TwE6LemmaK

open CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.AGLEmbedding.R3

structure LemKFacts : Prop where
  length : (e6SylL ()).length = 81
  nodup : (e6SylL ()).Nodup
  mul_mem : ∀ A ∈ e6SylL (), ∀ B ∈ e6SylL (), mmulL 3 6 A B ∈ e6SylL ()
  cases : ∀ A ∈ e6SylL (), A = midL 3 6 ∨ nfix6 A < 81 ∨
    ∃ s ∈ lemKTab, A = mmulL 3 6 s.2.2.1 s.2.2.2 ∨ A = mmulL 3 6 s.2.2.2 s.2.2.1
  fix_orth : ∀ s ∈ lemKTab, ∀ A, (A = mmulL 3 6 s.2.2.1 s.2.2.2 ∨ A = mmulL 3 6 s.2.2.2 s.2.2.1) →
    ∀ v ∈ lemKFix A, lemKDot s.1 v % 3 = 0 ∧ lemKDot s.2.1 v % 3 = 0

private theorem aux_toMatL_mem_of_mem_wordsL {n : ℕ}
    (S : Submonoid (Matrix (Fin n) (Fin n) (ZMod 3))) :
    ∀ Bs : List (List ℕ), (∀ B ∈ Bs, toMatL 3 n B ∈ S) →
      ∀ A ∈ wordsL 3 n Bs, toMatL 3 n A ∈ S
  | [], _, A, hA => by
    rw [wordsL, List.mem_singleton] at hA
    subst hA
    rw [toMatL_midL]
    exact S.one_mem
  | B :: Bs, hB, A, hA => by
    simp only [wordsL, List.mem_flatMap, List.mem_map, List.mem_range] at hA
    obtain ⟨M, hM, a, -, rfl⟩ := hA
    rw [toMatL_mmulL, toMatL_mpowL]
    exact S.mul_mem (S.pow_mem (hB B List.mem_cons_self) a)
      (aux_toMatL_mem_of_mem_wordsL S Bs (fun B' hB' => hB B' (List.mem_cons_of_mem _ hB')) M hM)

private theorem aux_exists_mem_wordsL_eq_one {n : ℕ} :
    ∀ Bs : List (List ℕ), ∃ A ∈ wordsL 3 n Bs, toMatL 3 n A = 1
  | [] => ⟨midL 3 n, List.mem_singleton_self _, toMatL_midL 3 n⟩
  | B :: Bs => by
    obtain ⟨M, hM, hM1⟩ := aux_exists_mem_wordsL_eq_one (n := n) Bs
    refine ⟨mmulL 3 n (mpowL 3 n B 0) M, ?_, ?_⟩
    · simp only [wordsL, List.mem_flatMap, List.mem_map, List.mem_range]
      exact ⟨M, hM, 0, by norm_num, rfl⟩
    · rw [toMatL_mmulL, toMatL_mpowL, hM1, pow_zero, mul_one]

theorem lemKFacts_of_check (h : lemKCheck () = true) : LemKFacts := by
  simp only [lemKCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem, Bool.or_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨hlen, hnd⟩, hgen⟩, hcases⟩, horth⟩ := h
  refine ⟨hlen, hnd, ?_, ?_, ?_⟩
  ·
    intro A hA B hB
    let T : Submonoid (Matrix (Fin 6) (Fin 6) (ZMod 3)) :=
      Submonoid.closure {M | ∃ g ∈ lemKGens, M = toMatL 3 6 g}
    have hT : ∀ C ∈ e6SylL (), toMatL 3 6 C ∈ T := by
      intro C hC
      exact aux_toMatL_mem_of_mem_wordsL T lemKGens
        (fun g hg => Submonoid.subset_closure ⟨g, hg, rfl⟩) C hC
    have hT' : ∀ M ∈ T, ∃ C ∈ e6SylL (), toMatL 3 6 C = M := by
      intro M hM
      refine Submonoid.closure_induction_right
        (motive := fun m _ => ∃ C ∈ e6SylL (), toMatL 3 6 C = m) ?_ ?_ hM
      · obtain ⟨C, hC, hC1⟩ := aux_exists_mem_wordsL_eq_one (n := 6) lemKGens
        exact ⟨C, hC, hC1⟩
      · intro x _ y hy ih
        obtain ⟨C, hC, rfl⟩ := ih
        obtain ⟨g, hg, hgy⟩ := hy
        rw [hgy]
        exact ⟨mmulL 3 6 C g, hgen C hC g hg, toMatL_mmulL 3 6 C g⟩
    have hprod : toMatL 3 6 (mmulL 3 6 A B) ∈ T := by
      rw [toMatL_mmulL]
      exact T.mul_mem (hT A hA) (hT B hB)
    obtain ⟨C, hC, hCeq⟩ := hT' (toMatL 3 6 (mmulL 3 6 A B)) hprod
    obtain ⟨hClen, hCb⟩ := wordsL_spec 3 6 (by norm_num) lemKGens C hC
    have hCB : C = mmulL 3 6 A B :=
      toMatL_inj 3 6 hClen (length_mmulL 3 6 A B) hCb (lt_mmulL 3 6 (by norm_num) A B) hCeq
    rw [hCB] at hC
    exact hC
  ·
    intro A hA
    simpa only [or_assoc] using hcases A hA
  ·
    intro s hs A hA v hv
    have hmem : A ∈ [mmulL 3 6 s.2.2.1 s.2.2.2, mmulL 3 6 s.2.2.2 s.2.2.1] := by
      rcases hA with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    exact horth s hs A hmem v hv

theorem lemKFacts : LemKFacts :=
  lemKFacts_of_check lemKCheck_true

end CFSG.StandardType.TwE6LemmaK

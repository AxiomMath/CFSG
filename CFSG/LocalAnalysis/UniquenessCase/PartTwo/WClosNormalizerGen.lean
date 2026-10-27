module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThreeOne
public import CFSG.Quasithin.Background.HTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem normalizer_inf_centralizer_le_normalizer_wClos (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (i : ℕ) (hW : E3.wClos V i D.T ≤ centralizer (V : Set G)) :
    normalizer ((D.T ⊓ centralizer (V : Set G) : Subgroup G) : Set G) ≤
      normalizer (E3.wClos V i D.T : Set G) := by
  have hS : CFSG.Quasithin.IsSylowIn 2 D.T D.M :=
    CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM
  have hYH : D.T ⊓ centralizer (V : Set G) ≤ D.M :=
    fun _ hx => D.sylowM.le hx.1
  have hY : IsPGroup 2 (D.T ⊓ centralizer (V : Set G) : Subgroup G) :=
    (s15_13A_isSylowOf_inf_centralizer D h).isPGroup
  have hWY : E3.wClos V i D.T ≤ D.T ⊓ centralizer (V : Set G) :=
    le_inf (E3.wClos_le i D.T) hW
  exact E3.e3_15_normalizer hS hYH hY hWY

theorem normalizer_wClos_le_of_le_centralizer (D : Data G) (h129 : R129_1 D)
    (h61 : UC6.R6_1 D) (hne : D.sig.Nonempty)
    (hrk : ∀ p ∈ D.sig, 3 ≤ pRank p D.M) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (i : ℕ) (hW : E3.wClos V i D.T ≤ centralizer (V : Set G))
    (hWne : E3.wClos V i D.T ≠ ⊥) :
    normalizer (E3.wClos V i D.T : Set G) ≤ D.M ∧
      UniqueMax D.M (D.M ⊓ normalizer (E3.wClos V i D.T : Set G)) := by
  have hX2 : IsPGroup 2 (E3.wClos V i D.T) :=
    D.sylowM.isPGroup.to_le (E3.wClos_le i D.T)
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ centralizer (V : Set G))
      (D.M ⊓ centralizer (V : Set G)) := s15_13A_isSylowOf_inf_centralizer D h
  obtain ⟨p, hp, R, hRle, hRp, hRc⟩ := s15_13A_exists_noncyclic D h129 h61 hne hrk h hS
  have hRM : R ≤ D.M := hRle.trans inf_le_left
  have hRN : R ≤ normalizer (E3.wClos V i D.T : Set G) :=
    hRle.trans (inf_le_right.trans
      (normalizer_inf_centralizer_le_normalizer_wClos D h i hW))
  have hNM : normalizer (E3.wClos V i D.T : Set G) ≤ D.M :=
    normalizer_le_of_noncyclic D h61 hp hRM hRp hRc hWne hX2 hRN
  refine ⟨hNM, ?_⟩
  refine Set.ext fun N => ?_
  rw [Set.mem_singleton_iff]
  constructor
  · intro hN
    have hRleN : R ≤ N := (le_inf hRM hRN).trans hN.2
    have hmem : N ∈ calMOf R := ⟨hN.1, hRleN⟩
    rw [h61 p hp R hRM hRp hRc] at hmem
    exact Set.mem_singleton_iff.mp hmem
  · rintro rfl
    exact ⟨D.maxLocal, inf_le_left⟩

theorem aParam_autI_eq_aBar (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V) :
    E3.aParam (autI h.isElemAbelian D.M) = aBar D.M ⊥ V h.isElemAbelian := by
  show E3.aParam (autI h.isElemAbelian D.M) =
    E3.aParam (barSub (⊥ : Subgroup G) V h.isElemAbelian D.M)
  rw [TwelveTwentyThree.barSub_bot_eq_map_autI V h.isElemAbelian D.M,
    CFSG.Quasithin.H.aParam_map_congrHom]

theorem commutator_wClos_eq_bot_of_lt (D : Data G) (h111 : W3Thm111 G) {V : Subgroup G}
    (h : Hyp125 D ⊥ V) {i : ℕ} (hm : MBarGT D.M ⊥ V 2)
    (hi : aBar D.M ⊥ V h.isElemAbelian + i < mBar D.M ⊥ V h.isElemAbelian) :
    ⁅E3.wClos V i D.T, V⁆ = ⊥ := by
  have hV1 : InCalV1 D.M D.T V := by
    rcases h.1 with ⟨hW, -⟩ | ⟨hV0, -⟩
    · exact hW.1.1
    · exact absurd rfl hV0.1.1
  have hm' : MBarGT D.M ⊥ V (aBar D.M ⊥ V h.isElemAbelian + i) :=
    (h.mBarGT_iff_lt_mBar _).2 hi
  have hs : aBar D.M ⊥ V h.isElemAbelian + i < E3.sParam h.isElemAbelian := by
    have h1 := TwelveShort.lt_sParam_of_mBarGT D h111 hV1 hm hm'
    rwa [show hV1.1.2.2.2 = h.isElemAbelian from Subsingleton.elim _ _] at h1
  have ha : E3.aParam (autI h.isElemAbelian D.M) = aBar D.M ⊥ V h.isElemAbelian :=
    aParam_autI_eq_aBar D h
  have hi' : i < E3.sParam h.isElemAbelian - E3.aParam (autI h.isElemAbelian D.M) := by
    rw [ha]; omega
  exact (CFSG.LocalAnalysis.WeakClosure81.six_eleven_one_generic (V := V) (H := D.M)
    (S := D.T) (U := V) (Z := V) h.isElemAbelian
    (TwelveShort.isSylowIn_of_le D D.sylowM.le) h.pairFacts.le_normalizer h.isElemAbelian
    le_rfl hi').1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

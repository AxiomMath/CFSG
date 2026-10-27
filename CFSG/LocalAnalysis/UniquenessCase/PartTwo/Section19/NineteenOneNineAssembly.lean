module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenOneGamma
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenOneMinShapeAt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenGlueTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenNineVZero
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4BorelQuotientHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ComponentClassification.CatLeafProof (IsChar2LieShape lieModel_eq_of_isChar2LieShape)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem r19_1At_of (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp19 D V₀ V p L)
    (hglue : ∀ (hshape : IsL2 (Bar2 L) 2 ∨ IsU3 (Bar2 L) 2),
      R19_glue_2At D V₀ V p L h hshape)
    (h8 : ∀ K (hK : Ctx19_1 D V₀ V p L K), R19_8At D V₀ V p L K hK)
    (hSg : UC6S846.SigmaStd D)
    (h3 : ∀ K (hK : Ctx19_1 D V₀ V p L K), R19_3At D V₀ V p L K hK)
    (h4 : ∀ K (hK : Ctx19_1 D V₀ V p L K), R19_4At D V₀ V p L K hK)
    (hmin : ∀ K (hK : Ctx19_1 D V₀ V p L K), Gap19_1_minShapeAt D V₀ V p L K hK) :
    R19_1At D V₀ V p L h := by
  constructor
  · intro hL2
    obtain ⟨K, hK⟩ := hglue (Or.inl hL2)
    exact false_of_R19_8At_of_eight_le_gamma (h8 K hK)
      (eight_le_gammaN_of_invFix D hK hSg (h3 K hK) (h4 K hK)
        (invFixAt_of_minShapeAt D hK (hmin K hK) (h8 K hK).2.1 (h8 K hK).2.2.2))
  · intro hU3
    obtain ⟨K, hK⟩ := hglue (Or.inr hU3)
    exact false_of_R19_8At_of_eight_le_gamma (h8 K hK)
      (eight_le_gammaN_of_invFix D hK hSg (h3 K hK) (h4 K hK)
        (invFixAt_of_minShapeAt D hK (hmin K hK) (h8 K hK).2.1 (h8 K hK).2.2.2))

section Certified

private theorem one_lt_of_isU4 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (hV : Hyp19 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V) (h1767 : S17.R17_67At D V₀ V)
    {n : ℕ} (hU4 : IsU4 (Bar2 L) n) : 1 < n := by
  have hXL : conjClosure D.M L = L :=
    (conjClosure_eq_and_shape_of_R17_67 hV h1767 (Or.inr hU4)).1
  have h42 : S17.Concl17_42 D L L p := by
    have h' := h1742 L p (S17.calLp_subset_calC D p hV.hL) hV.hp
    rwa [hXL] at h'
  rcases h42 with h1 | h2 | h3 | h4 | h5
  · rcases h1 with hthin | ⟨m, hU3⟩ | hL3
    · exact absurd hthin (S17.not_thin8_of_isU4_bar2 hU4)
    · exact absurd
        (lieModel_eq_of_isChar2LieShape hU3 (by unfold IsChar2LieShape; simp) hU4).2.1
        (by omega)
    · exact absurd (CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique (by norm_num) hL3
        hU4).1 (by decide)
  · obtain ⟨m, x, -, -, -, hshape, -⟩ := h2
    rcases hshape with ⟨hL2, -⟩ | ⟨hSz, -⟩
    · exact absurd (lieModel_eq_of_isChar2LieShape hL2 S17.isChar2LieShape_PSL hU4).2.1
        (by decide)
    · exact absurd
        (lieModel_eq_of_isChar2LieShape hSz S17.isChar2LieShape_twistedB2 hU4).2.1
        (by decide)
  · obtain ⟨m, hU5m, -, -, -, -⟩ := h3
    exact absurd
      (lieModel_eq_of_isChar2LieShape hU5m (by unfold IsChar2LieShape; simp) hU4).2.1
      (by omega)
  · obtain ⟨m, hSp, -, -, -, -, -⟩ := h4
    rcases hSp with hSp | hG2
    · exact absurd (lieModel_eq_of_isChar2LieShape hSp S17.isChar2LieShape_PSp hU4).2.1
        (by decide)
    · exact absurd (lieModel_eq_of_isChar2LieShape hG2 (by unfold IsChar2LieShape; simp) hU4).2.1
        (by decide)
  · obtain ⟨m, hU4m, hm, -, -⟩ := h5
    have hmn : n = m :=
      (lieModel_eq_of_isChar2LieShape hU4m S17.isChar2LieShape_PSU_four hU4).2.2
    omega

theorem false_of_shape19_9 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp19 D V₀ V p L)
    (h171 : S17.R17_1At D V₀ V h.hyp125)
    (h1742 : S17.R17_42At D V₀ V) (h1767 : S17.R17_67At D V₀ V)
    (h8103 : F08.R8103 D) (h8106 : F08.R8106 D) (h127 : R127 D) (h869 : F08.R869 D)
    {n : ℕ} (hn : (IsU5 (Bar2 L) n ∧ n = 2) ∨ IsU4 (Bar2 L) n) : False := by
  have hV0 : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.big
  have hLc : L ∈ calC D.M := S17.calLp_subset_calC D p h.hL
  have hn2 : 2 ≤ n := by
    rcases hn with ⟨-, rfl⟩ | hU4
    · norm_num
    · have h1 : 1 < n := one_lt_of_isU4 h h1742 h1767 hU4
      omega
  obtain ⟨hXL, hshape67⟩ := conjClosure_eq_and_shape_of_R17_67 h h1767 hn
  have hnEven : Even n := by
    rcases hn with ⟨-, rfl⟩ | hU4
    · exact ⟨1, by norm_num⟩
    · rcases hshape67 with h2 | ⟨-, hpow⟩
      · rw [h2]
        exact ⟨1, by norm_num⟩
      · obtain ⟨k, hk⟩ := hpow
        have h1 : 1 < n := one_lt_of_isU4 h h1742 h1767 hU4
        rcases k with _ | k
        · rw [hk] at h1
          exact absurd h1 (by norm_num)
        · rw [hk]
          exact ⟨2 ^ k, by rw [pow_succ']; ring⟩
  have hns : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    not_isStronglyPEmbedded_of_KU4U5 h hV0 h171 hXL
      Inputs1719.kU4U5CartanQuotient_holds hn hn2 hnEven
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 L
  have h8102 : F08.Hyp8102 D L P p n := ⟨hLc, hn, hns, h.hp, hP⟩
  obtain ⟨-, -, -, -, ⟨B, hB⟩, -, -, -⟩ := h8103 L P p n h8102
  have h106 : pCoreOf 2 D.M ⊓ centralizer (B : Set G) = ⊥ := h8106 L P p n h8102 B hB
  have hV0core : V₀ ≤ pCoreOf 2 D.M := hyp19_v0_le_pCore h
  have hPL : P ≤ L := hP.le
  have hLV0 : L ≤ centralizer (V₀ : Set G) := le_centralizer_V0_of_shape19_9 h h127 h869 hn
  have hle : V₀ ≤ centralizer (B : Set G) :=
    Subgroup.le_centralizer_iff.mp ((hB.2.1.trans hPL).trans hLV0)
  have hbot : V₀ ≤ (⊥ : Subgroup G) := by
    rw [← h106]
    exact le_inf hV0core hle
  exact hV0 (le_bot_iff.1 hbot)

theorem r19_9At_of (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp19 D V₀ V p L)
    (h171 : S17.R17_1At D V₀ V h.hyp125)
    (h1742 : S17.R17_42At D V₀ V) (h1767 : S17.R17_67At D V₀ V)
    (h8103 : F08.R8103 D) (h8106 : F08.R8106 D) (h127 : R127 D) (h869 : F08.R869 D) :
    R19_9At D V₀ V p L h := by
  constructor
  · intro hU5
    exact false_of_shape19_9 h h171 h1742 h1767 h8103 h8106 h127 h869 (Or.inl ⟨hU5, rfl⟩)
  · intro hU4
    exact false_of_shape19_9 h h171 h1742 h1767 h8103 h8106 h127 h869 (Or.inr hU4)

theorem r19_1At_of_final
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h128 : W4Lem12_8) (hMin : Inputs1719.K_SU3MinDegree)
    (h36 : Inputs1719.W4Lem3_6)
    {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp19 D V₀ V p L)
    (h42 : S17.R17_42At D V₀ V) (h641 : S17.R17_64_1At D V₀ V) (h642 : S17.R17_64_2At D V₀ V)
    (h643 : S17.R17_64_3At D V₀ V) (h68 : S17.R17_68At D V₀ V)
    (h8 : ∀ K (hK : Ctx19_1 D V₀ V p L K), R19_8At D V₀ V p L K hK)
    (hSg : UC6S846.SigmaStd D)
    (h3 : ∀ K (hK : Ctx19_1 D V₀ V p L K), R19_3At D V₀ V p L K hK)
    (h4 : ∀ K (hK : Ctx19_1 D V₀ V p L K), R19_4At D V₀ V p L K hK) :
    R19_1At D V₀ V p L h :=
  r19_1At_of D h (fun hs => r19_glue_2At_of D h h42 h641 h642 h643 h68 hs) h8 hSg h3 h4
    (fun K hK => gap19_1_minShapeAt_of D hK h68
      (fun h82 h84 => not_isU3_of_ctx19_1 D hx h61 h127 h1214 h128 hMin h36 hK h82 h84))

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

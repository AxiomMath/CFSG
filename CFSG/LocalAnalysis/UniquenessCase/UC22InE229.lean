module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22tc
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASSec
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASShape
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CFa
import CFSG.LocalAnalysis.UniquenessCase.UC22P20za
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Sec
public import CFSG.Quasithin.Vol2.Ch11SecE3LieSzLow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC
open CFSG.Quasithin (IsSylowIn)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.WeakClosure81 (CFShape ShapeInEAS IsoInvPred inE_of_cfShape
  cfShape_quotient isSylowIn_barImage shapeInEAS_of_ambient_fstar
  quasithinIsSylowTwo_of_isSylowInTop nParam_le_of_lie_noSQ shapeInEAS_alt6_l3
  nonempty_mulEquiv_barInf_conj)

variable {G : Type} [Group G] [Finite G]

@[expose] def InE229Shape (n : ℕ) (X : Type) [Group X] : Prop :=
  IsSz X n ∨ IsL2 X n ∨ IsU3 X n ∨ IsL3 X n ∨ IsSp4 X n

theorem isoInvPred_inE229Shape (n : ℕ) : IsoInvPred (fun X _ => InE229Shape n X) := by
  rintro X Y _ _ ⟨e⟩ (h | h | h | h | h)
  · exact Or.inl (LieModel.of_mulEquiv e h)
  · exact Or.inr (Or.inl (LieModel.of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (LieModel.of_mulEquiv e h))))

theorem uc22ine229_nParamSingle_of_prod {X : Type} [Group X] {n : ℕ}
    (h : IsSz X n ∨ IsL2 X n ∨ (n = 3 ∧ IsSU3 X 3)) : NParamSingle X n := by
  rcases h with h | h | ⟨rfl, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

theorem uc22ine229_shape_quot {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X) {n : ℕ}
    (h : NParamSingle X n) : InE229Shape n (X ⧸ Subgroup.center X) := by
  rcases h with h | h | h | h | h
  · haveI := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h
    exact Or.inl (LieModel.quotient_center (uc22p21k_center_eq_bot hq) h)
  · haveI := LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
    exact Or.inr (Or.inl (LieModel.quotient_center (uc22p21k_center_eq_bot hq) h))
  · exact Or.inr (Or.inr (Or.inl h.2))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h.2)))
  · haveI := LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (LieModel.quotient_center (uc22p21k_center_eq_bot hq) h))))

theorem uc22ine229_cfShape (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) {n : ℕ}
    (hn : NParam L n) : CFShape ↥(L ⊔ D.T) (fun X _ => InE229Shape n X) := by
  intro Λ _ hcf hnc
  have hTs : Group.IsSolvable ↥D.T := by
    haveI : Group.IsNilpotent ↥D.T := D.sylowM.isPGroup.isNilpotent
    infer_instance
  obtain ⟨K, hK, hLK⟩ := hL.2.2.2
  have hsSup : sSup (CFSG.Quasithin.cComp L) = L := by
    rw [uc22p20p_cComp_eq_range D hL hK hLK, sSup_range]
    exact hLK.symm
  obtain ⟨C, hC, ⟨e⟩⟩ := uc22p20b_compFactorsOfCComp L D.T hL.1 hTs hsSup Λ hcf hnc
  obtain ⟨C₀, hC₀, hs⟩ : ∃ C₀ ∈ calC L, NParamSingle (Bar2 C₀) n := by
    rcases hn with hs | ⟨L₁, _, h₁, -, -, -, hsh⟩
    · exact ⟨L, ⟨IsSubnormal.refl L, hL.2.1, uc22pw_isQuasisimple_of_single D hL hs⟩, hs⟩
    · exact ⟨L₁, h₁, uc22ine229_nParamSingle_of_prod (hsh L₁ (Set.mem_insert _ _))⟩
  obtain ⟨t, -, rfl⟩ := uc22pw_swap D hL hC₀ (uc22p20p_mem_calC D hL hC)
  obtain ⟨e₁⟩ := nonempty_mulEquiv_barInf_conj t C₀
  obtain ⟨e₂⟩ := uc22p21k_barInf_equiv_of_calC hC₀
  exact isoInvPred_inE229Shape n _ _ ⟨e₂.symm.trans (e₁.symm.trans e)⟩
    (uc22ine229_shape_quot hC₀.2.2 hs)

theorem uc22ine229_shapeInEAS_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    ShapeInEAS n (fun X _ => InE229Shape n X) :=
  shapeInEAS_of_ambient_fstar (isoInvPred_inE229Shape n) fun Q _ _ _ hs _ hT hFT hP => by
    have hT' := quasithinIsSylowTwo_of_isSylowInTop hT
    refine (CFSG.Quasithin.E1.nParam_le_iff (by omega)).mp ?_
    rcases hP with h | h | h | h | h
    · exact (CFSG.Quasithin.Vol2.Ch11.SecE3.nParam_eq_of_isSz
        (LieModel.suzukiModel h).2 hs hT' hFT).le
    · exact nParam_le_of_lie_noSQ hn hs hT' hFT
        (Or.inl (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h))
    · exact nParam_le_of_lie_noSQ hn hs hT' hFT
        (Or.inr (Or.inl (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)))
    · exact nParam_le_of_lie_noSQ hn hs hT' hFT
        (Or.inr (Or.inr (Or.inl (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h))))
    · exact nParam_le_of_lie_noSQ hn hs hT' hFT
        (Or.inr (Or.inr (Or.inr (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h))))

theorem uc22ine229_inE_of_calL_of_two_le (D : Data G)
    {L : Subgroup G} (hL : L ∈ calL D.T D.M) {n : ℕ} (hn : NParam L n) (hn2 : 2 ≤ n) :
    CFSG.Quasithin.E1.InE n (⊤ : Subgroup (Bar2 (L ⊔ D.T))) :=
  inE_of_cfShape (by omega) (isSylowIn_barImage (uc22p22ta_isSylowIn D le_sup_right))
    (cfShape_quotient (CFSG.pCore 2 ↥(L ⊔ D.T)) (uc22ine229_cfShape D hL hn))
    (uc22ine229_shapeInEAS_of_two_le hn2)

theorem inE229_of_two_le (D : Data G) (Ch : Choice2011 G)
    (hn2 : H1930 D → ∀ c : Ctx22b D Ch, 2 ≤ c.n) : InE229 D Ch :=
  fun h1930 c => uc22ine229_inE_of_calL_of_two_le D c.hL0.1 c.hn (hn2 h1930 c)

theorem inE229_of_hn3 (D : Data G) (Ch : Choice2011 G)
    (hn3 : H1930 D → ∀ c : Ctx22b D Ch, 3 ≤ c.n) : InE229 D Ch :=
  inE229_of_two_le D Ch fun h1930 c => by have := hn3 h1930 c; omega

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

module

public import CFSG.Quasithin.Vol2.Ch10Reselect.Assembly701A
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.E6Hyp
public import CFSG.Quasithin.Vol2.Ch12Sec2Inputs
public import CFSG.Quasithin.Vol2.Ch7OrthFF
public import CFSG.Quasithin.Vol2.Ch7SL3Pair

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem not_isFFModule_of_hyp702A (hyp : Hyp7_0_2A G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L) :
    ¬ IsFFModule (autI hV ⊤) := by
  intro hFF
  have hle := autI_top_le_normalizer (T := T) (L := L) (I := I) hV hNM
  have hFF' : IsFFModule (Subgroup.normalizer (autI hV (fsuL0 T L) :
      Set (MulAut (IntMod (fsuV T I) hV)))) := by
    obtain ⟨A, hA, hA1, hA2, hcard⟩ := hFF
    exact ⟨A, hA.trans hle, hA1, hA2, hcard⟩
  have hsq : ∀ v : IntMod (fsuV T I) hV, v ^ 2 = 1 := IntMod.sq_eq_one
  obtain ⟨A, hA⟩ := ((B1_4_5 hsq _).out 1 2).mp hFF'
  exact hyp.notFF hV.1 ⟨A, hA⟩

theorem hypE61_of_tiA (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h3228 : Stmt3_2_2_eight) (hyp : Hyp7_0_2A G T L I)
    (hTI : IsTISetUnder (fsuV T I) (fsuM T L)) : E6.HypE61 T (fsuM T L) (fsuV T I) := by
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hU := lemma_1_2_7_three hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian h37 h38 h39
    hyp.fsu.sylow hyp.fsu.maximal
  have hVT := fsuV_le_T hyp.fsu hV hN
  have hTN : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  have hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    (le_fsuL0 T L).trans (le_sup_left.trans hN)
  have hQ : pCoreOf 2 (fsuL0 T L ⊔ T) = T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
    (h3228 G T L I hyp.fsu).2.2
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (fsuV T I : Set G) : Subgroup G) : Set G) := by
    rw [← hQ]
    exact (sup_le_sup_right (le_fsuL0 T L) T).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hTI' : IsTISetIn (fsuV T I) (fsuM T L) := by
    refine ⟨hVT.trans (le_sup_right.trans hU.1.2), fun g hg hgN => ?_⟩
    have h := hTI g hg hgN
    convert h using 2
    ext x
    rw [mem_conjSubgroup_iff, mem_conjugate_iff']
  refine ⟨hyp.fsu.simple, hyp.fsu.nonabelian, hyp.fsu.qtke, hyp.fsu.sylow,
    ⟨hU.1.1, le_sup_right.trans hU.1.2⟩, fsuV_ne_bot hyp.fsu, hV, hVT, hTN, hTI', ?_⟩
  refine ⟨⟨hU.1.1, inf_le_right.trans inf_le_left⟩, fun M' hM' => ?_⟩
  exact hU.2 M' ⟨hM'.1, (le_inf hLTQ (le_inf hU.1.2 (sup_le hLN hTN))).trans hM'.2⟩

theorem not_isFFStarOffender_autOnA (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hyp : Hyp7_0_2A G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    ∀ _ : IsMulCommutative ↥(fsuV T I), ¬ ∃ A : Subgroup (MulAut ↥(fsuV T I)),
      IsFFStarOffender (V := ↥(fsuV T I)) (autOn (fsuL0 T L ⊔ T) (fsuV T I)) A := by
  rintro _ ⟨A, hAX, hA1, hA2, hmax⟩
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hle : autOn (fsuL0 T L ⊔ T) (fsuV T I) ≤
      Subgroup.normalizer (autOn (fsuL0 T L) (fsuV T I) : Set (MulAut ↥(fsuV T I))) :=
    (autOn_le_autOn (fsuV T I) le_top).trans (autI_top_le_normalizer hV hNM)
  exact hyp.notFF inferInstance ⟨A, hAX.trans hle, hA1, hA2, hmax⟩

theorem not_isFFModule_autOn_supA (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hyp : Hyp7_0_2A G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    ∃ _ : IsMulCommutative ↥(fsuV T I),
      ¬ IsFFModule (V := ↥(fsuV T I)) (autOn (fsuL0 T L ⊔ T) (fsuV T I)) := by
  have hc : IsMulCommutative ↥(fsuV T I) := hV.1
  refine ⟨hc, fun hFF => ?_⟩
  obtain ⟨A, hA⟩ := B6.exists_isFFStarOffender hFF
  exact not_isFFStarOffender_autOnA h37 h38 h39 hyp hV hN hc ⟨A, hA⟩

theorem not_orthA (hyp : Hyp7_0_2A G T L I) {n : ℕ} (hn : 1 ≤ n)
    (h : ∃ _ : IsMulCommutative ↥(fsuV T I),
      BinaryOrthogonalFour (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥ n) : False := by
  obtain ⟨hc, h⟩ := h
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · exact hyp.notOrth hc ⟨n, h1, h⟩
  · have hn1 : n = 1 := le_antisymm h1 hn
    subst hn1
    obtain ⟨A, hA⟩ := B6.exists_isFFStarOffender
      (OrthFF.isFFModule_normalizer_of_binaryOrthogonalFour_one h)
    exact hyp.notFF hc ⟨A, hA⟩

theorem thompsonJ_le_centralizer_fsuVA (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hyp : Hyp7_0_2A G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    thompsonJ T ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hnFF := not_isFFModule_of_hyp702A hyp hV hNM
  have hVT := fsuV_le_T hyp.fsu hV hN
  have hTN : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  unfold thompsonJ
  refine iSup₂_le fun A hA => ?_
  by_contra hA1
  apply hnFF
  obtain ⟨B, hBX, hB1, hB2, hBcard⟩ := isFFModule_autOn hV hVT hTN hA.1 hA hA1
  exact ⟨B, hBX.trans (autI_mono hV le_top), hB1, hB2, hBcard⟩

end CFSG.Quasithin.H13

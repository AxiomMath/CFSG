module

public import CFSG.Quasithin.Vol2.Ch7SL3Pair
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem327TI
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch12Sec2Inputs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3
open scoped IsMulCommutative

theorem stmtFSUModule_of_eight (h3228 : Stmt3_2_2_eight) : StmtFSUModule := by
  intro G _ _ T L I hfsu
  obtain ⟨hVX, ⟨hnorm, helem, -⟩, -⟩ := h3228 G T L I hfsu
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩,
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVX).mp hnorm⟩
  · have h := helem.toIsMulCommutative.is_comm.comm
      (⟨⟨a, hVX a.2⟩, Subgroup.mem_subgroupOf.mpr a.2⟩ :
        ↥((conjClosure I T).subgroupOf (conjClosure L T ⊔ T)))
      ⟨⟨b, hVX b.2⟩, Subgroup.mem_subgroupOf.mpr b.2⟩
    apply Subtype.ext
    exact congrArg (fun z : ↥((conjClosure I T).subgroupOf (conjClosure L T ⊔ T)) =>
      ((z : ↥(conjClosure L T ⊔ T)) : G)) h
  · have h := elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (A := (conjClosure I T).subgroupOf (conjClosure L T ⊔ T)) ⟨x, hVX hx⟩
      (Subgroup.mem_subgroupOf.mpr hx)
    simpa using congrArg Subtype.val h

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem hypE61_of_ti (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h3228 : Stmt3_2_2_eight) (hyp : Hyp7_0_2 G T L I)
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

theorem isTISetUnder_of_le_normalizer (h325 : Stmt3_2_5) (hfsu : FSU G T L I)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) : IsTISetUnder (fsuV T I) (fsuM T L) :=
  TI325.of_stmt3_2_5_of_le_normalizer h325 hfsu hTL

theorem mParam_le_rParam_of_ti (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h3228 : Stmt3_2_2_eight) (h63 : ASInputs.AS_E_6_3)
    (hyp : Hyp7_0_2 G T L I) (hTI : IsTISetUnder (fsuV T I) (fsuM T L))
    (hV : IsElemAbelian 2 (fsuV T I)) (hm : 2 < mParam (autI hV ⊤)) :
    (mParam (autI hV ⊤) : ℕ∞) ≤ rParam (fsuV T I) := by
  obtain ⟨-, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hE := hypE61_of_ti h37 h38 h39 hmod h3228 hyp hTI
  have heq := autI_fsuM_eq_top hV hNM
  rw [← heq] at hm ⊢
  exact (h63 G T (fsuM T L) (fsuV T I) hV hE hm).1

end CFSG.Quasithin.H13

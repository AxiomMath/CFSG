module

public import CFSG.Quasithin.Vol2.Ch12Sec5Tr3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 S125St S125Tr S125Tr2 S125Tr3 S125W Matrix
open CFSG.LieType.SteinbergBR.BlockPar CFSG.LocalAnalysis.ComponentInitial.LinearFlag

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)

namespace S125L2G

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem hres_of {d e : ℕ} {J : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))}
    (hJQ : J ≤ (parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))))
    (h : CFSG.perfectResidual ↥(parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e)
      (ZMod 2))) = J.subgroupOf parQ) :
    (CFSG.perfectResidual ↥(parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e)
      (ZMod 2)))).map parQ.subtype = J := by
  rw [h, Subgroup.subgroupOf_map_subtype, inf_of_le_left hJQ]

theorem T_le_V (F : Frame125 T L V) (hTV : T ≤ Subgroup.normalizer (V : Set G)) :
    T ≤ Subgroup.normalizer ((F.V1 : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer ((F.V3 : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer ((F.V4 : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer ((F.V6 : Subgroup G) : Set G) :=
  ⟨T_le_normalizer_sub F hTV _ fun u hu => (coordFix_V1_iff u).2 (stabGam_of_upperTri hu 2),
    T_le_normalizer_sub F hTV _ fun u hu => (coordFix_V3_iff u).2 (stabGam_of_upperTri hu 3),
    T_le_normalizer_sub F hTV _ fun u hu => (coordFix_V4_iff u).2 (stabGam_of_upperTri hu 1),
    T_le_normalizer_sub F hTV _ fun u hu => (coordFix_V6_iff u).2 (stabGam_of_upperTri hu 4)⟩

theorem noO2_GL32 : S125Pb.NoO2 (GL (Fin 3) (ZMod 2) × GL (Fin 2) (ZMod 2)) :=
  S125Pb.noO2_prod (S125Pb.noO2_GL 3 S125Pb.noO2_SL3) (S125Pb.noO2_GL 2 S125Pb.noO2_SL2)

theorem noO2_GL23 : S125Pb.NoO2 (GL (Fin 2) (ZMod 2) × GL (Fin 3) (ZMod 2)) :=
  S125Pb.noO2_prod (S125Pb.noO2_GL 2 S125Pb.noO2_SL2) (S125Pb.noO2_GL 3 S125Pb.noO2_SL3)

theorem part1_groups (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    F.IsStab (mi T L F.V1) 2 ∧
      Nonempty (↥(autOn (mi T L F.V1) V) ⧸ CFSG.pCore 2 ↥(autOn (mi T L F.V1) V) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) ∧
      QuotSL (li L F.V1) (ri T L F.V1) V 3 := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hst := isStab_V1 F hf.normalizes hf.T_le
  refine ⟨hst, quotient_pCore_of_isStab hst (by norm_num) noO2_GL32, ?_⟩
  exact quotSL_of F hH hf (by norm_num) hst (T_le_V F hf.T_le).1
    (hres_of parJR_le_parQ S125Pb.perfectResidual_parQ23) S125Pb.uniRad_le_parJR
    (fun N hN hn hp => S125Pb.le_uniRad_of_parJR (S125Pb.noO2_GL 3 S125Pb.noO2_SL3) hN hn hp)
    S125Pb.quotient_parJR

theorem part2_groups (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    F.IsStab (mi T L F.V3) 3 ∧
      Nonempty (↥(autOn (mi T L F.V3) V) ⧸ CFSG.pCore 2 ↥(autOn (mi T L F.V3) V) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) × Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      QuotSL (li L F.V3) (ri T L F.V3) V 3 ∧
      ri T L F.V3 ≤ Subgroup.centralizer ((F.V3 : Subgroup G) : Set G) := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hst := isStab_V3 F hf.normalizes hf.T_le
  have hTW := (T_le_V F hf.T_le).2.1
  have hres := hres_of parJL_le_parQ S125Pb.perfectResidual_parQ32
  refine ⟨hst, quotient_pCore_of_isStab hst (by norm_num) noO2_GL23, ?_, ?_⟩
  · exact quotSL_of F hH hf (by norm_num) hst hTW hres S125Pb.uniRad_le_parJL
      (fun N hN hn hp => S125Pb.le_uniRad_of_parJL (S125Pb.noO2_GL 3 S125Pb.noO2_SL3) hN hn hp)
      S125Pb.quotient_parJL
  · have hliL : li L F.V3 ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
    refine ri_le_centralizer (sub_le F _) ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
      (sup_le (hliL.trans hf.normalizes) hf.T_le)) fun x hx v hv => ?_
    obtain ⟨g, hg, h11, rfl⟩ := rbar_le_kerChiL F hf (by norm_num) hst hTW parJL_le_parQ hres
      (fun A => by
        obtain ⟨⟨g, hg⟩, hgA⟩ := S125Pb.chiLJ_surjective (a := Fin 3) (b := Fin 2) A
        exact ⟨g, hg, hgA⟩)
      (S125Pb.noO2_GL 3 S125Pb.noO2_SL3) hx
    apply F.e.injective
    rw [e_theta_apply, wedgeMat_mulVec_of_fix (d := 3)
      (reindex_fix_of_blocks₁₁ (by norm_num) hg h11), ofAdd_toAdd]
    intro k hk
    exact (mem_sub_iff F _ v).1 hv k (by revert k; decide)

theorem part3_groups (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    autOn (mi T L F.V4) V = autOn (li L F.V4) V ∧ F.IsStab (mi T L F.V4) 1 ∧
      QuotSL (li L F.V4) (ri T L F.V4) V 4 ∧
      ri T L F.V4 ≤ Subgroup.centralizer ((F.V4 : Subgroup G) : Set G) := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hst := isStab_V4 F hf.normalizes hf.T_le
  have hTW := (T_le_V F hf.T_le).2.2.1
  have hres := hres_of parJR_le_parQ S125Pb.perfectResidual_parQ14
  refine ⟨?_, hst, ?_, ?_⟩
  · have h1 := autOn_mi_eq_theta F (by norm_num : 1 + 4 = 5) hst
    have h2 := lbar_eq F hf.normalizes hf.T_le (by norm_num : 1 + 4 = 5) hst hres
    rw [S125Pb.parJR_eq_parQ_of_fin_one] at h2
    exact h1.trans h2.symm
  · exact quotSL_of F hH hf (by norm_num) hst hTW hres S125Pb.uniRad_le_parJR
      (fun N hN hn hp => S125Pb.le_uniRad_of_parJR (S125Pb.noO2_GL 4 S125Pb.noO2_SL4) hN hn hp)
      S125Pb.quotient_parJR
  · have hliL : li L F.V4 ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
    refine ri_le_centralizer (sub_le F _) ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
      (sup_le (hliL.trans hf.normalizes) hf.T_le)) fun x hx v hv => ?_
    obtain ⟨g, hg, h22, rfl⟩ := rbar_le_kerChiR F hf (by norm_num) hst hTW parJR_le_parQ hres
      (fun A => by
        obtain ⟨⟨g, hg⟩, hgA⟩ := S125Pb.chiRJ_surjective (a := Fin 1) (b := Fin 4) A
        exact ⟨g, hg, hgA⟩)
      (S125Pb.noO2_GL 4 S125Pb.noO2_SL4) hx
    obtain ⟨h0, h1⟩ := reindex_fixV4 hg h22
    apply F.e.injective
    rw [e_theta_apply, wedgeMat_mulVec_V4 h0 h1, ofAdd_toAdd]
    intro k hk
    exact (mem_sub_iff F _ v).1 hv k (by revert k; decide)

theorem part4_groups (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    autOn (mi T L F.V6) V = autOn (li L F.V6) V ∧ F.IsStab (mi T L F.V6) 4 ∧
      QuotSL (li L F.V6) (ri T L F.V6) V 4 ∧
      ri T L F.V6 ≤ Subgroup.centralizer ((F.V6 : Subgroup G) : Set G) := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hst := isStab_V6 F hf.normalizes hf.T_le
  have hTW := (T_le_V F hf.T_le).2.2.2
  have hres := hres_of parJL_le_parQ S125Pb.perfectResidual_parQ41
  refine ⟨?_, hst, ?_, ?_⟩
  · have h1 := autOn_mi_eq_theta F (by norm_num : 4 + 1 = 5) hst
    have h2 := lbar_eq F hf.normalizes hf.T_le (by norm_num : 4 + 1 = 5) hst hres
    rw [S125Pb.parJL_eq_parQ_of_fin_one] at h2
    exact h1.trans h2.symm
  · exact quotSL_of F hH hf (by norm_num) hst hTW hres S125Pb.uniRad_le_parJL
      (fun N hN hn hp => S125Pb.le_uniRad_of_parJL (S125Pb.noO2_GL 4 S125Pb.noO2_SL4) hN hn hp)
      S125Pb.quotient_parJL
  · have hliL : li L F.V6 ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
    refine ri_le_centralizer (sub_le F _) ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
      (sup_le (hliL.trans hf.normalizes) hf.T_le)) fun x hx v hv => ?_
    obtain ⟨g, hg, h11, rfl⟩ := rbar_le_kerChiL F hf (by norm_num) hst hTW parJL_le_parQ hres
      (fun A => by
        obtain ⟨⟨g, hg⟩, hgA⟩ := S125Pb.chiLJ_surjective (a := Fin 4) (b := Fin 1) A
        exact ⟨g, hg, hgA⟩)
      (S125Pb.noO2_GL 4 S125Pb.noO2_SL4) hx
    apply F.e.injective
    rw [e_theta_apply, wedgeMat_mulVec_of_fix (d := 4)
      (reindex_fix_of_blocks₁₁ (by norm_num) hg h11), ofAdd_toAdd]
    intro k hk
    exact (mem_sub_iff F _ v).1 hv k (by revert k; decide)

end S125L2G

end CFSG.Quasithin.H13

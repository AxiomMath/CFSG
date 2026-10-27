module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenDiag
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SwapSp4InF

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}

theorem inFSq_of_isSp4_of_normal_sup {H K T : Subgroup G} {n : ℕ}
    (hK : Inputs1719.K_SwapSp4InF)
    (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal)
    (hperf : ⁅K, K⁆ = K) (hSp : IsSp4 (Bar2 K) n)
    (hTsyl : IsSylowIn 2 T H) (hsup : K ⊔ T = H)
    (hswap : S17.SwapsParabolics T K) :
    CFSG.LocalAnalysis.WeakClosure81.InFSq n H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimpleK : IsSimpleGroup (Bar2 K) := (uc22p22a_sp4_simple (Bar2 K) n hSp).1
  obtain ⟨⟨eKC⟩, -, hsimpleC, -, hFstar, -, -⟩ :=
    fstar_imageBar2_of_normal hKH hKn hTsyl hsup hperf hsimpleK
  have hSpC : IsSp4 ↥(imageBar2 H K) n := LieModel.of_mulEquiv eKC hSp
  have hSsyl : IsSylowIn 2 (imageBar2 H T) ⊤ := isSylowIn_imageBar2 hTsyl
  have hsupC : imageBar2 H K ⊔ imageBar2 H T = ⊤ := by
    rw [← imageBar2_sup hKH hTsyl.1, hsup, imageBar2_self]
  have hswapC : S17.SwapsParabolics (imageBar2 H T) (imageBar2 H K) := by
    obtain ⟨t, htT, P, hP, hPmove⟩ := hswap
    have htH : t ∈ H := hTsyl.1 htT
    have hKt : K.map (MulAut.conj t).toMonoidHom = K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKn htH)
    have hTt : T.map (MulAut.conj t).toMonoidHom = T :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htT)
    have hTKt : (T ⊓ K).map (MulAut.conj t).toMonoidHom = T ⊓ K := by
      rw [Subgroup.map_inf T K _ (MulAut.conj t).injective, hTt, hKt]
    have hO2K : pCoreOf 2 K ≤ T ⊓ K := by
      have hTK : IsSylowIn 2 (T ⊓ K) K := by
        have h2 : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ K) K := by
          have h3 := CFSG.isSylowTwoOf_inf_of_normal (S := T) (X := H) (N := K)
            ⟨hTsyl.1, hTsyl.2.1, hTsyl.2.2⟩ hKH
            ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKn)
          rwa [inf_comm] at h3
        exact ⟨h2.1, h2.2.1, h2.2.2⟩
      have hKnorm : ((pCoreOf 2 K).subgroupOf K).Normal := by
        rw [Subgroup.normal_subgroupOf_iff (CFSG.LieType.BorelTits.pCoreOf_le 2 K)]
        intro x y hx hy
        exact CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hy hx
      exact hTK.le_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 K) hKnorm
        (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 K)
    have hTKleP : T ⊓ K ≤ P := by
      intro x hx
      exact hP.2.1 ⟨hx.2, Subgroup.le_normalizer hx⟩
    have hPtK : P.map (MulAut.conj t).toMonoidHom ≤ K := by
      rw [← hKt]
      exact Subgroup.map_mono hP.1
    have hO2P : pCoreOf 2 K ≤ P := hO2K.trans hTKleP
    have hPtO2 : pCoreOf 2 K ≤ P.map (MulAut.conj t).toMonoidHom :=
      hO2K.trans (hTKt ▸ Subgroup.map_mono hTKleP)
    have hmove : (imageBar2 H P).map (MulAut.conj (piBar2 H ⟨t, htH⟩)).toMonoidHom =
        imageBar2 H (P.map (MulAut.conj t).toMonoidHom) :=
      imageBar2_map_conj (hP.1.trans hKH) htH
    refine ⟨piBar2 H ⟨t, htH⟩, ?_, imageBar2 H P, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨⟨t, htH⟩, Subgroup.mem_subgroupOf.mpr htT, rfl⟩
    · rw [imageBar2_inf_of_isSylowIn hTsyl]
      exact imageBar2_isMaxParabolicOver hKH hKn hTsyl hP
    · intro hEq
      have hinj := imageBar2_injective_of_pCoreOf_le hKH hKn hP.1 hPtK hO2P hPtO2
        (by rw [← hmove, hEq])
      exact hPmove hinj.symm
  exact hK (Bar2 H) (imageBar2 H K) (imageBar2 H T) n hFstar hsimpleC hSpC
    (uc22p22a_two_le_of_isSp4 hSp) hSsyl hsupC hswapC

theorem inFSq_sup_T_of_isSp4_swap (h : Hyp18 D V₀ V p L)
    (hK : Inputs1719.K_SwapSp4InF)
    (hSp : IsSp4 (Bar2 (UC22.conjClosure D.M L)) (S17.nOf L))
    (hSwap : S17.SwapsParabolics D.T (UC22.conjClosure D.M L)) :
    CFSG.LocalAnalysis.WeakClosure81.InFSq (S17.nOf L)
      (UC22.conjClosure D.M L ⊔ D.T) := by
  have hsX : IsSimpleGroup (Bar2 (UC22.conjClosure D.M L)) :=
    (uc22p22a_sp4_simple (Bar2 (UC22.conjClosure D.M L)) (S17.nOf L) hSp).1
  have hXL : UC22.conjClosure D.M L = L :=
    conjClosure_eq_self_of_isSimpleGroup_bar2 h.hL.1 hsX
  rw [hXL] at hSp hSwap ⊢
  have hnorm : L ⊔ D.T ≤ Subgroup.normalizer (L : Set G) := by
    refine sup_le Subgroup.le_normalizer ?_
    refine D.sylowM.le.trans ?_
    rw [← hXL]
    exact TwelveTwentyThree.le_normalizer_conjClosure D.M L
  have hKn : (L.subgroupOf (L ⊔ D.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hnorm
  exact inFSq_of_isSp4_of_normal_sup hK le_sup_left hKn h.hL.1.2.1 hSp
    (TwelveShort.isSylowIn_of_le D le_sup_right) rfl hSwap

section Certified


theorem r18_7b_of_ne_bot_XT_sp4 (h : Hyp18 D V₀ V p L) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (hSg : UC6S846.SigmaStd D)
    (hV₀ : V₀ ≠ ⊥) (hX1 : barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) ≠ ⊥)
    (h17_66_1 : S17.R17_66_1At D V₀ V) (h18_4 : R18_4At D V₀ V p L)
    (hK : Inputs1719.K_SwapSp4InF)
    (hSp : IsSp4 (Bar2 (UC22.conjClosure D.M L)) (S17.nOf L))
    (hSwap : S17.SwapsParabolics D.T (UC22.conjClosure D.M L)) :
    R18_7bAt D V₀ V p L h :=
  r18_7b_of_ne_bot_XT h hx h61 h127 h1114 h162 hTor h1482 h126 hSg hV₀ hX1 h17_66_1 h18_4
    (inFSq_sup_T_of_isSp4_swap h hK hSp hSwap)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

module

public import CFSG.Quasithin.H13.A5S1328Vertex
public import CFSG.Quasithin.H13.A5S1328Sym4A5
public import CFSG.Quasithin.H13.A5S1328Blk2
public import CFSG.Quasithin.H13.A5S1328Blk3
public import CFSG.Quasithin.H13.A5S1328Sym2
public import CFSG.Quasithin.H13.A5S1328Sym5

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem res1328aSym_corrected'_A5 (S : Setting G T L V)
    (h132two : Stmt13_3_2_two)
    (h132fsu : Stmt13_3_2_three_fsu) (h132A5 : Stmt13_3_2_three_A5) (h331 : Stmt3_3_1)
    (h512 : Stmt5_1_2) (h5172 : Stmt5_1_7_two) (hA5 : CFSG.Quasithin.F112R.F112SliceA5) {H K : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) (hKc : K ∈ cComp H)
    (hHK : H = K ⊔ T) (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  classical
  have hZK : ⁅quasithinOmegaOneCenter T, K⁆ ≠ ⊥ := by
    intro h
    apply hHZ
    rw [hHK]
    refine sup_le ?_ (T_le_centralizer_omegaOneCenter T)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact h)
  have hKloc : quasithinIsLocal T K :=
    ⟨S.isPGroup_T, cComp_subset_lFamily hH.1.1 hKc,
      (isSylowTwoOf_of_le S.h13.sylow le_sup_right).2.2, by rw [← hHK]; exact hH.1.2⟩
  have hKf : quasithinIsFaithfulLocal T K :=
    Vol2.Ch11.SecS.isFaithfulLocal_of_omegaOneCenter S.h13.qtke S.h13.sylow hKloc hZK
  obtain ⟨VH, ⟨S'⟩⟩ := exists_setting h132two h132fsu h132A5 (QTH13.of_faithful S.h13 S.a5 hKf)
    (S.h13.a5 S.a5 K hKf)
  have hJL : ¬ thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) (L ⊔ T) : Set G) := fun hJ =>
    S.thompsonJ_not_le_centralizer h5172 hH hHZ
      (hJ.trans (Subgroup.centralizer_le S.V_le_conjClosure))
  have hJK : ¬ thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) (K ⊔ T) : Set G) := fun hJ =>
    S.thompsonJ_not_le_centralizer_UH h331 h5172 hH hHZ (by rw [Setting.UH, hHK]; exact hJ)
  rw [eq_bot_iff]
  intro ζ hζ
  rw [Subgroup.mem_bot]
  by_contra hζ1
  obtain ⟨hB1, hB2⟩ := S.borels_of_centralizer S' hH hHZ hHK
    (fun _ hz => S.Z_decomp h512 hJL hz) (fun _ hz => S'.Z_decomp h512 hJK hz) hζ.1 hζ.2 hζ1
  have hyp : Hyp111R L K T := S.hyp111R_of_borels S' hH hHK hB1 hB2
  obtain ⟨L1', L2', hsw, hlist⟩ := S.f112_of_borels_corrected_A5 hA5 S' hH hHK hyp
  rcases hsw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at hlist
    exact S.not_f112ListC_of_vertex_exclusion S' (vertex_excl S hTK hB2 hyp) hlist
  · rw [h1, h2] at hlist
    have hsp2 := vertex_excl S' S.T_le_NL hB1 hyp.symm
    rw [Setting.Sp_comm] at hsp2
    exact S'.not_f112ListC_of_vertex_exclusion S hsp2 hlist

end Setting

theorem res1328a_of_corrected_A5 (h132two : Stmt13_3_2_two)
    (h132fsu : Stmt13_3_2_three_fsu) (h132A5 : Stmt13_3_2_three_A5) (h331 : Stmt3_3_1)
    (h512 : Stmt5_1_2) (h5172 : Stmt5_1_7_two) (hA5 : CFSG.Quasithin.F112R.F112SliceA5) (h126 : TheoremC126) :
    Res1328a := by
  intro G _ _ T L V S H K hH hHZ hKc hHK hTK _
  have hZK := S.res1328aSym_corrected'_A5 h132two h132fsu h132A5 h331 h512 h5172 hA5 hH hHZ hKc
    hHK hTK
  obtain ⟨VH, ⟨S'⟩⟩ := S.exists_setting_cComp h132two h132fsu h132A5 hH hHZ hKc hHK
  have hO := S.pCoreOf_KT_eq h331 h512 h5172 h126 S' hH hHZ hHK hZK
  refine S'.rootFourLiftQuot_of ?_
  rw [S'.cT, hO]

end CFSG.Quasithin.H13.A5

end

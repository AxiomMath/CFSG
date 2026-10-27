module

public import CFSG.Quasithin.H13.A5Final
public import CFSG.Quasithin.Vol2.Ch5Sec1Basic
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.H13.A5S1328
public import CFSG.Quasithin.Background.E2TwoNoNStmt

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.Assembly.LowTwoRank

theorem T_le_centralizer_omegaOneCenter {G : Type} [Group G] (T : Subgroup G) :
    T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact ((Subgroup.mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.mp hz).2.1) t ht).symm

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem hyp501 :
    Hyp5_0_1 G T (Subgroup.normalizer (L : Set G)) L 2 where
  simple := S.h13.simple
  nonabelian := S.h13.nonabelian
  qtke := S.h13.qtke
  sylow := S.h13.sylow
  maxTwoLocal := S.uniqueM.1.1
  T_le := S.T_le_NL
  maximal := S.maximal
  faithful := S.h13.faithful
  L_le := Subgroup.le_normalizer
  normal := le_rfl
  two_le := le_rfl
  lie := S.lieModel_L

theorem isCh5Module : IsCh5Module T L V := by
  obtain ⟨h1, h2⟩ := isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp S.reduced
  exact ⟨h1, h2, fun h => S.irr.2.1 (S.irr.2.2.2.1.symm.trans h)⟩

theorem isSolvable_of_hStar_ofNoN
    (h331 : Stmt3_3_1) (h523 : Stmt5_2_3) (h1222 : Stmt12_2_2) (hE22 : E2.E22StatementNoN)
    (hRes : Res1328a) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    Group.IsSolvable ↥H := by
  set M := Subgroup.normalizer (L : Set G) with hM
  obtain ⟨hMP, -⟩ := S.hyp501.minParabolic_of_isHStar h331 hH
  by_contra hns
  have hSQ : SQTKGroup ↥H := by
    obtain ⟨hk, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian hH.1
    exact ⟨hq, hk⟩
  obtain ⟨⟨K, hKc, hHK, -, -⟩, -⟩ := hE22 G H T (H ⊓ M) hMP hSQ hns
  have hTZ := T_le_centralizer_omegaOneCenter T
  have hZK : ⁅quasithinOmegaOneCenter T, K⁆ ≠ ⊥ := by
    intro h
    apply hHZ
    rw [hHK]
    refine sup_le ?_ hTZ
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact h)
  have hTH : T ≤ H := hH.1.1
  have hKl : K ∈ lFamily T := cComp_subset_lFamily hTH hKc
  have hKloc : quasithinIsLocal T K :=
    ⟨S.isPGroup_T, hKl, (isSylowTwoOf_of_le S.h13.sylow le_sup_right).2.2,
      by rw [← hHK]; exact hH.1.2⟩
  have hKf : quasithinIsFaithfulLocal T K :=
    Vol2.Ch11.SecS.isFaithfulLocal_of_omegaOneCenter S.h13.qtke S.h13.sylow hKloc hZK
  have hA5 := (quasithinO2QuotientIso_iff K _).1 (S.h13.a5 S.a5 K hKf)
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := S.le_normalizer_of_cComp h1222 hH hKc hHK hZK
  have hHN : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have hn : 1 < E1.nParam H :=
    E1.LiftS5.one_lt_nParam_of_rootFourLiftQuot hHN (le_of_mem_cComp hKc) hA5
      (isSylowTwoOf_of_le S.h13.sylow hTH) (hRes G T L V S H K hH hHZ hKc hHK hTK hA5)
  have hV := S.isCh5Module
  rcases h523 G T M L H V 2 S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow S.uniqueM.1.1
      S.T_le_NL S.maximal S.h13.faithful Subgroup.le_normalizer le_rfl le_rfl S.lieModel_L hH
      hn hV.1 hV.2.1 hV.2.2 with ⟨-, -, KZ, hKZ, hHKZ, -⟩ | hM23 | hLie
  · apply hHZ
    rw [eq_oTwoUpper_sup_of_isSylowTwoOf' (isSylowTwoOf_of_le S.h13.sylow hTH)]
    exact sup_le (hHKZ.trans (le_of_mem_cComp hKZ)) hTZ
  · exact S.h13.not_excluded (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM23)))))
  · apply S.h13.not_excluded
    rcases hLie with ⟨t, n, f, hf, -, hadm, hlie⟩ | hlie
    · exact Or.inl ⟨t, n, f, hf, hadm, hlie⟩
    · refine Or.inl ⟨.PSU, 5, 2, le_rfl, ?_, hlie⟩
      refine ⟨Nat.prime_two, by norm_num, ?_⟩
      exact ⟨by norm_num, by decide⟩

end Setting

@[expose] def Rest1327 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (_ : Setting G T L V) (H : Subgroup G),
    IsHStar T (Subgroup.normalizer (L : Set G)) H →
    ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) → Group.IsSolvable ↥H → False

theorem stmt13_2_7_ofNoN
    (h331 : Stmt3_3_1) (h523 : Stmt5_2_3) (h1222 : Stmt12_2_2) (hE22 : E2.E22StatementNoN)
    (hRes : Res1328a) (hrest : Rest1327) : Stmt13_2_7 := by
  intro G _ _ T L V S H hH
  by_contra hHZ
  exact hrest G T L V S H hH hHZ (S.isSolvable_of_hStar_ofNoN h331 h523 h1222 hE22 hRes hH hHZ)

end CFSG.Quasithin.H13.A5

module

public import CFSG.RankThree.PartTwo.Sec8.Hering611Defs
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.KFacts.K71Lift
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL)

section Basic

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}

theorem Frame611.isElemAbelian (F : Frame611 G A c L E T d) :
    CFSG.Assembly.IsElemAbelian 3 A := F.mem_S.1.1

theorem Frame611.maximal (F : Frame611 G A c L E T d) :
    ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A := F.mem_S.1.2.1

theorem Frame611.d_mem_A (F : Frame611 G A c L E T d) : d ∈ A := F.mem_E.2 F.d_mem.1

theorem Frame611.d_ne_one (F : Frame611 G A c L E T d) : d ≠ 1 :=
  fun h => F.d_not_mem (h ▸ Subgroup.one_mem _)

theorem Frame611.c_pow_three (F : Frame611 G A c L E T d) : c ^ 3 = 1 :=
  F.isElemAbelian.2 c F.c_mem

theorem Frame611.d_pow_three (F : Frame611 G A c L E T d) : d ^ 3 = 1 :=
  F.isElemAbelian.2 d F.d_mem_A

theorem Frame611.comm_of_mem (F : Frame611 G A c L E T d) {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    x * y = y * x :=
  congrArg Subtype.val (F.isElemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem Frame611.mem_thetaComponentsAt_L (F : Frame611 G A c L E T d) :
    L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c F.mem_L

theorem Frame611.A_le_normalizer_L (h45 : Sec4.Item4_5) (F : Frame611 G A c L E T d) :
    A ≤ Subgroup.normalizer (L : Set G) :=
  Sec6.le_normalizer_of_mem_thetaComponentsAt h45 F.standing.toTheoremFourHyp F.isElemAbelian
    F.c_mem F.c_ne_one L F.mem_thetaComponentsAt_L

theorem Frame611.center_L_bot (F : Frame611 G A c L E T d) :
    Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ := by
  obtain ⟨φ⟩ := F.iso_L
  exact CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv
    (φ.trans (Sec4.projSLEquivPSL (GaloisField 3 (3 * 2))))
    (CFSG.GorensteinWalter.psl2_center_eq_bot (GaloisField 3 (3 * 2)))

variable {S K : Subgroup G}

theorem Cfg611.mem_thetaComponentsAt_K (C : Cfg611 G A c L E T d S K) :
    K ∈ thetaComponentsAt 3 d := lZeroStarAt_subset A d C.mem_K

theorem Cfg611.A_le_normalizer_K (h45 : Sec4.Item4_5) (C : Cfg611 G A c L E T d S K) :
    A ≤ Subgroup.normalizer (K : Set G) :=
  Sec6.le_normalizer_of_mem_thetaComponentsAt h45 C.standing.toTheoremFourHyp
    C.toFrame611.isElemAbelian C.toFrame611.d_mem_A C.toFrame611.d_ne_one K
    C.mem_thetaComponentsAt_K

theorem Cfg611.K_le_centralizer (C : Cfg611 G A c L E T d S K) :
    K ≤ Subgroup.centralizer ({d} : Set G) :=
  Sec6.le_centralizer_of_mem_thetaComponentsAt C.mem_thetaComponentsAt_K

theorem Frame611.d_not_mem_L (F : Frame611 G A c L E T d) : d ∉ L := by
  intro hdL
  obtain ⟨hdN, hnot⟩ := KFacts.InducesStdKind.inducesOuterTheta L F.d_field (by decide)
  exact hnot ⟨_, (KFacts.thetaQuotMulAut_compAction_of_mem hdL hdN).symm⟩

end Basic

end CFSG.RankThree.PartTwo.Sec8.Hering611

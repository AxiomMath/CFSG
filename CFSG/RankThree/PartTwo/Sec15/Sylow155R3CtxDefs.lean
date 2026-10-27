module

public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec13.Statements
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

section Notation

variable {G : Type} [Group G]

abbrev res3C (d : G) : Subgroup G := Subgroup.centralizer ({d} : Set G)

abbrev Res3Bar (d : G) : Type := ↥(res3C d) ⧸ CFSG.pPrimeCore 3 ↥(res3C d)

abbrev res3Proj (d : G) : ↥(res3C d) →* Res3Bar d :=
  QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(res3C d))

abbrev res3Pt (d x : G) (hx : x ∈ res3C d) : Res3Bar d := res3Proj d ⟨x, hx⟩

abbrev res3Img (d : G) (H : Subgroup G) : Subgroup (Res3Bar d) :=
  (H.subgroupOf (res3C d)).map (res3Proj d)

end Notation

variable {G : Type} [Group G] [Finite G]

structure Res3Ctx (A : Subgroup G) (c : G) (L : Subgroup G) (d : G) (K : Subgroup G) :
    Prop where
  R : Sec15R G A c L
  J2 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)
  ncard : (omegaA A).ncard = 3
  d_mem : d ∈ A
  d_ne : d ≠ 1
  d_Z : ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S L ∧
    (Subgroup.center S).map S.subtype = Subgroup.zpowers d
  d_L : d ∈ L
  c_notMem : c ∉ L
  AL_card : Nat.card ↥(A ⊓ L) = 9
  A_eq : A = Subgroup.zpowers c ⊔ (A ⊓ L)
  AL_le : A ⊓ L ≤ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G))
  K_mem : K ∈ thetaComponentsAt 3 d
  K_le : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K
  K_eq : K = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
    inSubgroup (aschbacherSolvableCore 3) K
  K_cover : Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) (alternatingGroup (Fin 6))
  NA : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G)
  Pstar_elem : CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A)
  Pstar_card : Nat.card (oThreeWStar A) = 9
  Pstar_syl : CFSG.ABGLocalTools.IsSylowOf 3 (oThreeWStar A) (wStar A)
  omega : omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers c)

namespace Res3Ctx

variable {A : Subgroup G} {c : G} {L : Subgroup G} {d : G} {K : Subgroup G}

theorem c_mem (h : Res3Ctx A c L d K) : c ∈ A :=
  h.R.toSec13Data.mem_A

theorem le_C (h : Res3Ctx A c L d K) : A ≤ res3C d := fun _ ha =>
  Subgroup.mem_centralizer_singleton_iff.mpr (h.R.toSec13Data.commute ha h.d_mem)

theorem c_mem_C (h : Res3Ctx A c L d K) : c ∈ res3C d :=
  h.le_C h.c_mem

theorem d_mem_C (h : Res3Ctx A c L d K) : d ∈ res3C d :=
  h.le_C h.d_mem

theorem centralizer_le_C (h : Res3Ctx A c L d K) :
    Subgroup.centralizer (A : Set G) ≤ res3C d := fun _ hg =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    ((Subgroup.mem_centralizer_iff.mp hg d h.d_mem).symm)

end Res3Ctx

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3

module

public import CFSG.Quasithin.Background.C31Asm
public import CFSG.Quasithin.Background.C31BasicPf
public import CFSG.Quasithin.Background.C31SporPf
public import CFSG.Quasithin.Background.C31NonLie
public import CFSG.Quasithin.Background.KGSchurMult2Pf

public section

namespace CFSG.Quasithin.C31

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem sqtkSimpleList_of_isComponentOf
    {H K : Subgroup G} (hH : IsSQTKIn H) (hK : CFSG.Open.IsComponentOf K H) :
    CFSG.Milestones.SQTKSimpleList (↥K ⧸ Subgroup.center ↥K) := by
  have hcat : CFSG.SectionRank.IsSQTKCat ↥H := by
    refine ⟨fun p hp hp2 => ?_, hH.2⟩
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact sqt_iff.mp hH.1 p hp hp2
  have hq : CFSG.IsQuasisimple ↥K := A3.isQuasisimple_iff_open.mpr hK.2.2
  let e₁ : ↥(K.subgroupOf H) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hK.1
  let N : Subgroup ↥(K.subgroupOf H) := (Subgroup.center ↥K).comap e₁.toMonoidHom
  have : N.Normal := Subgroup.Normal.comap inferInstance _
  let e : ↥(K.subgroupOf H) ⧸ N ≃* ↥K ⧸ Subgroup.center ↥K :=
    QuotientGroup.congr N (Subgroup.center ↥K) e₁
      (Subgroup.map_comap_eq_self_of_surjective e₁.surjective _)
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2.1
  have : IsSimpleGroup (↥(K.subgroupOf H) ⧸ N) := e.isSimpleGroup
  have hnonab : ∃ a b : ↥(K.subgroupOf H) ⧸ N, a * b ≠ b * a :=
    nonab_of_mulEquiv e.symm hq.2.2
  exact A36A.a23List_of_mulEquiv e.symm
    (CFSG.Milestones.cl_lit_sqtk_simple_list_section ↥H hcat (K.subgroupOf H) N hnonab)

theorem asc31Statement_of_inputs
    (h36 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A36Statement Y)
    (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (h38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y) (hA3 : A3Orbits G)
    (hSch : ∀ K : Subgroup G, IsSQTKIn K → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
      OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K))
    (hInsp33 : InspC33) (hInsp : InspC31Sporadic) (hLie : C31LieStep G) :
    ASC31Statement G :=
  asc31Statement_of (C31B.c31BasicStep_of h36 h38 hA3 hSch hInsp33)
    (C31Spor.c31SporStep_of hA3 (C22Pf.asc22One_of hA37) hInsp schurMult2M23_holds
      schurMult2M24_holds schurMult2J4_holds schurMult2He_holds)
    C31NL.c31NonLieStep_holds hLie fun _ _ _ _ _ _ h hK => sqtkSimpleList_of_isComponentOf h.sqtk hK

end CFSG.Quasithin.C31

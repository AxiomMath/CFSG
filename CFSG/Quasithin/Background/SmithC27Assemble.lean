module

public import CFSG.Quasithin.Background.SmithC27AltMain
public import CFSG.Quasithin.Background.SmithC27L2
public import CFSG.Quasithin.H13.VolIC129Holds
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace SmithC27

variable {G : Type} [Group G] [Finite G]

theorem c27Concl_of_cases (hC129 : ASC129Statement G)
    (hI : B5.B51IrrInputs) (hA21 : AsA21SQTKSection) (hA36 : AsA36NoOddCover) (hB51 : AsB51)
    {H R M K : Subgroup G} (h : Hyp27 H R M K)
    (hc : IsChiBlock2 H K ∨ IsExcA7Block K ∨ IsSylowTwoOf R (K ⊔ R)) :
    C27Concl H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) := by
  refine c27Concl_of_parts (c27_one h) (c27_two h) ?_
  have hchi_case : IsChiBlock2 H K →
      C27Three H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) := by
    intro hchi
    rcases hchi.2 with ⟨n, hn, hL⟩ | ⟨m, hm, htype⟩
    · exact three_of_lin2 h hA21 hB51 hchi hn hL
    · exact three_of_isAltType hC129 hI hA21 hA36 h hchi hm htype
  rcases hc with hchi | hexc | hS
  · exact hchi_case hchi
  · exact three_of_isExcA7Block hI hA21 hA36 h hexc
  · exact hchi_case (isChiBlock2_of_sylow hC129 h hS)

end SmithC27

theorem asc27Statement_of_residue_of_inputs
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hI : B5.B51IrrInputs) (hA21 : AsA21SQTKSection) (hA36 : AsA36NoOddCover) (hB51 : AsB51)
    (hres : ∀ (G : Type) [Group G] [Finite G], SmithC27.ASC27Residue G) :
    ∀ (G : Type) [Group G] [Finite G], ASC27Statement G := fun G _ _ =>
  SmithC27.asc27Statement_of_residue_of_cases (hres G) fun _ _ _ _ h hc =>
    SmithC27.c27Concl_of_cases (hC129 G) hI hA21 hA36 hB51 h hc

theorem asc27Statement_of_residue
    (hres : ∀ (G : Type) [Group G] [Finite G], SmithC27.ASC27Residue G) :
    ∀ (G : Type) [Group G] [Finite G], ASC27Statement G :=
  asc27Statement_of_residue_of_inputs H13.VolI.asc129Statement_holds
    (FFC.b51IrrInputs_of_ffc asB42_holds asI16Cover_of FFC.asB51NonsplitOffSp4_holds)
    asA21SQTKSection asA36NoOddCover_holds B5.asB51_holds hres

end CFSG.Quasithin

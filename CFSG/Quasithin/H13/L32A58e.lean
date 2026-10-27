module

public import CFSG.Quasithin.H13.L32A58c
public import CFSG.Quasithin.H13.L32A58d
public import CFSG.Quasithin.H13.L32A58S
public import CFSG.Quasithin.H13.L32A55Q

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Setup.Family

variable {G : Type} [Group G] [Finite G]

namespace T53

theorem lemma14_5_5_of (h55 : Lemma14_5_5Q) (h4 : Lemma14_7_4_two_three) :
    ∀ (G : Type) [Group G] [Finite G] (T L V V₂ Y : Subgroup G), Ctx G T L V V₂ Y →
      pCoreOf 2 (hY T L V₂ Y) ≠ ⊥ := by
  intro G _ _ T L V V₂ Y C
  exact h55 G T L V V₂ Y C.hyp C.hV2 C.hYo C.hYG1 C.hTY C.hS3 C.not_le_M (C.quot_xT h4).1
    (C.inf_eq h4)

namespace Ctx

variable {T L V V₂ Y : Subgroup G} (C : Ctx G T L V V₂ Y)
include C

theorem isSolvable_hY (h4 : Lemma14_7_4_two_three) (h55 : Lemma14_5_5Q) (h36 : A36ForSQTK)
    (h1434 : Lemma1434One) (hSym : Lemma14_5_8Sym) : Group.IsSolvable ↥(hY T L V₂ Y) := by
  have hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥ := lemma14_5_5_of h55 h4 G T L V V₂ Y C
  by_contra hns
  obtain ⟨K, hK⟩ := exists_mem_cComp hns
  have hKf := C.faithful_of_mem_cComp h4 hQ h36 hK
  have hiso := C.quot_of_mem_cComp h4 hQ h36 h1434 hK
  have hO2 := C.pCoreOf_eq_of_mem_cComp h4 hQ hK hiso
  obtain ⟨hKn, hHK, ⟨eGL⟩, hXK, hYK⟩ := C.structure_of_mem_cComp h4 hQ hK hiso
  have hcard := C.card_vH h4 hQ hK hKn hHK eGL hXK hYK hO2
  have hnat := C.binaryNaturalSL_vH hQ hK eGL hO2 hcard
  have hE := C.vH_eq_conjClosure_V2 hcard
  have hSL : quasithinO2QuotientIso K (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    (quasithinO2QuotientIso_iff _ _).mpr ⟨eGL.trans (slEquivGL 3).symm⟩
  exact hSym G T L V V₂ Y K C.hyp C.hV2 C.hYo C.hYG1 C.hTY C.hS3 C.not_le_M hQ hK hKf hHK hSL
    hO2 C.V2_le_vH hE hnat

end Ctx

end T53

end CFSG.Quasithin.H13.L32A

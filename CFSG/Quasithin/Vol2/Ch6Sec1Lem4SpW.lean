module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4V4
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpM
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveJ

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique CFSG.Blueprint.NativeSporadic

theorem noFiveOver_of_mulEquiv614 {W W' : Type} [Group W] [Group W'] (e : W ≃* W')
    (h : FiveNorm.NoFiveOver W') : FiveNorm.NoFiveOver W := by
  intro S H hS hSH hcard
  refine h (S.map e.toMonoidHom) (H.map e.toMonoidHom) (FiveNorm.isSylowTwoOf_map_mulEquiv e hS)
    (Subgroup.map_mono hSH) ?_
  rw [Subgroup.card_map_of_injective e.injective, Subgroup.card_map_of_injective e.injective]
  exact hcard

theorem noFiveOver_altList614
    {W : Type} [Group W] (hW : Ch1.AltList W) : FiveNorm.NoFiveOver W := by
  obtain ⟨n, hn5, hn8, ⟨e⟩⟩ := hW
  interval_cases n
  · exact noFiveOver_of_mulEquiv614 e FiveNorm.noFiveOver_alt5
  · exact noFiveOver_of_mulEquiv614 e FiveNorm.noFiveOver_alt6
  · exact noFiveOver_of_mulEquiv614 e FiveNorm.noFiveOver_alt7
  · exact noFiveOver_of_mulEquiv614 e FiveNorm.noFiveOver_alt8

theorem noFiveOver_sporadicList614
    (hJ4 : FiveNorm.NoFiveOver (Carrier .J4)) {W : Type} [Group W] (hW : Ch1.SporadicList W) :
    FiveNorm.NoFiveOver W := by
  obtain ⟨s, hs, ⟨e⟩⟩ := hW
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact noFiveOver_of_mulEquiv614 e FiveNorm.noFiveOver_M11
  · exact noFiveOver_of_mulEquiv614 e FiveNorm.noFiveOver_M12
  · exact noFiveOver_of_mulEquiv614 e FiveNorm.fiveRigid_M22.2.2
  · exact noFiveOver_of_mulEquiv614 e FiveNorm.fiveRigid_M23.2.2
  · exact noFiveOver_of_mulEquiv614 e FiveNorm.noFiveOver_M24
  · exact noFiveOver_of_mulEquiv614 e FiveNorm.fiveRigid_J1.2.2
  · exact noFiveOver_of_mulEquiv614 e FiveNorm.fiveRigid_J2.2.2
  · exact noFiveOver_of_mulEquiv614 e hJ4
  · exact noFiveOver_of_mulEquiv614 e FiveNorm.fiveRigid_HS.2.2
  · exact noFiveOver_of_mulEquiv614 e FiveNorm.noFiveOver_He
  · exact noFiveOver_of_mulEquiv614 e FiveNorm.fiveRigid_Ru.2.2

theorem kg614FiveSpor_of_J4
    (hJ4 : FiveNorm.NoFiveOver (Carrier .J4)) : KG614FiveSpor :=
  kg614FiveSpor_of_noFiveOver fun _ _ _ hW =>
    hW.elim noFiveOver_altList614 (noFiveOver_sporadicList614 hJ4)

end CFSG.Quasithin.H13

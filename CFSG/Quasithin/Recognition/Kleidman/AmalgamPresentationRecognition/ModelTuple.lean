module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.ModelData
public import CFSG.Sporadic.J3.Group

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

open CFSG.Sporadic.J3 CFSG.Sporadic.Th

abbrev J3Model : Type := ↥(J Native.j3Data)

@[expose] def pairL {G : Type*} [Group G] (g h : G) (l : ℤ) : G :=
  if l = 1 then g else if l = -1 then g⁻¹ else if l = 2 then h else h⁻¹

noncomputable def uN (k : ℕ) : J3Model :=
  wordG (pairL (a Native.j3Data) (b Native.j3Data)) (uWord k)

noncomputable def uJ : Fin 7 → J3Model := fun i => uN i

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

end

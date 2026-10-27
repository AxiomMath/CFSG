module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporLat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatJ3Dc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.QuasithinUnique.Ch1.SporLat.J3K CFSG.Sporadic.Schreier in
theorem k105SporAt_J3 :
    K105SporAt .J3 := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .J3 ≃* ↥j3P := j3PermEquiv
  exact k105SporAt_of_list (s := .J3) S_sylow (L := #[1, 3, 3, 9, 15]) complete
    (fun j hj => member_card hj) (by decide) (N := 392445)
    (by rw [card_j3P, card_S]) (by norm_num) e

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10

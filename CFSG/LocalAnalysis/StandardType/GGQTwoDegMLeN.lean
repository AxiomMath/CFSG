module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDegDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoDegFrame

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem qTwoDeg_m_le_N {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {k : QTwoRowKind} {m d c : ℕ} (hrow : QTwoRowData k m d c Bs L x) (hm : 5 ≤ m)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    {N : ℕ} (hN : 6 ≤ N) {e' : Fin (N - 1) ≃ ι}
    (hM : M = (CoxeterMatrix.A (N - 1)).reindex e') :
    m ≤ N := by
  obtain ⟨ρ, hρ, -⟩ := qTwoDegFrame_perm_equiv hP.2 (by omega) hM
  obtain ⟨p, hinj, -⟩ := qTwoDegFrame_path hrow.elemAb ρ hρ
    (le_sup_left : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦) (by omega) hrow.weyl
  have h := Fintype.card_le_of_injective (fun i : Fin m => p i.val)
    (fun i j hij => Fin.ext (hinj i.val i.2 j.val j.2 hij))
  simpa using h

end CFSG.StandardType.QTwo

end

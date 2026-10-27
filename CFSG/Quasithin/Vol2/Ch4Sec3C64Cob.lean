module

public import CFSG.Quasithin.H13.VolIC113
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.C2Blocks

public section

namespace CFSG.Quasithin.H13.Ch4.C64

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {L TH : Subgroup G}
  {α : ↥L →* alternatingGroup (Fin 7)} {β : ↥(blockU L) →* Multiplicative (AltHeart 7)}

theorem pCoreOf_le_centralizer_blockU (hL : IsShort2 L) (hTH : IsPGroup 2 TH)
    (hTN : TH ≤ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 (L ⊔ TH) ≤ Subgroup.centralizer (blockU L : Set G) := by
  have h := C1.inf_centralizer_blockU_eq hL le_sup_left (VolI.sup_le_normalizer hTN)
    fun _ hg => C1.exists_pow_mem_of_mem_sup hTH hTN hg
  rw [← h]
  exact inf_le_right

end CFSG.Quasithin.H13.Ch4.C64

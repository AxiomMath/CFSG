module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Suzuki
import CFSG.Quasithin.Background.F918Z8Op4d
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.RankThree.S4Free.SzModels

open CFSG.Blueprint CFSG.Open CFSG.BenderSuzuki.MatrixGroups

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem nonempty_mulEquiv_suzukiMatrixGroup (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nonempty (suzukiGroup a K ≃* SuzukiMatrixGroup a) := by
  have hsz : CFSG.Quasithin.IsSz (2 * a + 1) (suzukiGroup a K) :=
    ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨m, -, hm, he⟩ := CFSG.Quasithin.opq4d_exists_mulEquiv_suzukiMatrixGroup hsz
  obtain rfl : m = a := by omega
  exact he

theorem nonempty_mulEquiv_sz (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nonempty (suzukiGroup a K ≃* Sz a) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_suzukiMatrixGroup ha hK
  exact ⟨e.trans (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a).symm⟩

end CFSG.RankThree.S4Free.SzModels

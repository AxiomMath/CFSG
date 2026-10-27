module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUBlockX
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUCompl
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUCoordAt

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem ggQTwoXInLU_coord {N : ℕ} {K : Type} [Field K] [Finite K]
    (hS : GGQTwoSetting 3 B Bs x L D J) (hxL : x ∈ L) (hN : 7 ≤ N)
    (F : GGQTwoXInLUFrame Bs (ggG0 3 B x L D J) N K) :
    ∃ n : ℕ, 3 ∣ n ∧ 6 ≤ n ∧ Nonempty (GGQTwoXInLUCoord Bs (ggG0 3 B x L D J) L x n K) := by
  obtain ⟨I, lam, z, hlam, hI, hL, hz, hzx⟩ := ggQTwoXInLU_blockX hS hxL hN F
  obtain ⟨j₀, rfl⟩ := ggQTwoXInLU_compl hS hN F hlam hI hL hz hzx
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 6 ≤ n := by omega
  obtain ⟨h3, ⟨C⟩⟩ := ggQTwoXInLU_coordAt hS hn F hlam hL hz hzx
  obtain ⟨C', -, -⟩ := C.relabel (Equiv.swap 0 j₀) (Equiv.swap_apply_left 0 j₀)
  exact ⟨n, h3, hn, ⟨C'.toCoord⟩⟩

end CFSG.StandardType

end

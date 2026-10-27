module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2dAuxTrans
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2dAuxLam

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin

theorem levTwoS2d_Phi_eq_lambda (n : ℕ) (hn : 4 ≤ n) (p : ℕ) [Fact p.Prime] (_hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) :
    Φ = {β | IsRt (isFiniteType_cartanD n) β ∧ lam c β = 0} := by
  ext β
  constructor
  · intro hβ; exact ⟨hΦ.isRt β hβ, hΦ.fix β hβ⟩
  · rintro ⟨hβrt, hβlam⟩
    obtain ⟨s, hsΦ, -, hcard, -⟩ := hΦ.rank
    obtain ⟨α, hαs⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
    have hαΦ : α ∈ Φ := hsΦ (Finset.mem_coe.mpr hαs)
    obtain ⟨w, hw⟩ := levTwoS2d_isRt_transitive n hn (hΦ.isRt α hαΦ) hβrt
    exact hΦ.sat β hβrt hβlam ⟨α, hαΦ, w, hw⟩

end CFSG.StandardType.LevTwo

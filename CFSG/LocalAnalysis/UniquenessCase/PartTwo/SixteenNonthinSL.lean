module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfCover
import CFSG.Quasithin.Background.F918D9
import CFSG.Quasithin.Background.JonesParshallSLFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem s16nt_cover_sl_of_four_le {K : Type} [Field K] [Finite K] {n m : ℕ} (hn : 4 ≤ n)
    (hK : Nat.card K = 2 ^ m) : S16BoundCover (FFModel.nat (StatedSL n K)) 0 := by
  intro W _ _ hW2 H Z hZ hcomm hreal
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ m := by rw [← Nat.card_eq_fintype_card]; exact hK
  have : CharP K 2 := charP_of_card_eq_prime_pow hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hπ
  have hcomm' : XMod.commOf ↥H (⊤ : Subgroup W) = ⊤ := by
    rw [commOf_eq_commSub, ← commV_eq_commSub]; exact hcomm
  have hcard := card_le_pow_finrank_H1_dual (Γ := ↥(StatedSL n K)) hW2 H ⊤ Z le_top
    (fun z hz x hx => mem_fixV.1 (hZ hz) x hx) (fun x hx v hv => Subgroup.mem_top _) hcomm'
    π hπ.1 (SLCover.natRepQ n K) β hβs hβk (fun γ v hv => hβe γ v hv)
  rwa [CFSG.Quasithin.JonesParshall.finrank_H1_SL_of_four_le hn
    (SLCover.binaryNaturalSL_dual n K)] at hcard

theorem s16nt_cover_sl_three {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 1 < m)
    (hK : Nat.card K = 2 ^ m) : S16BoundCover (FFModel.nat (StatedSL 3 K)) 0 := by
  intro W _ _ hW2 H Z hZ hcomm hreal
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ m := by rw [← Nat.card_eq_fintype_card]; exact hK
  have : CharP K 2 := charP_of_card_eq_prime_pow hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hπ
  have hcomm' : XMod.commOf ↥H (⊤ : Subgroup W) = ⊤ := by
    rw [commOf_eq_commSub, ← commV_eq_commSub]; exact hcomm
  have hcard := card_le_pow_finrank_H1_dual (Γ := ↥(StatedSL 3 K)) hW2 H ⊤ Z le_top
    (fun z hz x hx => mem_fixV.1 (hZ hz) x hx) (fun x hx v hv => Subgroup.mem_top _) hcomm'
    π hπ.1 (SLCover.natRepQ 3 K) β hβs hβk (fun γ v hv => hβe γ v hv)
  rwa [CFSG.Quasithin.JonesParshall.finrank_H1_SL3_of_one_lt hF hm
    (SLCover.binaryNaturalSL_dual 3 K)] at hcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end

module

public import CFSG.LocalAnalysis.StandardType.GGFrameTBInputs
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteEndLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly TableB CFSG.Open

theorem frameTBRange_of_torusLift {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J) {n : ℕ} (hn : n = 7 ∨ n = 8)
    (hBs : Nat.card Bs = 3 ^ n) (hL : commutator L = ⊤) {lab : LargeEvenLabel} {R : Type}
    [Group R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    (hlift : lab.tag = .twA → GGTorusLift 3 (ggUnitaryTorusRank 3 (lab.rank + 1)) R)
    (hlift8 : lab.tag = .E8 → GGTorusLift 3 7 R) :
    frameTBRange lab (n - 1) := by
  have hcfg := hR.1
  obtain ⟨-, -, -, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hm : ∀ {r : ℕ}, GGTorusLift 3 r R → r + 1 ≤ LargeEvenTwoLocalRank 3 G := fun h =>
    succ_le_twoLocalRank_of_torusLift Nat.prime_three hLx (hS.1.1.2 x hS.2.1) hS.2.2.1 hL θ h
  have hBc : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hS.1.2.1
  have hBle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.2.1.1
  have hle : LargeEvenTwoLocalRank 3 G ≤ n :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (by rw [← hBc, ← hBs]; exact hBle)
  refine frameTBRange_of_dimension hn (fun htag => ?_) (fun htag => ?_)
  · have h := hm (hlift htag)
    unfold ggUnitaryTorusRank at h
    split_ifs at h <;> omega
  · have h := hm (hlift8 htag)
    rcases hn with rfl | rfl <;> omega

end CFSG.StandardType.FrameRoute

end

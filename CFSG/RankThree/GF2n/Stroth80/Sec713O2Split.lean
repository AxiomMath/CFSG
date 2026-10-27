module

public import CFSG.RankThree.GF2n.Stroth80.Sec713O2Easy

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG

@[expose] def Step713O2HardStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → ¬ OmegaPlusNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    pCore 2 (MbarPrime M Q Z Z0) ≤
      ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))).subgroupOf (MbarPrime M Q Z Z0)

theorem step713O2_of_hard (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (hA : Sec7AExistsStatement) (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hHard : Step713O2HardStatement) : Step713O2Statement := by
  intro G _ _ M Q Z B _ hc n t hs hn4 Z0 hZ0
  classical
  let K : Subgroup (Mbar M Q) := bar M Q (NormH0 M Z Z0)
  let H : Subgroup (Mbar M Q) := bar M Q (H0 M Z)
  let Nbar : Subgroup (Mbar M Q) := bar M Q (hc.CN t)
  let N' : Subgroup H := Nbar.subgroupOf H
  let M' : Subgroup H := K.subgroupOf H
  have hKH : K ≤ H := MbarPrimeLe M Q Z Z0
  have hHardM' : pCore 2 ↥M' ≤ N'.subgroupOf M' :=
    hHard G M Q Z B hc n t hs hn4 Z0 hZ0
  have hEasyM' : N'.subgroupOf M' ≤ pCore 2 ↥M' :=
    CN_le_pCore_two_MbarPrime h34 h51 hA hZt hZcard hc hs hZ0
  have hEqM' : pCore 2 ↥M' = N'.subgroupOf M' := le_antisymm hHardM' hEasyM'
  let e : ↥M' ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKH
  have hmapP : (pCore 2 ↥M').map e.toMonoidHom = pCore 2 ↥K :=
    CFSG.pCore_map_iso 2 e
  have hmapN : (N'.subgroupOf M').map e.toMonoidHom = Nbar.subgroupOf K := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨⟨y.1, hKH y.2⟩, y.2⟩, hy, rfl⟩
  show pCore 2 ↥K = Nbar.subgroupOf K
  calc pCore 2 ↥K = (pCore 2 ↥M').map e.toMonoidHom := hmapP.symm
    _ = (N'.subgroupOf M').map e.toMonoidHom := by rw [hEqM']
    _ = Nbar.subgroupOf K := hmapN

end CFSG.RankThree.GF2n.Stroth80

module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinData
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-! The ambient quotient `Ĥ/(VU) ≃ D₆` has index six, and this index is
unchanged after transporting both subgroups by an inner automorphism. -/

public theorem firstCase_klein_conjugate_VU_index_six
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (g : G) :
    ((conjugateSubgroup (twoCoreOf c.Hhat ⊔ c.U) g⁻¹).subgroupOf
      (conjugateSubgroup c.Hhat g⁻¹)).index = 6 := by
  let B : Subgroup G := twoCoreOf c.Hhat ⊔ c.U
  let H : Subgroup G := c.Hhat
  let e : G →* G := (MulAut.conj g⁻¹).toMonoidHom
  have hBleH : B ≤ H := by
    have h26 := theorem_2_6 hmin c
    dsimp [B, H]
    apply sup_le
    · exact Subgroup.map_subtype_le (pCore 2 c.Hhat)
    · rw [h26.1]
      exact Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat)
  have hBindex : (B.subgroupOf H).index = 6 := by
    let B0 : Subgroup (↥H) := B.subgroupOf H
    let Bjoin : Subgroup (↥H) := pCore 2 H ⊔ pPrimeCore 2 H
    have hBjoinmap : Bjoin.map H.subtype = B := by
      have h26 := theorem_2_6 hmin c
      dsimp [B, H, Bjoin]
      rw [Subgroup.map_sup]
      simp [twoCoreOf, oddCoreOf, h26.1]
    have hBjoin0 : Bjoin = B0 := by
      ext z
      constructor
      · intro hz
        apply (Subgroup.mem_subgroupOf).2
        rw [← hBjoinmap]
        exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      · intro hz
        have hzB : (z : G) ∈ B := (Subgroup.mem_subgroupOf).1 hz
        rw [← hBjoinmap] at hzB
        rcases Subgroup.mem_map.mp hzB with ⟨w, hw, hwz⟩
        have hweq : w = z := by
          apply Subtype.ext
          simpa using hwz
        simpa [hweq] using hw
    have hqcard : Nat.card (H ⧸ B0) = 6 := by
      obtain ⟨eq⟩ := firstCase_klein_quotient_d6 hmin c hfirst hklein
      calc
        Nat.card (H ⧸ B0) = Nat.card (H ⧸ Bjoin) := by rw [hBjoin0]
        _ = Nat.card (DihedralGroup 3) := by
          simpa [H, Bjoin] using Nat.card_congr eq.toEquiv
        _ = 6 := by rw [DihedralGroup.nat_card]
    have hidx : B0.index = 6 := by
      rw [Subgroup.index_eq_card]
      exact hqcard
    simpa [B0] using hidx
  have hrel : (B.map e).relIndex (H.map e) = B.relIndex H := by
    exact Subgroup.relIndex_map_map_of_injective B H
      (MulAut.conj g⁻¹).injective
  have htarget :
      ((conjugateSubgroup (twoCoreOf c.Hhat ⊔ c.U) g⁻¹).subgroupOf
        (conjugateSubgroup c.Hhat g⁻¹)).index =
      (B.subgroupOf H).index := by
    change (B.map e).relIndex (H.map e) = B.relIndex H
    exact hrel
  rw [htarget, hBindex]

end CFSG.GorensteinWalter

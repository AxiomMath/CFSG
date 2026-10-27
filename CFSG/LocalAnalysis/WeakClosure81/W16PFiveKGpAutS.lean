module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveSubgroup
public import CFSG.GH74.Uniqueness.Bender.Aut
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup
open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise

theorem Shape166.exists_eq_conj_of_isSz
    {X : Type} [Group X] [Finite X] {Y : Subgroup X} {n : ℕ}
    (hSz : CFSG.Quasithin.IsSz n X) (hY : IsElemAbelian 2 Y)
    (hcardY : Nat.card Y = 2 ^ n) (α : MulAut X) (hα : α * α = 1)
    (hαY : ∀ y ∈ Y, α y = y) : ∃ y ∈ Y, α = MulAut.conj y := by
  have hB : BenderType X n 2 1 := rankOne_benderType_sz hSz
  obtain ⟨l, hll, hσ⟩ := hB.exists_inner_of_sq_eq_one_suzuki α hα
  have hY2 : IsPGroup 2 Y := IsPGroup.of_card (n := n) hcardY
  obtain ⟨S, hYS⟩ := hY2.exists_le_sylow
  obtain ⟨t, hc⟩ := hB.exists_benderCore S
  have hYroot : Y ≤ rootCenter (S : Subgroup X) :=
    hc.elemAbelian_le_rootCenter hYS fun z hz => by
      have := hY.2 z hz
      simpa [sq] using this
  have hYrootEq : Y = rootCenter (S : Subgroup X) :=
    Subgroup.eq_of_le_of_card_ge hYroot (by rw [hcardY, hc.card_center])
  have hlS : l ∈ (S : Subgroup X) := by
    have hcent : l ∈ Subgroup.centralizer (Y : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : l * y * l⁻¹ = y := by
        rw [← hσ y]
        exact hαY y hy
      have h1 : l * y = y * l := by
        rw [← mul_inv_eq_iff_eq_mul]
        exact hy'
      exact h1.symm
    have hcentEq : Subgroup.centralizer (Y : Set X) = (S : Subgroup X) := by
      rw [hYrootEq, hc.centralizer_rootCenter_eq, hc.fixCartan_eq_bot, sup_bot_eq]
    exact hcentEq ▸ hcent
  have hlroot : l ∈ rootCenter (S : Subgroup X) := hc.mem_rootCenter_of_mul_self hlS hll
  have hlY : l ∈ Y := by rw [hYrootEq]; exact hlroot
  exact ⟨l, hlY, MulEquiv.ext fun k => hσ k⟩

end CFSG.LocalAnalysis.WeakClosure81

end

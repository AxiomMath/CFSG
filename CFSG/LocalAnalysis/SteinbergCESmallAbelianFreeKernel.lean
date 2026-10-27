module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.LocalAnalysis

open scoped IsMulCommutative

namespace FreeKernel

theorem card_dvd_card_of_free {H X : Type*} [Group H] [Finite H] [MulAction H X] [Finite X]
    (Y : Set X) (hY : ∀ h : H, ∀ y ∈ Y, h • y ∈ Y)
    (hfree : ∀ h : H, ∀ y ∈ Y, h • y = y → h = 1) : Nat.card H ∣ Nat.card Y := by
  classical
  let Ys : SubMulAction H X := { carrier := Y, smul_mem' := fun h y hy => hY h y hy }
  let := Fintype.ofFinite H
  let := Fintype.ofFinite Ys
  let := Fintype.ofFinite (Quotient (MulAction.orbitRel H Ys))
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group H Ys
  rw [Finset.sum_eq_single (1 : H)] at hB
  · have h1 : Fintype.card (MulAction.fixedBy Ys (1 : H)) = Fintype.card Ys :=
      Fintype.card_congr (Equiv.subtypeUnivEquiv fun y => one_smul H y)
    rw [h1] at hB
    change Nat.card H ∣ Nat.card Ys
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hB]
    exact Dvd.intro_left _ rfl
  · intro g _ hg
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨y, hy⟩ => hg (hfree g y y.2 (congrArg Subtype.val hy))⟩
  · intro h
    exact absurd (Finset.mem_univ 1) h

variable (p : ℕ) [Fact p.Prime] (H A : Type*) [Group H] [CommGroup A] [IsElementaryAbelian p A]
  [MulDistribMulAction H A]

end FreeKernel

open FreeKernel

end CFSG.LocalAnalysis

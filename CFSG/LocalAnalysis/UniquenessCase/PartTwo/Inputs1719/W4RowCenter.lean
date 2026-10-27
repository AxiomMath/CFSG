module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Inner
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.QuasithinUnique.Setup.X1

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} {S : Type} [Group S]

theorem odd_card_center_of_o2Trivial (hO2 : O2Trivial L) :
    Odd (Nat.card (Subgroup.center ↥L)) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥L) 2
    (even_iff_two_dvd.1 hev)
  have hzL : orderOf (x : ↥L) = 2 := by rw [Subgroup.orderOf_coe, hx]
  have hzW : orderOf ((x : ↥L) : MulAut W) = 2 := by rw [Subgroup.orderOf_coe, hzL]
  let P : Subgroup (MulAut W) := Subgroup.zpowers ((x : ↥L) : MulAut W)
  have hP2 : IsPGroup 2 P :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzW]; norm_num)
  have hPnorm : (P.subgroupOf L).Normal := by
    have hzpow : P.subgroupOf L = Subgroup.zpowers (x : ↥L) := by
      ext y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext hk⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, congrArg Subtype.val hk⟩
    rw [hzpow]
    exact Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 x.2)
  have hmem : ((x : ↥L) : MulAut W) ∈ P := Subgroup.mem_zpowers _
  rw [hO2 P (Subgroup.zpowers_le.2 (x : ↥L).2) hPnorm hP2, Subgroup.mem_bot] at hmem
  rw [hmem, orderOf_one] at hzW
  norm_num at hzW

theorem center_eq_bot_of_o2Trivial_of_cover (hperf : Group.IsPerfect ↥L) (hO2 : O2Trivial L)
    (e₀ : (↥L ⧸ Subgroup.center ↥L) ≃* S)
    (hCover : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥) :
    Subgroup.center ↥L = ⊥ := by
  have hker : (redHom L e₀).ker = Subgroup.center ↥L := by
    ext y
    rw [MonoidHom.mem_ker, redHom_eq_one_iff L e₀ y]
  rw [← hker]
  exact hCover ↥L (redHom L e₀) (redHom_surjective L e₀) hker.le
    (by rw [hker]; exact odd_card_center_of_o2Trivial hO2)

theorem exists_orderOf_eq_two_of_cq (e₀ : (↥L ⧸ Subgroup.center ↥L) ≃* S)
    (h2 : 2 ∣ Nat.card S) : ∃ t ∈ L, orderOf t = 2 := by
  have h2Q : 2 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    rwa [Nat.card_congr e₀.toEquiv]
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2
    (h2Q.trans (Subgroup.card_quotient_dvd_card (Subgroup.center ↥L)))
  exact ⟨t, t.2, by rwa [Subgroup.orderOf_coe]⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

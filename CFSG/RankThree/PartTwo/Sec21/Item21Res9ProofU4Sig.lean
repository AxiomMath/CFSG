module

public import CFSG.CGT.T75N.L29Rad
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.LocalRank.PrimeComplementCentralizesNormal
public import CFSG.RankThree.PartTwo.Sec3.ThompsonFamilyG
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)

namespace Item21Res9Proof

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_zpowers_zpow_of_cube {c : G} (hc3 : c ^ 3 = 1) {k : ℤ} (hk : ¬ (3 : ℤ) ∣ k) :
    c ∈ zpowers (c ^ k) := by
  refine ⟨k, ?_⟩
  change (c ^ k) ^ k = c
  rw [← zpow_mul]
  have hc3' : c ^ (3 : ℤ) = 1 := by rw [zpow_ofNat, hc3]
  have hkk : k * k % 3 = 1 := by
    have : k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases this with h | h <;> simp [Int.mul_emod, h]
  rw [zpow_eq_zpow_emod (k * k) hc3', hkk, zpow_one]

theorem weak_of_fus {c : G}
    (hfus : ∀ g : G, g * c * g⁻¹ ∈ normalizer ((zpowers c : Subgroup G) : Set G) →
      g * c * g⁻¹ ∈ zpowers c) (g : G)
    (hg : (zpowers c).map (MulAut.conj g).toMonoidHom ≤ normalizer (zpowers c : Set G)) :
    (zpowers c).map (MulAut.conj g).toMonoidHom = zpowers c := by
  rw [MonoidHom.map_zpowers] at hg ⊢
  have hgc : g * c * g⁻¹ ∈ zpowers c := hfus g (hg (mem_zpowers _))
  have hle : zpowers ((MulAut.conj g).toMonoidHom c) ≤ zpowers c := zpowers_le.mpr hgc
  refine eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective c).symm.le

end Item21Res9Proof

open Item21Res9Proof

end CFSG.RankThree.PartTwo.Sec21

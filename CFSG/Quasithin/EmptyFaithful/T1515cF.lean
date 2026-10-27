module

public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.ComponentClassification

variable {G : Type} [Group G] [Finite G]

theorem le_oddCoreIn_of_isSubnormal1515c {X S : Subgroup G} (hS : IsSubnormal S X)
    (hodd : Odd (Nat.card S)) : S ≤ oddCoreIn X := by
  intro s hs
  have hSO : (⟨s, hs⟩ : S) ∈ componentClassificationOddCore S :=
    OddCore.maximal S ⊤ inferInstance (by simpa using hodd) (Subgroup.mem_top _)
  obtain ⟨hX, hXO⟩ := (OddCore.subnormal_mem_iff hS s hs).mp hSO
  exact ⟨⟨s, hX⟩, hXO, rfl⟩

theorem isPGroup_two_center_of_isComponentOf1515c {L H : Subgroup G} (hL : IsComponentOf L H)
    (hO : oddCoreIn H = ⊥) : IsPGroup 2 (Subgroup.center ↥L) := by
  intro z
  set x : G := (((z : ↥(Subgroup.center ↥L)) : ↥L) : G) with hx
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
  set w : G := x ^ 2 ^ k with hw
  have hwo : Odd (orderOf w) := by
    rw [hw, orderOf_pow' _ h2k, hkm, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  have hxL : x ∈ L := ((z : ↥(Subgroup.center ↥L)) : ↥L).2
  have hwL : w ∈ L := L.pow_mem hxL _
  have hcomm : ∀ l ∈ L, l * w = w * l := by
    intro l hl
    have hzc := Subgroup.mem_center_iff.mp z.2 ⟨l, hl⟩
    have hxl : l * x = x * l := congrArg Subtype.val hzc
    exact ((Commute.pow_right (show Commute l x from hxl) (2 ^ k)).eq)
  have hleL : Subgroup.zpowers w ≤ L := Subgroup.zpowers_le.mpr hwL
  have hnormL : ((Subgroup.zpowers w).subgroupOf L).Normal := by
    refine Subgroup.normal_of_le_center ?_
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    show (l : G) * (g : G) = (g : G) * (l : G)
    have hc : Commute (l : G) w := hcomm l l.2
    rw [← hn]
    exact (hc.zpow_right n).eq
  have hsubL : IsSubnormal (Subgroup.zpowers w) L := A3.subnormal_of_normal hleL hnormL
  have hsubH : IsSubnormal (Subgroup.zpowers w) H := A3.subnormal_trans hsubL hL.2.1
  have hodd : Odd (Nat.card (Subgroup.zpowers w)) := by
    rw [Nat.card_zpowers]
    exact hwo
  have hle := le_oddCoreIn_of_isSubnormal1515c hsubH hodd
  rw [hO] at hle
  have hw1 : w = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers w))
  exact ⟨k, Subtype.ext (Subtype.ext (by simpa [hx, hw] using hw1))⟩

end CFSG.Quasithin

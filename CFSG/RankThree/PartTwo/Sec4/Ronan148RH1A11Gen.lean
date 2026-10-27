module

public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec14.Ronan148RH2Inner
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SCenter
public import CFSG.RankThree.PartTwo.Sec4.RonanK429Rows

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.RankThree.PartTwo.Sec14.Ronan148R (exists_inner_rep)

section Gen

variable {G : Type} [Group G] [Finite G]

theorem card_sup_of_commute_of_inf {H K : Subgroup G}
    (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) (hinf : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute H K hc).1
  rw [hinf, Subgroup.card_bot, mul_one] at h
  exact h

theorem eq_one_of_mem_centralizer_of_partTwo (hEF : partTwoE G = partTwoF G)
    {L F F' : Subgroup G} (hZ : ∀ x ∈ L, x ∈ Subgroup.centralizer (L : Set G) → x = 1)
    (hF'L : F' ≤ L) (hFF' : F ≤ F') (hF : CFSG.Assembly.IsElemAbelian 3 F)
    (hF9 : Nat.card F = 9) (hF' : CFSG.Assembly.IsElemAbelian 3 F') (hF'27 : Nat.card F' = 27)
    {t : G} (htL : t ∈ L) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (htF : ∀ f ∈ F, t * f = f * t)
    {w : G} (hw : w ∈ Subgroup.centralizer (L : Set G)) (hw3 : w ^ 3 = 1) : w = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hw1
  have hW : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers w) :=
    CFSG.RankThree.PartTwo.Sec13.isElemAbelian_zpowers hw3
  have hWc : Nat.card (Subgroup.zpowers w) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hw3 hw1]
  have hWC : Subgroup.zpowers w ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.zpowers_le.mpr hw
  have hLW : ∀ x ∈ L, ∀ y ∈ Subgroup.zpowers w, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hWC hy) x hx
  have hinf : ∀ {H : Subgroup G}, H ≤ L → H ⊓ Subgroup.zpowers w = ⊥ := by
    intro H hH
    rw [eq_bot_iff]
    rintro x ⟨hxH, hxW⟩
    exact Subgroup.mem_bot.mpr (hZ x (hH hxH) (hWC hxW))
  have hFL : F ≤ L := hFF'.trans hF'L
  have hcF : ∀ x ∈ F, ∀ y ∈ Subgroup.zpowers w, x * y = y * x := fun x hx y hy =>
    hLW x (hFL hx) y hy
  have hE : CFSG.Assembly.IsElemAbelian 3 (F ⊔ Subgroup.zpowers w) :=
    CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup hF hW hcF
  have hEc : Nat.card ↥(F ⊔ Subgroup.zpowers w) = 27 := by
    rw [card_sup_of_commute_of_inf hcF (hinf hFL), hF9, hWc]
  have hEt : F ⊔ Subgroup.zpowers w ≤
      Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · intro f hf
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hx)
      exact ((Commute.zpow_left (show Commute t f from htF f hf) k)).eq
    · intro y hy
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hx)
      exact ((Commute.zpow_left (show Commute t y from hLW t htL y hy) k)).eq
  have ht2' : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hEmem : F ⊔ Subgroup.zpowers w ∈ partTwoE G :=
    ⟨hE, hEc, Subgroup.zpowers t, fun h => ht1 (Subgroup.zpowers_eq_bot.mp h),
      IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, ht2'] <;> norm_num⟩, hEt⟩
  have hcF' : ∀ x ∈ F', ∀ y ∈ Subgroup.zpowers w, x * y = y * x := fun x hx y hy =>
    hLW x (hF'L hx) y hy
  have hB : CFSG.Assembly.IsElemAbelian 3 (F' ⊔ Subgroup.zpowers w) :=
    CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup hF' hW hcF'
  have hBc : Nat.card ↥(F' ⊔ Subgroup.zpowers w) = 81 := by
    rw [card_sup_of_commute_of_inf hcF' (hinf hF'L), hF'27, hWc]
  have hEB : F ⊔ Subgroup.zpowers w ≤ F' ⊔ Subgroup.zpowers w := sup_le_sup_right hFF' _
  obtain ⟨M, hBM, hmax⟩ := Finite.exists_le_maximal
    (p := fun M : Subgroup G => CFSG.Assembly.IsElemAbelian 3 M) hB
  have hMF : M ∈ partTwoF G :=
    ⟨hmax.prop, fun B' hB' hMB' => le_antisymm (hmax.2 hB' hMB') hMB',
      F ⊔ Subgroup.zpowers w, hEmem, le_trans hEB hBM⟩
  have hME : M ∈ partTwoE G := by
    rw [hEF]
    exact hMF
  have hle := Subgroup.card_le_of_le hBM
  rw [hBc, hME.2.1] at hle
  norm_num at hle

theorem le_of_inner_of_centralizer {L A : Subgroup G} (hZ : Subgroup.center L = ⊥)
    (hcube : CubeInner L) (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hC : ∀ w ∈ Subgroup.centralizer (L : Set G), w ^ 3 = 1 → w = 1) : A ≤ L := by
  intro a ha
  have ha3 : a ^ 3 = 1 := hA.2 a ha
  obtain ⟨aL, haL, haL3, hrep⟩ := exists_inner_rep hZ hcube (hAN ha) ha3
  have hwC : aL⁻¹ * a ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := hrep l hl
    calc l * (aL⁻¹ * a) = aL⁻¹ * (aL * l * aL⁻¹) * a := by group
      _ = aL⁻¹ * (a * l * a⁻¹) * a := by rw [h1]
      _ = aL⁻¹ * a * l := by group
  have hcomm : a * aL = aL * a := by
    have h1 := hrep aL haL
    calc a * aL = a * aL * a⁻¹ * a := by group
      _ = aL * aL * aL⁻¹ * a := by rw [h1]
      _ = aL * a := by group
  have hw3 : (aL⁻¹ * a) ^ 3 = 1 := by
    have hc : Commute aL⁻¹ a := (Commute.inv_left (show Commute aL a from hcomm.symm))
    rw [hc.mul_pow, inv_pow, haL3, ha3, inv_one, one_mul]
  have hw1 := hC _ hwC hw3
  have : a = aL := by
    calc a = aL * (aL⁻¹ * a) := by group
      _ = aL := by rw [hw1, mul_one]
  rw [this]
  exact haL

end Gen

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end

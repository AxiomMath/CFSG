module

public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type*} [Group G] [Finite G]

private theorem r148r_comm {H : Subgroup G} (h : CFSG.Assembly.IsElemAbelian 3 H)
    {x y : G} (hx : x ∈ H) (hy : y ∈ H) : x * y = y * x := by
  have := h.1
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : H) ⟨y, hy⟩)

private theorem r148r_isElemAbelian_of_le {H K : Subgroup G}
    (h : CFSG.Assembly.IsElemAbelian 3 H) (hK : K ≤ H) :
    CFSG.Assembly.IsElemAbelian 3 K := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => h.2 x (hK hx)⟩
  exact r148r_comm h (hK a.2) (hK b.2)

private theorem r148r_exists_nine {W : Subgroup G} (hWe : CFSG.Assembly.IsElemAbelian 3 W)
    (hgt : 3 < Nat.card W) :
    ∃ W' : Subgroup G, W' ≤ W ∧ CFSG.Assembly.IsElemAbelian 3 W' ∧ Nat.card W' = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWpg : IsPGroup 3 W := fun g => ⟨1, Subtype.ext (by simpa using hWe.2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hWpg
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have h1 : 3 ^ k ≤ 3 := by
      calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 3 := by norm_num
    rw [hk] at hgt
    exact absurd hgt (not_lt.mpr h1)
  have hdvd : 3 ^ 2 ∣ Nat.card W := by
    rw [hk]
    exact pow_dvd_pow 3 hk2
  obtain ⟨W₀, hW₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  refine ⟨W₀.map W.subtype, Subgroup.map_subtype_le W₀,
    r148r_isElemAbelian_of_le hWe (Subgroup.map_subtype_le W₀), ?_⟩
  rw [Subgroup.card_map_of_injective W.subtype_injective, hW₀] <;> norm_num

private theorem r148r_inf_zpowers_bot {x y : G} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hyx : y ∉ Subgroup.zpowers x) :
    Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDc : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hZc : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hy3 hy1]
  have hdvd : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers y) ∣ 3 := by
    have h := Subgroup.card_dvd_of_le
      (inf_le_left : Subgroup.zpowers x ⊓ Subgroup.zpowers y ≤ Subgroup.zpowers x)
    rwa [hDc] at h
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    have hle : Subgroup.zpowers x ⊓ Subgroup.zpowers y = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [hDc, h3]))
    have hsub : Subgroup.zpowers x ≤ Subgroup.zpowers y := inf_eq_left.mp hle
    have heq : Subgroup.zpowers x = Subgroup.zpowers y :=
      Subgroup.eq_of_le_of_card_ge hsub (le_of_eq (by rw [hZc, hDc]))
    exact hyx (by rw [heq]; exact Subgroup.mem_zpowers y)

private theorem r148r_card_sup {H K : Subgroup G}
    (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) (hinf : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute H K hc).1
  rw [hinf, Subgroup.card_bot, mul_one] at h
  exact h

private theorem r148r_mem_normalizer {g t : G} (h : t * g = g * t) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
  refine Subgroup.centralizer_le_normalizer ((Subgroup.zpowers t : Subgroup G) : Set G)
    (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hx)
  exact ((show Commute t g from h).zpow_left k).eq

theorem card_le_three_of_partTwo (hEF : partTwoE G = partTwoF G) {L W : Subgroup G}
    (hZ : Subgroup.center L = ⊥) {dL t f : G} (hdL : dL ∈ L) (hdL3 : dL ^ 3 = 1)
    (hdL1 : dL ≠ 1) (htL : t ∈ L) (ht2 : orderOf t = 2) (htd : t * dL = dL * t)
    (hfL : f ∈ L) (hf3 : f ^ 3 = 1) (hfd : f * dL = dL * f) (hfn : f ∉ Subgroup.zpowers dL)
    (hW : W ≤ Subgroup.centralizer (L : Set G)) (hWe : CFSG.Assembly.IsElemAbelian 3 W) :
    Nat.card W ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hgt
  rw [not_le] at hgt
  have hLW : ∀ x ∈ L, ∀ w ∈ W, x * w = w * x := fun x hx w hw =>
    Subgroup.mem_centralizer_iff.mp (hW hw) x hx
  have hLWb : L ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxL, hxW⟩
    rw [Subgroup.mem_bot]
    have hxc : (⟨x, hxL⟩ : L) ∈ Subgroup.center L :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hLW g.1 g.2 x hxW)
    rw [hZ, Subgroup.mem_bot] at hxc
    exact congrArg Subtype.val hxc
  have hbot : ∀ {H K : Subgroup G}, H ≤ L → K ≤ W → H ⊓ K = ⊥ := by
    intro H K hH hK
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ L ⊓ W := ⟨hH hx.1, hK hx.2⟩
    rw [hLWb] at hx'
    exact hx'
  obtain ⟨W', hW'W, hW'e, hW'card⟩ := r148r_exists_nine hWe hgt
  have hDL : Subgroup.zpowers dL ≤ L := Subgroup.zpowers_le.mpr hdL
  have hFL : Subgroup.zpowers f ≤ L := Subgroup.zpowers_le.mpr hfL
  have hDc : Nat.card (Subgroup.zpowers dL) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hdL3 hdL1]
  have hf1 : f ≠ 1 := fun h => hfn (h ▸ Subgroup.one_mem _)
  have hFc : Nat.card (Subgroup.zpowers f) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hf3 hf1]
  have hcommDF : ∀ x ∈ Subgroup.zpowers dL, ∀ y ∈ Subgroup.zpowers f, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((show Commute dL f from hfd.symm).zpow_zpow i j).eq
  have hDFe : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers dL ⊔ Subgroup.zpowers f) :=
    CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup
      (CFSG.RankThree.PartTwo.Sec13.isElemAbelian_zpowers hdL3)
      (CFSG.RankThree.PartTwo.Sec13.isElemAbelian_zpowers hf3) hcommDF
  have hDFc : Nat.card ↥(Subgroup.zpowers dL ⊔ Subgroup.zpowers f) = 9 := by
    rw [r148r_card_sup hcommDF (r148r_inf_zpowers_bot hdL3 hdL1 hf3 hf1 hfn), hDc, hFc]
      <;> norm_num
  have hDW : ∀ x ∈ Subgroup.zpowers dL, ∀ y ∈ W', x * y = y * x := fun x hx y hy =>
    hLW x (hDL hx) y (hW'W hy)
  have hDWe : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers dL ⊔ W') :=
    CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup
      (CFSG.RankThree.PartTwo.Sec13.isElemAbelian_zpowers hdL3) hW'e hDW
  have hDWc : Nat.card ↥(Subgroup.zpowers dL ⊔ W') = 27 := by
    rw [r148r_card_sup hDW (hbot hDL hW'W), hDc, hW'card] <;> norm_num
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hEnorm : Subgroup.zpowers dL ⊔ W' ≤
      Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (r148r_mem_normalizer htd))
      (fun w hw => r148r_mem_normalizer (hLW t htL w (hW'W hw)))
  have hEmem : Subgroup.zpowers dL ⊔ W' ∈ partTwoE G :=
    ⟨hDWe, hDWc, Subgroup.zpowers t, fun h => ht1 (Subgroup.zpowers_eq_bot.mp h),
      IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, ht2] <;> norm_num⟩, hEnorm⟩
  have hHL : Subgroup.zpowers dL ⊔ Subgroup.zpowers f ≤ L := sup_le hDL hFL
  have hcommB : ∀ x ∈ Subgroup.zpowers dL ⊔ Subgroup.zpowers f, ∀ y ∈ W', x * y = y * x :=
    fun x hx y hy => hLW x (hHL hx) y (hW'W hy)
  have hBe : CFSG.Assembly.IsElemAbelian 3
      ((Subgroup.zpowers dL ⊔ Subgroup.zpowers f) ⊔ W') :=
    CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup hDFe hW'e hcommB
  have hBc : Nat.card ↥((Subgroup.zpowers dL ⊔ Subgroup.zpowers f) ⊔ W') = 81 := by
    rw [r148r_card_sup hcommB (hbot hHL hW'W), hDFc, hW'card] <;> norm_num
  have hEB : Subgroup.zpowers dL ⊔ W' ≤ (Subgroup.zpowers dL ⊔ Subgroup.zpowers f) ⊔ W' :=
    sup_le (le_trans le_sup_left le_sup_left) le_sup_right
  obtain ⟨M, hBM, hmax⟩ := Finite.exists_le_maximal
    (p := fun M : Subgroup G => CFSG.Assembly.IsElemAbelian 3 M) hBe
  have hMF : M ∈ partTwoF G :=
    ⟨hmax.prop, fun B' hB' hMB' => le_antisymm (hmax.2 hB' hMB') hMB',
      Subgroup.zpowers dL ⊔ W', hEmem, le_trans hEB hBM⟩
  have hME : M ∈ partTwoE G := by
    rw [hEF]
    exact hMF
  have hle := Subgroup.card_le_of_le hBM
  rw [hBc, hME.2.1] at hle
  norm_num at hle

end CFSG.RankThree.PartTwo.Sec14.Ronan148R

end

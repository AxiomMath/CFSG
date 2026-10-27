module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217ALe

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint

theorem false_of_frame_big_abelian {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (a y : ↥L) (W : Subgroup ↥L) (ha : a ∉ Subgroup.center ↥L) (ha3 : a ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hay : a * y = y * a)
    (hyD : y ∉ Subgroup.zpowers a ⊔ Subgroup.center ↥L) (hW0 : W ≠ ⊥) (hW2 : IsPGroup 2 W)
    (haW : ∀ w ∈ W, a * w = w * a) (hyN : y ∈ Subgroup.normalizer (W : Set ↥L))
    (Dg : Subgroup G) (hDe : CFSG.Assembly.IsElemAbelian 3 Dg)
    (hDC : ∀ d ∈ Dg, ∀ x ∈ L, d * x = x * d) (hD9 : 9 ≤ Nat.card Dg)
    (h3 : CFSG.Assembly.RankThreeEven.localRank 3 G ≤ 3) : False := by
  set aG : G := (a : G) with haG
  set yG : G := (y : G) with hyG
  have haG3 : aG ^ 3 = 1 := by have := congrArg Subtype.val ha3; simpa using this
  have hyG3 : yG ^ 3 = 1 := by have := congrArg Subtype.val hy3; simpa using this
  have haG1 : aG ≠ 1 := by
    intro h1
    apply ha
    have : a = 1 := Subtype.ext h1
    rw [this]; exact one_mem _
  have hyG1 : yG ≠ 1 := fun h1 => hy1 (Subtype.ext h1)
  have hDa : ∀ d ∈ Dg, d * aG = aG * d := fun d hd => hDC d hd aG a.2
  have hDy : ∀ d ∈ Dg, d * yG = yG * d := fun d hd => hDC d hd yG y.2
  have hay' : aG * yG = yG * aG := congrArg Subtype.val hay
  have hae : CFSG.Assembly.IsElemAbelian 3 (zpowers aG) := isElemAbelian_zpowers haG3
  have hye : CFSG.Assembly.IsElemAbelian 3 (zpowers yG) := isElemAbelian_zpowers hyG3
  have hcommz : ∀ {H : Subgroup G} {g : G}, H ≤ centralizer ({g} : Set G) →
      ∀ x ∈ H, ∀ b ∈ zpowers g, x * b = b * x := by
    intro H g hH x hx b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have : Commute x g := mem_centralizer_singleton_iff.1 (hH hx)
    exact (this.zpow_right i).eq
  have hDa_le : Dg ≤ centralizer ({aG} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (hDa d hd)
  have hDy_le : Dg ≤ centralizer ({yG} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (hDy d hd)
  have haz_y : zpowers aG ≤ centralizer ({yG} : Set G) := by
    rw [zpowers_le]; exact mem_centralizer_singleton_iff.2 hay'
  set R₁ : Subgroup G := Dg ⊔ zpowers aG with hR₁
  set R₂ : Subgroup G := R₁ ⊔ zpowers yG with hR₂
  have hR₁e : CFSG.Assembly.IsElemAbelian 3 R₁ :=
    isElemAbelian_sup_of_commute hDe hae (hcommz hDa_le)
  have hR₁y : R₁ ≤ centralizer ({yG} : Set G) := sup_le hDy_le haz_y
  have hR₂e : CFSG.Assembly.IsElemAbelian 3 R₂ :=
    isElemAbelian_sup_of_commute hR₁e hye (hcommz hR₁y)
  have hcenter : ∀ z : ↥L, (z : G) ∈ Dg → z ∈ center ↥L := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hDC z hz g g.2).symm
  have hord_a : orderOf aG = 3 := orderOf_eq_prime haG3 haG1
  have hord_y : orderOf yG = 3 := orderOf_eq_prime hyG3 hyG1
  have hdisj1 : Disjoint Dg (zpowers aG) := by
    rw [Subgroup.disjoint_def]
    intro x hxD hxa
    rcases mem_zpowers_of_pow_three haG3 hxa with h1 | h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hxD
      exact ha (hcenter a hxD)
    · exfalso
      rw [h1] at hxD
      have h2 : (a ^ 2 : ↥L) ∈ center ↥L := hcenter (a ^ 2) (by simpa using hxD)
      apply ha
      have : a = (a ^ 2) ^ 2 := by
        have : (a ^ 2) ^ 2 = a ^ 3 * a := by group
        rw [this, ha3, one_mul]
      rw [this]; exact pow_mem h2 2
  have hcard1 : 3 * Nat.card Dg ≤ Nat.card R₁ := by
    have := card_mul_le_card_sup_of_disjoint Dg (zpowers aG) hdisj1
    rw [Nat.card_zpowers, hord_a] at this
    rw [hR₁]
    omega
  have hy_not_R₁ : yG ∉ R₁ := by
    intro hyR
    obtain ⟨d, hd, b, hb, hdb⟩ := (mem_sup_of_commute (hcommz hDa_le)).1 hyR
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    apply hyD
    have hdL : d ∈ L := by
      have : d = yG * (aG ^ i)⁻¹ := by rw [← hdb]; group
      rw [this]
      exact L.mul_mem y.2 (L.inv_mem (L.zpow_mem a.2 i))
    have hz : (⟨d, hdL⟩ : ↥L) ∈ center ↥L := hcenter _ hd
    have hy' : y = (⟨d, hdL⟩ : ↥L) * a ^ i := by
      apply Subtype.ext
      simpa using hdb.symm
    rw [hy']
    exact mul_mem (mem_sup_right hz) (mem_sup_left (zpow_mem_zpowers a i))
  have hdisj2 : Disjoint R₁ (zpowers yG) := by
    rw [Subgroup.disjoint_def]
    intro x hxR hxy
    rcases mem_zpowers_of_pow_three hyG3 hxy with h1 | h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hxR) hy_not_R₁
    · exfalso
      rw [h1] at hxR
      apply hy_not_R₁
      have : yG = (yG ^ 2) ^ 2 := by
        have : (yG ^ 2) ^ 2 = yG ^ 3 * yG := by group
        rw [this, hyG3, one_mul]
      rw [this]; exact pow_mem hxR 2
  have hcard2 : 3 * Nat.card R₁ ≤ Nat.card R₂ := by
    have := card_mul_le_card_sup_of_disjoint R₁ (zpowers yG) hdisj2
    rw [Nat.card_zpowers, hord_y] at this
    rw [hR₂]
    omega
  have hcard81 : 81 ≤ Nat.card R₂ := by omega
  set WG : Subgroup G := W.map L.subtype with hWG
  have hWG0 : WG ≠ ⊥ := by
    intro h0
    apply hW0
    rw [eq_bot_iff]
    intro w hw
    have : (w : G) ∈ WG := Subgroup.mem_map_of_mem L.subtype hw
    rw [h0, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  have hWG2 : IsPGroup 2 WG := hW2.of_surjective (L.subtype.subgroupMap W)
    (L.subtype.subgroupMap_surjective W)
  have hDN : Dg ≤ normalizer (WG : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (WG : Set G))
    intro d hd
    rw [mem_centralizer_iff]
    rintro _ ⟨w, -, rfl⟩
    exact (hDC d hd w w.2).symm
  have haN : zpowers aG ≤ normalizer (WG : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (WG : Set G))
    rw [zpowers_le, mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    exact (congrArg Subtype.val (haW w hw)).symm
  have hyN' : zpowers yG ≤ normalizer (WG : Set G) := by
    rw [zpowers_le]
    exact Subgroup.le_normalizer_map L.subtype (Subgroup.mem_map_of_mem L.subtype hyN)
  have hR₂N : R₂ ≤ normalizer (WG : Set G) := sup_le (sup_le hDN haN) hyN'
  obtain ⟨k, hk⟩ := isElemAbelian_card_eq_pow hR₂e
  have hk4 : 4 ≤ k := by
    by_contra hk4
    have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hle := le_localRank_of_elemAbelian hWG0 hWG2 hR₂e hR₂N hk
  omega

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

module

public import CFSG.OddTranspositions.HypothesisC
public import CFSG.OddTranspositions.DeltaCentSet

import CFSG.OddTranspositions.SixNineUnconditional
import CFSG.OddTranspositions.AalphaCommute
import CFSG.OddTranspositions.BlockAction
import CFSG.Timmesfeld.Bridge.OddLocalCommonBasic

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72

theorem disjoint_alpha_DalphaStar {G : Type*} [Group G] {D α : Set G} (hα : IsBlock D α) :
    Disjoint α (DalphaStar D α) := by
  rw [Set.disjoint_left]
  rintro x hxα ⟨β, hβ, hxβ⟩
  exact (mem_Dalpha_iff.mp hβ).2.2.1
    (eq_of_mem_of_mem_blockClass hα (mem_Dalpha_iff.mp hβ).1 (mem_blockClass_self α)
      ⟨x, hxβ, hxα⟩)

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem mem_DalphaStar_of_mem_D_of_not_mem_alpha_of_commute (hC : HypothesisC D) {u x : G}
    (hu : u ∈ hC.alpha) (hxD : x ∈ D) (hxα : x ∉ hC.alpha) (hxu : Commute x u) :
    x ∈ DalphaStar D hC.alpha := by
  have hx' : x ∈ hC.alpha ∪ DalphaStar D hC.alpha ∪ AalphaStar D hC.alpha := by
    rw [← hC.eq_alpha_union]
    exact hxD
  rcases hx' with (hxα' | hxS) | hxA
  · exact absurd hxα' hxα
  · exact hxS
  · exact absurd hxu (not_commute_of_mem_AalphaStar hC hxA hu)

theorem DalphaStar_subset_centSet_of_mem_alpha (hC : HypothesisC D) {u w v z : G}
    (hu : u ∈ hC.alpha) (hv : v ∈ hC.alpha) (htri : IsTriangle D u w v)
    (hbα : u * v * z ∈ hC.alpha) :
    DalphaStar D hC.alpha ⊆ centSet D z := by
  intro x hx
  obtain ⟨β, hβ, hxβ⟩ := mem_DalphaStar_iff.mp hx
  obtain ⟨-, -, -, hcomm⟩ := mem_Dalpha_iff.mp hβ
  have hxuv : Commute x (u * v) :=
    ((hcomm u hu x hxβ).symm).mul_right ((hcomm v hv x hxβ).symm)
  have hxb : Commute x (u * v * z) := (hcomm (u * v * z) hbα x hxβ).symm
  refine ⟨DalphaStar_subset hC.isBlock_alpha hx, ?_⟩
  have hz_eq : z = u * v * (u * v * z) := by
    calc z = (u * v * (u * v)) * z := by rw [htri.uv_mul_self hC.setup.oddT, one_mul]
      _ = u * v * (u * v * z) := by group
  rw [hz_eq]
  exact hxuv.mul_right hxb

theorem alpha_union_DalphaStar_subset_normalizer (hC : HypothesisC D) {u : G}
    (hu : u ∈ hC.alpha) :
    hC.alpha ∪ DalphaStar D hC.alpha ⊆ Subgroup.normalizer hC.alpha := by
  intro x hx
  rcases hx with hxα | hxStar
  · exact mem_normalizer_of_mem_alpha hC.isBlock_alpha hxα
  · obtain ⟨β, hβ, hxβ⟩ := mem_DalphaStar_iff.mp hxStar
    exact OddLocal.mem_normalizer_of_commute_of_isBlock hC.isBlock_alpha.isBlock hu
      ((mem_Dalpha_iff.mp hβ).2.2.2 u hu x hxβ).symm

theorem centSet_subset_alpha_of_transitive (hC : HypothesisC D) {u z : G} (hu : u ∈ hC.alpha)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x)
    (hsub : centSet D z ⊆ hC.alpha ∪ DalphaStar D hC.alpha) :
    centSet D z ⊆ hC.alpha := by
  have hKN : localGroup D z ≤ Subgroup.normalizer hC.alpha :=
    (Subgroup.closure_le (Subgroup.normalizer hC.alpha)).mpr
      (hsub.trans (alpha_union_DalphaStar_subset_normalizer hC hu))
  intro x hx
  obtain ⟨k, hk, hkx⟩ := htrans x hx
  have himg := Subgroup.mem_normalizer_iff_conj_image_eq.mp (hKN hk)
  have hmem : k * u * k⁻¹ ∈ hC.alpha := by
    rw [← himg]
    exact ⟨u, hu, rfl⟩
  rwa [← hkx]

theorem uvz_not_mem_alpha_of_mem_alpha (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {u w v : G} (hu : u ∈ hC.alpha) (hv : v ∈ hC.alpha) (htri : IsTriangle D u w v)
    {n : ℕ} (hn : Odd n) (hord : orderOf (u * v * w) = 2 * n) {z : G}
    (hzdef : (u * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x) :
    u * v * z ∉ hC.alpha := by
  intro hbα
  obtain ⟨-, hz1, hzu, -, -, -⟩ :=
    htri.third_kind hC.setup.oddT hC.setup.normal hn hord
  rw [hzdef] at hz1 hzu
  have hstar_cent := DalphaStar_subset_centSet_of_mem_alpha hC hu hv htri hbα
  have hKgen : localGroup D z =
      Subgroup.closure (((localGroup D z : Subgroup G) : Set G) ∩ D) := by
    have hKD : ((localGroup D z : Subgroup G) : Set G) ∩ D = centSet D z := by
      ext x
      exact ⟨fun hx => ⟨hx.2, commute_of_mem_localGroup hx.1⟩,
        fun hx => ⟨mem_localGroup_of_mem hx, hx.1⟩⟩
    rw [hKD]
    rfl
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hC.hd (hC.isBlock_alpha.subset hu))
  let hC' : HypothesisC D := hC.conj g
  have hC'd : hC'.d = u := hg
  have hC'alpha : hC'.alpha = hC.alpha := by
    show (hC.conj g).alpha = hC.alpha
    rw [HypothesisC.conj_alpha]
    exact eq_of_mem_of_mem_blockClass hC.isBlock_alpha
      (mem_blockClass_iff.mpr ⟨g, rfl⟩) (mem_blockClass_self hC.alpha)
      ⟨u, ⟨hC.d, hC.d_mem_alpha, hg⟩, hu⟩
  have hEX : hC'.E ⊆ (localGroup D z : Set G) := by
    intro e he
    have heStar : e ∈ DalphaStar D hC.alpha := by
      rw [← hC'alpha]
      rwa [hC'.DalphaStar_alpha]
    exact mem_localGroup_of_mem (hstar_cent heStar)
  have hdX : hC'.d ∈ localGroup D z := by
    rw [hC'd]
    exact mem_localGroup_of_mem ⟨htri.1, hzu.symm⟩
  have hperp := inter_D_subset_perp hC' hKgen hdX hEX
    (thirdK_eq_localGroup z ▸ thirdK_lt_top_of_no_solvable_normal hrad hz1).ne
  have hcent_sub : centSet D z ⊆ hC.alpha ∪ DalphaStar D hC.alpha := by
    intro x hx
    have hthis := hperp ⟨mem_localGroup_of_mem hx, hx.1⟩
    rwa [hC'alpha] at hthis
  have hcent_alpha := centSet_subset_alpha_of_transitive hC hu htrans hcent_sub
  obtain ⟨e, heE⟩ := OddLocal.nonempty hC.hE
  have heStar : e ∈ DalphaStar D hC.alpha := by
    rw [hC.DalphaStar_alpha]
    exact heE
  exact (Set.disjoint_left.mp (disjoint_alpha_DalphaStar hC.isBlock_alpha)
    (hcent_alpha (hstar_cent heStar))) heStar

theorem uvz_mem_DalphaStar_and_isTriangle_of_mem_alpha (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {u w v : G} (hu : u ∈ hC.alpha) (hv : v ∈ hC.alpha) (htri : IsTriangle D u w v)
    {n : ℕ} (hn : Odd n) (hord : orderOf (u * v * w) = 2 * n) {z : G}
    (hzdef : (u * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x) :
    u * v * z ∈ DalphaStar D hC.alpha ∧ IsTriangle D u w (u * v * z) := by
  obtain ⟨hzz, -, hzu, -, hzw, hbD⟩ :=
    htri.third_kind hC.setup.oddT hC.setup.normal hn hord
  rw [hzdef] at hzz hzu hzw hbD
  have hD := hC.setup.oddT
  set b : G := u * v * z with hbdef
  have hbα : b ∉ hC.alpha := by
    rw [hbdef]
    exact uvz_not_mem_alpha_of_mem_alpha hC hrad hu hv htri hn hord hzdef htrans
  have hbStar : b ∈ DalphaStar D hC.alpha := by
    rw [hbdef]
    exact mem_DalphaStar_of_mem_D_of_not_mem_alpha_of_commute hC hu hbD hbα
      (((Commute.refl u).mul_right htri.2.2.2.2.1).mul_right hzu.symm).symm
  have hub : u ≠ b := by
    rw [hbdef]
    intro h
    have hvz : v * z = 1 := by
      have h' := congrArg (fun x => u⁻¹ * x) h
      simpa [mul_assoc, hD.inv_eq htri.1] using h'
    have hvz' : v = z := by
      rw [← hD.inv_eq htri.2.1]
      exact (eq_inv_of_mul_eq_one_right hvz).symm
    exact htri.2.2.2.2.2.2 (hvz' ▸ hzw)
  have hub_comm : Commute u b := by
    rw [hbdef]
    exact ((Commute.refl u).mul_right htri.2.2.2.2.1).mul_right hzu.symm
  have hbw : ¬ Commute b w := by
    rw [hbdef]
    intro hbw
    have hbz : Commute ((u * v) * z * z) w := hbw.mul_left hzw
    have hzeq : (u * v) * z * z = u * v := by
      rw [mul_assoc (u * v) z z, hzz, mul_one]
    rw [hzeq] at hbz
    exact htri.not_commute_mul hD hbz.symm
  have htri' : IsTriangle D u w b :=
    ⟨htri.1, hbD, htri.2.2.1, hub, hub_comm, htri.2.2.2.2.2.1, hbw⟩
  exact ⟨by simpa [hbdef] using hbStar, by simpa [hbdef] using htri'⟩

theorem exists_thirdKind_uvz_of_mem_alpha (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {u w v : G} (hu : u ∈ hC.alpha) (hv : v ∈ hC.alpha) (htri : IsTriangle D u w v)
    {n : ℕ} (hn : Odd n) (hord : orderOf (u * v * w) = 2 * n) {z : G}
    (hzdef : (u * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x) :
    u * v * z ∈ DalphaStar D hC.alpha ∧ IsTriangle D u w (u * v * z) ∧
      Odd (orderOf (v * w)) ∧ 1 < orderOf (v * w) ∧
      orderOf (u * (u * v * z) * w) = 2 * orderOf (v * w) ∧
      (u * (u * v * z) * w) ^ orderOf (v * w) = z := by
  have hD := hC.setup.oddT
  obtain ⟨hzz, hz1, hzu, hzv, hzw, hbD⟩ :=
    htri.third_kind hD hC.setup.normal hn hord
  rw [hzdef] at hzz hz1 hzu hzv hzw hbD
  obtain ⟨hbStar, htri'⟩ :=
    uvz_mem_DalphaStar_and_isTriangle_of_mem_alpha hC hrad hu hv htri hn hord hzdef htrans
  set b : G := u * v * z with hbdef
  have hbStar' : b ∈ DalphaStar D hC.alpha := by rwa [hbdef]
  have htri'' : IsTriangle D u w b := by rwa [hbdef]
  set m : ℕ := orderOf (v * w) with hm
  have hm_odd : Odd m := by
    rw [hm]
    exact hD.odd_of_not_commute htri.2.1 htri.2.2.1 htri.2.2.2.2.2.2
  have hm_gt1 : 1 < m := by
    have hne1 : m ≠ 1 := by
      intro h1
      rw [orderOf_eq_one_iff] at h1
      exact htri.2.2.2.2.2.2 (hD.eq_of_mul_eq_one htri.2.1 h1 ▸ Commute.refl w)
    have := orderOf_pos (v * w)
    omega
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  have hcomm_vw_z : Commute (v * w) z := (hzv.mul_right hzw).symm
  have heq : u * b * w = v * w * z := by
    rw [hbdef]
    calc u * (u * v * z) * w = (u * u) * v * z * w := by group
      _ = v * z * w := by rw [hD.mul_self_eq_one htri.1, one_mul]
      _ = v * w * z := by rw [mul_assoc v z w, hzw.eq, ← mul_assoc]
  have hord_m : orderOf (u * b * w) = 2 * m := by
    rw [heq]
    have h := orderOf_mul_eq_two_mul_of_odd hcomm_vw_z hm_odd hz2
    rwa [← hm] at h
  have hzm : z ^ m = z := by
    obtain ⟨k, hk⟩ := hm_odd
    rw [hk, pow_succ, pow_mul, pow_two, hzz, one_pow, one_mul]
  have hpow : (u * b * w) ^ m = z := by
    rw [heq, hcomm_vw_z.mul_pow]
    have hvm : (v * w) ^ m = 1 := by
      rw [hm]
      exact pow_orderOf_eq_one (v * w)
    rw [hvm, hzm, one_mul]
  exact ⟨by simpa [hbdef] using hbStar', by simpa [hbdef] using htri'', hm_odd,
    by simpa [hm] using hm_gt1, by simpa [hbdef, hm] using hord_m,
    by simpa [hbdef, hm] using hpow⟩

theorem exists_thirdKind_mem_DalphaStar_of_mem_alpha (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {u w v : G} (hu : u ∈ hC.alpha) (hv : v ∈ hC.alpha) (htri : IsTriangle D u w v)
    {n : ℕ} (hn : Odd n) (hord : orderOf (u * v * w) = 2 * n) {z : G}
    (hzdef : (u * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x) :
    ∃ v' ∈ DalphaStar D hC.alpha, IsTriangle D u w v' ∧
      ∃ m : ℕ, Odd m ∧ 1 < m ∧ orderOf (u * v' * w) = 2 * m ∧ (u * v' * w) ^ m = z := by
  obtain ⟨hstar, htri', hodd, hgt, hord', hpow⟩ :=
    exists_thirdKind_uvz_of_mem_alpha hC hrad hu hv htri hn hord hzdef htrans
  exact ⟨u * v * z, hstar, htri', orderOf (v * w), hodd, hgt, hord', hpow⟩

theorem exists_thirdKind_mem_DalphaStar (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {u w v : G} (hu : u ∈ hC.alpha) (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n)
    (hn1 : 1 < n) (hord : orderOf (u * v * w) = 2 * n) {z : G} (hzdef : (u * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x) :
    ∃ v' ∈ DalphaStar D hC.alpha, IsTriangle D u w v' ∧
      ∃ m : ℕ, Odd m ∧ 1 < m ∧ orderOf (u * v' * w) = 2 * m ∧ (u * v' * w) ^ m = z := by
  by_cases hv : v ∈ hC.alpha
  · exact exists_thirdKind_mem_DalphaStar_of_mem_alpha hC hrad hu hv htri hn hord hzdef htrans
  · exact ⟨v, mem_DalphaStar_of_mem_D_of_not_mem_alpha_of_commute hC hu htri.2.1 hv
      htri.2.2.2.2.1.symm, htri, n, hn, hn1, hord, hzdef⟩

end CFSG.OddTranspositions

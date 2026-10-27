module

public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofCen
import CFSG.RankThree.PartTwo.Sec13.Item136Lift

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS CFSG.ABGLocalTools
open scoped Pointwise

@[expose] def KS1617FusX : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 ≤ n → ¬ 3 ∣ n → Sec4.IsoLThreePi X 2 n →
    ∀ D : Subgroup X, CFSG.Assembly.IsElemAbelian 3 D → Nat.card D = 9 →
    ∀ y ∈ D, y ≠ 1 → ∀ z ∈ D, z ≠ 1 → ∃ w ∈ Subgroup.normalizer (D : Set X), w * y * w⁻¹ = z

theorem ks1617Fus_of (hX : KS1617FusX) : KS1617Fus := by
  intro G _ _ L D n hn hn3 hiso hDL hDab hD9 y hy hy1 z hz hz1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set θG := θ.map L.subtype with hθG
  have hθ3 := Proof1617.not_three_dvd_card_thetaG L
  have hθL : θG ≤ L := Subgroup.map_subtype_le _
  have hθnorm : θ.Normal := by
    have := Sec4.aschbacherSolvableCore_characteristic ↥L
    infer_instance
  have hD3 : IsPGroup 3 D := IsPGroup.of_card (n := 2) (by rw [hD9]; norm_num)
  set π : ↥L →* ↥L ⧸ θ := QuotientGroup.mk' θ with hπ
  have hDθ : ∀ g ∈ D, g ∈ θG → g = 1 := fun g hgD hgθ =>
    Proof1617.eq_one_of_isPGroup_of_not_dvd hD3 hθ3 hgD hgθ
  have hπinj : ∀ a b : ↥L, (a : G) ∈ D → (b : G) ∈ D → π a = π b → a = b := by
    intro a b ha hb hab
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hab
    have h1 : (a : G)⁻¹ * b ∈ θG := ⟨_, hab, by simp⟩
    have h2 := hDθ _ (D.mul_mem (D.inv_mem ha) hb) h1
    exact Subtype.ext (by rw [← mul_inv_cancel_left (a : G) b, h2, mul_one])
  set DL : Subgroup ↥L := D.subgroupOf L with hDL'
  set Db : Subgroup (↥L ⧸ θ) := DL.map π with hDb
  have hDbab : CFSG.Assembly.IsElemAbelian 3 Db :=
    Proof1617.isElemAbelian_map' π (Proof1617.isElemAbelian_subgroupOf hDab L)
  have hDb9 : Nat.card Db = 9 := by
    have hinj : Set.InjOn π DL := fun a ha b hb hab => hπinj a b ha hb hab
    rw [hDb, Sec13.card_map_eq_of_injOn π hinj, Proof1617.card_subgroupOf_of_le hDL, hD9]
  set yL : ↥L := ⟨y, hDL hy⟩ with hyL
  set zL : ↥L := ⟨z, hDL hz⟩ with hzL
  have hyb : π yL ∈ Db := ⟨yL, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hzb : π zL ∈ Db := ⟨zL, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
  have hyb1 : π yL ≠ 1 := by
    intro h1
    apply hy1
    have := hπinj yL 1 hy D.one_mem (by rw [h1, map_one])
    exact congrArg Subtype.val this
  have hzb1 : π zL ≠ 1 := by
    intro h1
    apply hz1
    have := hπinj zL 1 hz D.one_mem (by rw [h1, map_one])
    exact congrArg Subtype.val this
  obtain ⟨wb, hwbN, hwbyz⟩ := hX _ n hn hn3 hiso Db hDbab hDb9 _ hyb hyb1 _ hzb hzb1
  obtain ⟨w₁, rfl⟩ := QuotientGroup.mk'_surjective θ wb
  obtain ⟨hMcard, hDsyl⟩ := Proof1617.isSylowOf_sup_thetaG hDL hD9 hD3
  set M := θG ⊔ D with hM
  have hDN : D ≤ Subgroup.normalizer (θG : Set G) := fun d hd =>
    Subgroup.mem_normalizer_fintype fun t ht =>
      Proof1617.conj_mem_thetaG (Subgroup.le_normalizer (hDL hd)) ht
  have hMset : (M : Set G) = (θG : Set G) * (D : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left θG D hDN
  have hw₁L : (w₁ : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer w₁.2
  have hw₁D : ∀ d ∈ D, (w₁ : G) * d * (w₁ : G)⁻¹ ∈ M := by
    intro d hd
    set dL : ↥L := ⟨d, hDL hd⟩ with hdL
    have hdb : π dL ∈ Db := ⟨dL, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
    have h1 : π w₁ * π dL * (π w₁)⁻¹ ∈ Db :=
      (Subgroup.mem_normalizer_iff.mp hwbN _).mp hdb
    obtain ⟨d', hd', hd'eq⟩ := h1
    rw [← map_inv, ← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at hd'eq
    have h2 : ((d' : G))⁻¹ * ((w₁ : G) * d * (w₁ : G)⁻¹) ∈ θG := ⟨_, hd'eq, by simp [hdL]⟩
    have heq : (w₁ : G) * d * (w₁ : G)⁻¹ =
        ((d' : G) * (((d' : G))⁻¹ * ((w₁ : G) * d * (w₁ : G)⁻¹)) * (d' : G)⁻¹) * (d' : G) := by
      group
    rw [heq]
    refine M.mul_mem ?_ (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hd'))
    exact Subgroup.mem_sup_left (Proof1617.conj_mem_thetaG (Subgroup.le_normalizer d'.2) h2)
  have hw₁M : (w₁ : G) ∈ Subgroup.normalizer (M : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hx' : x ∈ (θG : Set G) * (D : Set G) := hMset ▸ hx
    obtain ⟨t, ht, d, hd, rfl⟩ := hx'
    have heq : (w₁ : G) * (t * d) * (w₁ : G)⁻¹ =
        ((w₁ : G) * t * (w₁ : G)⁻¹) * ((w₁ : G) * d * (w₁ : G)⁻¹) := by group
    rw [heq]
    exact M.mul_mem (Subgroup.mem_sup_left (Proof1617.conj_mem_thetaG hw₁L ht)) (hw₁D d hd)
  have hDw : IsSylowOf 3 (D.map (MulAut.conj (w₁ : G)).toMonoidHom) M := by
    refine isSylowOf_of_card ?_ ?_
    · rintro _ ⟨d, hd, rfl⟩
      exact hw₁D d hd
    · rw [Subgroup.card_map_of_injective (MulAut.conj (w₁ : G)).injective, hDsyl.card_eq]
  obtain ⟨m, hm, hmeq⟩ := Proof1617.exists_conj_eq_of_isSylowOf hDsyl hDw
  have hm' : m ∈ (θG : Set G) * (D : Set G) := hMset ▸ hm
  obtain ⟨t, ht, d₀, hd₀, rfl⟩ := hm'
  have htL : t ∈ L := hθL ht
  refine ⟨t⁻¹ * w₁, Subgroup.mem_inf.mpr ⟨L.mul_mem (L.inv_mem htL) w₁.2, ?_⟩, ?_⟩
  · refine Subgroup.mem_normalizer_fintype fun d hd => ?_
    have h1 : (w₁ : G) * d * (w₁ : G)⁻¹ ∈ D.map (MulAut.conj (w₁ : G)).toMonoidHom :=
      ⟨d, hd, rfl⟩
    rw [hmeq] at h1
    obtain ⟨d', hd', hd'eq⟩ := h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hd'eq
    have heq : t⁻¹ * (w₁ : G) * d * (t⁻¹ * (w₁ : G))⁻¹ = d₀ * d' * d₀⁻¹ := by
      calc t⁻¹ * (w₁ : G) * d * (t⁻¹ * (w₁ : G))⁻¹ = t⁻¹ * ((w₁ : G) * d * (w₁ : G)⁻¹) * t := by
            group
        _ = t⁻¹ * (t * d₀ * d' * (t * d₀)⁻¹) * t := by rw [hd'eq]
        _ = d₀ * d' * d₀⁻¹ := by group
    have hmem : d₀ * d' * d₀⁻¹ ∈ D := D.mul_mem (D.mul_mem hd₀ hd') (D.inv_mem hd₀)
    rw [← heq] at hmem
    exact hmem
  ·
    have hwy : t⁻¹ * (w₁ : G) * y * (t⁻¹ * (w₁ : G))⁻¹ ∈ D := by
      have h1 : (w₁ : G) * y * (w₁ : G)⁻¹ ∈ D.map (MulAut.conj (w₁ : G)).toMonoidHom :=
        ⟨y, hy, rfl⟩
      rw [hmeq] at h1
      obtain ⟨d', hd', hd'eq⟩ := h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hd'eq
      have heq : t⁻¹ * (w₁ : G) * y * (t⁻¹ * (w₁ : G))⁻¹ = d₀ * d' * d₀⁻¹ := by
        calc t⁻¹ * (w₁ : G) * y * (t⁻¹ * (w₁ : G))⁻¹ =
              t⁻¹ * ((w₁ : G) * y * (w₁ : G)⁻¹) * t := by group
          _ = t⁻¹ * (t * d₀ * d' * (t * d₀)⁻¹) * t := by rw [hd'eq]
          _ = d₀ * d' * d₀⁻¹ := by group
      have hmem : d₀ * d' * d₀⁻¹ ∈ D := D.mul_mem (D.mul_mem hd₀ hd') (D.inv_mem hd₀)
      rw [← heq] at hmem
      exact hmem
    set tL : ↥L := ⟨t, htL⟩ with htL'
    have htθ : tL ∈ θ := by
      obtain ⟨t', ht', ht'e⟩ := ht
      have : t' = tL := Subtype.ext ht'e
      rw [← this]
      exact ht'
    have hπt : π tL = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact htθ
    set wL : ↥L := tL⁻¹ * w₁ with hwL
    have hwyL : ((wL * yL * wL⁻¹ : ↥L) : G) = t⁻¹ * (w₁ : G) * y * (t⁻¹ * (w₁ : G))⁻¹ := by
      simp [hwL, htL', hyL]
    have h1 : π (wL * yL * wL⁻¹) = π zL := by
      rw [map_mul, map_mul, map_inv, hwL, map_mul, map_inv, hπt, inv_one, one_mul]
      exact hwbyz
    have h2 := hπinj (wL * yL * wL⁻¹) zL (by rw [hwyL]; exact hwy) hz h1
    have h3 := congrArg Subtype.val h2
    rw [hwyL] at h3
    exact h3

end CFSG.RankThree.PartTwo.Sec16

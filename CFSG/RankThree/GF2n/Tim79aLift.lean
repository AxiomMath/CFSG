module

public import CFSG.RankThree.GF2n.Tim79aSec23Defs
public import CFSG.GroupTheory.PGroupFixedPointCongruence

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G]

theorem Sec23Data.eq_top_of_sup_center_of_mem {V H : Subgroup G} (hD : Sec23Data V H)
    {K : Subgroup (Xbar V H)} (hK : K ⊔ Subgroup.center (Xbar V H) = ⊤)
    (hdK : ∃ d ∈ Dy V H, d ∈ K) : K = ⊤ := by
  obtain ⟨d, hdD, hdK⟩ := hdK
  obtain ⟨d₀, hcls⟩ := hD.isClass
  have hDK : Dy V H ⊆ K := by
    intro g hg
    have h1 : IsConj d₀ d := by
      rw [hcls] at hdD
      exact hdD
    have h2 : IsConj d₀ g := by
      rw [hcls] at hg
      exact hg
    obtain ⟨x, rfl⟩ := isConj_iff.mp (h1.symm.trans h2)
    have hx : x ∈ K ⊔ Subgroup.center (Xbar V H) := by
      rw [hK]
      exact Subgroup.mem_top x
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    have hzd : z * d = d * z := (Subgroup.mem_center_iff.mp hz d).symm
    have hconj : y * z * d * (y * z)⁻¹ = y * d * y⁻¹ := by
      calc y * z * d * (y * z)⁻¹ = y * (z * d) * z⁻¹ * y⁻¹ := by group
        _ = y * (d * z) * z⁻¹ * y⁻¹ := by rw [hzd]
        _ = y * d * y⁻¹ := by group
    rw [hconj]
    exact K.mul_mem (K.mul_mem hy hdK) (K.inv_mem hy)
  have hcl : Subgroup.closure (Dy V H) ≤ K := (Subgroup.closure_le K).mpr hDK
  rw [hD.gen] at hcl
  exact top_le_iff.mp hcl

theorem barOf_xOf_le_of_sup_center {V H T : Subgroup G} (hD : Sec23Data V H)
    (hK : (barOf V H T).subgroupOf (barOf V H (xOf V H)) ⊔
      Subgroup.center (Xbar V H) = ⊤)
    (hdK : ∃ d ∈ Dy V H, d ∈ (barOf V H T).subgroupOf (barOf V H (xOf V H))) :
    barOf V H (xOf V H) ≤ barOf V H T := by
  have htop := Sec23Data.eq_top_of_sup_center_of_mem hD hK hdK
  intro y hy
  have hmem : (⟨y, hy⟩ : Xbar V H) ∈ (barOf V H T).subgroupOf (barOf V H (xOf V H)) := by
    rw [htop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hmem

theorem xOf_le_of_barOf_le {V H U T : Subgroup G} (hVH : V ≤ H) (hWU : wOf V H ≤ U)
    (h : barOf V H (xOf V H) ≤ barOf V H (U ⊔ T)) : xOf V H ≤ U ⊔ T := by
  intro x hx
  have hxH : x ∈ H := xOf_le_H hVH hx
  have hX : piBar V H ⟨x, hxH⟩ ∈ barOf V H (xOf V H) :=
    mem_barOf_iff.mpr ⟨⟨x, hxH⟩, hx, rfl⟩
  obtain ⟨y, hyUT, hy⟩ := mem_barOf_iff.mp (h hX)
  have h1 : piBar V H (y⁻¹ * ⟨x, hxH⟩) = 1 := by
    rw [map_mul, map_inv, hy, inv_mul_cancel]
  have h2 : ((y⁻¹ * ⟨x, hxH⟩ : ↥H) : G) ∈ U := hWU ((piBar_eq_one_iff _).mp h1)
  have h3 : x = (y : G) * ((y⁻¹ * ⟨x, hxH⟩ : ↥H) : G) := by simp
  rw [h3]
  exact (U ⊔ T).mul_mem hyUT ((le_sup_left : U ≤ U ⊔ T) h2)

theorem xOf_le_sup_of_sup_center {V H U T : Subgroup G} (hD : Sec23Data V H) (hVH : V ≤ H)
    (hWU : wOf V H ≤ U)
    (hK : (barOf V H (U ⊔ T)).subgroupOf (barOf V H (xOf V H)) ⊔
      Subgroup.center (Xbar V H) = ⊤)
    (hdK : ∃ d ∈ Dy V H, d ∈ (barOf V H (U ⊔ T)).subgroupOf (barOf V H (xOf V H))) :
    xOf V H ≤ U ⊔ T :=
  xOf_le_of_barOf_le hVH hWU (barOf_xOf_le_of_sup_center hD hK hdK)

private theorem wOf_isPGroup_two (V H : Subgroup G) : IsPGroup 2 (wOf V H) :=
  (isPGroup_pCore H).to_le (wOf_le_pCore V H)

theorem centralizer_inf_wOf_ne_bot {V H : Subgroup G} [Finite G] (hW : wOf V H ≠ ⊥)
    {S : Subgroup G} (hSH : S ≤ H) (hS : IsPGroup 2 S) :
    wOf V H ⊓ Subgroup.centralizer (S : Set G) ≠ ⊥ := by
  intro hC
  have hmod := CFSG.GroupTheory.card_modEq_one_of_isPGroup_normalizes_of_inf_centralizer_eq_bot
    (p := 2) hS (fun s hs => H_le_normalizer_wOf V H (hSH hs)) hC
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (wOf_isPGroup_two V H)
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 : 1 < Nat.card (wOf V H) := (Subgroup.one_lt_card_iff_ne_bot (wOf V H)).mpr hW
    rw [hn] at h1
    norm_num at h1
  obtain ⟨k, hk⟩ := dvd_pow_self 2 hn0
  rw [hn, hk] at hmod
  unfold Nat.ModEq at hmod
  omega

theorem normalizer_mem_of_centralizer_le {V H : Subgroup G} [Finite G] (hVTI : IsTI V)
    (hW : wOf V H ≠ ⊥) {S : Subgroup G} (hSH : S ≤ H) (hS : IsPGroup 2 S)
    (hCV : wOf V H ⊓ Subgroup.centralizer (S : Set G) ≤ V) {b : G}
    (hbH : b ∈ H) (hbS : b ∈ Subgroup.normalizer (S : Set G)) :
    b ∈ Subgroup.normalizer (V : Set G) := by
  have hle : wOf V H ⊓ Subgroup.centralizer (S : Set G) ≤ V ⊓ conjSubgroup b V := by
    intro x hx
    have hbx : b⁻¹ * x * b ∈ wOf V H ⊓ Subgroup.centralizer (S : Set G) := by
      refine ⟨?_, ?_⟩
      · have h1 := (Subgroup.mem_normalizer_iff.mp
          (H_le_normalizer_wOf V H (H.inv_mem hbH)) x).mp hx.1
        simpa using h1
      · show b⁻¹ * x * b ∈ Subgroup.centralizer (S : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        have hs' : b * s * b⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hbS s).mp hs
        have hc := Subgroup.mem_centralizer_iff.mp hx.2 (b * s * b⁻¹) hs'
        calc s * (b⁻¹ * x * b) = b⁻¹ * ((b * s * b⁻¹) * x) * b := by group
          _ = b⁻¹ * (x * (b * s * b⁻¹)) * b := by rw [hc]
          _ = b⁻¹ * x * b * s := by group
    exact ⟨hCV hx, mem_conjSubgroup.mpr (hCV hbx)⟩
  have hne : V ⊓ conjSubgroup b V ≠ ⊥ := by
    intro h
    exact centralizer_inf_wOf_ne_bot hW hSH hS (eq_bot_iff.mpr (hle.trans (le_of_eq h)))
  exact mem_normalizer_iff_conjSubgroup_eq.mpr (conjSubgroup_eq_of_isTI hVTI hne)

end CFSG.RankThree.GF2n.Tim79a

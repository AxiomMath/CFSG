module

public import Mathlib.GroupTheory.IsPerfect
import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

theorem w135c2_exists_involution_pow_mul_conj_of_perfect {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hperf : Group.IsPerfect ↥L)
    (hL : ∀ N : Subgroup ↥L, N.Normal → Odd (Nat.card N) → N ≤ center ↥L)
    {t : G} (htN : t ∈ normalizer (L : Set G)) (ht : t * t = 1)
    (htc : ∃ x ∈ L, t * x ≠ x * t) :
    ∃ l ∈ L, ∃ k : ℕ, (t * (l⁻¹ * t * l)) ^ k ∈ L ∧ (t * (l⁻¹ * t * l)) ^ k ≠ 1 ∧
      (t * (l⁻¹ * t * l)) ^ k * (t * (l⁻¹ * t * l)) ^ k = 1 := by
  classical
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
  have hmemL : ∀ l ∈ L, t * (l⁻¹ * t * l) ∈ L := by
    intro l hl
    have h1 : t * l⁻¹ * t⁻¹ ∈ L := (mem_normalizer_iff.mp htN l⁻¹).mp (inv_mem hl)
    have e : t * (l⁻¹ * t * l) = t * l⁻¹ * t⁻¹ * l := by rw [htinv]; group
    rw [e]
    exact mul_mem h1 hl
  by_cases hev : ∃ l ∈ L, Even (orderOf (t * (l⁻¹ * t * l)))
  · obtain ⟨l, hl, k, hk⟩ := hev
    refine ⟨l, hl, k, pow_mem (hmemL l hl) k, fun h1 => ?_, ?_⟩
    · have hpos := orderOf_pos (t * (l⁻¹ * t * l))
      have hk0 : 0 < k := by omega
      have := orderOf_le_of_pow_eq_one hk0 h1
      omega
    · rw [← pow_add, ← hk, pow_orderOf_eq_one]
  · push Not at hev
    exfalso
    obtain ⟨x₀, hx₀, hne⟩ := htc
    have hzle : zpowers t ≤ normalizer (L : Set G) := (zpowers_le).mpr htN
    have hcoe := coe_mul_of_right_le_normalizer_left L (zpowers t) hzle
    have htH : t ∈ L ⊔ zpowers t := mem_sup_right (mem_zpowers t)
    have : Fintype ↥(L ⊔ zpowers t) := Fintype.ofFinite _
    let τ : ↥(L ⊔ zpowers t) := ⟨t, htH⟩
    have hτ1 : τ ≠ 1 := by
      intro h
      have h' : t = 1 := congrArg Subtype.val h
      exact hne (by rw [h', one_mul, mul_one])
    have hτ2 : τ * τ = 1 := Subtype.ext ht
    have hiso : ∀ g : ↥(L ⊔ zpowers t), (g * τ * g⁻¹) * τ = τ * (g * τ * g⁻¹) →
        g * τ * g⁻¹ = τ := by
      intro g hg
      have hgm : (g : G) ∈ ((L ⊔ zpowers t : Subgroup G) : Set G) := g.2
      rw [hcoe] at hgm
      obtain ⟨l, hl, s, hs, hls⟩ := Set.mem_mul.mp hgm
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hs
      have hconj' : (g : G) * t * (g : G)⁻¹ = l * t * l⁻¹ := by
        rw [← hls]
        group
      have hconj : ((g * τ * g⁻¹ : ↥(L ⊔ zpowers t)) : G) = l * t * l⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hconj'
      have hcomm : (l * t * l⁻¹) * t = t * (l * t * l⁻¹) := by
        have := congrArg Subtype.val hg
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
        rw [← hconj']
        exact this
      have hodd := hev l⁻¹ (inv_mem hl)
      rw [inv_inv] at hodd
      have hsq : (t * (l * t * l⁻¹)) ^ 2 = 1 := by
        have hs2 : (l * t * l⁻¹) * (l * t * l⁻¹) = 1 := by
          calc (l * t * l⁻¹) * (l * t * l⁻¹) = l * (t * t) * l⁻¹ := by group
            _ = 1 := by rw [ht, mul_one, mul_inv_cancel]
        calc (t * (l * t * l⁻¹)) ^ 2 = t * ((l * t * l⁻¹) * t) * (l * t * l⁻¹) := by
              rw [pow_two]; group
          _ = t * (t * (l * t * l⁻¹)) * (l * t * l⁻¹) := by rw [hcomm]
          _ = (t * t) * ((l * t * l⁻¹) * (l * t * l⁻¹)) := by group
          _ = 1 := by rw [ht, hs2, one_mul]
      have hdvd := orderOf_dvd_of_pow_eq_one hsq
      have hle : orderOf (t * (l * t * l⁻¹)) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      have hpos := orderOf_pos (t * (l * t * l⁻¹))
      have h1 : orderOf (t * (l * t * l⁻¹)) = 1 := by
        rcases (by omega : orderOf (t * (l * t * l⁻¹)) = 1 ∨ orderOf (t * (l * t * l⁻¹)) = 2)
          with h | h
        · exact h
        · exact absurd (h ▸ even_two) hodd
      rw [orderOf_eq_one_iff] at h1
      have heq : l * t * l⁻¹ = t := by
        calc l * t * l⁻¹ = t⁻¹ * (t * (l * t * l⁻¹)) := by group
          _ = t := by rw [h1, mul_one, htinv]
      exact Subtype.ext (hconj.trans heq)
    obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar _ τ hτ1 hτ2 hiso
    set NL : Subgroup ↥L := (N.map (L ⊔ zpowers t).subtype).subgroupOf L with hNL
    have hNLn : NL.Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [hNL, mem_subgroupOf] at hx ⊢
      obtain ⟨n, hn, hnx⟩ := hx
      have hgH : (g : G) ∈ L ⊔ zpowers t := mem_sup_left g.2
      refine ⟨⟨g, hgH⟩ * n * ⟨g, hgH⟩⁻¹, hNn.conj_mem n hn _, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hnx ⊢
      rw [hnx]
    have hNLodd : Odd (Nat.card NL) := by
      have hle : NL.map L.subtype ≤ N.map (L ⊔ zpowers t).subtype := by
        rintro _ ⟨x, hx, rfl⟩
        exact hx
      have hdvd := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective L.subtype_injective,
        Subgroup.card_map_of_injective (L ⊔ zpowers t).subtype_injective] at hdvd
      exact Odd.of_dvd_nat hNodd hdvd
    have hbot := hL NL hNLn hNLodd
    have hmem : ∀ x : ↥L, (x : G) * t * (x : G)⁻¹ * t⁻¹ ∈ L := by
      intro x
      have h1 : t * (x : G)⁻¹ * t⁻¹ ∈ L :=
        (mem_normalizer_iff.mp htN (x : G)⁻¹).mp (inv_mem x.2)
      have e : (x : G) * t * (x : G)⁻¹ * t⁻¹ =
          (x : G) * (t * (x : G)⁻¹ * t⁻¹) := by group
      rw [e]
      exact mul_mem x.2 h1
    have hcent : ∀ x : ↥L,
        (⟨(x : G) * t * (x : G)⁻¹ * t⁻¹, hmem x⟩ : ↥L) ∈ center ↥L := by
      intro x
      refine hbot ?_
      rw [hNL, mem_subgroupOf]
      have hxH : (x : G) ∈ L ⊔ zpowers t := mem_sup_left x.2
      exact ⟨_, hN ⟨(x : G), hxH⟩, rfl⟩
    let c : ↥L →* center ↥L :=
      MonoidHom.mk' (fun x => ⟨⟨(x : G) * t * (x : G)⁻¹ * t⁻¹, hmem x⟩, hcent x⟩)
        (fun x y => by
          apply Subtype.ext
          apply Subtype.ext
          have hcyx : (x : G) * ((y : G) * t * (y : G)⁻¹ * t⁻¹)
              = ((y : G) * t * (y : G)⁻¹ * t⁻¹) * (x : G) := by
            have h := congrArg (fun z : ↥L => (z : G))
              (Subgroup.mem_center_iff.mp (hcent y) x)
            simpa using h
          have hcommw : ((y : G) * t * (y : G)⁻¹ * t⁻¹) *
                ((x : G) * t * (x : G)⁻¹ * t⁻¹)
              = ((x : G) * t * (x : G)⁻¹ * t⁻¹) *
                ((y : G) * t * (y : G)⁻¹ * t⁻¹) := by
            have h := congrArg (fun z : ↥L => (z : G))
              (Subgroup.mem_center_iff.mp (hcent x)
                (⟨(y : G) * t * (y : G)⁻¹ * t⁻¹, hmem y⟩ : ↥L))
            simpa using h
          calc
            ((x * y : ↥L) : G) * t * (((x * y : ↥L) : G))⁻¹ * t⁻¹
                = (x : G) * ((y : G) * t * (y : G)⁻¹ * t⁻¹) * t
                    * (x : G)⁻¹ * t⁻¹ := by
                  simp only [Subgroup.coe_mul]
                  group
            _ = ((y : G) * t * (y : G)⁻¹ * t⁻¹) *
                  ((x : G) * t * (x : G)⁻¹ * t⁻¹) := by
                  rw [hcyx]; group
            _ = ((x : G) * t * (x : G)⁻¹ * t⁻¹) *
                  ((y : G) * t * (y : G)⁻¹ * t⁻¹) := hcommw)
    have hker : c.ker = ⊤ := top_le_iff.mp (by
      rw [← hperf.commutator_eq_top]
      exact Abelianization.commutator_subset_ker c)
    have hc1 : ∀ x : ↥L, c x = 1 := by
      intro x
      have hx : x ∈ c.ker := by rw [hker]; exact Subgroup.mem_top x
      exact MonoidHom.mem_ker.mpr hx
    have hw1 : x₀ * t * x₀⁻¹ * t⁻¹ = 1 := by
      have h := congrArg (fun z : center ↥L => (((z : ↥L) : G))) (hc1 ⟨x₀, hx₀⟩)
      exact h
    apply hne
    calc t * x₀ = (x₀ * t * x₀⁻¹ * t⁻¹)⁻¹ * (x₀ * t) := by group
      _ = x₀ * t := by rw [hw1, inv_one, one_mul]

end CFSG.LocalAnalysis.WeakClosure81

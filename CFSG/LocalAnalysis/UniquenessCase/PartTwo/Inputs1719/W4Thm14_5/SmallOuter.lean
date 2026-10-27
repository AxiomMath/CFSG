module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Simple
import CFSG.LocalAnalysis.UniquenessCase.UC22K147SpUSp4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open Subgroup

theorem eq_bot_of_odd_of_isSimpleGroup {A : Type} [Group A] [Finite A] [IsSimpleGroup A]
    (hev : Even (Nat.card A)) (N : Subgroup A) (hN : N.Normal) (hodd : Odd (Nat.card N)) :
    N = ⊥ := by
  rcases hN.eq_bot_or_eq_top with h | h
  · exact h
  · rw [h, Subgroup.card_top] at hodd
    exact absurd hev (Nat.not_even_iff_odd.mpr hodd)

theorem exists_involution_pow_mul_conj {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : ∀ N : Subgroup ↥L, N.Normal → Odd (Nat.card N) → N = ⊥)
    {t : G} (htN : t ∈ normalizer (L : Set G)) (ht : t * t = 1) (htc : ∃ x ∈ L, t * x ≠ x * t) :
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
    have hc : x₀ * t * x₀⁻¹ * t⁻¹ ∈ L := by
      have h1 : t * x₀⁻¹ * t⁻¹ ∈ L := (mem_normalizer_iff.mp htN x₀⁻¹).mp (inv_mem hx₀)
      have e : x₀ * t * x₀⁻¹ * t⁻¹ = x₀ * (t * x₀⁻¹ * t⁻¹) := by group
      rw [e]
      exact mul_mem hx₀ h1
    have hcN : (⟨_, hc⟩ : ↥L) ∈ NL := by
      rw [hNL, mem_subgroupOf]
      have hx₀H : x₀ ∈ L ⊔ zpowers t := mem_sup_left hx₀
      exact ⟨_, hN ⟨x₀, hx₀H⟩, rfl⟩
    rw [hbot, mem_bot] at hcN
    have h1 : x₀ * t * x₀⁻¹ * t⁻¹ = 1 := congrArg Subtype.val hcN
    apply hne
    calc t * x₀ = (x₀ * t * x₀⁻¹ * t⁻¹)⁻¹ * (x₀ * t) := by group
      _ = x₀ * t := by rw [h1, inv_one, one_mul]

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem range_pow_mul_le_sup (ρ : Representation (ZMod 2) G V) (a b : G) (k : ℕ) :
    LinearMap.range ((ρ ((a * b) ^ k) : V →ₗ[ZMod 2] V) - 1) ≤
      LinearMap.range ((ρ a : V →ₗ[ZMod 2] V) - 1) ⊔
        LinearMap.range ((ρ b : V →ₗ[ZMod 2] V) - 1) := by
  induction k with
  | zero =>
    rw [pow_zero, map_one, sub_self, LinearMap.range_zero]
    exact bot_le
  | succ k ih =>
    rw [pow_succ]
    exact (UC22.K147SpU.range_mul_le_sup ρ _ _).trans
      (sup_le ih (UC22.K147SpU.range_mul_le_sup ρ a b))

theorem finrank_range_pow_mul_conj_le [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (t l : G) (k : ℕ) :
    Module.finrank (ZMod 2) (LinearMap.range
        ((ρ ((t * (l⁻¹ * t * l)) ^ k) : V →ₗ[ZMod 2] V) - 1)) ≤
      2 * Module.finrank (ZMod 2) (LinearMap.range ((ρ t : V →ₗ[ZMod 2] V) - 1)) := by
  have h1 := Submodule.finrank_mono (range_pow_mul_le_sup ρ t (l⁻¹ * t * l) k)
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range ((ρ t : V →ₗ[ZMod 2] V) - 1))
    (LinearMap.range ((ρ (l⁻¹ * t * l) : V →ₗ[ZMod 2] V) - 1))
  have h3 := UC22.K147SpU.finrank_range_conj ρ t l
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

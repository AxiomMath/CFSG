module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import CFSG.LocalAnalysis.StandardType.FS81.L3TwoFixedPointFree
import CFSG.StronglyEmbedded.SteinbergBSPrimeFixedPointFreeNilpotent
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.StandardType.FrameRoute.FS81

theorem le_of_l3Two_section_fixedPointFree {G : Type} [Group G] [Finite G] {T T₀ P : Subgroup G}
    (hT₀T : T₀ ≤ T) (hT₀ : T ≤ Subgroup.normalizer (T₀ : Set G))
    (hPT : P ≤ Subgroup.normalizer (T : Set G)) (hPT₀ : P ≤ Subgroup.normalizer (T₀ : Set G))
    (hP : Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    {b : G} (hbP : b ∈ P) (hb : orderOf b = 3)
    (hfix : ∀ t ∈ T, b * t * b⁻¹ * t⁻¹ ∈ T₀ → t ∈ T₀) : T ≤ T₀ := by
  classical
  have hNnormal : (T₀.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hT₀T).mpr hT₀
  let N : Subgroup ↥T := T₀.subgroupOf T
  exact letI : N.Normal := hNnormal
        show T ≤ T₀ from by
          obtain ⟨τ, hfixτ⟩ := l3Two_quotient_fixedPointFree (hN := hNnormal) hPT hPT₀ hbP hfix
          let α : MulAut (↥T ⧸ N) := τ ⟨b, hbP⟩
          have hb3 : (⟨b, hbP⟩ : ↥P) ^ 3 = 1 := by
            have h : orderOf (⟨b, hbP⟩ : ↥P) = 3 := (Subgroup.orderOf_mk b hbP).trans hb
            have := pow_orderOf_eq_one (⟨b, hbP⟩ : ↥P)
            rwa [h] at this
          have hα3 : α ^ 3 = 1 := by
            change (τ ⟨b, hbP⟩) ^ 3 = 1
            rw [← map_pow, hb3, map_one]
          have hsub : Subsingleton (↥T ⧸ N) := by
            rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three (orderOf α)
                (orderOf_dvd_of_pow_eq_one hα3) with h1 | h3
            · have hα1 : α = 1 := orderOf_eq_one_iff.mp h1
              refine ⟨fun x y => ?_⟩
              have hx : α x = x := by rw [hα1]; rfl
              have hy : α y = y := by rw [hα1]; rfl
              rw [hfixτ x hx, hfixτ y hy]
            · have hnil : Group.IsNilpotent (↥T ⧸ N) :=
                CFSG.StronglyEmbedded.prime_order_fixed_point_free_automorphism_nilpotent α
                  Nat.prime_three h3 (fun x hx => hfixτ x hx)
              have hsol : IsSolvable (↥T ⧸ N) := @IsNilpotent.to_isSolvable _ _ hnil
              exact l3TwoFixedPointFree_holds ↥P (↥T ⧸ N) hP τ ⟨b, hbP⟩
                ((Subgroup.orderOf_mk b hbP).trans hb) hsol hfixτ
          intro t ht
          have h1 : (QuotientGroup.mk' N ⟨t, ht⟩ : ↥T ⧸ N) = 1 := Subsingleton.elim _ _
          change ((⟨t, ht⟩ : ↥T) : ↥T ⧸ N) = 1 at h1
          rw [QuotientGroup.eq_one_iff] at h1
          exact Subgroup.mem_subgroupOf.mp h1

theorem le_of_centralizer_le_l3Two {G : Type} [Group G] [Finite G] {T T₀ D : Subgroup G}
    (hT₀ : IsPGroup 2 T₀) (hT₀T : T₀ ≤ T) (hTN : T ≤ Subgroup.normalizer (T₀ : Set G))
    (hDT : D ≤ Subgroup.normalizer (T : Set G)) (hDT₀ : D ≤ Subgroup.normalizer (T₀ : Set G))
    (hD : Nonempty (↥D ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    {b : G} (hbD : b ∈ D) (hb : orderOf b = 3)
    (hC : ∀ x ∈ T, x * b = b * x → x ∈ T₀) : T ≤ T₀ := by
  classical
  exact letI : Fintype ↥T₀ := Fintype.ofFinite ↥T₀
        show T ≤ T₀ from by
          have hbN : b ∈ Subgroup.normalizer (T₀ : Set G) := hDT₀ hbD
          have hb_conj : ∀ s : ↥T₀, b * (s : G) * b⁻¹ ∈ T₀ := fun s =>
            (Subgroup.mem_normalizer_iff.mp hbN (s : G)).mp s.2
          refine le_of_l3Two_section_fixedPointFree hT₀T hTN hDT hDT₀ hD hbD hb ?_
          intro t ht hc
          let u : G := t⁻¹ * (b * t * b⁻¹ * t⁻¹) * t
          have huT₀ : u ∈ T₀ := by
            have htn : t⁻¹ ∈ Subgroup.normalizer (T₀ : Set G) :=
              (Subgroup.normalizer (T₀ : Set G)).inv_mem (hTN ht)
            show t⁻¹ * (b * t * b⁻¹ * t⁻¹) * t ∈ T₀
            simpa using (Subgroup.mem_normalizer_iff.mp htn _).mp hc
          have htu : t * u = b * t * b⁻¹ := by
            show t * (t⁻¹ * (b * t * b⁻¹ * t⁻¹) * t) = b * t * b⁻¹
            group
          let g : ↥T₀ → ↥T₀ :=
            fun s => ⟨u * (b * (s : G) * b⁻¹), T₀.mul_mem huT₀ (hb_conj s)⟩
          have hgs : ∀ s : ↥T₀, (t : G) * (g s : G) = b * (t * (s : G)) * b⁻¹ := by
            intro s
            show t * (u * (b * (s : G) * b⁻¹)) = b * (t * (s : G)) * b⁻¹
            calc t * (u * (b * (s : G) * b⁻¹))
                = (t * u) * (b * (s : G) * b⁻¹) := by group
              _ = (b * t * b⁻¹) * (b * (s : G) * b⁻¹) := by rw [htu]
              _ = b * (t * (s : G)) * b⁻¹ := by group
          have hb3 : b ^ 3 = 1 := by
            rw [← hb]
            exact pow_orderOf_eq_one b
          have hg3 : ∀ s : ↥T₀, g (g (g s)) = s := by
            intro s
            apply Subtype.ext
            have h1 : (t : G) * ((g (g (g s)) : ↥T₀) : G) = t * (s : G) := by
              calc (t : G) * ((g (g (g s)) : ↥T₀) : G)
                  = b * (t * ((g (g s) : ↥T₀) : G)) * b⁻¹ := hgs (g (g s))
                _ = b * (b * (t * ((g s : ↥T₀) : G)) * b⁻¹) * b⁻¹ := by rw [hgs (g s)]
                _ = b * (b * (b * (t * (s : G)) * b⁻¹) * b⁻¹) * b⁻¹ := by rw [hgs s]
                _ = b ^ 3 * (t * (s : G)) * (b ^ 3)⁻¹ := by
                      rw [show b ^ 3 = b * b * b by
                        rw [show (3 : ℕ) = 1 + 1 + 1 by norm_num, pow_add, pow_add, pow_one]]
                      group
                _ = t * (s : G) := by rw [hb3, inv_one, mul_one, one_mul]
            exact mul_left_cancel h1
          have h3ndvd : ¬ 3 ∣ Fintype.card ↥T₀ := by
            intro hdiv
            obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT₀
            rw [Nat.card_eq_fintype_card] at hk
            rw [hk] at hdiv
            have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdiv
            exact (by norm_num : ¬ (3 : ℕ) ∣ 2) h32
          let F : Function.End ↥T₀ := g
          have hEnd : F ^ 3 ^ 1 = 1 := by
            rw [pow_one]
            show g^[3] = (id : ↥T₀ → ↥T₀)
            funext s
            show g (g (g s)) = s
            exact hg3 s
          have hmod := Equiv.Perm.card_fixedPoints_modEq (f := F) (p := 3) (n := 1) hEnd
          have h3notdvd_fp : ¬ 3 ∣ Fintype.card (Function.fixedPoints F) := by
            intro hdiv
            have h : Fintype.card ↥T₀ ≡ 0 [MOD 3] := hmod.trans hdiv.modEq_zero_nat
            exact h3ndvd (Nat.modEq_zero_iff_dvd.mp h)
          obtain ⟨s, hs⟩ : ∃ s : ↥T₀, g s = s := by
            have hfp0 : Fintype.card (Function.fixedPoints F) ≠ 0 := by
              intro h0
              have : 3 ∣ Fintype.card (Function.fixedPoints F) := by
                rw [h0]
                exact dvd_zero 3
              exact h3notdvd_fp this
            obtain ⟨s⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hfp0)
            exact ⟨(s : ↥T₀), Function.mem_fixedPoints_iff.mp s.2⟩
          have hxs : (t : G) * (s : G) = b * (t * (s : G)) * b⁻¹ := by
            have := hgs s
            rwa [hs] at this
          have hxT : t * (s : G) ∈ T := T.mul_mem ht (hT₀T s.2)
          have hxcomm : (t * (s : G)) * b = b * (t * (s : G)) := by
            calc (t * (s : G)) * b = (b * (t * (s : G)) * b⁻¹) * b := congrArg (· * b) hxs
              _ = b * (t * (s : G)) := by group
          have hxT₀ : t * (s : G) ∈ T₀ := hC _ hxT hxcomm
          have ht' : t = (t * (s : G)) * (s : G)⁻¹ := by group
          rw [ht']
          exact T₀.mul_mem hxT₀ (T₀.inv_mem s.2)

end CFSG.StandardType.FrameRoute.FS81

end

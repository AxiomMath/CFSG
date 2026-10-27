module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Alt8
public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.Quasithin.J4L4

local notation "A₈" => alternatingGroup (Fin 8)

variable {G : Type*} [Group G]

theorem false_of_card_normalizing [Finite G] {P B : Subgroup G} (hP : IsPGroup 2 P)
    (hcard : 2 ^ 13 < Nat.card P) (hPB : P ≤ Subgroup.normalizer (B : Set G)) (e : ↥B ≃* A₈)
    (hC : ∀ g : G, orderOf g = 5 → ∀ K : Subgroup G, IsPGroup 2 K →
      K ≤ Subgroup.centralizer ({g} : Set G) → Nat.card K ≤ 64) : False := by
  obtain ⟨a, ha⟩ := exists_order_five
  set g : G := ((e.symm a : ↥B) : G) with hg
  have hg5 : orderOf g = 5 := by
    rw [hg, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ha]
  let ρ : ↥P →* MulAut A₈ :=
    (MulAut.congr e).toMonoidHom.comp (B.normalizerMonoidHom.comp (Subgroup.inclusion hPB))
  have hrange : Nat.card ρ.range ≤ 128 := by
    refine card_le_of_isPGroup_mulAut ?_
    exact hP.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hker : Nat.card ρ.ker ≤ 64 := by
    let K : Subgroup G := ρ.ker.map P.subtype
    have hKP : IsPGroup 2 K := hP.to_le (Subgroup.map_subtype_le _)
    have hKc : K ≤ Subgroup.centralizer ({g} : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : (MulAut.congr e) (B.normalizerMonoidHom (Subgroup.inclusion hPB x)) = 1 := hx
      have h2 : B.normalizerMonoidHom (Subgroup.inclusion hPB x) = 1 :=
        (MulAut.congr e).injective (h1.trans (map_one _).symm)
      have h3 := congrArg (fun φ : MulAut ↥B => ((φ (e.symm a) : ↥B) : G)) h2
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h3
      have h4 : (x : G) * g * (x : G)⁻¹ = g := h3
      exact (mul_inv_eq_iff_eq_mul.1 h4)
    have := hC g hg5 K hKP hKc
    rwa [Subgroup.card_map_of_injective P.subtype_injective] at this
  have hmul := Subgroup.card_ker_mul_card_range ρ
  have h128 : Nat.card ρ.ker * Nat.card ρ.range ≤ 64 * 128 := Nat.mul_le_mul hker hrange
  have : (2 : ℕ) ^ 13 = 64 * 128 := by norm_num
  omega

end CFSG.Quasithin.J4L4

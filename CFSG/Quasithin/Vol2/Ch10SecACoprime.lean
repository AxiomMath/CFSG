module

public import CFSG.Quasithin.Vol2.Ch10SecABasic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem commutator_inf_centralizer_eq_bot {W D : Subgroup G} [Finite D]
    [hWab : IsMulCommutative ↥W] (h2 : ∀ w ∈ W, w ^ 2 = 1) (hD : Odd (Nat.card D))
    (hDW : D ≤ Subgroup.normalizer (W : Set G)) :
    ⁅W, D⁆ ⊓ Subgroup.centralizer (D : Set G) = ⊥ := by
  have := Fintype.ofFinite ↥D
  have hconj : ∀ d : ↥D, ∀ w : ↥W, (d : G) * w * (d : G)⁻¹ ∈ W := fun d w =>
    (Subgroup.mem_normalizer_iff.mp (hDW d.2) w).mp w.2
  set c : ↥D → ↥W →* ↥W := fun d =>
    { toFun := fun w => ⟨(d : G) * w * (d : G)⁻¹, hconj d w⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) } with hc
  have hcv : ∀ d w, ((c d w : ↥W) : G) = (d : G) * w * (d : G)⁻¹ := fun d w => rfl
  set τ : ↥W →* ↥W :=
    { toFun := fun w => ∏ d : ↥D, c d w
      map_one' := by simp
      map_mul' := fun a b => by rw [← Finset.prod_mul_distrib]; simp } with hτ
  have hτv : ∀ w, τ w = ∏ d : ↥D, c d w := fun w => rfl
  have hτc : ∀ (d₀ : ↥D) (w : ↥W), τ (c d₀ w) = τ w := by
    intro d₀ w
    rw [hτv, hτv]
    refine Fintype.prod_equiv (Equiv.mulRight d₀) _ _ fun d => ?_
    apply Subtype.ext
    simp only [hcv, Equiv.coe_mulRight, Subgroup.coe_mul, mul_inv_rev]
    group
  have hτfix : ∀ w : ↥W, (∀ d : ↥D, c d w = w) → τ w = w := by
    intro w hw
    rw [hτv, Finset.prod_congr rfl fun d _ => hw d, Finset.prod_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := hD
    have hw2 : w ^ 2 = 1 := Subtype.ext (by simpa using h2 w w.2)
    rw [hk, pow_succ, pow_mul, hw2, one_pow, one_mul]
  set K : Subgroup G := τ.ker.map W.subtype with hK
  have hcomm : ⁅W, D⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro w hw d hd
    refine ⟨⟨w * d * w⁻¹ * d⁻¹, ?_⟩, ?_, rfl⟩
    · have := W.mul_mem hw (hconj ⟨d, hd⟩ ⟨w⁻¹, W.inv_mem hw⟩)
      simpa [mul_assoc] using this
    · rw [SetLike.mem_coe, MonoidHom.mem_ker]
      have he : (⟨w * d * w⁻¹ * d⁻¹, by
          have := W.mul_mem hw (hconj ⟨d, hd⟩ ⟨w⁻¹, W.inv_mem hw⟩)
          simpa [mul_assoc] using this⟩ : ↥W) =
          ⟨w, hw⟩ * c ⟨d, hd⟩ ⟨w⁻¹, W.inv_mem hw⟩ :=
        Subtype.ext (by simp [hcv, mul_assoc])
      have hinv : (⟨w⁻¹, W.inv_mem hw⟩ : ↥W) = (⟨w, hw⟩ : ↥W)⁻¹ := rfl
      rw [he, map_mul, hτc, ← map_mul, hinv, mul_inv_cancel, map_one]
  rw [eq_bot_iff]
  rintro x ⟨hxc, hxC⟩
  obtain ⟨w, hw, rfl⟩ := hcomm hxc
  have hfix : ∀ d : ↥D, c d w = w := fun d => Subtype.ext (by
    have h3 := Subgroup.mem_centralizer_iff.mp hxC d d.2
    simp only [Subgroup.coe_subtype] at h3
    rw [hcv, h3]
    group)
  rw [Subgroup.mem_bot]
  have h1 := hτfix w hfix
  rw [MonoidHom.mem_ker.mp hw] at h1
  rw [← h1]
  rfl

end CFSG.Quasithin.Vol2.Ch10.SecA

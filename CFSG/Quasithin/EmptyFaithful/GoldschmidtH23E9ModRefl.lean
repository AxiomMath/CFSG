module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.Quasithin.EmptyFaithful.S151bW3Mod

public section

namespace CFSG.Quasithin.SixData151b

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

variable {W : Type*} [CommGroup W] [Finite W] (S : SixData151b W 5)

theorem dih5_involution_inv_r :
    ∀ y : DihedralGroup 5, y ^ 2 = 1 → y ≠ 1 →
      y * DihedralGroup.r 1 * y⁻¹ = (DihedralGroup.r 1)⁻¹ := by
  decide

omit [Finite W] in
theorem reflection_inv_a₂ {x : MulAut W} (hx : x ∈ S.A₂) (hx2 : orderOf x = 2) :
    x * S.a₂ * x⁻¹ = S.a₂⁻¹ := by
  obtain ⟨y, rfl⟩ := S.exists_ι₂ hx
  have hy2 : y ^ 2 = 1 := by
    apply S.ι₂_injective
    rw [map_pow, map_one]
    have := pow_orderOf_eq_one (S.ι₂ y)
    rwa [hx2] at this
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hx2
    omega
  have h := dih5_involution_inv_r y hy2 hy1
  rw [S.a₂_eq_ι₂, ← map_inv, ← map_mul, ← map_mul, h, map_inv]

omit [Finite W] in
theorem reflection_inv_a₁ {x : MulAut W} (hx : x ∈ S.A₁) (hx2 : orderOf x = 2) :
    x * S.a₁ * x⁻¹ = S.a₁⁻¹ := by
  have h := S.swap.reflection_inv_a₂ (x := x) hx hx2
  rwa [swap_a₂] at h

omit [Finite W] in
theorem fix_W₁_of_mem_A₂ {x : MulAut W} (hx : x ∈ S.A₂) {w : W} (hw : w ∈ S.W₁) : x w = w :=
  (six_module151b S.comm S.winf).2.2.2 x hx w hw

omit [Finite W] in
theorem mem_W₂_of_mem_A₂ {x : MulAut W} (hx : x ∈ S.A₂) {w : W} (hw : w ∈ S.W₂) : x w ∈ S.W₂ :=
  (six_module151b S.comm S.winf).2.1 x hx w hw

theorem two_le_rk_fix_reflection₂ (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {x : MulAut W} (hx : x ∈ S.A₂) (hx2 : orderOf x = 2) :
    2 ≤ rk ↥(S.W₂ ⊓ fixV (Subgroup.zpowers x)) := by
  have hxsq : x ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2] at this
  have hst : ∀ w ∈ S.W₂, x w ∈ S.W₂ := fun w hw => S.mem_W₂_of_mem_A₂ hx hw
  have h1 := rk_commSub_add_rk_inf_fixV (g := x) (W := S.W₂) (invariant_zpowers151b hst)
  have h2 := rk_mono (commSub_le_fixV_of_sq151b hW hxsq hst)
  have h3 : rk S.W₂ = 4 := rk_eq_four_of_card_sixteen151b hW (S.card_W₂ hcard)
  omega

theorem rk_fix_reflection₂_le (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {x : MulAut W} (hx : x ∈ S.A₂) (hx2 : orderOf x = 2) :
    rk ↥(S.W₂ ⊓ fixV (Subgroup.zpowers x)) ≤ 2 := by
  have hxsq : x ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2] at this
  have hinv := S.reflection_inv_a₂ hx hx2
  set F : Subgroup W := S.W₂ ⊓ fixV (Subgroup.zpowers x) with hF
  set F' : Subgroup W := F.map S.a₂.toMonoidHom with hF'
  have hFle : F ≤ S.W₂ := inf_le_left
  have hF'le : F' ≤ S.W₂ := by
    rintro _ ⟨f, hf, rfl⟩
    exact S.mem_W₂_of_mem_A₂ S.a₂_mem hf.1
  have hxx : x * x = 1 := by rw [← pow_two]; exact hxsq
  have hrel : S.a₂ * x * S.a₂⁻¹ * x = S.a₂ * S.a₂ := by
    have h1 : x * S.a₂⁻¹ = S.a₂ * x := by
      have : x * S.a₂⁻¹ * x⁻¹ = S.a₂ := by
        calc x * S.a₂⁻¹ * x⁻¹ = (x * S.a₂ * x⁻¹)⁻¹ := by group
          _ = S.a₂ := by rw [hinv, inv_inv]
      calc x * S.a₂⁻¹ = (x * S.a₂⁻¹ * x⁻¹) * x := by group
        _ = S.a₂ * x := by rw [this]
    calc S.a₂ * x * S.a₂⁻¹ * x = S.a₂ * (x * S.a₂⁻¹) * x := by group
      _ = S.a₂ * (S.a₂ * x) * x := by rw [h1]
      _ = S.a₂ * S.a₂ * (x * x) := by group
      _ = S.a₂ * S.a₂ := by rw [hxx, mul_one]
  have hinf : F ⊓ F' = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwF, f, hf, rfl⟩
    have hxf : x f = f := mem_fixV_zpowers_iff.mp hf.2
    have hxw : x (S.a₂ f) = S.a₂ f := mem_fixV_zpowers_iff.mp hwF.2
    have hw2 : S.a₂ f ∈ S.W₂ := hF'le ⟨f, hf, rfl⟩
    have hfix2 : (S.a₂ * S.a₂) (S.a₂ f) = S.a₂ f := by
      rw [← hrel]
      show S.a₂ (x (S.a₂⁻¹ (x (S.a₂ f)))) = S.a₂ f
      rw [hxw]
      show S.a₂ (x (S.a₂⁻¹ (S.a₂ f))) = S.a₂ f
      rw [MulAut.inv_apply_self, hxf]
    have hmem : S.a₂ f ∈ fixV (Subgroup.zpowers (S.a₂ * S.a₂)) := mem_fixV_zpowers_iff.mpr hfix2
    have h6 : S.a₂ = (S.a₂ * S.a₂) ^ 3 := by
      have h5 : S.a₂ ^ 5 = 1 := S.a₂_pow (Or.inr rfl)
      have h66 : S.a₂ ^ 6 = S.a₂ := by rw [pow_succ, h5, one_mul]
      rw [← pow_two, ← pow_mul]
      exact h66.symm
    have hfix1 : S.a₂ (S.a₂ f) = S.a₂ f := by
      have := mem_fixV.mp hmem ((S.a₂ * S.a₂) ^ 3) (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 3)
      rwa [← h6] at this
    have hbot : S.a₂ f ∈ S.W₂ ⊓ fixV (Subgroup.zpowers S.a₂) :=
      ⟨hw2, mem_fixV_zpowers_iff.mpr hfix1⟩
    rw [S.fixV_inf_a₂ (Or.inr rfl) hW] at hbot
    exact hbot
  have hcardF' : rk F' = rk F := by
    unfold rk
    rw [hF', Subgroup.card_map_of_injective S.a₂.injective]
  have h1 := rk_sup_add_rk_inf F F'
  rw [hinf, rk_bot] at h1
  have h2 : rk ↥(F ⊔ F') ≤ rk S.W₂ := rk_mono (sup_le hFle hF'le)
  have h3 : rk S.W₂ = 4 := rk_eq_four_of_card_sixteen151b hW (S.card_W₂ hcard)
  omega

theorem card_fix_reflection₂ (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256) {x : MulAut W}
    (hx : x ∈ S.A₂) (hx2 : orderOf x = 2) :
    Nat.card ↥(S.W₂ ⊓ fixV (Subgroup.zpowers x)) = 4 := by
  have h1 := S.two_le_rk_fix_reflection₂ hW hcard hx hx2
  have h2 := S.rk_fix_reflection₂_le hW hcard hx hx2
  have h3 : rk ↥(S.W₂ ⊓ fixV (Subgroup.zpowers x)) = 2 := by omega
  rw [card_eq_two_pow hW, h3]
  norm_num

theorem card_fix_reflection₁ (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256) {x : MulAut W}
    (hx : x ∈ S.A₁) (hx2 : orderOf x = 2) :
    Nat.card ↥(S.W₁ ⊓ fixV (Subgroup.zpowers x)) = 4 :=
  S.swap.card_fix_reflection₂ hW hcard hx hx2

end CFSG.Quasithin.SixData151b

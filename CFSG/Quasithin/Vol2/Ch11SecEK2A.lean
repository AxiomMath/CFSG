module

public import CFSG.Quasithin.Vol2.Ch11SecEFacts2
public import CFSG.Quasithin.Vol2.Ch11SecBK7I
public import CFSG.Quasithin.Vol2.Ch11SecBK7H

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (qSp qSp_mul)
open scoped IsMulCommutative commutatorElement

namespace EK2

variable {K : Type*} [Field K] [CharP K 2]

theorem exists_smul_of_singular {x y z x₀ y₀ z₀ : K} (h : x * z = y ^ 2)
    (h₀ : x₀ * z₀ = y₀ ^ 2) (hs : (x + x₀) * (z + z₀) = (y + y₀) ^ 2)
    (hne : x₀ ≠ 0 ∨ z₀ ≠ 0) : ∃ c : K, x = c * x₀ ∧ y = c * y₀ ∧ z = c * z₀ := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hxz : x * z₀ = x₀ * z := by linear_combination hs - h - h₀ + (y * y₀ - x₀ * z) * h2
  by_cases hx₀ : x₀ = 0
  · have hz₀ : z₀ ≠ 0 := hne.resolve_left (not_not.mpr hx₀)
    subst hx₀
    have hy₀ : y₀ = 0 := (pow_eq_zero_iff two_ne_zero).mp (by rw [← h₀, zero_mul])
    subst hy₀
    have hx : x = 0 := (mul_eq_zero.mp (by rw [hxz, zero_mul] : x * z₀ = 0)).resolve_right hz₀
    subst hx
    have hy : y = 0 := (pow_eq_zero_iff two_ne_zero).mp (by rw [← h, zero_mul])
    subst hy
    refine ⟨z / z₀, by ring, by ring, by field_simp⟩
  · refine ⟨x / x₀, by field_simp, ?_, ?_⟩
    · have hz : z = x / x₀ * z₀ := by
        field_simp
        linear_combination -hxz
      have hy : (y - x / x₀ * y₀) ^ 2 = 0 := by
        have hx1 : x = x / x₀ * x₀ := by field_simp
        linear_combination (-1) * h + z * hx1 + x / x₀ * x₀ * hz + (x / x₀) ^ 2 * h₀ +
          ((x / x₀) ^ 2 * y₀ ^ 2 - x / x₀ * y * y₀) * h2
      exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hy)
    · field_simp
      linear_combination -hxz

end EK2

open EK2 CFSG.Quasithin.Vol2.Ch11.SecB CFSG.Quasithin.Vol2.Ch11.SecB.K7 in
theorem factSp4R2Big_holds : FactSp4R2Big := by
  intro G _ _ L V X T V₁ V₂ n hfl hk hCL A hA _ hmA
  obtain ⟨_, K, _, _, _, hK, π, f, hf, g, -, -, hV₂⟩ := exists_coord_flag24 hfl hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAV : ∀ {a : G}, a ∈ A → a ∈ Subgroup.normalizer (V : Set G) := fun ha =>
    r2_le_normalizer hfl (hA ha)
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 : ((a * b⁻¹ : ↥V) : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨(a * b⁻¹).2, (hf.eq_iff a b).mp hab⟩
    rw [hCL, Subgroup.mem_bot] at h1
    exact mul_inv_eq_one.mp (Subtype.ext h1)
  set Ψ : K × K × K → MulAut ↥V := fun t =>
    ((π (g * qSp t.1 t.2.1 t.2.2 * g⁻¹) : ↥(autOn L V)) : MulAut ↥V) with hΨ
  have hΨmul : ∀ t t' : K × K × K, Ψ t * Ψ t' = Ψ (t + t') := by
    intro t t'
    simp only [hΨ, ← Subgroup.coe_mul, ← map_mul]
    rw [show g * qSp t.1 t.2.1 t.2.2 * g⁻¹ * (g * qSp t'.1 t'.2.1 t'.2.2 * g⁻¹) =
      g * (qSp t.1 t.2.1 t.2.2 * qSp t'.1 t'.2.1 t'.2.2) * g⁻¹ by group, qSp_mul]
    rfl
  have hΨ0 : Ψ 0 = 1 := by
    have h1 := hΨmul 0 0
    rwa [add_zero, mul_eq_left] at h1
  have hΨf : ∀ t w, f (Ψ t w) =
      mat 2 K g *ᵥ (mat 2 K (qSp t.1 t.2.1 t.2.2) *ᵥ (mat 2 K g⁻¹ *ᵥ f w)) := fun t w => by
    rw [hΨ, hf.act4, KA.gconj_mulVec_sp]
  have hθ : ∀ a (ha : a ∈ A), ∃ t, SecA.conjV V a (hAV ha) = Ψ t := by
    intro a ha
    obtain ⟨x, y, z, hq⟩ := exists_qSp_of_mem_r2 hfl hK hf hV₂ (hA ha)
    exact ⟨(x, y, z), hq⟩
  have hmemV₂ : ∀ v : ↥V, (v : G) ∈ V₂ ↔ mat 2 K g⁻¹ *ᵥ f v ∈ spPlane K := by
    intro v
    rw [← Subgroup.mem_subgroupOf, hV₂, hf.mem_pre, Submodule.mem_toAddSubgroup, mem_gmapSp]
  have hAp : IsPGroup 2 A := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hA
  obtain ⟨a, ha, t, hat, hD⟩ : ∃ a, ∃ ha : a ∈ A, ∃ t : K × K × K,
      SecA.conjV V a (hAV ha) = Ψ t ∧ t.1 * t.2.2 ≠ t.2.1 ^ 2 := by
    by_contra hall
    push Not at hall
    have hsing : ∀ x : ↥(autOn A V), ∀ t, (x : MulAut ↥V) = Ψ t →
        t.1 * t.2.2 = t.2.1 ^ 2 := by
      intro x t hxt
      obtain ⟨a, ha, haV, hx⟩ := SecA.mem_autOn_iff.mp x.2
      exact hall a ha t (by rw [← hxt, hx])
    have hθ' : ∀ x : ↥(autOn A V), ∃ t, (x : MulAut ↥V) = Ψ t := by
      intro x
      obtain ⟨a, ha, haV, hx⟩ := SecA.mem_autOn_iff.mp x.2
      obtain ⟨t, ht⟩ := hθ a ha
      exact ⟨t, by rw [hx, ← ht]⟩
    choose θ hθx using hθ'
    have hcard : Nat.card (autOn A V) =
        2 ^ E3.mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) :=
      card_autOn_eq_two_pow hAp (fun a ha => hAV ha) rfl
    have h1 : 1 < Nat.card (autOn A V) := by
      rw [hcard]
      exact Nat.one_lt_two_pow (by omega)
    have : Nontrivial ↥(autOn A V) := Finite.one_lt_card_iff_nontrivial.mp h1
    obtain ⟨x₀, hx₀⟩ := exists_ne (1 : ↥(autOn A V))
    have hθ0 : (θ x₀).1 ≠ 0 ∨ (θ x₀).2.2 ≠ 0 := by
      by_contra h0
      push Not at h0
      have hy0 : (θ x₀).2.1 = 0 := by
        have h3 := hsing x₀ (θ x₀) (hθx x₀)
        rw [h0.1, zero_mul] at h3
        exact (pow_eq_zero_iff two_ne_zero).mp h3.symm
      apply hx₀
      apply Subtype.ext
      rw [hθx x₀, Subgroup.coe_one,
        show θ x₀ = 0 from Prod.ext h0.1 (Prod.ext hy0 h0.2), hΨ0]
    have hmult : ∀ x : ↥(autOn A V), ∃ c : K, (θ x).1 = c * (θ x₀).1 ∧
        (θ x).2.1 = c * (θ x₀).2.1 ∧ (θ x).2.2 = c * (θ x₀).2.2 := by
      intro x
      have hs := hsing (x * x₀) (θ x + θ x₀) (by rw [Subgroup.coe_mul, hθx x, hθx x₀, hΨmul])
      exact exists_smul_of_singular (hsing x (θ x) (hθx x)) (hsing x₀ (θ x₀) (hθx x₀)) hs hθ0
    choose c hc using hmult
    have hinj : Function.Injective c := by
      intro x x' hxx
      apply Subtype.ext
      have he : θ x = θ x' := Prod.ext (by rw [(hc x).1, (hc x').1, hxx])
        (Prod.ext (by rw [(hc x).2.1, (hc x').2.1, hxx]) (by rw [(hc x).2.2, (hc x').2.2, hxx]))
      rw [hθx x, hθx x', he]
    have h2 := Nat.card_le_card_of_injective c hinj
    rw [hcard, hK] at h2
    have h3 : 2 ^ n < 2 ^ E3.mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) :=
      Nat.pow_lt_pow_right (by norm_num) hmA
    omega
  obtain ⟨x, y, z⟩ := t
  have hD' : x * z - y ^ 2 ≠ 0 := sub_ne_zero.mpr hD
  have hcommV₂ : ∀ a' (ha' : a' ∈ A) (v : ↥V),
      ((SecA.conjV V a' (hAV ha') v * v⁻¹ : ↥V) : G) ∈ V₂ := by
    intro a' ha' v
    obtain ⟨t', ht'⟩ := hθ a' ha'
    rw [hmemV₂, ht', hf.map_mul_inv, hΨf, Matrix.mulVec_sub, mat_inv_mulVec, qSp_mulVec,
      mem_spPlane]
    simp only [Pi.sub_apply, vec4_apply_inr0, vec4_apply_inr1, sub_self, and_self]
  have hle : ⁅V, A⁆ ≤ V₂ := by
    rw [Subgroup.commutator_le]
    intro v hv a' ha'
    have hc : ⁅v, a'⁆ =
        (((SecA.conjV V a' (hAV ha') ⟨v, hv⟩ * (⟨v, hv⟩ : ↥V)⁻¹ : ↥V) : G))⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, SecA.conjV_apply_coe,
        commutatorElement_def]
      group
    rw [hc]
    exact V₂.inv_mem (hcommV₂ a' ha' ⟨v, hv⟩)
  have hge : V₂ ≤ ⁅V, A⁆ := by
    intro w hw
    set w' : ↥V := ⟨w, hfl.le₂ hw⟩ with hw'
    obtain ⟨hk2, hk3⟩ := (hmemV₂ w').mp hw
    set k := mat 2 K g⁻¹ *ᵥ f w' with hk
    set b₀ := (z * k (.inl 0) - y * k (.inl 1)) / (x * z - y ^ 2) with hb₀
    set b₁ := (x * k (.inl 1) - y * k (.inl 0)) / (x * z - y ^ 2) with hb₁
    obtain ⟨v, hv⟩ := hf.surj (mat 2 K g *ᵥ vec4 0 0 b₀ b₁)
    have hvw : SecA.conjV V a (hAV ha) v * v⁻¹ = w' := by
      apply hfinj
      rw [hf.map_mul_inv, hat, hΨf, hv, mat_inv_mulVec, ← Matrix.mulVec_sub,
        ← mat_mulVec_inv g (f w'), ← hk]
      congr 1
      have hDinv : (x * z - y ^ 2) * (x * z - y ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hD'
      rw [qSp_mulVec]
      refine vec4_eq ?_ ?_ ?_ ?_
      · simp only [Pi.sub_apply, vec4_apply_inl0, vec4_apply_inr0, vec4_apply_inr1]
        rw [hb₀, hb₁, div_eq_mul_inv, div_eq_mul_inv]
        linear_combination k (.inl 0) * hDinv
      · simp only [Pi.sub_apply, vec4_apply_inl1, vec4_apply_inr0, vec4_apply_inr1]
        rw [hb₀, hb₁, div_eq_mul_inv, div_eq_mul_inv]
        linear_combination k (.inl 1) * hDinv
      · simp only [Pi.sub_apply, vec4_apply_inr0, sub_self]
        exact hk2.symm
      · simp only [Pi.sub_apply, vec4_apply_inr1, sub_self]
        exact hk3.symm
    have h1 := conjV_comm_mem ha (hAV ha) v
    rw [hvw] at h1
    exact h1
  refine ⟨le_antisymm hle hge, le_antisymm ?_ ?_⟩
  ·
    rintro u ⟨huV, huA⟩
    set u' : ↥V := ⟨u, huV⟩ with hu'
    have hfix : SecA.conjV V a (hAV ha) u' = u' := Subtype.ext (by
      rw [SecA.conjV_apply_coe, hu', Subgroup.mem_centralizer_iff.mp huA a ha,
        mul_inv_cancel_right])
    have h1 := congrArg f hfix
    rw [hat, hΨf] at h1
    have h2 := congrArg (fun v => mat 2 K g⁻¹ *ᵥ v) h1
    simp only [mat_inv_mulVec] at h2
    rw [qSp_mulVec] at h2
    have e0 := congrFun h2 (.inl 0)
    have e1 := congrFun h2 (.inl 1)
    simp only [vec4_apply_inl0, vec4_apply_inl1] at e0 e1
    refine (hmemV₂ u').mpr ⟨?_, ?_⟩
    · have h3 : (x * z - y ^ 2) * (mat 2 K g⁻¹ *ᵥ f u') (.inr 0) = 0 := by
        linear_combination z * e0 - y * e1
      exact (mul_eq_zero.mp h3).resolve_left hD'
    · have h3 : (x * z - y ^ 2) * (mat 2 K g⁻¹ *ᵥ f u') (.inr 1) = 0 := by
        linear_combination x * e1 - y * e0
      exact (mul_eq_zero.mp h3).resolve_left hD'
  ·
    intro u hu
    refine ⟨hfl.le₂ hu, Subgroup.mem_centralizer_iff.mpr fun a' ha' => ?_⟩
    set u' : ↥V := ⟨u, hfl.le₂ hu⟩ with hu'
    obtain ⟨t', ht'⟩ := hθ a' ha'
    have hfix : SecA.conjV V a' (hAV ha') u' = u' := by
      apply hfinj
      rw [ht', hΨf, qSp_fix_plane _ _ _ ((hmemV₂ u').mp hu), mat_mulVec_inv]
    have h2 := congrArg Subtype.val hfix
    rw [SecA.conjV_apply_coe] at h2
    calc a' * u = a' * u * a'⁻¹ * a' := by group
      _ = u * a' := by rw [h2]

end CFSG.Quasithin.Vol2.Ch11.SecE

module

public import CFSG.Quasithin.Vol2.Ch11SecBK7K
public import CFSG.Quasithin.Vol2.Ch11SecBK7C
public import CFSG.Quasithin.Vol2.Ch11SecBK7H

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (qSp qSp_mul)
open scoped IsMulCommutative

open K7 in
theorem factSp4NoTransv_holds : FactSp4NoTransv := by
  intro G _ _ L V X T V₁ V₂ n hfl hk A hA hmA hnt
  obtain ⟨_, K, _, _, _, hK, π, f, hf, g, -, -, hV₂⟩ := exists_coord_flag24 hfl hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut ↥V) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hAV : ∀ {a : G}, a ∈ A → a ∈ Subgroup.normalizer (V : Set G) := fun ha =>
    r2_le_normalizer hfl (hA ha)
  set ρ : StatedSp 2 K → MulAut ↥V := fun γ => ((π γ : ↥(autOn L V)) : MulAut ↥V) with hρ
  have hρmul : ∀ γ δ, ρ (γ * δ) = ρ γ * ρ δ := fun γ δ => by
    simp only [hρ, map_mul, Subgroup.coe_mul]
  have hρinv : ∀ γ, ρ γ⁻¹ = (ρ γ)⁻¹ := fun γ => by
    simp only [hρ, map_inv, Subgroup.coe_inv]
  set e₀ : Fin 2 ⊕ Fin 2 → K := vec4 1 0 0 0 with he₀
  set e₁ : Fin 2 ⊕ Fin 2 → K := vec4 0 1 0 0 with he₁
  have hy0 : mat 2 K g *ᵥ e₀ ≠ 0 := v0_ne_zero g
  have hy'0 : mat 2 K g *ᵥ e₁ ≠ 0 := fun h => by
    have := congrFun (congrArg (fun x => mat 2 K g⁻¹ *ᵥ x) h) (.inl 1)
    simp only [mat_inv_mulVec, Matrix.mulVec_zero, he₁, vec4_apply_inl1, Pi.zero_apply] at this
    exact one_ne_zero this
  have htrv : ∀ (u : Fin 2 ⊕ Fin 2 → K) (c : K), ρ (trv (mat 2 K g *ᵥ u) c) =
      ρ (g * trv u c * g⁻¹) := fun u c => by rw [trv_conj]
  have hθ : ∀ x : ↥(autOn A V), ∃ t : K × K × K,
      (x : MulAut ↥V) = ρ (g * qSp t.1 t.2.1 t.2.2 * g⁻¹) := by
    intro x
    obtain ⟨a, ha, haV, hx⟩ := SecA.mem_autOn_iff.mp x.2
    obtain ⟨x₁, x₂, x₃, hq⟩ := exists_qSp_of_mem_r2 hfl hK hf hV₂ (hA ha)
    exact ⟨(x₁, x₂, x₃), by rw [hx]; exact hq⟩
  choose θ hθ using hθ
  have hmeet : ∀ (x : ↥(autOn A V)) (c : K),
      (x : MulAut ↥V) = ρ (trv (mat 2 K g *ᵥ e₁) c) → c = 0 := by
    intro x c hxc
    by_contra hc
    obtain ⟨a, ha, haV, hx⟩ := SecA.mem_autOn_iff.mp x.2
    exact hnt a ha (mQuot_singleton_eq hf fix_of_autOn hK haV hy'0 hc (by rw [← hx, hxc]))
  have hconj : ∀ a b : ↥(StatedSp 2 K), g * a * g⁻¹ * (g * b * g⁻¹)⁻¹ = g * (a * b⁻¹) * g⁻¹ :=
    fun a b => by group
  have hconj' : ∀ a b : ↥(StatedSp 2 K), g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ :=
    fun a b => by group
  let Φ : ↥(autOn A V) × K → K × K × K := fun p =>
    ((θ p.1).1, (θ p.1).2.1, (θ p.1).2.2 + p.2)
  have hΦinj : Function.Injective Φ := by
    rintro ⟨x, c⟩ ⟨x', c'⟩ h
    simp only [Φ, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have h3' : (θ x).2.2 - (θ x').2.2 = -(c - c') := by linear_combination h3
    have hxx : ((x * x'⁻¹ : ↥(autOn A V)) : MulAut ↥V) =
        ρ (trv (mat 2 K g *ᵥ e₁) (c - c')) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hθ x, hθ x', ← hρinv, ← hρmul, hconj,
        qSp_mul_inv, htrv, he₁, trv_e1, h1, h2, sub_self, sub_self, h3']
    have hc : c = c' := sub_eq_zero.mp (hmeet _ _ hxx)
    subst hc
    have hθe : θ x = θ x' := Prod.ext h1 (Prod.ext h2 (add_right_cancel h3))
    have hxe : x = x' := Subtype.ext (by rw [hθ x, hθ x', hθe])
    rw [hxe]
  have hcardA : Nat.card (autOn A V) = Nat.card K ^ 2 := by
    rw [card_autOn_eq_two_pow ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hA)
      (fun a ha => hAV ha) hmA, hK, ← pow_mul, mul_comm]
  have hΦbij : Function.Bijective Φ := by
    refine (Nat.bijective_iff_injective_and_card Φ).mpr ⟨hΦinj, ?_⟩
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, hcardA]
    ring
  have hcomm : ∀ (c : K) (v : ↥V), ρ (trv (mat 2 K g *ᵥ e₀) c) v * v⁻¹ ∈
      (⁅V, A⁆).subgroupOf V := by
    intro c v
    obtain ⟨⟨x, d⟩, hxd⟩ := hΦbij.2 (-c, 0, 0)
    simp only [Φ, Prod.mk.injEq] at hxd
    obtain ⟨d1, d2, d3⟩ := hxd
    have d3' : (θ x).2.2 = -d := by linear_combination d3
    have hxdec : (x : MulAut ↥V) = ρ (trv (mat 2 K g *ᵥ e₀) c) *
        ρ (trv (mat 2 K g *ᵥ e₁) d) := by
      rw [hθ x, htrv, htrv, ← hρmul, hconj', he₀, he₁, trv_e0, trv_e1, qSp_mul, d1, d2, d3']
      simp only [add_zero, zero_add]
    obtain ⟨b₀, hb₀⟩ : ∃ b : K, (mat 2 K g⁻¹ *ᵥ f v) (.inr 0) = b := ⟨_, rfl⟩
    obtain ⟨v₂, hv₂⟩ := hf.surj (mat 2 K g *ᵥ vec4 0 0 b₀ 0)
    have hfix1 : ρ (trv (mat 2 K g *ᵥ e₀) c) (v * v₂⁻¹) = v * v₂⁻¹ := by
      refine trv_fix hf fix_of_autOn hy0 c ?_
      have e1 : f (v * v₂⁻¹) = mat 2 K g *ᵥ (mat 2 K g⁻¹ *ᵥ f v - vec4 0 0 b₀ 0) := by
        rw [hf.map_mul_inv, hv₂, Matrix.mulVec_sub, mat_mulVec_inv]
      rw [e1, spB_mat, toBilin'_spJ_apply]
      simp [Fin.sum_univ_two, he₀, vec4, hb₀]
    have hfix2 : ρ (trv (mat 2 K g *ᵥ e₁) d) v₂ = v₂ := by
      refine trv_fix hf fix_of_autOn hy'0 d ?_
      rw [hv₂, spB_mat, toBilin'_spJ_apply]
      simp [Fin.sum_univ_two, he₁, vec4]
    rw [comm_eq_of_fix hfix1]
    have e : ρ (trv (mat 2 K g *ᵥ e₀) c) v₂ = (x : MulAut ↥V) v₂ := by
      rw [hxdec, MulAut.mul_apply, hfix2]
    rw [e]
    obtain ⟨a, ha, haV, hx⟩ := SecA.mem_autOn_iff.mp x.2
    rw [hx]
    exact conjV_comm_mem ha haV v₂
  obtain ⟨l, hl0, hl1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hfl.two_le hK
  have hsq : ∀ u : ↥V, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hfl.elem.2 u u.2)
  refine le_commutator_of_le_acomm (le_acomm hf fix_of_autOn
    (commV_autOn_eq_top hfl.le_normalizer hfl.commutator_eq) hsq hl0 hl1 hy0) ?_
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨c, u, rfl⟩
  exact hcomm c u

end CFSG.Quasithin.Vol2.Ch11.SecB

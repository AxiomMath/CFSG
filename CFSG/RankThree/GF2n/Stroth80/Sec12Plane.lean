module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Decomp

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.act_fixes_Wp (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) {t : G}
    (ht : t ∈ LB M Q B) {T : M₀.E → M₀.E} (hT : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x))
    {y : M₀.E} (hy : y ∈ PerpSub M₀ (Lgen M B)) : T y = y := by
  obtain ⟨c, hcP, hcQ, rfl⟩ := (hc.mem_img_PerpB_iff h y).mpr hy
  rw [← hT c hcQ]
  exact (M₀.comm_mem_iff hcQ ((hc.conj_mem_Q_of_mem_M (hc.LB_le_M ht)).1 c hcQ)).mp
    (hc.comm_LB_PerpB_mem_Z ht hcP)

theorem finrank_span_pair_of_B {b f : M₀.E} (hb0 : b ≠ 0) (hfb : M₀.B f b = 1) :
    Module.finrank K (Submodule.span K {b, f}) = 2 := by
  have hli : LinearIndependent K ![b, f] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : M₀.B (s • b + t • f) b = 0 := by rw [hst]; simp
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      M₀.alt, hfb] at h1
    have ht : t = 0 := by simpa using h1
    subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hb0, rfl⟩
  have hr : Set.range ![b, f] = {b, f} := by
    ext x
    simp [Matrix.range_cons, Set.pair_comm]
  have := finrank_span_eq_card hli
  rw [hr] at this
  simpa using this

theorem Ctx.finrank_U (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) {n : ℕ}
    (hw : Width Q Z n) (hd : Module.finrank K (PerpSub M₀ (Lgen M B)) = 2) {b f : M₀.E}
    (hb0 : b ≠ 0) (hbW : b ∈ hc.Wn h) (hfb : M₀.B f b = 1) :
    Module.finrank K
      (M₀.B.orthogonal (Submodule.span K {b, f} ⊔ PerpSub M₀ (Lgen M B))) = 2 * n - 4 := by
  have hK : 1 < Nat.card K := by
    rw [h.card]
    have := hc.hyp.q4
    omega
  have hE := h.finrank_E hw hK
  have hP := finrank_span_pair_of_B (M₀ := M₀) (K := K) hb0 hfb
  have hinf : Submodule.span K {b, f} ⊓ PerpSub M₀ (Lgen M B) = ⊥ := by
    rw [eq_bot_iff]
    rintro e ⟨he1, he2⟩
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp he1
    have hb' : M₀.B (s • b + t • f) b = 0 := hc.B_Wp_Wn h he2 hbW
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      M₀.alt, hfb] at hb'
    have ht : t = 0 := by simpa using hb'
    subst ht
    rw [zero_smul, add_zero] at he2 ⊢
    have hsb : s • b ∈ hc.Wn h ⊓ PerpSub M₀ (Lgen M B) := ⟨(hc.Wn h).smul_mem s hbW, he2⟩
    rw [hc.Wn_inf_Wp h, Submodule.mem_bot] at hsb
    exact hsb
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {b, f})
    (PerpSub M₀ (Lgen M B))
  rw [hinf, finrank_bot, hP, hd] at h1
  have h2 := LinearMap.BilinForm.finrank_orthogonal (modelB_nondegenerate M₀)
    (Submodule.span K {b, f} ⊔ PerpSub M₀ (Lgen M B))
  rw [h2, hE]
  omega

end CFSG.RankThree.GF2n.Stroth80

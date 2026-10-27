module

public import CFSG.RankThree.GF2n.Smith81.S81YE5Def

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE5

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.RootGen

variable
  {K : Type} [Field K]

theorem e7_pairNF [CharP K 2] {x y : G7 K} (hx : IsRootEltG x) (hy : IsRootEltG y) :
    ∃ (e : G7 K) (a b : K) (δ : Fin (Tag.rank .E7) → ℤ), a ≠ 0 ∧ b ≠ 0 ∧ IsRoot .E7 δ ∧
      e * x * e⁻¹ = e7Data_valid.xm K theta a ∧ e * y * e⁻¹ = e7Data_valid.xm K δ b := by
  obtain ⟨p, a, ha, rfl⟩ := fe3_isRootEltG_conj_theta hx
  obtain ⟨q, d, hd, rfl⟩ := fe3_isRootEltG_conj_theta hy
  obtain ⟨w, b₁, hb₁, b₂, hb₂, hg⟩ := bruhat_decomp (p⁻¹ * q)
  obtain ⟨d', hconj₂, hdd⟩ := bor_conj_xm_theta hb₂ d
  obtain ⟨γ', c'', hγ', hconjW, hcc⟩ := nW_conj_xm_theta w d'
  obtain ⟨a', hconj₁, haa⟩ := bor_conj_xm_theta (inv_mem hb₁) a
  have hq : q = p * (b₁ * nW K w * b₂) := by
    rw [← hg, mul_inv_cancel_left]
  have hx_e : b₁⁻¹ * p⁻¹ * (p * e7Data_valid.xm K theta a * p⁻¹) * (b₁⁻¹ * p⁻¹)⁻¹
      = e7Data_valid.xm K theta a' := by
    rw [← hconj₁]
    group
  have hy_e : b₁⁻¹ * p⁻¹ * (q * e7Data_valid.xm K theta d * q⁻¹) * (b₁⁻¹ * p⁻¹)⁻¹
      = e7Data_valid.xm K γ' c'' := by
    rw [hq]
    calc b₁⁻¹ * p⁻¹ * (p * (b₁ * nW K w * b₂) * e7Data_valid.xm K theta d
          * (p * (b₁ * nW K w * b₂))⁻¹) * (b₁⁻¹ * p⁻¹)⁻¹
        = nW K w * (b₂ * e7Data_valid.xm K theta d * b₂⁻¹) * (nW K w)⁻¹ := by group
      _ = nW K w * e7Data_valid.xm K theta d' * (nW K w)⁻¹ := by rw [hconj₂]
      _ = e7Data_valid.xm K γ' c'' := hconjW
  exact ⟨b₁⁻¹ * p⁻¹, a', c'', γ', haa ha, hcc (hdd hd), hγ', hx_e, hy_e⟩

theorem e7_lineNF [CharP K 2] {g : G7 K} {c : K} (hc : c ≠ 0) :
    ∃ (u : G7 K) (μ : Fin e7Data.d) (c₀ : K), u ∈ Uni K ∧ c₀ ≠ 0 ∧
      c • act7 g (w0 : V K) = c₀ • act7 u (Finsupp.single μ 1) := by
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := bruhat_decomp g
  obtain ⟨u, hu, t, ht, rfl⟩ := bor_eq_mul hb₁
  obtain ⟨c₂, hc₂⟩ := endo_bor_w0 (K := K) hb₂
  obtain ⟨μ, hμ⟩ := endo_nW_single (K := K) w ⟨0, by decide⟩
  obtain ⟨c₃, hc₃⟩ := endo_tor_single (K := K) ht μ
  have hmul : ∀ (g h : G7 K) (v : V K), act7 (g * h) v = act7 g (act7 h v) :=
    fun g h v => by rw [act7_mul]; rfl
  have hw0 : act7 b₂ (w0 : V K) = c₂ • (w0 : V K) := by rw [act7_apply]; exact hc₂
  have hnw : act7 (nW K w) (w0 : V K) = Finsupp.single μ 1 := by rw [act7_apply]; exact hμ
  have ht3 : act7 t (Finsupp.single μ 1) = c₃ • Finsupp.single μ 1 := by
    rw [act7_apply]; exact hc₃
  have hw0ne : (w0 : V K) ≠ 0 := Finsupp.single_ne_zero.2 one_ne_zero
  have hμne : (Finsupp.single μ 1 : V K) ≠ 0 := Finsupp.single_ne_zero.2 one_ne_zero
  have hc₂0 : c₂ ≠ 0 := by
    rintro rfl
    apply hw0ne
    have h1 : act7 b₂ (w0 : V K) = 0 := by rw [hw0, zero_smul]
    exact (act7 b₂).map_eq_zero_iff.1 h1
  have hc₃0 : c₃ ≠ 0 := by
    rintro rfl
    apply hμne
    have h1 : act7 t (Finsupp.single μ 1) = 0 := by rw [ht3, zero_smul]
    exact (act7 t).map_eq_zero_iff.1 h1
  refine ⟨u, μ, c * c₂ * c₃, hu, mul_ne_zero (mul_ne_zero hc hc₂0) hc₃0, ?_⟩
  have key : act7 (u * t * nW K w * b₂) (w0 : V K)
      = (c₂ * c₃) • act7 u (Finsupp.single μ 1) := by
    simp only [hmul, hw0, map_smul, hnw, ht3, smul_smul]
  rw [key, smul_smul, mul_assoc]

theorem e7_single_mem_range_theta [CharP K 2] {a : K} {μ : Fin e7Data.d}
    (h : (Finsupp.single μ 1 : V K) ∈
      LinearMap.range ((act7 (e7Data_valid.xm K theta a) : V K →ₗ[K] V K) - 1)) :
    pr μ theta = 1 := by
  obtain ⟨v, hv⟩ := h
  simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, act7_xm] at hv
  have hsm : a • e7Data.rootOp K theta v = Finsupp.single μ 1 := by
    rw [← hv]; abel
  have hr : (Finsupp.single μ 1 : V K) ∈ LinearMap.range (e7Data.rootOp K theta) := by
    rw [← hsm]
    exact Submodule.smul_mem _ a (LinearMap.mem_range_self (e7Data.rootOp K theta) v)
  rw [rootOp_range_eq_supported (K := K) isRoot_theta, Finsupp.mem_supported'] at hr
  by_contra hne
  have h0 := hr μ (by simp [hne])
  rw [Finsupp.single_eq_same] at h0
  exact one_ne_zero h0

end CFSG.RankThree.GF2n.Smith81.RootGenE5

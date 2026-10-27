module

public import CFSG.RankThree.GF2n.Smith81.S81YE4Line
public import CFSG.RankThree.GF2n.Smith81.S81YE4Levi

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE4

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.RankThree.GF2n.Smith81.RootGen CFSG.RankThree.GF2n.Smith81.RootGenE5

variable
  {K : Type} [Field K]


theorem single_mem_range_root [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) {a : K}
    {μ : Fin e7Data.d}
    (h : (Finsupp.single μ 1 : V K) ∈
      LinearMap.range ((act7 (e7Data_valid.xm K γ a) : V K →ₗ[K] V K) - 1)) :
    pr μ γ = 1 := by
  obtain ⟨v, hv⟩ := h
  simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, act7_xm] at hv
  have hsm : a • e7Data.rootOp K γ v = Finsupp.single μ 1 := by
    rw [← hv]; abel
  have hr : (Finsupp.single μ 1 : V K) ∈ LinearMap.range (e7Data.rootOp K γ) := by
    rw [← hsm]
    exact Submodule.smul_mem _ a (LinearMap.mem_range_self (e7Data.rootOp K γ) v)
  rw [rootOp_range_eq_supported (K := K) hγ, Finsupp.mem_supported'] at hr
  by_contra hne
  have h0 := hr μ (by simp [hne])
  rw [Finsupp.single_eq_same] at h0
  exact one_ne_zero h0

theorem move_normal_form4 [CharP K 2] {a : K} {δ : Fin (Tag.rank .E7) → ℤ} (hδ : δ ∈ Perp)
    (hδne : δ ≠ -theta4) (b : K) {q : V K} (hq : IsPureL q)
    (hqr : q ∈ LinearMap.range ((act7 (e7Data_valid.xm K theta4 a) : V K →ₗ[K] V K) - 1)) :
    ∃ n : G7 K, n ∈ LG K ∧
      (∀ a' : K, n * e7Data_valid.xm K theta4 a' = e7Data_valid.xm K theta4 a' * n) ∧
      act7 (e7Data_valid.xm K δ b) (act7 n q) = act7 n q := by
  obtain ⟨g, hg, c, hc, rfl⟩ := hq
  obtain ⟨u, μ, c₀, hu, hucomm, hμidx, hc₀, hline⟩ := e4V_lineNF hg hc
  have hucomm' : ∀ a' : K,
      u⁻¹ * e7Data_valid.xm K theta4 a' = e7Data_valid.xm K theta4 a' * u⁻¹ := by
    intro a'
    calc u⁻¹ * e7Data_valid.xm K theta4 a'
        = u⁻¹ * (e7Data_valid.xm K theta4 a' * u) * u⁻¹ := by group
      _ = u⁻¹ * (u * e7Data_valid.xm K theta4 a') * u⁻¹ := by rw [hucomm a']
      _ = e7Data_valid.xm K theta4 a' * u⁻¹ := by group
  have hcomm : ∀ x : V K, act7 u⁻¹ (act7 (e7Data_valid.xm K theta4 a) x) =
      act7 (e7Data_valid.xm K theta4 a) (act7 u⁻¹ x) := by
    intro x
    have h1 : act7 (u⁻¹ * e7Data_valid.xm K theta4 a) x =
        act7 u⁻¹ (act7 (e7Data_valid.xm K theta4 a) x) := by
      rw [act7_mul, LinearEquiv.mul_apply]
    have h2 : act7 (e7Data_valid.xm K theta4 a * u⁻¹) x =
        act7 (e7Data_valid.xm K theta4 a) (act7 u⁻¹ x) := by
      rw [act7_mul, LinearEquiv.mul_apply]
    rw [← h1, ← h2, hucomm' a]
  have hinv : ∀ s : V K, act7 u⁻¹ (act7 u s) = s := by
    intro s
    have h1 : act7 (u⁻¹ * u) s = act7 u⁻¹ (act7 u s) := by
      rw [act7_mul, LinearEquiv.mul_apply]
    rw [← h1, inv_mul_cancel]
    simp [act7_one]
  have hkey : ∀ x : V K,
      act7 u⁻¹ (((act7 (e7Data_valid.xm K theta4 a) : V K →ₗ[K] V K) - 1) x) =
        ((act7 (e7Data_valid.xm K theta4 a) : V K →ₗ[K] V K) - 1) (act7 u⁻¹ x) := by
    intro x
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, map_sub, hcomm]
  have hμ1 : pr μ theta4 = 1 := by
    refine single_mem_range_root isRoot_theta4 (a := a) ?_
    rw [hline, LinearMap.mem_range] at hqr
    obtain ⟨w, hw⟩ := hqr
    rw [LinearMap.mem_range]
    refine ⟨c₀⁻¹ • act7 u⁻¹ w, ?_⟩
    rw [map_smul, ← hkey, hw, map_smul, hinv, smul_smul, inv_mul_cancel₀ hc₀, one_smul]
  obtain ⟨γ, hγidx, hγ1, hγδ⟩ := exists_pr_ne4 hδ hδne
  obtain ⟨n, hnL, hncomm, hnμγ⟩ := exists_levi_move4 (K := K) hμidx hμ1 hγidx hγ1
  have hN : ∀ s : V K, act7 (n * u⁻¹) (act7 u s) = act7 n s := by
    intro s
    have h1 : act7 (n * u⁻¹) (act7 u s) = act7 n (act7 u⁻¹ (act7 u s)) := by
      rw [act7_mul, LinearEquiv.mul_apply]
    rw [h1, hinv]
  have hval : act7 (n * u⁻¹) (c • act7 g (Finsupp.single (a0 : Fin e7Data.d) 1)) =
      c₀ • (Finsupp.single γ 1 : V K) := by
    rw [hline, map_smul, hN, hnμγ]
  have hfix : act7 (e7Data_valid.xm K δ b) (Finsupp.single γ 1 : V K) = Finsupp.single γ 1 := by
    rw [act7_xm, rootOp_single (K := K) hδ.1 γ, if_neg hγδ, smul_zero, add_zero]
  refine ⟨n * u⁻¹, mul_mem hnL (inv_mem hu), ?_, ?_⟩
  · intro a'
    calc n * u⁻¹ * e7Data_valid.xm K theta4 a'
        = n * (u⁻¹ * e7Data_valid.xm K theta4 a') := mul_assoc _ _ _
      _ = n * (e7Data_valid.xm K theta4 a' * u⁻¹) := by rw [hucomm' a']
      _ = (n * e7Data_valid.xm K theta4 a') * u⁻¹ := (mul_assoc _ _ _).symm
      _ = (e7Data_valid.xm K theta4 a' * n) * u⁻¹ := by rw [hncomm a']
      _ = e7Data_valid.xm K theta4 a' * (n * u⁻¹) := mul_assoc _ _ _
  · rw [hval, map_smul, hfix]

end CFSG.RankThree.GF2n.Smith81.RootGenE4

module

public import CFSG.RankThree.GF2n.Smith81.S81YE5Pair
public import CFSG.RankThree.GF2n.Smith81.S81YE5Nbeta

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE5

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.RootGen

variable
  {K : Type} [Field K]


theorem move_normal_form [CharP K 2] {a : K} (ha : a ≠ 0) {δ : Fin (Tag.rank .E7) → ℤ}
    (hδ : IsRoot .E7 δ) (hδne : δ ≠ -theta) (b : K) {q : V K}
    (hq : ∃ (g : G7 K) (c : K), c ≠ 0 ∧ q = c • act7 g (w0 : V K))
    (hqr : q ∈ LinearMap.range ((act7 (e7Data_valid.xm K theta a) : V K →ₗ[K] V K) - 1)) :
    ∃ n : G7 K, (∀ a' : K, n * e7Data_valid.xm K theta a' = e7Data_valid.xm K theta a' * n) ∧
      act7 (e7Data_valid.xm K δ b) (act7 n q) = act7 n q := by
  obtain ⟨g, c, hc, rfl⟩ := hq
  obtain ⟨u, μ, c₀, hu, hc₀, hline⟩ := e7_lineNF (g := g) hc
  have hcomm : ∀ x : V K, act7 u⁻¹ (act7 (e7Data_valid.xm K theta a) x) =
      act7 (e7Data_valid.xm K theta a) (act7 u⁻¹ x) := by
    intro x
    have h1 : act7 (u⁻¹ * e7Data_valid.xm K theta a) x =
        act7 u⁻¹ (act7 (e7Data_valid.xm K theta a) x) := by
      rw [act7_mul, LinearEquiv.mul_apply]
    have h2 : act7 (e7Data_valid.xm K theta a * u⁻¹) x =
        act7 (e7Data_valid.xm K theta a) (act7 u⁻¹ x) := by
      rw [act7_mul, LinearEquiv.mul_apply]
    rw [← h1, ← h2, fe3_uni_comm_xm_theta (inv_mem hu) a]
  have hinv : ∀ s : V K, act7 u⁻¹ (act7 u s) = s := by
    intro s
    have h1 : act7 (u⁻¹ * u) s = act7 u⁻¹ (act7 u s) := by
      rw [act7_mul, LinearEquiv.mul_apply]
    rw [← h1, inv_mul_cancel]
    simp [act7_one]
  have hkey : ∀ x : V K,
      act7 u⁻¹ (((act7 (e7Data_valid.xm K theta a) : V K →ₗ[K] V K) - 1) x) =
        ((act7 (e7Data_valid.xm K theta a) : V K →ₗ[K] V K) - 1) (act7 u⁻¹ x) := by
    intro x
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, map_sub, hcomm]
  have hμ : pr μ theta = 1 := by
    refine e7_single_mem_range_theta (a := a) ?_
    rw [hline, LinearMap.mem_range] at hqr
    obtain ⟨w, hw⟩ := hqr
    rw [LinearMap.mem_range]
    refine ⟨c₀⁻¹ • act7 u⁻¹ w, ?_⟩
    rw [map_smul, ← hkey, hw, map_smul, hinv, smul_smul, inv_mul_cancel₀ hc₀, one_smul]
  obtain ⟨γ, hγθ, hγδ⟩ := exists_pr_ne hδ hδne
  obtain ⟨n, hncomm, hnμγ⟩ := exists_levi_move (K := K) hμ hγθ
  have hN : ∀ s : V K, act7 (n * u⁻¹) (act7 u s) = act7 n s := by
    intro s
    have h1 : act7 (n * u⁻¹) (act7 u s) = act7 n (act7 u⁻¹ (act7 u s)) := by
      rw [act7_mul, LinearEquiv.mul_apply]
    rw [h1, hinv]
  have hval : act7 (n * u⁻¹) (c • act7 g (w0 : V K)) = c₀ • (Finsupp.single γ 1 : V K) := by
    rw [hline, map_smul, hN, hnμγ]
  have hfix : act7 (e7Data_valid.xm K δ b) (Finsupp.single γ 1 : V K) = Finsupp.single γ 1 := by
    rw [act7_xm, rootOp_single (K := K) hδ γ, if_neg hγδ, smul_zero, add_zero]
  refine ⟨n * u⁻¹, ?_, ?_⟩
  · intro a'
    calc n * u⁻¹ * e7Data_valid.xm K theta a'
        = n * (u⁻¹ * e7Data_valid.xm K theta a') := mul_assoc _ _ _
      _ = n * (e7Data_valid.xm K theta a' * u⁻¹) := by
          rw [fe3_uni_comm_xm_theta (inv_mem hu) a']
      _ = (n * e7Data_valid.xm K theta a') * u⁻¹ := (mul_assoc _ _ _).symm
      _ = (e7Data_valid.xm K theta a' * n) * u⁻¹ := by rw [hncomm a']
      _ = e7Data_valid.xm K theta a' * (n * u⁻¹) := mul_assoc _ _ _
  · rw [hval, map_smul, hfix]

end CFSG.RankThree.GF2n.Smith81.RootGenE5

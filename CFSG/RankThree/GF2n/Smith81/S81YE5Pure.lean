module

public import CFSG.RankThree.GF2n.Smith81.S81YE5Pair
public import CFSG.RankThree.GF2n.Smith81.S81E7Fe7

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE5

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.RootGen

variable
  {K : Type} [Field K]


theorem e7_pure_sub [CharP K 2] {r : V K ≃ₗ[K] V K} (hr : IsRt5 r) {p : V K}
    (hp : IsPurePt (EAut K) (w0 : V K) p) :
    r p - p = 0 ∨ IsPurePt (EAut K) (w0 : V K) (r p - p) := by
  obtain ⟨g, hgroot, rfl⟩ := isRt5_iff.mp hr
  obtain ⟨p₁, a, ha, hg⟩ := fe3_isRootEltG_conj_theta hgroot
  obtain ⟨g', hg'EAut, c, hc, rfl⟩ := hp
  obtain ⟨h, rfl⟩ := mem_EAut_iff_act7.mp hg'EAut
  obtain ⟨u, μ, c₀, hu, hc₀, hline⟩ := e7_lineNF (g := p₁⁻¹ * h) hc
  have hv : act7 p₁⁻¹ (c • act7 h (w0 : V K)) = c₀ • act7 u (Finsupp.single μ 1) := by
    rw [← hline, map_smul, act7_mul, LinearEquiv.mul_apply]
  have hgact : ∀ z : V K, act7 g z = act7 p₁ (act7 (e7Data_valid.xm K theta a) (act7 p₁⁻¹ z)) := by
    intro z
    rw [hg, act7_mul, act7_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have hinv : ∀ z : V K, act7 p₁ (act7 p₁⁻¹ z) = z := by
    intro z
    have h1 : act7 (p₁ * p₁⁻¹) z = z := by
      rw [mul_inv_cancel, act7_one] <;> rfl
    rw [act7_mul, LinearEquiv.mul_apply] at h1
    exact h1
  have key : ∀ z : V K, act7 g z - z =
      act7 p₁ (act7 (e7Data_valid.xm K theta a) (act7 p₁⁻¹ z) - act7 p₁⁻¹ z) := by
    intro z
    rw [map_sub (act7 p₁), hgact z, hinv z]
  have hact_comm : ∀ w : V K, act7 (e7Data_valid.xm K theta a) (act7 u w) =
      act7 u (act7 (e7Data_valid.xm K theta a) w) := by
    intro w
    have h2 : act7 (e7Data_valid.xm K theta a * u) w = act7 (u * e7Data_valid.xm K theta a) w := by
      rw [fe3_uni_comm_xm_theta hu a]
    rw [act7_mul, LinearEquiv.mul_apply, act7_mul, LinearEquiv.mul_apply] at h2
    rw [h2]
  have hxv : ∀ s : V K, act7 (e7Data_valid.xm K theta a) (c₀ • act7 u s) - c₀ • act7 u s =
      c₀ • act7 u (act7 (e7Data_valid.xm K theta a) s - s) := by
    intro s
    rw [map_smul, hact_comm, map_sub, smul_sub]
  have hx2 : act7 (e7Data_valid.xm K theta a) (Finsupp.single μ 1) - Finsupp.single μ 1 =
      a • (if pr μ theta = -1 then Finsupp.single (shift theta μ) 1 else 0) := by
    rw [act7_xm, add_sub_cancel_left, E7Model.rootOp_single (K := K) isRoot_theta μ]
  rw [key, hv, hxv]
  by_cases hμ : pr μ theta = -1
  · right
    rw [if_pos hμ] at hx2
    obtain ⟨g'', hg''mem, hg''w⟩ := weight_vec_mem_orbit (K := K) (shift theta μ)
    have hY : act7 p₁ (act7 u (Finsupp.single (shift theta μ) 1)) =
        vAut K (((p₁ * u : G7 K) : (Module.End K (V K))ˣ) * g'') (w0 : V K) := by
      rw [← hg''w]
      simp only [act7, vAut_apply, Units.val_mul, Module.End.mul_apply, Subgroup.coe_mul]
    have hmem : vAut K (((p₁ * u : G7 K) : (Module.End K (V K))ˣ) * g'') ∈ EAut K :=
      Subgroup.mem_map.mpr ⟨((p₁ * u : G7 K) : (Module.End K (V K))ˣ) * g'',
        mul_mem (p₁ * u : G7 K).2 hg''mem, rfl⟩
    refine ⟨vAut K (((p₁ * u : G7 K) : (Module.End K (V K))ˣ) * g''), hmem, c₀ * a,
      mul_ne_zero hc₀ ha, ?_⟩
    rw [hx2]
    simp only [map_smul, smul_smul]
    rw [hY]
  · left
    rw [if_neg hμ, smul_zero] at hx2
    rw [hx2, map_zero, smul_zero, map_zero]

end CFSG.RankThree.GF2n.Smith81.RootGenE5

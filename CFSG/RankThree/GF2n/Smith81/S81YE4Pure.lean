module

public import CFSG.RankThree.GF2n.Smith81.S81YE4Line

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE4

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.RankThree.GF2n.Smith81.RootGen CFSG.RankThree.GF2n.Smith81.RootGenE5

variable
  {K : Type} [Field K]

theorem e4V_pure_sub [CharP K 2] {x : G7 K} (hx : IsRootEltL K x) {q : V K} (hq : IsPureL q) :
    act7 x q - q = 0 ∨ IsPureL (act7 x q - q) := by
  obtain ⟨p, hpLam, c₁, hc₁, hxeq⟩ := hx.exists_conj_theta4
  have hpLG : p ∈ LG K := mem_LG.2 hpLam
  obtain ⟨g, hgLG, c, hc, hqeq⟩ := hq
  subst hqeq
  have hxact : ∀ z : V K, act7 x z = act7 p (act7 (e7Data_valid.xm K theta4 c₁) (act7 p⁻¹ z)) := by
    intro z
    rw [hxeq, act7_mul, act7_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have hinv : ∀ z : V K, act7 p (act7 p⁻¹ z) = z := by
    intro z
    have h1 : act7 (p * p⁻¹) z = z := by
      rw [mul_inv_cancel, act7_one] <;> rfl
    rw [act7_mul, LinearEquiv.mul_apply] at h1
    exact h1
  have key : ∀ z : V K, act7 x z - z =
      act7 p (act7 (e7Data_valid.xm K theta4 c₁) (act7 p⁻¹ z) - act7 p⁻¹ z) := by
    intro z
    rw [map_sub (act7 p), hxact z, hinv z]
  obtain ⟨u, μ, c₀, hu, hucomm, hμI, hc₀, hline⟩ :=
    e4V_lineNF (g := p⁻¹ * g) (mul_mem (inv_mem hpLG) hgLG) hc
  have hv : act7 p⁻¹ (c • act7 g (Finsupp.single (a0 : Fin e7Data.d) 1)) =
      c₀ • act7 u (Finsupp.single μ 1) := by
    rw [← hline, map_smul, act7_mul, LinearEquiv.mul_apply]
  have hact_comm : ∀ (a : K) (w : V K), act7 (e7Data_valid.xm K theta4 a) (act7 u w) =
      act7 u (act7 (e7Data_valid.xm K theta4 a) w) := by
    intro a w
    calc act7 (e7Data_valid.xm K theta4 a) (act7 u w)
        = act7 (e7Data_valid.xm K theta4 a * u) w := by
          rw [act7_mul, LinearEquiv.mul_apply]
      _ = act7 (u * e7Data_valid.xm K theta4 a) w := by
          rw [hucomm a]
      _ = act7 u (act7 (e7Data_valid.xm K theta4 a) w) := by
          rw [act7_mul, LinearEquiv.mul_apply]
  have hxv : ∀ s : V K, act7 (e7Data_valid.xm K theta4 c₁) (c₀ • act7 u s) - c₀ • act7 u s =
      c₀ • act7 u (act7 (e7Data_valid.xm K theta4 c₁) s - s) := by
    intro s
    rw [map_smul, hact_comm c₁ s, map_sub, smul_sub]
  have hx2 : act7 (e7Data_valid.xm K theta4 c₁) (Finsupp.single μ 1) - Finsupp.single μ 1 =
      c₁ • (if pr μ theta4 = -1 then Finsupp.single (shift theta4 μ) 1 else 0) := by
    rw [act7_xm, add_sub_cancel_left, E7Model.rootOp_single (K := K) isRoot_theta4 μ]
  rw [key, hv, hxv]
  by_cases hμ : pr μ theta4 = -1
  · right
    rw [if_pos hμ] at hx2
    have hν : shift theta4 μ ∈ idx0 := shift_mem_idx0 theta4_mem_Perp hμI hμ
    obtain ⟨l, hlLam, hl⟩ := Lam_transitive_wt (K := K) a0.2 hν
    have hlG : lamToG7 (⟨l, hlLam⟩ : ↥(Lam K)) ∈ LG K := lamToG7_mem _
    have hL : act7 (lamToG7 (⟨l, hlLam⟩ : ↥(Lam K))) (Finsupp.single (a0 : Fin e7Data.d) 1) =
        Finsupp.single (shift theta4 μ) 1 := hl
    have hY : act7 p (act7 u (Finsupp.single (shift theta4 μ) 1)) =
        act7 (p * u * lamToG7 (⟨l, hlLam⟩ : ↥(Lam K))) (Finsupp.single (a0 : Fin e7Data.d) 1) := by
      simp only [act7_mul, LinearEquiv.mul_apply, hL]
    refine ⟨p * u * lamToG7 (⟨l, hlLam⟩ : ↥(Lam K)), mul_mem (mul_mem hpLG hu) hlG,
      c₀ * c₁, mul_ne_zero hc₀ hc₁, ?_⟩
    rw [hx2]
    simp only [map_smul, smul_smul]
    rw [hY]
  · left
    rw [if_neg hμ, smul_zero] at hx2
    rw [hx2, map_zero, smul_zero, map_zero]

theorem e4_pure_sub [CharP K 2] {r : W K ≃ₗ[K] W K} (hr : IsRt4 r) {p : W K}
    (hp : IsPurePt (EAut0 K) (p0 K) p) :
    r p - p = 0 ∨ IsPurePt (EAut0 K) (p0 K) (r p - p) := by
  obtain ⟨l, hroot, rfl⟩ := isRt4_iff.1 hr
  rcases e4V_pure_sub hroot (isPureL_emb hp) with h0 | hP
  · left
    apply emb_injective
    rw [map_sub, emb_act4, map_zero]
    exact h0
  · right
    apply isPurePt_of_isPureL
    rw [map_sub, emb_act4]
    exact hP

end CFSG.RankThree.GF2n.Smith81.RootGenE4

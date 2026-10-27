module

public import CFSG.RankThree.GF2n.Smith81.S81YE4Mnf
public import CFSG.RankThree.GF2n.Smith81.S81YE4Odd

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE4

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.RankThree.GF2n.Smith81.RootGen CFSG.RankThree.GF2n.Smith81.RootGenE5

variable
  {K : Type} [Field K]

theorem move_conj {A r s c' : W K ≃ₗ[K] W K} {p : W K}
    (hcomm : c' * (A * r * A⁻¹) = (A * r * A⁻¹) * c')
    (hfix : (A * s * A⁻¹) (c' (A p)) = c' (A p)) :
    (A⁻¹ * c' * A) * r = r * (A⁻¹ * c' * A) ∧ s ((A⁻¹ * c' * A) p) = (A⁻¹ * c' * A) p := by
  refine ⟨?_, ?_⟩
  · calc A⁻¹ * c' * A * r
        = A⁻¹ * (c' * (A * r * A⁻¹)) * A := by group
      _ = A⁻¹ * ((A * r * A⁻¹) * c') * A := by rw [hcomm]
      _ = r * (A⁻¹ * c' * A) := by group
  · have hs' : ∀ x : W K, s (A⁻¹ x) = A⁻¹ ((A * s * A⁻¹) x) := by
      intro x
      simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    simp only [LinearEquiv.mul_apply]
    rw [hs', hfix]

theorem e4_move_nf [CharP K 2] {a : K} {δ : Fin (Tag.rank .E7) → ℤ} (hδ : δ ∈ Perp)
    (hδne : δ ≠ -theta4) (b : K) {q : W K} (hq : IsPurePt (EAut0 K) (p0 K) q)
    (hqr : q ∈ LinearMap.range
      ((vAut0 K (xuWUnit theta4_mem_Perp a) : W K →ₗ[K] W K) - 1)) :
    ∃ c ∈ EAut0 K, c * vAut0 K (xuWUnit theta4_mem_Perp a) =
        vAut0 K (xuWUnit theta4_mem_Perp a) * c ∧
      vAut0 K (xuWUnit hδ b) (c q) = c q := by
  have hqE : IsPureL (emb K q) := isPureL_emb hq
  have hqrE : emb K q ∈ LinearMap.range
      ((act7 (e7Data_valid.xm K theta4 a) : V K →ₗ[K] V K) - 1) := by
    obtain ⟨w, hw⟩ := hqr
    refine LinearMap.mem_range.2 ⟨emb K w, ?_⟩
    rw [← hw]
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, map_sub,
      emb_xuWUnit]
  obtain ⟨n, hnL, hncomm, hnfix⟩ := move_normal_form4 (a := a) hδ hδne b hqE hqrE
  obtain ⟨N, hN⟩ := exists_lam_of_mem_LG hnL
  refine ⟨act4 N, mem_EAut0_iff_act4.2 ⟨N, rfl⟩, ?_, ?_⟩
  · have hNc : N * xuLam theta4_mem_Perp a = xuLam theta4_mem_Perp a * N := by
      apply lamToG7_injective
      rw [lamToG7_mul, lamToG7_mul, lamToG7_xuLam, hN]
      exact hncomm a
    rw [← act4_xuLam theta4_mem_Perp a, ← act4_mul, ← act4_mul, hNc]
  · apply emb_injective
    rw [emb_xuWUnit, emb_act4, hN]
    exact hnfix

theorem e4_move [Finite K] [CharP K 2] {r s : W K ≃ₗ[K] W K} (hr : IsRt4 r) (hs : IsRt4 s)
    (hB : ¬ (Odd (orderOf (r * s)) ∧ r * s ≠ 1)) {p : W K}
    (hp : IsPurePt (EAut0 K) (p0 K) p)
    (hpr : p ∈ LinearMap.range ((r : W K →ₗ[K] W K) - 1)) :
    ∃ c ∈ EAut0 K, c * r = r * c ∧ s (c p) = c p := by
  obtain ⟨E, a, b, δ, hδ, ha, hb, hEr, hEs, -⟩ := e4_pairNF_W hr hs
  have hAconj : ∀ x : W K ≃ₗ[K] W K, orderOf (act4 E * x * (act4 E)⁻¹) = orderOf x := fun x =>
    orderOf_injective (MulAut.conj (act4 E)).toMonoidHom (MulAut.conj (act4 E)).injective x
  have hδne : δ ≠ -theta4 := by
    intro hδeq
    subst hδeq
    have hEs' : act4 E * s * (act4 E)⁻¹ =
        vAut0 K (xuWUnit (neg_mem_Perp theta4_mem_Perp) b) := hEs
    have hAA : act4 E * (r * s) * (act4 E)⁻¹ =
        vAut0 K (xuWUnit theta4_mem_Perp a * xuWUnit (neg_mem_Perp theta4_mem_Perp) b) := by
      calc act4 E * (r * s) * (act4 E)⁻¹
          = (act4 E * r * (act4 E)⁻¹) * (act4 E * s * (act4 E)⁻¹) := by group
        _ = vAut0 K (xuWUnit theta4_mem_Perp a) *
              vAut0 K (xuWUnit (neg_mem_Perp theta4_mem_Perp) b) := by
          rw [hEr, hEs']
        _ = vAut0 K (xuWUnit theta4_mem_Perp a * xuWUnit (neg_mem_Perp theta4_mem_Perp) b) :=
          (map_mul _ _ _).symm
    have hord : orderOf (r * s) =
        orderOf (xuWUnit theta4_mem_Perp a * xuWUnit (neg_mem_Perp theta4_mem_Perp) b) := by
      rw [← hAconj (r * s), hAA]
      exact orderOf_injective (vAut0 K).toMonoidHom (vAut0 K).injective _
    apply hB
    refine ⟨?_, ?_⟩
    · rw [hord]
      exact xuW_theta4_neg_odd ha hb
    · intro h1
      apply xuW_theta4_neg_ne_one ha hb
      apply (vAut0 K).injective
      rw [map_one, ← hAA, h1]
      simp
  have hA : act4 E ∈ EAut0 K := mem_EAut0_iff_act4.2 ⟨E, rfl⟩
  have hX : ∀ x : W K, vAut0 K (xuWUnit theta4_mem_Perp a) (act4 E x) = act4 E (r x) := by
    intro x
    rw [← hEr]
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  have hq : IsPurePt (EAut0 K) (p0 K) (act4 E p) := by
    obtain ⟨g, hgΓ, c, hc, hpc⟩ := hp
    obtain ⟨k, rfl⟩ := mem_EAut0_iff_act4.1 hgΓ
    refine ⟨act4 (E * k), mem_EAut0_iff_act4.2 ⟨E * k, rfl⟩, c, hc, ?_⟩
    rw [hpc, map_smul, act4_mul, LinearEquiv.mul_apply]
  have hqr : act4 E p ∈ LinearMap.range
      ((vAut0 K (xuWUnit theta4_mem_Perp a) : W K →ₗ[K] W K) - 1) := by
    obtain ⟨w, hw⟩ := hpr
    refine LinearMap.mem_range.2 ⟨act4 E w, ?_⟩
    rw [← hw]
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, map_sub, hX]
  obtain ⟨c', hc'Γ, hc'comm, hc'fix⟩ := e4_move_nf hδ hδne b hq hqr
  have hcomm : c' * (act4 E * r * (act4 E)⁻¹) = (act4 E * r * (act4 E)⁻¹) * c' := by
    rw [hEr]
    exact hc'comm
  have hfix : (act4 E * s * (act4 E)⁻¹) (c' (act4 E p)) = c' (act4 E p) := by
    rw [hEs]
    exact hc'fix
  exact ⟨(act4 E)⁻¹ * c' * act4 E, mul_mem (mul_mem (inv_mem hA) hc'Γ) hA,
    (move_conj hcomm hfix).1, (move_conj hcomm hfix).2⟩

end CFSG.RankThree.GF2n.Smith81.RootGenE4

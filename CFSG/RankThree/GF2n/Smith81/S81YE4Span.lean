module

public import CFSG.RankThree.GF2n.Smith81.S81YE4Push

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE4

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.RankThree.GF2n.Smith81.RootGen CFSG.RankThree.GF2n.Smith81.RootGenE5

variable
  {K : Type} [Field K]

theorem e4_fixed_coord_zero [CharP K 2] {a : K} (ha : a ≠ 0) {c' : W K}
    (hc : vAut0 K (xuWUnit theta4_mem_Perp a) c' = c') (μ : Idx0)
    (hμ : pr (μ : Fin e7Data.d) theta4 = -1) : c' μ = 0 := by
  have h1 : act7 (e7Data_valid.xm K theta4 a) (emb K c') = emb K c' := by
    rw [← emb_xuWUnit theta4_mem_Perp a c', hc]
  rw [act7_xm] at h1
  have h2 : a • e7Data.rootOp K theta4 (emb K c') = 0 := by
    simpa using h1
  have hr : e7Data.rootOp K theta4 (emb K c') = 0 :=
    (smul_eq_zero.mp h2).resolve_left ha
  have hb : pr (shift theta4 (μ : Fin e7Data.d)) theta4 = 1 :=
    pr_shift_self isRoot_theta4 hμ
  have hsh : shift (-theta4) (shift theta4 (μ : Fin e7Data.d)) = (μ : Fin e7Data.d) :=
    shift_neg_shift isRoot_theta4 hμ
  have h := rootOp_apply (K := K) isRoot_theta4 (emb K c') (shift theta4 (μ : Fin e7Data.d))
  rw [hr, if_pos hb, hsh] at h
  have h3 : emb K c' (μ : Fin e7Data.d) = 0 := by
    simpa using h.symm
  rw [← emb_apply_coe c' μ]
  exact h3

theorem e4_single_fixed [CharP K 2] (a : K) (μ : Idx0) (hμ : pr (μ : Fin e7Data.d) theta4 ≠ -1) :
    vAut0 K (xuWUnit theta4_mem_Perp a) (Finsupp.single μ 1) = Finsupp.single μ 1 := by
  apply emb_injective
  rw [emb_xuWUnit, emb_single, act7_xm, rootOp_single (K := K) isRoot_theta4, if_neg hμ,
    smul_zero, add_zero]

theorem e4_single_pure [CharP K 2] (P : ↥(Lam K)) (μ : Idx0) :
    IsPurePt (EAut0 K) (p0 K) (act4 P (Finsupp.single μ 1)) := by
  obtain ⟨l, hl, hlμ⟩ := Lam_transitive_wt (K := K) a0.2 μ.2
  obtain ⟨L, hLμ⟩ : ∃ L : ↥(Lam K),
      ((L : (Module.End K (V K))ˣ) : Module.End K (V K)) (Finsupp.single (a0 : Fin e7Data.d) 1) =
        Finsupp.single (μ : Fin e7Data.d) 1 :=
    ⟨⟨l, hl⟩, hlμ⟩
  have hL : act4 L (p0 K) = Finsupp.single μ 1 := by
    apply emb_injective
    rw [emb_act4, emb_p0, emb_single, act7_apply]
    exact hLμ
  have hP : act4 P (Finsupp.single μ 1) = act4 (P * L) (p0 K) := by
    rw [act4_mul, LinearEquiv.mul_apply, hL]
  refine ⟨act4 (P * L), (mem_EAut0_iff_act4).2 ⟨P * L, rfl⟩, 1, one_ne_zero, ?_⟩
  rw [one_smul]
  exact hP

theorem e4_spanC [CharP K 2] {r : W K ≃ₗ[K] W K} (hr : IsRt4 r) :
    ∀ c : W K, r c = c →
      c ∈ Submodule.span K {v : W K | r v = v ∧ (v = 0 ∨ IsPurePt (EAut0 K) (p0 K) v)} := by
  obtain ⟨gr, hroot, rfl⟩ := isRt4_iff.1 hr
  intro c hc
  obtain ⟨p, hp, a, ha, hg⟩ := IsRootEltL.exists_conj_theta4 hroot
  obtain ⟨P, hPp⟩ : ∃ P : ↥(Lam K), lamToG7 P = p := ⟨⟨(p : (Module.End K (V K))ˣ), hp⟩, rfl⟩
  have hgr : gr = P * xuLam theta4_mem_Perp a * P⁻¹ := by
    apply lamToG7_injective
    rw [lamToG7_mul, lamToG7_mul, lamToG7_inv, lamToG7_xuLam, hPp, hg]
  have hact : act4 gr = act4 P * vAut0 K (xuWUnit theta4_mem_Perp a) * (act4 P)⁻¹ := by
    rw [hgr, act4_mul, act4_mul, act4_inv, act4_xuLam]
  have hfix : ∀ x : W K,
      act4 gr x = act4 P (vAut0 K (xuWUnit theta4_mem_Perp a) ((act4 P).symm x)) := by
    intro x
    rw [hact, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv]
  have hc' : vAut0 K (xuWUnit theta4_mem_Perp a) ((act4 P).symm c) = (act4 P).symm c := by
    have h1 := hfix c
    rw [hc] at h1
    have h2 : (act4 P).symm c =
        (act4 P).symm (act4 P (vAut0 K (xuWUnit theta4_mem_Perp a) ((act4 P).symm c))) := by
      rw [← h1]
    rw [LinearEquiv.symm_apply_apply] at h2
    exact h2.symm
  obtain ⟨c', hcc'⟩ : ∃ c' : W K, (act4 P).symm c = c' := ⟨_, rfl⟩
  rw [hcc'] at hc'
  have hcP : c = act4 P c' := by
    rw [← hcc', LinearEquiv.apply_symm_apply]
  have hsum : c' = ∑ μ ∈ c'.support, c' μ • (Finsupp.single μ 1 : W K) := by
    refine Eq.trans (Finsupp.sum_single c').symm ?_
    unfold Finsupp.sum
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finsupp.smul_single_one]
  have hzero : ∀ μ ∈ c'.support, pr (μ : Fin e7Data.d) theta4 ≠ -1 := by
    intro μ hμ hpr
    exact (Finsupp.mem_support_iff.mp hμ) (e4_fixed_coord_zero ha hc' μ hpr)
  have hT : ∀ μ : Idx0, pr (μ : Fin e7Data.d) theta4 ≠ -1 →
      act4 P (Finsupp.single μ 1) ∈
        {v : W K | act4 gr v = v ∧ (v = 0 ∨ IsPurePt (EAut0 K) (p0 K) v)} := by
    intro μ hμ
    refine ⟨?_, Or.inr (e4_single_pure P μ)⟩
    rw [hfix, LinearEquiv.symm_apply_apply, e4_single_fixed a μ hμ]
  have key : act4 P c' = ∑ μ ∈ c'.support, c' μ • act4 P (Finsupp.single μ 1) := by
    calc act4 P c' = act4 P (∑ μ ∈ c'.support, c' μ • (Finsupp.single μ 1 : W K)) := by
          rw [← hsum]
      _ = ∑ μ ∈ c'.support, c' μ • act4 P (Finsupp.single μ 1) := by
          rw [map_sum]
          simp only [map_smul]
  rw [hcP, key]
  exact Submodule.sum_mem _ fun μ hμ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (hT μ (hzero μ hμ)))

end CFSG.RankThree.GF2n.Smith81.RootGenE4

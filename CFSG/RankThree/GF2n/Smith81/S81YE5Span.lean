module

public import CFSG.RankThree.GF2n.Smith81.S81YE5Def
public import CFSG.RankThree.GF2n.Smith81.S81E7Fe7

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE5

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.RootGen

variable
  {K : Type} [Field K]

theorem e7_spanC [CharP K 2] {r : V K ≃ₗ[K] V K} (hr : IsRt5 r) :
    ∀ c : V K, r c = c →
      c ∈ Submodule.span K {v : V K | r v = v ∧ (v = 0 ∨ IsPurePt (EAut K) (w0 : V K) v)} := by
  obtain ⟨g, hgroot, rfl⟩ := isRt5_iff.mp hr
  obtain ⟨p, a, ha, hg⟩ := fe3_isRootEltG_conj_theta hgroot
  have hconj : ∀ v : V K, act7 g v = act7 p (act7 (e7Data_valid.xm K theta a) (act7 p⁻¹ v)) := by
    intro v
    rw [hg, act7_mul, act7_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have hL : ∀ v : V K, act7 p⁻¹ (act7 p v) = v := by
    intro v
    rw [act7_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  have hR : ∀ v : V K, act7 p (act7 p⁻¹ v) = v := by
    intro v
    rw [act7_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  intro c hc
  obtain ⟨q, hq⟩ : ∃ q : V K, act7 p⁻¹ c = q := ⟨_, rfl⟩
  have hX : act7 (e7Data_valid.xm K theta a) q = q := by
    have h1 : act7 p (act7 (e7Data_valid.xm K theta a) q) = c := by
      rw [← hq, ← hconj c, hc]
    calc act7 (e7Data_valid.xm K theta a) q
        = act7 p⁻¹ (act7 p (act7 (e7Data_valid.xm K theta a) q)) := (hL _).symm
      _ = q := by rw [h1, hq]
  have hrq : e7Data.rootOp K theta q = 0 := by
    rw [act7_xm] at hX
    have h2 : a • e7Data.rootOp K theta q = 0 := by
      simpa using hX
    exact (smul_eq_zero.mp h2).resolve_left ha
  have hq0 : ∀ μ : Fin e7Data.d, pr μ theta = -1 → q μ = 0 := by
    intro μ hμ
    have hb : pr (shift theta μ) theta = 1 := pr_shift_self isRoot_theta hμ
    have hsh : shift (-theta) (shift theta μ) = μ := shift_neg_shift isRoot_theta hμ
    have h := rootOp_apply (K := K) isRoot_theta q (shift theta μ)
    rw [hrq, if_pos hb, hsh] at h
    simpa using h.symm
  have hqsum : q = ∑ μ ∈ q.support, q μ • (Finsupp.single μ 1 : V K) := by
    refine Eq.trans (Finsupp.sum_single q).symm ?_
    unfold Finsupp.sum
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finsupp.smul_single_one]
  have hfix : ∀ μ : Fin e7Data.d, pr μ theta ≠ -1 →
      act7 (e7Data_valid.xm K theta a) (Finsupp.single μ 1) = Finsupp.single μ 1 := by
    intro μ hμ
    rw [act7_xm, rootOp_single (K := K) isRoot_theta μ, if_neg hμ, smul_zero, add_zero]
  have hfixA : ∀ μ : Fin e7Data.d, pr μ theta ≠ -1 →
      act7 g (act7 p (Finsupp.single μ 1)) = act7 p (Finsupp.single μ 1) := by
    intro μ hμ
    rw [hconj, hL, hfix μ hμ]
  have hpure : ∀ μ : Fin e7Data.d, IsPurePt (EAut K) (w0 : V K) (act7 p (Finsupp.single μ 1)) := by
    intro μ
    obtain ⟨g', hg', hg'w⟩ := weight_vec_mem_orbit (K := K) μ
    refine ⟨vAut K ((p : (Module.End K (V K))ˣ) * g'), ?_, 1, one_ne_zero, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨(p : (Module.End K (V K))ˣ) * g', mul_mem p.2 hg', rfl⟩
    · rw [one_smul, ← hg'w]
      simp only [act7, vAut_apply, Units.val_mul, Module.End.mul_apply]
  have hT : ∀ μ : Fin e7Data.d, pr μ theta ≠ -1 →
      act7 p (Finsupp.single μ 1) ∈
        {v : V K | act7 g v = v ∧ (v = 0 ∨ IsPurePt (EAut K) (w0 : V K) v)} :=
    fun μ hμ => ⟨hfixA μ hμ, Or.inr (hpure μ)⟩
  have hsupp : ∀ μ ∈ q.support, pr μ theta ≠ -1 :=
    fun μ hμ hpr => Finsupp.mem_support_iff.mp hμ (hq0 μ hpr)
  have hcq : c = act7 p q := by rw [← hq, hR c]
  have key : act7 p q = ∑ μ ∈ q.support, q μ • act7 p (Finsupp.single μ 1) := by
    calc act7 p q = act7 p (∑ μ ∈ q.support, q μ • (Finsupp.single μ 1 : V K)) := by
          rw [← hqsum]
      _ = ∑ μ ∈ q.support, q μ • act7 p (Finsupp.single μ 1) := by
          rw [map_sum]
          simp only [map_smul]
  rw [hcq, key]
  exact Submodule.sum_mem _ fun μ hμ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (hT μ (hsupp μ hμ)))

end CFSG.RankThree.GF2n.Smith81.RootGenE5

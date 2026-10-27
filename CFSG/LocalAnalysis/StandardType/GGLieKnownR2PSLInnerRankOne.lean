module

public import CFSG.LinearAlgebra.RootGroupSL.RankOneGraph
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LinearAlgebra.RootGroupSL.NoOuter
public import CFSG.LinearAlgebra.RootGroupSL.NormalizerX
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt

public section

namespace CFSG.StandardType.LieKnownR2.PSL

open CFSG.LinearAlgebra.RootGroupSL
open Matrix

private lemma lr2r1a_mulLeftEquiv_symm_apply {k : Type} [Field k] (u : kˣ) (x : k) :
    (mulLeftEquiv k u).symm x = (u : k)⁻¹ * x := by
  change LinearMap.mulLeft k ((u⁻¹ : kˣ) : k) x = (u : k)⁻¹ * x
  rw [LinearMap.mulLeft_apply, Units.val_inv_eq_inv_val]

private lemma lr2r1a_det_mulLeftEquiv_self {k : Type} [Field k] (u : kˣ) :
    LinearEquiv.det (mulLeftEquiv k u) = u := by
  have he : ((mulLeftEquiv k u) : k →ₗ[k] k) = LinearMap.mulLeft k (u : k) := rfl
  have h := det_mulLeft_eq_norm (k := k) (E := k) (mulLeftEquiv k u) (u : k) he
  have hnorm : Algebra.norm k (u : k) = (u : k) := by simp [Algebra.norm_self]
  apply Units.ext
  rw [h, hnorm]

theorem rankOne_graph_form_inv_sq {k : Type} [Field k] [Finite k] [CharP k 2]
    (α : MulAut (SpecialLinearGroup k (DSpace k k)))
    (hR : (rootSL k k k).map α.toMonoidHom = rootSL k k k)
    (hC : ∀ h ∈ Subgroup.normalizer (rootSL k k k : Set (SpecialLinearGroup k (DSpace k k))),
      α h * h⁻¹ ∈ QK k k k ⊔ Subgroup.center (SpecialLinearGroup k (DSpace k k)))
    (σ : k ≃+* k) (T : Module.Dual k (DSpace k k) ≃+ DSpace k k)
    (hT : ∀ (c : k) (f : Module.Dual k (DSpace k k)), T (c • f) = σ c • T f)
    (hα : ∀ (g : SpecialLinearGroup k (DSpace k k)) (f : Module.Dual k (DSpace k k)),
      α g (T f) = T (f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap)) :
    ∀ s : k, s ≠ 0 → σ s = (s ^ 2)⁻¹ := by
  classical
  intro s hs
  let s' : kˣ := Units.mk0 s hs
  let a : k ≃ₗ[k] k := mulLeftEquiv k s'
  let g : k ≃ₗ[k] k := mulLeftEquiv k s'⁻¹
  have hs'val : (s' : k) = s := rfl
  have ha : LinearEquiv.det a = s' := lr2r1a_det_mulLeftEquiv_self s'
  have hg : LinearEquiv.det g = s'⁻¹ := lr2r1a_det_mulLeftEquiv_self s'⁻¹
  have hdet : LinearEquiv.det a * LinearEquiv.det g * LinearEquiv.det (1 : k ≃ₗ[k] k) = 1 := by
    rw [ha, hg, map_one, mul_one, mul_inv_cancel]
  let t : SpecialLinearGroup k (DSpace k k) := blockSL a g 1 hdet
  have htN : t ∈
      Subgroup.normalizer (rootSL k k k : Set (SpecialLinearGroup k (DSpace k k))) := by
    rw [blockSL_mem_normalizer_iff]
    intro u
    refine ⟨(s' : k) * u, ?_⟩
    apply LinearMap.ext
    intro x
    change (mulLeftEquiv k s') ((LinearMap.mulLeft k u) ((1 : k ≃ₗ[k] k).symm x)) =
      (LinearMap.mulLeft k ((s' : k) * u)) x
    rw [mulLeftEquiv_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply]
    rw [show (LinearEquiv.symm (1 : k ≃ₗ[k] k)) x = x from rfl]
    rw [mul_assoc]
  have htriv : ∀ v : DSpace k k,
      (SpecialLinearGroup.toLinearEquiv t) v - v ∈ flagK k k k := by
    intro v
    rw [NoOuterGraph.mem_flagK_iff]
    simp [t, NoOuterGraph.blockSL_apply]
  obtain ⟨c, hcW, hcK⟩ := NoOuterGraph.action_flagW_and_second α hC htN
  have hw0 : ((1 : k), (0 : k), (0 : k)) ∈ flagW k k k := by
    rw [NoOuterGraph.mem_flagW_iff]; simp
  have hw0t : t ((1 : k), (0 : k), (0 : k)) = (s, 0, 0) := by
    simp [t, a, NoOuterGraph.blockSL_apply, mulLeftEquiv_apply, hs'val]
  have hfixw : α t ((1 : k), (0 : k), (0 : k)) = ((1 : k), (0 : k), (0 : k)) :=
    NoOuterGraph.action_fixes_flagW_of_trivial_quotient α hR T hα htriv hw0
  have hfirst : (c : k) * s = 1 := by
    have hcw' : (c : k) • t ((1 : k), (0 : k), (0 : k)) =
        ((1 : k), (0 : k), (0 : k)) := by
      rw [← hcW _ hw0, hfixw]
    have hfst := congrArg Prod.fst hcw'
    rw [hw0t] at hfst
    simpa using hfst
  have hceq : (c : k) = s⁻¹ := eq_inv_of_mul_eq_one_left hfirst
  let f : Module.Dual k (DSpace k k) :=
    (LinearMap.fst k k k).comp (LinearMap.snd k k (k × k))
  have hfW : f ∈ NoOuterGraph.AnnW k k k := by
    rw [Submodule.mem_dualAnnihilator]
    intro v hv
    simp [f, (NoOuterGraph.mem_flagW_iff v).mp hv |>.1]
  have hfK : f ∉ NoOuterGraph.AnnK k k k := by
    intro hf
    have hzero := ((Submodule.mem_dualAnnihilator f).mp hf) ((0 : k), (1 : k), (0 : k))
      (by rw [NoOuterGraph.mem_flagK_iff])
    simpa [f] using hzero
  have hvK : T f ∈ flagK k k k := NoOuterGraph.T_mem_flagK_of_mem_dualAnnW α hR T hα hfW
  have hvW : T f ∉ flagW k k k := by
    intro hw
    exact hfK (NoOuterGraph.mem_dualAnnK_of_T_mem_flagW α hR T hα hw)
  have hvKb : (T f).2.2 = 0 := (NoOuterGraph.mem_flagK_iff _).mp hvK
  have hxne : (T f).2.1 ≠ 0 := by
    intro hx
    exact hvW ((NoOuterGraph.mem_flagW_iff _).mpr ⟨hx, hvKb⟩)
  have htinv : (SpecialLinearGroup.toLinearEquiv t⁻¹) =
      blockDiag a⁻¹ g.symm (1 : k ≃ₗ[k] k) := by
    rw [SpecialLinearGroup.toLinearEquiv_eq_coe, SpecialLinearGroup.coe_inv]
    change (blockDiag a g (1 : k ≃ₗ[k] k))⁻¹ =
      blockDiag a⁻¹ g.symm (1 : k ≃ₗ[k] k)
    rw [blockDiag_inv]
    rfl
  have hfinv : f ∘ₗ (SpecialLinearGroup.toLinearEquiv t⁻¹).toLinearMap = s • f := by
    apply LinearMap.ext
    intro v
    change ((SpecialLinearGroup.toLinearEquiv t⁻¹) v).2.1 = s * v.2.1
    rw [htinv]
    simp only [NoOuterGraph.blockDiag_apply]
    rw [lr2r1a_mulLeftEquiv_symm_apply, Units.val_inv_eq_inv_val, inv_inv, hs'val]
  have hαTf : α t (T f) = σ s • T f := by
    rw [hα t f, hfinv, hT s f]
  have htTf : (t (T f)).2.1 = (s'⁻¹ : k) * (T f).2.1 := by
    simp [t, g, NoOuterGraph.blockSL_apply, mulLeftEquiv_apply]
  have hs'inv : (s'⁻¹ : k) = s⁻¹ := by
    rw [hs'val]
  have hsec := hcK (T f) hvK
  rw [hαTf] at hsec
  have hsec' : σ s * (T f).2.1 = (c : k) * ((s'⁻¹ : k) * (T f).2.1) := by
    simpa [htTf, smul_eq_mul] using hsec
  have heq : σ s * (T f).2.1 = (s⁻¹ * s⁻¹) * (T f).2.1 := by
    calc σ s * (T f).2.1 = (c : k) * ((s'⁻¹ : k) * (T f).2.1) := hsec'
      _ = (s⁻¹ * s⁻¹) * (T f).2.1 := by rw [hceq, hs'inv, mul_assoc]
  have hσ : σ s = s⁻¹ * s⁻¹ := mul_right_cancel₀ hxne heq
  calc σ s = s⁻¹ * s⁻¹ := hσ
    _ = (s ^ 2)⁻¹ := by rw [pow_two, _root_.mul_inv_rev]

theorem no_ringEquiv_inv_sq {k : Type} [Field k] [Finite k] [CharP k 2] (hk : 8 ≤ Nat.card k)
    (σ : k ≃+* k) (h : ∀ s : k, s ≠ 0 → σ s = (s ^ 2)⁻¹) : False := by
  classical
  haveI : Fintype k := Fintype.ofFinite k
  have hk' : 8 ≤ Fintype.card k := by
    rw [← Nat.card_eq_fintype_card]
    exact hk
  have hroot : ∀ w : k, w ≠ 0 → w ≠ 1 → w ^ 2 + w + 1 = 0 := by
    intro w hw0 hw1
    have hw1' : w + 1 ≠ 0 := fun hzero => hw1 (CharTwo.add_eq_zero.mp hzero)
    have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw0
    have hw12 : (w + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hw1'
    have hw1eq : w + (w + 1) = 1 := by
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    have hsum : σ w + σ (w + 1) = 1 := by
      rw [← map_add, hw1eq, map_one]
    have hrel : (w ^ 2)⁻¹ + ((w + 1) ^ 2)⁻¹ = 1 := by
      rw [← h w hw0, ← h (w + 1) hw1']
      exact hsum
    have key : (w + 1) ^ 2 + w ^ 2 = w ^ 2 * (w + 1) ^ 2 := by
      have hh := congrArg (fun x : k => x * (w ^ 2 * (w + 1) ^ 2)) hrel
      rw [add_mul, one_mul] at hh
      have h1 : (w ^ 2)⁻¹ * (w ^ 2 * (w + 1) ^ 2) = (w + 1) ^ 2 := by
        rw [← mul_assoc, inv_mul_cancel₀ hw2, one_mul]
      have h2 : ((w + 1) ^ 2)⁻¹ * (w ^ 2 * (w + 1) ^ 2) = w ^ 2 := by
        rw [mul_comm (w ^ 2) ((w + 1) ^ 2), ← mul_assoc, inv_mul_cancel₀ hw12, one_mul]
      rw [h1, h2] at hh
      exact hh
    have hw1sq : (w + 1) ^ 2 = w ^ 2 + 1 := by
      rw [CharTwo.add_sq, one_pow]
    have hl : (w ^ 2 + 1) + w ^ 2 = 1 := by
      rw [add_assoc, add_comm (1 : k) (w ^ 2)]
      exact CharTwo.add_cancel_left (w ^ 2) 1
    have hr : w ^ 2 * (w ^ 2 + 1) = w ^ 4 + w ^ 2 := by ring
    have hw4 : w ^ 4 + w ^ 2 + 1 = 0 := by
      have hh := key
      rw [hw1sq] at hh
      rw [hl, hr] at hh
      exact CharTwo.add_eq_zero.mpr hh.symm
    have hsq : (w ^ 2 + w + 1) ^ 2 = 0 := by
      rw [show w ^ 2 + w + 1 = w ^ 2 + (w + 1) by ring]
      rw [CharTwo.add_sq, CharTwo.add_sq, one_pow]
      rw [show (w ^ 2) ^ 2 = w ^ 4 by ring]
      rw [← add_assoc]
      exact hw4
    exact CharTwo.sq_inj.mp (hsq.trans (zero_pow (by norm_num : (2 : ℕ) ≠ 0)).symm)
  have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial k).natDegree = 2 := by
    rw [show (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial k) =
        Polynomial.C (1 : k) * Polynomial.X ^ 2 + Polynomial.C (1 : k) * Polynomial.X +
          Polynomial.C (1 : k) by
      simp only [Polynomial.C_1, one_mul]]
    exact Polynomial.natDegree_quadratic one_ne_zero
  have hs_card : 2 < (({0, 1} : Finset k)ᶜ).card := by
    rw [Finset.card_compl, Finset.card_pair (show (0 : k) ≠ 1 by norm_num)]
    omega
  have hs_eval : ∀ i ∈ ({0, 1} : Finset k)ᶜ,
      (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial k).eval i = 0 := by
    intro i hi
    rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    have hev : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial k).eval i = i ^ 2 + i + 1 := by
      simp
    rw [hev]
    exact hroot i hi.1 hi.2
  have hp0 : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial k) = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ _ hs_eval
      (by rw [hdeg]; exact hs_card)
  have hcoeff : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial k).coeff 2 = (1 : k) := by
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one]
  have h10 : (1 : k) = 0 := by
    rw [← hcoeff]
    exact congrArg (fun p : Polynomial k => p.coeff 2) hp0
  exact one_ne_zero h10

theorem false_of_graph_form_rankOne_Z {k : Type} [Field k] [Finite k] [CharP k 2]
    (hk : 8 ≤ Nat.card k) (α : MulAut (SpecialLinearGroup k (DSpace k k)))
    (hR : (rootSL k k k).map α.toMonoidHom = rootSL k k k)
    (hC : ∀ h ∈ Subgroup.normalizer (rootSL k k k : Set (SpecialLinearGroup k (DSpace k k))),
      α h * h⁻¹ ∈ QK k k k ⊔ Subgroup.center (SpecialLinearGroup k (DSpace k k)))
    (σ : k ≃+* k) (T : Module.Dual k (DSpace k k) ≃+ DSpace k k)
    (hT : ∀ (c : k) (f : Module.Dual k (DSpace k k)), T (c • f) = σ c • T f)
    (hα : ∀ (g : SpecialLinearGroup k (DSpace k k)) (f : Module.Dual k (DSpace k k)),
      α g (T f) = T (f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap)) : False :=
  no_ringEquiv_inv_sq hk σ (rankOne_graph_form_inv_sq α hR hC σ T hT hα)

theorem exists_conj_of_two_element_mem_Y_rankOne_Z {k : Type} [Field k] [Finite k] [CharP k 2]
    (hk : 8 ≤ Nat.card k) (α : MulAut (SpecialLinearGroup k (DSpace k k)))
    (hR : (rootSL k k k).map α.toMonoidHom = rootSL k k k)
    (hC : ∀ h ∈ Subgroup.normalizer (rootSL k k k : Set (SpecialLinearGroup k (DSpace k k))),
      α h * h⁻¹ ∈ QK k k k ⊔ Subgroup.center (SpecialLinearGroup k (DSpace k k)))
    (h2 : ∃ m : ℕ, α ^ (2 ^ m) = 1) :
    ∃ g : SpecialLinearGroup k (DSpace k k), α = MulAut.conj g := by
  classical
  have hX : 0 < Module.finrank k k := by
    rw [Module.finrank_self]
    exact Nat.zero_lt_one
  have hV : 3 ≤ Module.finrank k (DSpace k k) := by
    have h : Module.finrank k (DSpace k k) = 3 := by
      simp [DSpace, Module.finrank_prod, Module.finrank_self]
    omega
  obtain ⟨σ, hform⟩ :=
    exists_semilinear_form_of_mulAut_sl (F := k) (V := DSpace k k) hV α
  rcases hform with ⟨T, hT, hα⟩ | ⟨T, hT, hα⟩
  ·
    have hσ : σ = RingEquiv.refl k :=
      field_form_eq_refl (k := k) (E := k) (X := k) hX α hR hC σ T hT hα
    have hTlin : ∀ (c : k) (v : DSpace k k), T (c • v) = c • T v := by
      intro c v
      rw [hT c v, hσ]
      rfl
    exact exists_conj_of_linear_form (k := k) (V := DSpace k k) α T hTlin hα h2
  ·
    exact False.elim (false_of_graph_form_rankOne_Z (k := k) hk α hR hC σ T hT hα)

end CFSG.StandardType.LieKnownR2.PSL

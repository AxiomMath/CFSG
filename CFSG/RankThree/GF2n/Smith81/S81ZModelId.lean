module

public import CFSG.RankThree.GF2n.Smith81.S81ZRD
public import CFSG.RankThree.GF2n.Smith81.S81Gen76E7

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.Gen76


@[expose] def sw0 (K : Type) [Field K] : V K := endoE (sN K) (w0 : V K)

variable {K : Type} [Field K] [CharP K 2]

set_option maxRecDepth 20000 in
theorem sw0_eq : sw0 K = Finsupp.single (e7Data_valid.sRefl nodeA topIdx) 1 :=
  moves_nm (K := K) nodeA topIdx

theorem pr_sRefl_top : pr (e7Data_valid.sRefl nodeA topIdx) alpha7 = -1 := by
  unfold pr
  rw [e7Data_valid.sRefl_val]
  have : e7Data.wt (e7Data.weyl ((topIdx : Fin e7Data.d) : ℕ) nodeA) ⬝ᵥ alpha7 = -1 := by
    decide +kernel
  exact this

theorem shift_sRefl_top : shift alpha7 (e7Data_valid.sRefl nodeA topIdx) = topIdx := by
  apply shift_eq
  rw [e7Data_valid.sRefl_val]
  have : e7Data.wt ((topIdx : Fin e7Data.d) : ℕ) =
      e7Data.wt (e7Data.weyl ((topIdx : Fin e7Data.d) : ℕ) nodeA) + MinData.toWeight alpha7 := by
    decide +kernel
  exact this

theorem endoE_xE_alpha7_w0 (t : K) : endoE (xE alpha7 t) (w0 : V K) = (w0 : V K) := by
  have h : e7Data.rootOp K alpha7 (w0 : V K) = 0 :=
    rootOp_w0_eq_zero_of_pos isRoot_alpha7 (by rw [ht_single_one]; exact one_pos)
  rw [endoE_xE]
  show ((1 : Module.End K (V K)) + t • e7Data.rootOp K alpha7) (w0 : V K) = _
  rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, h, smul_zero, add_zero]

theorem endoE_xE_alpha7_sw0 (t : K) : endoE (xE alpha7 t) (sw0 K) = sw0 K + t • (w0 : V K) := by
  have h : e7Data.rootOp K alpha7 (sw0 K) = (w0 : V K) := by
    rw [sw0_eq, rootOp_single isRoot_alpha7, if_pos pr_sRefl_top, shift_sRefl_top]
  rw [endoE_xE]
  show ((1 : Module.End K (V K)) + t • e7Data.rootOp K alpha7) (sw0 K) = _
  rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, h]

theorem endoE_sN_sw0 : endoE (sN K) (sw0 K) = (w0 : V K) := by
  have hs : endoE (sN K * sN K) (w0 : V K) = (w0 : V K) := by
    rw [sN_sq, endoE_one, Module.End.one_apply]
  rw [endoE_mul, Module.End.mul_apply] at hs
  unfold sw0
  exact hs

theorem endoE_inv_xE (t : K) (v : V K) : endoE (xE alpha7 t)⁻¹ v = endoE (xE alpha7 t) v := by
  rw [xE_inv, CharTwo.neg_eq]

theorem sw0_notin_span : sw0 K ∉ Submodule.span K {(w0 : V K)} := by
  intro h
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 h
  have hne : e7Data_valid.sRefl nodeA topIdx ≠ topIdx := by
    intro heq
    have h1 : pr (e7Data_valid.sRefl nodeA topIdx) alpha7 = -1 := pr_sRefl_top
    rw [heq] at h1
    have h2 : pr topIdx alpha7 = 1 := pr_alpha7
    rw [h2] at h1
    omega
  have := congrArg (fun v : V K => v (e7Data_valid.sRefl nodeA topIdx)) hr
  rw [sw0_eq] at this
  simp [Finsupp.single_apply, hne.symm] at this

end CFSG.RankThree.GF2n.Smith81.S81Z

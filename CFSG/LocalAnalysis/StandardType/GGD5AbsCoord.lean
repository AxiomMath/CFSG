module

public import CFSG.LocalAnalysis.StandardType.GGD5Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

private def lup10ab_tauPerm : Equiv.Perm (Fin 5) where
  toFun := lup10ab_tau
  invFun := ![4, 3, 1, 0, 2]
  left_inv := by decide
  right_inv := by decide

private theorem lup10fa_cartan_eq (i j : Fin 5) :
    ((CartanMatrix.D 5 (lup10ab_tau i) (lup10ab_tau j) : ℤ) : ZMod 3) = lup10fa_C i j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem lup10ab_tau_ne_zero : ∀ i : Fin 5, i ≠ 4 → lup10ab_tau i ≠ 0 := by
  decide

private theorem lup10fa_fixed_vec :
    ∀ v : Fin 5 → ZMod 3, (∀ i : Fin 5, i ≠ 4 → (lup10fa_s i).mulVec v = v) →
      ∃ ν : ZMod 3, v = ν • lup10fa_x := by
  decide +kernel

private theorem lup10fa_s_mulVec (i : Fin 5) (w : Fin 5 → ZMod 3) :
    (lup10fa_s i).mulVec w
      = w - (∑ q : Fin 5, lup10fa_C i q * w q) • Pi.single i (1 : ZMod 3) := by
  have hs : lup10fa_s i =
      1 - Matrix.of (fun p q : Fin 5 =>
        (Pi.single i (1 : ZMod 3) : Fin 5 → ZMod 3) p * lup10fa_C i q) := by
    ext p q
    simp only [lup10fa_s, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, Pi.single_apply]
    by_cases h : p = i <;> simp [h]
  have hN : (Matrix.of (fun p q : Fin 5 =>
        (Pi.single i (1 : ZMod 3) : Fin 5 → ZMod 3) p * lup10fa_C i q)).mulVec w
      = fun p => (Pi.single i (1 : ZMod 3) : Fin 5 → ZMod 3) p *
          (∑ q : Fin 5, lup10fa_C i q * w q) := by
    ext p
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum, mul_assoc]
  rw [hs, Matrix.sub_mulVec, Matrix.one_mulVec, hN]
  ext p
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem lup10ab_coord {G : Type} [Group G] {Bs : Subgroup G} {x y : G} {L H : Subgroup G}
    (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.a = e 0)
    (hbas : M.toLin.Basis) :
    ∃ κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3),
      (∀ i : Fin 5, κ (M.coroot (e (lup10ab_tau i))) = Pi.single i 1) ∧
      (∀ (i : Fin 5) (v : M.V), κ (ggLin (p := 3) M.model (M.simple (e (lup10ab_tau i))) v) =
        (lup10fa_s i).mulVec (κ v)) ∧
      (x ≠ 1 → ∃ ν : ZMod 3, ν ≠ 0 ∧ κ M.xV = ν • lup10fa_x) := by
  have hlin : LinearIndependent (ZMod 3) (M.coroot : M.ι → M.V) := hbas.1
  have hcard : Fintype.card M.ι = finrank (ZMod 3) M.V := hbas.2
  have hlin5 : LinearIndependent (ZMod 3) (fun i : Fin 5 => M.coroot (e (lup10ab_tau i))) :=
    hlin.comp (fun i : Fin 5 => e (lup10ab_tau i)) (lup10ab_tauPerm.trans e).injective
  have hcard5 : Fintype.card (Fin 5) = finrank (ZMod 3) M.V :=
    (Fintype.card_congr e).trans hcard
  let b : Basis (Fin 5) (ZMod 3) M.V := basisOfLinearIndependentOfCardEqFinrank hlin5 hcard5
  have hb : ∀ i : Fin 5, b i = M.coroot (e (lup10ab_tau i)) := fun i =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hlin5 hcard5) i
  let κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3) := b.equivFun
  have hκ : ∀ i : Fin 5, κ (M.coroot (e (lup10ab_tau i))) = Pi.single i 1 := by
    intro i
    rw [← hb i]
    show b.equivFun (b i) = Pi.single i 1
    funext j
    rw [Module.Basis.equivFun_self, Pi.single_apply]
    exact if_congr eq_comm rfl rfl
  have hpair : ∀ i j : Fin 5,
      M.root (e (lup10ab_tau i)) (M.coroot (e (lup10ab_tau j))) = lup10fa_C i j := by
    intro i j
    rw [M.pairing (e (lup10ab_tau i)) (e (lup10ab_tau j)),
      hecart (lup10ab_tau i) (lup10ab_tau j)]
    exact lup10fa_cartan_eq i j
  have hrootval : ∀ (i : Fin 5) (v : M.V),
      M.root (e (lup10ab_tau i)) v = ∑ j : Fin 5, lup10fa_C i j * κ v j := by
    intro i v
    conv_lhs => rw [← b.sum_equivFun v]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, hb j, hpair i j, smul_eq_mul, mul_comm]
  have hsimple : ∀ (i : Fin 5) (v : M.V),
      κ (ggLin (p := 3) M.model (M.simple (e (lup10ab_tau i))) v) =
        (lup10fa_s i).mulVec (κ v) := by
    intro i v
    rw [M.simple_apply (e (lup10ab_tau i)) v, map_sub, map_smul, hκ i, hrootval i v]
    exact (lup10fa_s_mulVec i (κ v)).symm
  have hxfix : M.xV ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
    rw [M.fixed_x]
    exact Submodule.mem_span_singleton_self M.xV
  have hxfixed : ∀ k : M.ι, k ≠ M.a →
      ggLin (p := 3) M.model (M.simple k) M.xV = M.xV := by
    intro k hk
    exact mem_ggFixedSubmodule_iff.mp hxfix (M.simple k) (by
      rw [M.automizer_L]
      exact Subgroup.subset_closure ⟨k, hk, rfl⟩)
  have hw : ∀ i : Fin 5, i ≠ 4 → (lup10fa_s i).mulVec (κ M.xV) = κ M.xV := by
    intro i hi
    have hk : e (lup10ab_tau i) ≠ M.a := by
      intro h
      rw [he0] at h
      exact lup10ab_tau_ne_zero i hi (e.injective h)
    rw [← hsimple i M.xV, hxfixed (e (lup10ab_tau i)) hk]
  obtain ⟨ν, hν⟩ := lup10fa_fixed_vec (κ M.xV) hw
  refine ⟨κ, hκ, hsimple, fun hx1 => ⟨ν, ?_, hν⟩⟩
  intro hν0
  have hxV0 : M.xV = 0 := κ.map_eq_zero_iff.mp (by rw [hν, hν0, zero_smul])
  have h1 : (⟨x, M.hx⟩ : Bs) = 1 := by
    refine Additive.ofMul.injective (M.model.injective ?_)
    show M.xV = M.model 0
    rw [hxV0, map_zero]
  exact hx1 (by simpa using congrArg Subtype.val h1)

end CFSG.StandardType

end

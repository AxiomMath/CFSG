module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGPDDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem pdc_mulVec_refl (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) (i : Fin 4)
    (c : Fin 4 → ZMod 3) :
    (ggPDRefl M i).mulVec c = c - (M.mulVec c) i • Pi.single i 1 := by
  rw [ggPDRefl, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hsingle : (Matrix.single i i (1 : ZMod 3) * M).mulVec c
      = (M.mulVec c) i • Pi.single i 1 := by
    rw [← Matrix.mulVec_mulVec, Matrix.single_mulVec]
    ext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [hk]
  rw [hsingle]

theorem ggPD_coords {Q : Type} [Group Q] {A : Subgroup Q} (hcard : Nat.card A = 3 ^ 4)
    [Fact (Nat.Prime 3)] {Γ : Type} [Fintype Γ] [DecidableEq Γ] {C : Matrix Γ Γ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Additive ↥A ≃+ V}
    {φ : Γ → MulAut ↥A} {h : Γ → V} {α : Γ → Module.Dual (ZMod 3) V}
    (hD : GGExtDatum ι C φ h α) (e : Fin 4 ≃ Γ) :
    ∃ κ : Additive ↥A ≃+ (Fin 4 → ZMod 3), ∀ (i : Fin 4) (a : ↥A),
      κ (Additive.ofMul (φ (e i) a)) =
        (ggPDRefl (Matrix.of fun j k => (C (e j) (e k) : ZMod 3)) i).mulVec
          (κ (Additive.ofMul a)) := by
  classical
  have hcardV : Nat.card V = 3 ^ 4 := by
    rw [← Nat.card_congr ι.toEquiv]
    exact hcard
  haveI hfinV : Finite V := Nat.finite_of_card_ne_zero (by rw [hcardV]; norm_num)
  have hrank : Module.finrank (ZMod 3) V = 4 := by
    have hnat := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [Nat.card_zmod, hcardV] at hnat
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hnat).symm
  have hli : LinearIndependent (ZMod 3) (h ∘ e) := hD.indep.comp e e.injective
  have hcardb : Fintype.card (Fin 4) = Module.finrank (ZMod 3) V := by
    rw [Fintype.card_fin, hrank]
  let b : Module.Basis (Fin 4) (ZMod 3) V :=
    basisOfLinearIndependentOfCardEqFinrank hli hcardb
  have hb : ⇑b = h ∘ e := coe_basisOfLinearIndependentOfCardEqFinrank hli hcardb
  have hbj : ∀ j : Fin 4, b j = h (e j) := fun j => by rw [hb]; rfl
  let κ : Additive ↥A ≃+ (Fin 4 → ZMod 3) := ι.trans b.equivFun.toAddEquiv
  have hκ : ∀ x : Additive ↥A, κ x = b.equivFun (ι x) := fun x => rfl
  refine ⟨κ, fun i a => ?_⟩
  have hsingle : b.equivFun (h (e i)) = Pi.single i (1 : ZMod 3) := by
    rw [← hbj i, Module.Basis.equivFun_apply, Module.Basis.repr_self,
      Finsupp.single_eq_pi_single]
  have halpha : α (e i) (ι (Additive.ofMul a))
      = ((Matrix.of fun j k => (C (e j) (e k) : ZMod 3)).mulVec
          (b.equivFun (ι (Additive.ofMul a)))) i := by
    conv_lhs => rw [← Module.Basis.sum_equivFun b (ι (Additive.ofMul a))]
    rw [map_sum, Matrix.mulVec_apply_eq_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, smul_eq_mul, hbj j, hD.pair (e i) (e j), Matrix.of_apply]
    ring
  have hlin : κ (Additive.ofMul (φ (e i) a))
      = b.equivFun (ι (Additive.ofMul a) -
          α (e i) (ι (Additive.ofMul a)) • h (e i)) := by
    rw [hκ, ← ggLin_apply_ofMul (p := 3) ι (φ (e i)) a,
      hD.lin (e i) (ι (Additive.ofMul a))]
  rw [hlin, map_sub, map_smul, hsingle, halpha, pdc_mulVec_refl, hκ]
  rfl

end CFSG.StandardType

end

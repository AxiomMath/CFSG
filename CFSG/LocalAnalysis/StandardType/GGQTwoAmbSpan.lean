module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAmbModelBridge
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphCommon

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

theorem GGQTwoAmbModel.span_insert_xV {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p = 3) {Bs : Subgroup G} {x y : G} {L H : Subgroup G} (M : GGQTwoAmbModel p Bs x y L H)
    (hbas : GGQTwoAmbBasis M)
    (hdet : ((M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
      (fun i : {k // k ≠ M.a} => (i : M.ι))).det : ZMod p) ≠ 0) (hx0 : M.xV ≠ 0) :
    Submodule.span (ZMod p)
      (insert M.xV (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) = ⊤ := by
  subst hp
  classical
  haveI : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  haveI : FiniteDimensional (ZMod 3) M.V := Module.Finite.of_finite
  have hfix1 : ∀ v, (∀ g ∈ M.toLin.parab {k | k ≠ M.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {M.xV} := M.fixed_lin
  have hxα : ∀ j : {k // k ≠ M.a}, M.root j M.xV = 0 :=
    ggQ2g_alpha_fixed rfl M.toLin M.a M.xV hfix1
  have hdet' : (Matrix.of fun i j : {k // k ≠ M.a} => (M.cartan i j : ZMod 3)).det ≠ 0 := by
    have hmap : (Matrix.of fun i j : {k // k ≠ M.a} => (M.cartan i j : ZMod 3)) =
        (Int.castRingHom (ZMod 3)).mapMatrix
          (M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
            (fun i : {k // k ≠ M.a} => (i : M.ι))) := rfl
    rw [hmap, ← RingHom.map_det]
    exact hdet
  have hker0 : ∀ κ : {k // k ≠ M.a} → ZMod 3,
      (∀ i : {k // k ≠ M.a}, ∑ j : {k // k ≠ M.a}, (M.cartan i j : ZMod 3) * κ j = 0) →
        κ = 0 := by
    intro κ hκ
    refine Matrix.eq_zero_of_mulVec_eq_zero hdet' (funext fun i => ?_)
    simpa [Matrix.mulVec, dotProduct] using hκ i
  have hxs : M.xV ∉
      Submodule.span (ZMod 3) (Set.range fun i : {k // k ≠ M.a} => M.coroot i) := by
    intro hmem
    obtain ⟨κ, hκ⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ZMod 3)).mp hmem
    have hκk : ∀ i : {k // k ≠ M.a},
        ∑ j : {k // k ≠ M.a}, (M.cartan i j : ZMod 3) * κ j = 0 := by
      intro i
      have h := hxα i
      rw [← hκ, map_sum] at h
      simpa only [map_smul, smul_eq_mul, M.pairing, mul_comm] using h
    apply hx0
    rw [← hκ, hker0 κ hκk]
    simp
  have hind : LinearIndependent (ZMod 3) (fun i : {k // k ≠ M.a} => M.coroot i) :=
    hbas.1.comp (fun i : {k // k ≠ M.a} => (i : M.ι)) Subtype.val_injective
  have hcardΛ : Fintype.card {k // k ≠ M.a} = Fintype.card M.ι - 1 := Set.card_ne_eq M.a
  have hcardι : 0 < Fintype.card M.ι := Fintype.card_pos_iff.mpr ⟨M.a⟩
  have hdimeq : Module.finrank (ZMod 3) M.V = Fintype.card {k // k ≠ M.a} + 1 := by
    rw [← hbas.2, hcardΛ]
    omega
  have hspan := (hind.option hxs).span_eq_top_of_card_eq_finrank'
    (by rw [Fintype.card_option, hdimeq])
  rw [Option.range_eq] at hspan
  exact hspan

end CFSG.StandardType

end

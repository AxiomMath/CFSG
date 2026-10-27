module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDepSurv
public import CFSG.LocalAnalysis.StandardType.GGQTwoDepSix
public import CFSG.LocalAnalysis.StandardType.GGQTwoDepFive

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2_e6_pm (hHeart : GGQ2HeartInput) (D : GGQ2Lin 3) [FiniteDimensional (ZMod 3) D.V]
    (e : Fin 6 ≃ D.ι) (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (ha : D.a = e 1) (x : D.V)
    (hx0 : x ≠ 0)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A) :
    ∀ a ∈ A, ∃ g ∈ D.weyl, (∀ v, a v = g v) ∨ (∀ v, a v = -(g v)) := by
  rcases ggQ2_e6_finrank D e hE ha x hx0 hx with h6 | h5
  · have hcart := ggQ2xQ_cartan_E6 D e hE
    have hsym : ∀ i j, D.cartan i j = D.cartan j i := by
      intro i j
      obtain ⟨p, rfl⟩ := e.surjective i
      obtain ⟨q, rfl⟩ := e.surjective j
      rw [hcart p q, hcart q p]
      exact congrFun (congrFun (CartanMatrix.E_transpose 6) q) p
    have hroots := ggQ2_dep_six_roots D e hE ha h6 x hx0 hx
    have hpm := ggQ2_dep_six_pm D hsym e hE h6 hroots A hW hTF
    intro a ha
    obtain ⟨g, hgW, hgcase⟩ := hpm (ggContra a) (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
    let g' : Dual (ZMod 3) D.V ≃ₗ[ZMod 3] Dual (ZMod 3) D.V := g
    have hgW' : g' ∈ (D.dual hsym).weyl := hgW
    have hgcase' : (∀ f : Dual (ZMod 3) D.V, ggContra a f = g' f) ∨
        (∀ f : Dual (ZMod 3) D.V, ggContra a f = -(g' f)) := hgcase
    have hgmap : g' ∈ D.weyl.map ggContra := by
      rw [ggContra_weyl D hsym]
      exact hgW'
    obtain ⟨w, hwW, hwg⟩ := Subgroup.mem_map.mp hgmap
    rcases hgcase' with h1 | h2
    · refine ⟨w, hwW, Or.inl ?_⟩
      have heq : ggContra a = ggContra w := by
        ext f x
        rw [h1 f]
        exact congrArg (fun θ : Dual (ZMod 3) D.V => θ x)
          (congrArg (fun e : Dual (ZMod 3) D.V ≃ₗ[ZMod 3] Dual (ZMod 3) D.V => e f) hwg).symm
      intro v
      exact congrArg (fun t : D.V ≃ₗ[ZMod 3] D.V => t v) (ggContra_injective heq)
    · refine ⟨w, hwW, Or.inr ?_⟩
      let hneg : D.V ≃ₗ[ZMod 3] D.V := w.trans (LinearEquiv.neg (ZMod 3))
      have hhn : ∀ v, hneg v = -(w v) := by
        intro v
        simp [hneg, LinearEquiv.trans_apply, LinearEquiv.neg_apply]
      have hnegc : ∀ f, ggContra hneg f = -(ggContra w f) := ggContra_neg w hneg hhn
      have heq : ggContra a = ggContra hneg := by
        ext f x
        rw [h2 f, hnegc f, LinearMap.neg_apply, LinearMap.neg_apply,
          congrArg (fun θ : Dual (ZMod 3) D.V => θ x)
            (congrArg (fun e : Dual (ZMod 3) D.V ≃ₗ[ZMod 3] Dual (ZMod 3) D.V => e f) hwg)]
      intro v
      rw [congrArg (fun t : D.V ≃ₗ[ZMod 3] D.V => t v) (ggContra_injective heq), hhn v]
  · exact hHeart D e hE h5 A hW hTF

end CFSG.StandardType

end

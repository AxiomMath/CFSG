module

public import CFSG.LocalAnalysis.StandardType.GGTBJSpParabolicAut

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedSp)

theorem ggCommonJSpSplit_signed {K : Type} [Field K] {p r : ℕ} (hp : p.Prime)
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) (g : StatedSp r K)
    (hg : ∀ s ∈ (TableBSymp.spTorusSp (m := r) hζ).range,
      g * s * g⁻¹ ∈ (TableBSymp.spTorusSp (m := r) hζ).range) :
    ∃ u : (Fin r → Multiplicative (ZMod p)) → (Fin r → Multiplicative (ZMod p)),
      SpCoord.IsSignedPerm u ∧
        ∀ f, g * TableBSymp.spTorusSp (m := r) hζ f * g⁻¹ =
          TableBSymp.spTorusSp (m := r) hζ (u f) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let τ := TableBSymp.spTorusSp (m := r) hζ
  have hτ : Function.Injective τ := TableBSymp.spTorusSp_injective hζ hζo
  haveI : Finite τ.range :=
    Finite.of_surjective τ.rangeRestrict τ.rangeRestrict_surjective
  have hmap_le : τ.range.map (MulAut.conj g).toMonoidHom ≤ τ.range := by
    rintro x ⟨y, hy, rfl⟩
    exact hg y hy
  have hcard : Nat.card (τ.range.map (MulAut.conj g).toMonoidHom) = Nat.card τ.range :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hmap_eq : τ.range.map (MulAut.conj g).toMonoidHom = τ.range :=
    Subgroup.eq_of_le_of_card_ge hmap_le (le_of_eq hcard.symm)
  have hgN : g ∈ Subgroup.normalizer (τ.range : Set (StatedSp r K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hg x
    · intro hx
      have hx' : g * x * g⁻¹ ∈ τ.range.map (MulAut.conj g).toMonoidHom := by
        rw [hmap_eq]
        exact hx
      obtain ⟨y, hy, hyx⟩ := hx'
      have hyx' : (MulAut.conj g) y = (MulAut.conj g) x := by
        rw [MulAut.conj_apply, MulAut.conj_apply]
        exact hyx
      rw [← (MulAut.conj g).injective hyx']
      exact hy
  let κ : (Fin r → Multiplicative (ZMod p)) ≃* τ.range := MonoidHom.ofInjective hτ
  let e : MulAut τ.range := Subgroup.normalizerMonoidHom τ.range ⟨g, hgN⟩
  let u : MulAut (Fin r → Multiplicative (ZMod p)) := MulAut.congr κ.symm e
  have hκ : ∀ f, (κ f : StatedSp r K) = τ f := by
    intro f
    rw [MonoidHom.ofInjective_apply]
  have hu : ∀ f, u f = κ.symm (e (κ f)) := by
    intro f
    rfl
  have hconj : ∀ f, g * τ f * g⁻¹ = τ (u f) := by
    intro f
    have h1 : (e (κ f) : StatedSp r K) = (κ (u f) : StatedSp r K) := by
      rw [hu f]
      exact congrArg (fun z : τ.range => (z : StatedSp r K))
        (κ.apply_symm_apply (e (κ f))).symm
    calc g * τ f * g⁻¹ = (e (κ f) : StatedSp r K) := by
          rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hκ f]
      _ = (κ (u f) : StatedSp r K) := h1
      _ = τ (u f) := hκ (u f)
  refine ⟨u, ggTBJ_sp_isSignedPerm_of_torus_conj hp hζo hζ
    (g : GL (Fin r ⊕ Fin r) K) u ?_, hconj⟩
  intro f
  have h := congrArg (fun x : StatedSp r K => (x : GL (Fin r ⊕ Fin r) K)) (hconj f)
  simpa only [τ, Subgroup.coe_mul, Subgroup.coe_inv, TableBSymp.spTorusSp_coe] using h
end CFSG.StandardType

end

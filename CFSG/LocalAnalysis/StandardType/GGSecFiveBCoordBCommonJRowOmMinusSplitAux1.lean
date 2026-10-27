module

public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenConj
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ} {b c : K} {ζ : Kˣ}

theorem ggCommonJOmMinusSplit_torus_injective (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) :
    Function.Injective
      (omMinusTorus (p := p) b c hζ :
        (Fin m → Multiplicative (ZMod p)) →* StatedOmega (StatedQuadMinus (m + 1) K b c)) := by
  haveI : NeZero p := ⟨by rw [← hζo]; exact (orderOf_pos ζ).ne'⟩
  intro f g hfg
  refine omMinusTorusGL_injective hζ hζo ?_
  simpa only [coe_omMinusTorus] using
    congrArg (fun x : StatedOmega (StatedQuadMinus (m + 1) K b c) =>
      (x : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)) hfg

theorem ggCommonJOmMinusSplit_signed (hp : p.Prime) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (g : StatedOmega (StatedQuadMinus (m + 1) K b c))
    (hg : ∀ s ∈ (omMinusTorus (p := p) b c hζ).range,
      g * s * g⁻¹ ∈ (omMinusTorus (p := p) b c hζ).range) :
    ∃ u : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p)),
      SpCoord.IsSignedPerm u ∧
        ∀ f, g * omMinusTorus (p := p) b c hζ f * g⁻¹ =
          omMinusTorus (p := p) b c hζ (u f) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let V := Fin m → Multiplicative (ZMod p)
  let H := StatedOmega (StatedQuadMinus (m + 1) K b c)
  let τ : V →* H := omMinusTorus (p := p) b c hζ
  have hτ : Function.Injective τ :=
    ggCommonJOmMinusSplit_torus_injective (p := p) (m := m) (b := b) (c := c) hζ hζo
  let eT : V ≃* τ.range := MonoidHom.ofInjective hτ
  have heT (u : V) : ((eT u : τ.range) : H) = τ u := MonoidHom.ofInjective_apply hτ
  let κ : V →* τ.range :=
    ((MulAut.conj g).toMonoidHom.comp τ).codRestrict τ.range fun u =>
      hg (τ u) (by exact ⟨u, rfl⟩)
  have hκ (u : V) : ((κ u : τ.range) : H) = g * τ u * g⁻¹ := rfl
  let φ : V →* V := eT.symm.toMonoidHom.comp κ
  have hφ (u : V) : ((eT (φ u) : τ.range) : H) = g * τ u * g⁻¹ := by
    rw [show eT (φ u) = κ u from eT.apply_symm_apply (κ u), hκ]
  have hφinj : Function.Injective φ := by
    intro u v huv
    have h : g * τ u * g⁻¹ = g * τ v * g⁻¹ := by
      rw [← hφ u, ← hφ v]
      exact congrArg (fun w : V => ((eT w : τ.range) : H)) huv
    exact hτ (mul_left_cancel (mul_right_cancel h))
  let a : MulAut V := MulEquiv.ofBijective φ (Function.Injective.bijective_of_finite hφinj)
  have ha (u : V) : ((eT (a u) : τ.range) : H) = g * τ u * g⁻¹ := by
    have hau : a u = φ u := MulEquiv.ofBijective_apply φ _ u
    rw [hau]
    exact hφ u
  let G := GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K
  have hconjGL (u : V) : (g : G) * omMinusTorusGL hζ u * (g : G)⁻¹ =
      omMinusTorusGL hζ (a u) := by
    have hGL : (((eT (a u) : τ.range) : H) : G) = ((g * τ u * g⁻¹ : H) : G) :=
      congrArg (fun z : H => (z : G)) (ha u)
    calc (g : G) * omMinusTorusGL hζ u * (g : G)⁻¹
        = ((g * τ u * g⁻¹ : H) : G) := by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
          rfl
      _ = (((eT (a u) : τ.range) : H) : G) := hGL.symm
      _ = omMinusTorusGL hζ (a u) := by
          rw [show ((eT (a u) : τ.range) : H) = τ (a u) from heT (a u)]
          rfl
  exact ⟨a, isSignedPerm_of_conj_omMinusTorusGL hp hζ hζo (g : G) a hconjGL,
    fun f => (ha f).symm.trans (heT (a f))⟩

theorem ggCommonJOmMinusSplit_conj [Fact p.Prime] (hp2 : p ≠ 2)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    {E : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c))} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ m) :
    ∃ α : StatedOmega (StatedQuadMinus (m + 1) K b c) ≃*
        StatedOmega (StatedQuadMinus (m + 1) K b c),
      E = (omMinusTorus (p := p) b c hζ).range.map α.toMonoidHom := by
  exact exists_mulEquiv_eq_map_omMinusTorus (m := m) hp2 hirr hζ hζo hE hcard.ge

end CFSG.StandardType

end

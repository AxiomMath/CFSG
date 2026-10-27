module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflSp
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenDefs

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.SeitzReduction SpCoord

theorem ggKGOmR_isSignedPerm {m p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {ζ : Kˣ}
    (hp : p.Prime) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (w₀ : StatedOmega (StatedQuadPlus m K))
    (u : MulAut (Fin m → Multiplicative (ZMod p)))
    (hu : ∀ f, w₀ * omPlusTorus hζ f * w₀⁻¹ = omPlusTorus hζ (u f)) :
    IsSignedPerm ⇑u := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set g : GL (Fin m ⊕ Fin m) K := (w₀ : GL (Fin m ⊕ Fin m) K) with hg
  have hconj : ∀ f : Fin m → Multiplicative (ZMod p),
      g * TableBSymp.spTorusGL hζ f * g⁻¹ = TableBSymp.spTorusGL hζ (u f) := by
    intro f
    have h := congrArg (fun x : StatedOmega (StatedQuadPlus m K) =>
      (x : GL (Fin m ⊕ Fin m) K)) (hu f)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_omPlusTorus,
      omPlusTorusGL_eq_spTorusGL] using h
  have hrel : ∀ f : Fin m → Multiplicative (ZMod p),
      g * TableBSymp.spTorusGL hζ f = TableBSymp.spTorusGL hζ (u f) * g := by
    intro f
    calc g * TableBSymp.spTorusGL hζ f
        = (g * TableBSymp.spTorusGL hζ f * g⁻¹) * g := by group
      _ = TableBSymp.spTorusGL hζ (u f) * g := by rw [hconj f]
  obtain ⟨j, ε, hε, hj⟩ := ReflSp.exists_monomial_data hζo hζ g
  have hj' : ∀ (f : Fin m → Multiplicative (ZMod p)) (i : Fin m),
      Multiplicative.toAdd (u f (j i)) = ε i * Multiplicative.toAdd (f i) :=
    fun f i => hj f (u f) (hrel f) i
  have hε0 : ∀ i, ε i ≠ 0 := fun i => coord_sign_ne_zero hp (hε i)
  have hjinj : Function.Injective j := by
    intro i i' hji
    by_contra hne
    have h1 := hj' (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p))) i
    have h2 := hj' (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p))) i'
    rw [toAdd_mulSingle, if_pos rfl, mul_one] at h1
    rw [toAdd_mulSingle, if_neg (Ne.symm hne), mul_zero] at h2
    rw [show u (Pi.mulSingle i (Multiplicative.ofAdd 1)) (j i) =
        u (Pi.mulSingle i (Multiplicative.ofAdd 1)) (j i') by rw [hji]] at h1
    rw [h2] at h1
    exact hε0 i h1.symm
  let π : Equiv.Perm (Fin m) :=
    Equiv.ofBijective j ⟨hjinj, Finite.injective_iff_surjective.mp hjinj⟩
  exact ⟨π, ε, hε, fun f i => by
    rw [show π i = j i from Equiv.ofBijective_apply j _ i]
    exact hj' f i⟩

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalPrimaryPairing

public section

open Module Multiplicative Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

private theorem TBJOmData.p_ne_zero (Δ : TBJOmData Q p A r) (i : Fin r) : p ≠ 0 := by
  rintro rfl
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) DFunLike.coe_injective
  haveI : Finite (Fin r → Multiplicative (ZMod 0)) := Finite.of_injective Δ.τ Δ.τ_inj
  haveI : Finite (Multiplicative (ZMod 0)) :=
    Finite.of_surjective (Function.eval i) fun x => ⟨fun _ => x, rfl⟩
  haveI : Finite (ZMod 0) :=
    Finite.of_injective (Multiplicative.ofAdd) Multiplicative.ofAdd.injective
  exact not_finite (ZMod 0)

theorem TBJOmData.τ_apply_eq_pow (Δ : TBJOmData Q p A r)
    {f f₀ : Fin r → Multiplicative (ZMod p)} {m : ZMod p} {i : Fin r}
    (hi : toAdd (f i) = m * toAdd (f₀ i)) {u : V} (hu : u ∈ Δ.F.U i) :
    Δ.τ f u = (Δ.τ f₀ ^ m.val) u := by
  haveI : NeZero p := ⟨Δ.p_ne_zero i⟩
  rw [← Δ.θ_range i, LinearMap.mem_range] at hu
  obtain ⟨d, rfl⟩ := hu
  have h1 : toAdd (piMul r p f) i = toAdd (f i) := by simp [piMul_apply]
  have hpow : toAdd (piMul r p (f₀ ^ m.val)) i = m * toAdd (f₀ i) := by
    change toAdd ((f₀ ^ m.val) i) = m * toAdd (f₀ i)
    rw [Pi.pow_apply, toAdd_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]
  have hexp : toAdd (piMul r p f) i = toAdd (piMul r p (f₀ ^ m.val)) i :=
    h1.trans (hi.trans hpow.symm)
  rw [Δ.τ_eq f, ← map_pow Δ.τ f₀ m.val, Δ.τ_eq (f₀ ^ m.val), Δ.θ_act, Δ.θ_act, hexp]

theorem TBJOmData.τ_apply_eq_pow_of_orbit (Δ : TBJOmData Q p A r)
    {f f₀ : Fin r → Multiplicative (ZMod p)} {m : ZMod p} {h : K[X]}
    (horb : orbitSpace (Δ.τ f₀).toLinearMap h =
      ⨆ (j : Fin r) (_ : Δ.F.U j ≤ orbitSpace (Δ.τ f₀).toLinearMap h), Δ.F.U j)
    (hf : ∀ j, Δ.F.U j ≤ orbitSpace (Δ.τ f₀).toLinearMap h →
      toAdd (f j) = m * toAdd (f₀ j)) :
    ∀ u ∈ orbitSpace (Δ.τ f₀).toLinearMap h, Δ.τ f u = (Δ.τ f₀ ^ m.val) u := by
  intro u hu
  rw [horb] at hu
  refine Submodule.iSup_induction
    (motive := fun x => Δ.τ f x = (Δ.τ f₀ ^ m.val) x)
    (fun j : Fin r => ⨆ (_ : Δ.F.U j ≤ orbitSpace (Δ.τ f₀).toLinearMap h), Δ.F.U j)
    hu ?_ ?_ ?_
  · intro j x hx
    refine Submodule.iSup_induction
      (motive := fun x => Δ.τ f x = (Δ.τ f₀ ^ m.val) x)
      (fun _ : Δ.F.U j ≤ orbitSpace (Δ.τ f₀).toLinearMap h => Δ.F.U j) hx ?_ ?_ ?_
    · intro hUj y hy
      exact Δ.τ_apply_eq_pow (hf j hUj) hy
    · simp
    · intro x y hx hy
      simp only [map_add, hx, hy]
  · simp
  · intro x y hx hy
    simp only [map_add, hx, hy]

end OrthTorus

end CFSG.StandardType

end

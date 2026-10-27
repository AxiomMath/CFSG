module

public import CFSG.LocalAnalysis.StandardType.GGK2E6D5CoordBridge
public import CFSG.LocalAnalysis.StandardType.GGFrameModelNumD
public import CFSG.LocalAnalysis.StandardType.GGHdRo7DDefs

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.FrameRoute CFSG.StandardType.HdRo7D
open CFSG.StandardType.SpCoord

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem dsp_of_coord_even
    {G : Type} [Group G] {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (b : Module.Basis (Fin 6) (ZMod 3) V) (a : MulAut ↥Bs)
    (hu : MulAut.congr (coordMulEquiv ι b) a ∈ evenSignedPermSet 6)
    (hfix : ggLin (p := 3) ι a (b 0) = b 0) :
    DSP 3 b (ggLin (p := 3) ι a) := by
  classical
  let μ := coordMulEquiv ι b
  let u : MulAut (Fin 6 → Multiplicative (ZMod 3)) := MulAut.congr μ a
  let bk : Fin 6 → ↥Bs := fun i => Additive.toMul (ι.symm (b i))
  obtain ⟨π, c, hc, hprod, heven⟩ := hu
  have hu_bk : ∀ i, u (μ (bk i)) = μ (a (bk i)) := by
    intro i
    simp [u, MulAut.congr_apply]
  have hcoord : ∀ i k,
      b.equivFun (ggLin (p := 3) ι a (b i)) (π k) =
        c k * b.equivFun (b i) k := by
    intro i k
    have h := heven (μ (bk i)) k
    have hcongr : ((MulAut.congr (coordMulEquiv ι b)) a) (μ (bk i)) = μ (a (bk i)) := by
      exact hu_bk i
    rw [hcongr] at h
    have h' : Multiplicative.toAdd (μ (a (bk i)) (π k)) =
        c k * Multiplicative.toAdd (μ (bk i) k) := h
    have hleft : Multiplicative.toAdd (μ (a (bk i)) (π k)) =
        b.equivFun (ggLin (p := 3) ι a (b i)) (π k) := by
      simp [μ, bk, coordMulEquiv_apply, ggLin_apply]
    have hright : Multiplicative.toAdd (μ (bk i) k) = b.equivFun (b i) k := by
      simp [μ, bk, coordMulEquiv_apply]
    rw [hleft, hright] at h'
    exact h'
  have hact : ∀ i, ggLin (p := 3) ι a (b i) = c i • b (π i) := by
    intro i
    apply b.equivFun.injective
    ext j
    have h := hcoord i (π.symm j)
    have hπ : π (π.symm j) = j := Equiv.apply_symm_apply π j
    rw [hπ] at h
    rw [h]
    by_cases hij : i = π.symm j
    · subst hij
      simp [b.equivFun_self]
    · have hπi : π i ≠ j := by
        intro hji
        exact hij (by simpa using congrArg π.symm hji)
      simp [b.equivFun_self, hij, hπi]
  have hact0 := hact 0
  have hc0ne : c 0 ≠ 0 := by
    rcases hc 0 with h | h <;> (rw [h]; decide)
  have hfix' : b 0 = c 0 • b (π 0) := by
    simpa [hact0] using hfix.symm
  have hπ0 : π 0 = 0 := by
    by_contra hne
    have h := congrArg (fun v => b.equivFun v (π 0)) hfix'
    simp [b.equivFun_self, hne, Ne.symm hne] at h
    exact hc0ne h.symm
  have hc0 : c 0 = 1 := by
    have h := congrArg (fun v => b.equivFun v 0) hfix'
    simpa [b.equivFun_self, hπ0] using h.symm
  exact ⟨π, c, hπ0, hc0, hc, hprod, hact⟩

end CFSG.StandardType

end

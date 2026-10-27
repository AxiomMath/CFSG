module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Bridge
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86SwapTI

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

open CFSG.Quasithin CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive Equiv
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsIrrOn)

theorem natVia_top_of_swap {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {H : Subgroup (MulAut V)} {n : ℕ} {ψ : ↥H →* Perm (Fin n)} (hn : 7 ≤ n)
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (hirr : IsIrrOn H ⊤ ⊥) (hfix : fixV (altPre ψ) = ⊥) {τ : ↥H} (hτ : (ψ τ).IsSwap)
    (hidx : (fixV (Subgroup.zpowers (τ : MulAut V))).index ≤ 8) : NatVia ψ ⊤ := by
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    apply Additive.toMul.injective
    rw [toMul_add, toMul_zero, ← sq]
    exact hV _
  have hψs := surjective_of_isSwap hA hτ
  have hS := swapDisjoint_autRep hV hn hψ hψs hfix hτ hidx
  obtain ⟨a, b, hab, hs⟩ := hτ
  have hτ1 : (τ : MulAut V) ≠ 1 := by
    intro h
    have h1 : τ = 1 := Subtype.ext h
    rw [h1, map_one] at hs
    have h2 := congrArg (fun σ : Perm (Fin n) => σ a) hs
    simp only [Perm.coe_one, id_eq, swap_apply_left] at h2
    exact hab h2
  obtain ⟨v, hv⟩ : ∃ v : V, (τ : MulAut V) v ≠ v := by
    by_contra h
    push Not at h
    exact hτ1 (MulEquiv.ext fun x => (h x).trans rfl)
  have hwr : autRep H τ (Additive.ofMul v) - Additive.ofMul v ∈
      LinearMap.range (autRep H τ - 1) :=
    ⟨Additive.ofMul v, by rw [LinearMap.sub_apply, Module.End.one_apply]⟩
  have hw0 : autRep H τ (Additive.ofMul v) - Additive.ofMul v ≠ 0 := by
    rw [sub_ne_zero, autRep_apply, toMul_ofMul]
    exact fun h => hv (Additive.ofMul.injective h)
  obtain ⟨f, hf, hfab⟩ := hS.exists_equivariant_evenWeight (by omega) hψs hab hs hwr
  refine natVia_top_of_equivariant (by omega) hψs hirr hfix f (fun h x => ?_) ?_
  · rw [hf, autRep_apply]
  · intro h0
    apply hw0
    rw [← hfab, h0, LinearMap.zero_apply]

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

end

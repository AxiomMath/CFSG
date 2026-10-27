module

public import CFSG.LocalAnalysis.StandardType.GGFrameModelNumB
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs
public import Mathlib.LinearAlgebra.Basis.Fin

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.FrameRoute CFSG.StandardType.HdRo7C

@[expose] noncomputable def coordMulEquiv {E : Type} [Group E] {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {k : ℕ} (ι : Additive E ≃+ V)
    (b : Module.Basis (Fin k) (ZMod 3) V) :
    E ≃* (Fin k → Multiplicative (ZMod 3)) :=
  (AddEquiv.toMultiplicativeRight (ι.trans b.equivFun.toAddEquiv)).trans
    (MulEquiv.piMultiplicative (fun _ : Fin k => ZMod 3))

@[simp] theorem coordMulEquiv_apply {E : Type} [Group E] {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {k : ℕ} (ι : Additive E ≃+ V)
    (b : Module.Basis (Fin k) (ZMod 3) V) (z : E) (i : Fin k) :
    coordMulEquiv ι b z i =
      Multiplicative.ofAdd ((b.equivFun (ι (Additive.ofMul z))) i) := by
  rfl

@[simp] theorem coordMulEquiv_symm_apply {E : Type} [Group E] {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {k : ℕ} (ι : Additive E ≃+ V)
    (b : Module.Basis (Fin k) (ZMod 3) V)
    (f : Fin k → Multiplicative (ZMod 3)) :
    (coordMulEquiv ι b).symm f =
      Additive.toMul (ι.symm (b.equivFun.symm (fun i => Multiplicative.toAdd (f i)))) := by
  rfl

theorem c2sp_coordAut_mem_signedPermSet
    {E : Type} [Group E] {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (ι : Additive E ≃+ V) (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (a : MulAut E) (h : C2SP 3 b (ggLin (p := 3) ι a)) :
    (MulAut.congr (coordMulEquiv ι b) a :
      MulAut (Fin (n + 1) → Multiplicative (ZMod 3))) ∈ signedPermSet (n + 1) := by
  classical
  obtain ⟨σ, c, hσ0, hc0, hc, hspec⟩ := h
  refine ⟨σ, c, hc, ?_⟩
  intro f i
  have hμ : MulAut.congr (coordMulEquiv ι b) a f =
      fun j => coordMulEquiv ι b (a ((coordMulEquiv ι b).symm f)) j := rfl
  rw [hμ]
  have hz : ι (Additive.ofMul ((coordMulEquiv ι b).symm f)) =
      b.equivFun.symm (fun j => Multiplicative.toAdd (f j)) := by
    simp [coordMulEquiv]
  have hcoord : coordMulEquiv ι b (a ((coordMulEquiv ι b).symm f)) (σ i) =
      Multiplicative.ofAdd (c i * Multiplicative.toAdd (f i)) := by
    rw [coordMulEquiv_apply]
    have hι : ι (Additive.ofMul (a ((coordMulEquiv ι b).symm f))) =
        ggLin (p := 3) ι a (b.equivFun.symm (fun j => Multiplicative.toAdd (f j))) := by
      rw [← hz, ggLin_apply]
      simp
    rw [hι, Basis.equivFun_symm_apply]
    have hmap : ggLin (p := 3) ι a (∑ j, Multiplicative.toAdd (f j) • b j) =
        ∑ j, Multiplicative.toAdd (f j) • (c j • b (σ j)) := by
      rw [map_sum]
      simp only [map_smul, hspec]
    rw [hmap]
    rw [map_sum, Finset.sum_apply]
    have hterm2 : ∀ j, b.equivFun (Multiplicative.toAdd (f j) • (c j • b (σ j))) (σ i) =
        if j = i then c i * Multiplicative.toAdd (f i) else 0 := by
      intro j
      rw [map_smul, map_smul]
      simp only [Pi.smul_apply, smul_eq_mul, Basis.equivFun_self]
      by_cases hji : j = i
      · subst hji
        rw [if_pos rfl, if_pos rfl]
        ring
      · have hσ : σ j ≠ σ i := fun h => hji (σ.injective h)
        rw [if_neg hσ, if_neg hji]
        simp
    calc
      ∑ j, b.equivFun (Multiplicative.toAdd (f j) • (c j • b (σ j))) (σ i)
          = ∑ j, (if j = i then c i * Multiplicative.toAdd (f i) else 0) := by
            exact Finset.sum_congr rfl fun j _ => hterm2 j
      _ = c i * Multiplicative.toAdd (f i) := by
            simpa using (Finset.sum_ite_eq' (s := Finset.univ) i
              (fun _ => c i * Multiplicative.toAdd (f i)))
  simpa using congrArg Multiplicative.toAdd hcoord

theorem reflection_coordAut_mem_modelReflSet
    {G : Type} [Group G] {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {n : ℕ}
    (ι : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (a : MulAut ↥Bs) (hC2 : C2SP 3 b (ggLin (p := 3) ι a))
    (hR : GGIsReflection 3 a) :
    MulAut.congr (coordMulEquiv ι b) a ∈ modelReflSet (signedPermSet (n + 1)) := by
  classical
  let μ := coordMulEquiv ι b
  let u : MulAut (Fin (n + 1) → Multiplicative (ZMod 3)) := MulAut.congr μ a
  have hsign : u ∈ signedPermSet (n + 1) := c2sp_coordAut_mem_signedPermSet ι b a hC2
  refine ⟨hsign, ?_, ?_⟩
  ·
    have h2 : a ^ 2 = 1 := hR.1
    have hpow : u ^ 2 = MulAut.congr μ (a ^ 2) := by
      simpa [u] using (map_pow (MulAut.congr μ) a 2).symm
    rw [hpow, h2, map_one]
  ·
    have hfix : Nat.card {z : ↥Bs // a z = z} * 3 = Nat.card ↥Bs := hR.2
    have hu : ∀ z, u (μ.toEquiv z) = μ (a z) := by
      intro z
      simp [u]
    have hequiv : {z : ↥Bs // a z = z} ≃
        {f : Fin (n + 1) → Multiplicative (ZMod 3) // u f = f} := by
      refine Equiv.subtypeEquiv μ.toEquiv ?_
      intro z
      rw [hu]
      exact ⟨fun hz => by rw [hz]; rfl, fun hz => μ.injective hz⟩
    have hcard : Nat.card {f : Fin (n + 1) → Multiplicative (ZMod 3) // u f = f} =
        Nat.card {z : ↥Bs // a z = z} := Nat.card_congr hequiv.symm
    have hEcard : Nat.card ↥Bs = Nat.card (Fin (n + 1) → Multiplicative (ZMod 3)) :=
      Nat.card_congr μ.toEquiv
    rw [hcard, ← hEcard]
    exact hfix

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGQTwoForkTransport
public import CFSG.LocalAnalysis.StandardType.GGWAutModelNorm
public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem lr7l2_neg_mem_normalizer {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (W : Subgroup (U ≃ₗ[ZMod 3] U)) :
    LinearEquiv.neg (ZMod 3) ∈ Subgroup.normalizer (W : Set (U ≃ₗ[ZMod 3] U)) := by
  have hcomm : ∀ g : U ≃ₗ[ZMod 3] U,
      LinearEquiv.neg (ZMod 3) * g = g * LinearEquiv.neg (ZMod 3) := by
    intro g
    refine LinearEquiv.ext fun x => ?_
    simp only [LinearEquiv.mul_apply, LinearEquiv.neg_apply, map_neg]
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    rw [hcomm n, mul_assoc, mul_inv_cancel, mul_one]
    exact hn
  · intro hn
    rw [hcomm n, mul_assoc, mul_inv_cancel, mul_one] at hn
    exact hn

theorem ggQ2WeylFork_D {n : ℕ} (hn : 5 ≤ n) :
    GGQ2WeylFork n (CartanMatrix.D n)
      (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩) := by
  intro U _ _ h hb hspan α hα T hT
  obtain ⟨s, _hs, _hsW, hsh, hcases⟩ := ggQ2WeylNormD_fork hn h hb hspan α hα T hT
  rcases hcases with ⟨w, hw, hwT | hwT⟩ | ⟨w, hw, hwT | hwT⟩
  ·
    exact ⟨w, hw, 1, one_ne_zero, Or.inl fun i => by rw [hwT, one_smul]⟩
  ·
    exact ⟨w, hw, -1, by decide, Or.inl fun i => by rw [hwT, neg_one_smul]⟩
  ·
    have hTw : T = s * w := by
      refine LinearEquiv.ext fun v => ?_
      rw [hwT v, LinearEquiv.mul_apply]
    have hsN : s ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (U ≃ₗ[ZMod 3] U)) := by
      have hs_eq : s = T * w⁻¹ := by rw [hTw]; group
      rw [hs_eq]
      exact Subgroup.mul_mem _ hT (Subgroup.inv_mem _ (Subgroup.le_normalizer hw))
    have hw'' : s * w * s⁻¹ ∈ ggQ2WeylOf h α :=
      (Subgroup.mem_normalizer_iff.1 hsN w).1 hw
    have hconj : s * w = (s * w * s⁻¹) * s := by group
    have hmain : ∀ i, s (w (h i)) =
        (s * w * s⁻¹) (h (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ i)) :=
      fun i => by
        calc s (w (h i)) = (s * w) (h i) := by rw [LinearEquiv.mul_apply]
          _ = ((s * w * s⁻¹) * s) (h i) :=
                congrArg (fun e : U ≃ₗ[ZMod 3] U => e (h i)) hconj
          _ = (s * w * s⁻¹) (s (h i)) := by rw [LinearEquiv.mul_apply]
          _ = (s * w * s⁻¹)
                (h (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ i)) := by
                rw [hsh i]
    exact ⟨s * w * s⁻¹, hw'', 1, one_ne_zero, Or.inr fun i => by
      rw [hwT (h i), one_smul]; exact hmain i⟩
  ·
    have hTw : T = LinearEquiv.neg (ZMod 3) * (s * w) := by
      refine LinearEquiv.ext fun v => ?_
      rw [hwT v]
      simp only [LinearEquiv.mul_apply, LinearEquiv.neg_apply]
    have hneg : LinearEquiv.neg (ZMod 3) ∈
        Subgroup.normalizer (ggQ2WeylOf h α : Set (U ≃ₗ[ZMod 3] U)) :=
      lr7l2_neg_mem_normalizer _
    have hsN : s ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (U ≃ₗ[ZMod 3] U)) := by
      have hs_eq : s = (LinearEquiv.neg (ZMod 3))⁻¹ * T * w⁻¹ := by rw [hTw]; group
      rw [hs_eq]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hneg) hT)
        (Subgroup.inv_mem _ (Subgroup.le_normalizer hw))
    have hw'' : s * w * s⁻¹ ∈ ggQ2WeylOf h α :=
      (Subgroup.mem_normalizer_iff.1 hsN w).1 hw
    have hconj : s * w = (s * w * s⁻¹) * s := by group
    have hmain : ∀ i, s (w (h i)) =
        (s * w * s⁻¹) (h (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ i)) :=
      fun i => by
        calc s (w (h i)) = (s * w) (h i) := by rw [LinearEquiv.mul_apply]
          _ = ((s * w * s⁻¹) * s) (h i) :=
                congrArg (fun e : U ≃ₗ[ZMod 3] U => e (h i)) hconj
          _ = (s * w * s⁻¹) (s (h i)) := by rw [LinearEquiv.mul_apply]
          _ = (s * w * s⁻¹)
                (h (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ i)) := by
                rw [hsh i]
    exact ⟨s * w * s⁻¹, hw'', -1, by decide, Or.inr fun i => by
      rw [hwT (h i), neg_one_smul]; rw [hmain i]⟩

theorem ggQ2_D_swap_cartan {n : ℕ} (hn : 5 ≤ n) (i j : Fin n) :
    CartanMatrix.D n (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ i)
      (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ j) = CartanMatrix.D n i j := by
  have e : TauCeti.graphPermD n (by omega) =
      Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ := by
    refine Equiv.ext fun k => ?_
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1
      exact TauCeti.graphPermD_apply_left n _
    · subst h2
      exact TauCeti.graphPermD_apply_right n _
    · exact TauCeti.graphPermD_apply_of_ne_of_ne n _ k (fun h => h1 (Fin.ext h))
        (fun h => h2 (Fin.ext h))
  have h := TauCeti.cartanMatrix_D_graphPermD n (by omega) i j
  rw [e] at h
  simpa only [TauCeti.DynkinType.cartanMatrix_D] using h

theorem ggQ2_dNormal_of_normalizer (D : GGQ2Lin 3) {n : ℕ} (hn : 5 ≤ n)
    (f : Fin n ≃ {k // k ≠ D.a}) (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.D n i j)
    (hind : LinearIndependent (ZMod 3) (fun i : {k // k ≠ D.a} => D.coroot i))
    (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∃ (π : {k // k ≠ D.a} ≃ {k // k ≠ D.a}) (c : ZMod 3), c ≠ 0 ∧
      (∀ i j : {k // k ≠ D.a}, D.cartan (π i) (π j) = D.cartan i j) ∧
      ∃ w ∈ D.parab {k | k ≠ D.a}, ∀ i : {k // k ≠ D.a},
        T (D.coroot i) = c • w (D.coroot (π i)) := by
  classical
  obtain ⟨w, hw, c, hc, h | h⟩ := GGQ2Lin.fork_of_transport D (CartanMatrix.D n) f hf hind
    (ggQ2WeylFork_D hn) T hT
  · refine ⟨Equiv.refl _, c, hc, fun i j => rfl, w, hw, fun i => ?_⟩
    obtain ⟨j, rfl⟩ := f.surjective i
    exact h j
  · refine ⟨f.symm.trans ((Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩).trans f),
      c, hc, fun i j => ?_, w, hw, fun i => ?_⟩
    · obtain ⟨a, rfl⟩ := f.surjective i
      obtain ⟨b, rfl⟩ := f.surjective j
      simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
      rw [hf, hf]
      exact ggQ2_D_swap_cartan (by omega) a b
    · obtain ⟨j, rfl⟩ := f.surjective i
      simpa using h j

end CFSG.StandardType

end

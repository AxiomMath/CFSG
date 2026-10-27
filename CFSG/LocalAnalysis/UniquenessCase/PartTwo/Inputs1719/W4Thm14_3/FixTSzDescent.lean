module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDensity
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.QuasithinUnique.Setup.SL2Modules

variable {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
  {ρ : Representation (ZMod 2) G M} [Fact ρ.IsIrreducible]

private theorem exists_retraction {D E : Type*} [Field D] [Field E] (ι : D →+* E) :
    ∃ t : E →+ D, (∀ r x, t (ι r * x) = r * t x) ∧ t 1 = 1 := by
  letI : Algebra D E := ι.toAlgebra
  have hker : LinearMap.ker (Algebra.linearMap D E) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y h
    exact ι.injective h
  obtain ⟨t, ht⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap D E) hker
  have ht' : ∀ r, t (ι r) = r := fun r => by
    have h := congrArg (fun g : D →ₗ[D] D => g r) ht
    exact h
  refine ⟨t.toAddMonoidHom, ?_, ?_⟩
  · intro r x
    have h := t.map_smul r x
    rw [Algebra.smul_def] at h
    exact h
  · simpa using ht' 1

private theorem coordMap_of_retraction {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) M)
    {E : Type} [Field E] (ιD : EndRing ρ →+* E) (t : E →+ EndRing ρ)
    (ht : ∀ r x, t (ιD r * x) = r * t x) (ht1 : t 1 = 1) :
    ∃ T : (Fin m → E) →+ M,
      (∀ z, b.equivFun (T z) = fun i => t (z i)) ∧
      (∀ (g : G) (w : M), b.equivFun (ρ g w) = (matRep b g).mulVec (b.equivFun w)) ∧
      (∀ (g : G) (y : Fin m → E), T (matRepE b ιD g y) = ρ g (T y)) := by
  classical
  let T : (Fin m → E) →+ M :=
    { toFun := fun y => b.equivFun.symm (fun i => t (y i))
      map_zero' := by simp
      map_add' := fun y z => by
        change b.equivFun.symm (fun i => t (y i + z i)) =
          b.equivFun.symm (fun i => t (y i)) + b.equivFun.symm (fun i => t (z i))
        rw [← map_add]
        congr 1
        funext i
        exact map_add t (y i) (z i) }
  have hTcoord : ∀ z : Fin m → E, b.equivFun (T z) = fun i => t (z i) :=
    fun z => LinearEquiv.apply_symm_apply b.equivFun _
  have hcol : ∀ (g : G) (w : M),
      b.equivFun (ρ g w) = (matRep b g).mulVec (b.equivFun w) := by
    intro g w
    have h := LinearMap.toMatrix_mulVec_repr b b (repD ρ g) w
    rw [repD_apply] at h
    exact h.symm
  have hTA : ∀ (A : Matrix (Fin m) (Fin m) (EndRing ρ)) (y : Fin m → E),
      b.equivFun (T ((A.map ιD).mulVec y)) = A.mulVec (fun i => t (y i)) := by
    intro A y
    rw [hTcoord]
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => ht (A i j) (y j)
  have hT : ∀ (g : G) (y : Fin m → E), T (matRepE b ιD g y) = ρ g (T y) := by
    intro g y
    apply b.equivFun.injective
    rw [matRepE_apply, hTA, hcol g (T y), hTcoord y]
  exact ⟨T, hTcoord, hcol, hT⟩

theorem exists_norm_vector_of_equiv {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) M)
    {E : Type} [Field E] (ιD : EndRing ρ →+* E) {κ : Type} [Fintype κ] [DecidableEq κ]
    (R : G →* Matrix κ κ E) (Φ : (CFSG.QuasithinUnique.Setup.X7.matRep R).Equiv (matRepE b ιD))
    {e : κ → E} (he : e ≠ 0) (P : G → Prop) (hN : ∀ s, P s → ∃ z : κ → E,
      e = z + (R s).mulVec z + (R s).mulVec ((R s).mulVec z) +
        (R s).mulVec ((R s).mulVec ((R s).mulVec z)))
    {d : G} {c : E} (hc : c ≠ 1) (hd : (R d).mulVec e = c • e) :
    ∃ x : M, (∀ s, P s → ∃ y : M, x = y + ρ s y + ρ s (ρ s y) + ρ s (ρ s (ρ s y))) ∧ ρ d x ≠ x := by
  classical
  obtain ⟨t, ht, ht1⟩ := exists_retraction ιD
  obtain ⟨T, hTcoord, -, hT⟩ := coordMap_of_retraction b ιD t ht ht1
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin m, Φ e i0 ≠ 0 := by
    by_contra h
    push Not at h
    apply he
    apply Φ.toLinearEquiv.injective
    rw [map_zero]
    exact funext fun i => h i
  set c' : E := ((c - 1) * Φ e i0)⁻¹ with hc'def
  have hc'mul : c' * (c - 1) * Φ e i0 = 1 := by
    rw [mul_assoc, hc'def, inv_mul_cancel₀]
    exact mul_ne_zero (sub_ne_zero.mpr hc) hi0
  refine ⟨T (c' • Φ e), ?_, ?_⟩
  · intro s hs
    obtain ⟨z, hz⟩ := hN s hs
    refine ⟨T (c' • Φ z), ?_⟩
    have h1 : Φ e = Φ z + matRepE b ιD s (Φ z) +
        matRepE b ιD s (matRepE b ιD s (Φ z)) +
        matRepE b ιD s (matRepE b ιD s (matRepE b ιD s (Φ z))) := by
      conv_lhs => rw [hz]
      simp only [← CFSG.QuasithinUnique.Setup.X7.matRep_apply, map_add, equiv_apply]
    have h2 : c' • Φ e = c' • Φ z + matRepE b ιD s (c' • Φ z) +
        matRepE b ιD s (matRepE b ιD s (c' • Φ z)) +
        matRepE b ιD s (matRepE b ιD s (matRepE b ιD s (c' • Φ z))) := by
      rw [h1, smul_add, smul_add, smul_add]
      simp only [← map_smul]
    rw [h2, map_add, map_add, map_add]
    simp only [hT]
  · intro hfix
    have hdE : matRepE b ιD d (Φ e) = c • Φ e := by
      rw [← equiv_apply Φ d e, CFSG.QuasithinUnique.Setup.X7.matRep_apply, hd, map_smul]
    have hfix' : T ((c' * c) • Φ e) = T (c' • Φ e) := by
      have h1 := hT d (c' • Φ e)
      rw [map_smul, hdE, smul_smul] at h1
      rw [hfix] at h1
      exact h1
    have hcoord : t (c' * c * Φ e i0) = t (c' * Φ e i0) := by
      have h := congrFun (congrArg b.equivFun hfix') i0
      rw [hTcoord, hTcoord] at h
      simpa [Pi.smul_apply, smul_eq_mul] using h
    have hzero : t 1 = 0 := by
      have hsub : t (c' * c * Φ e i0 - c' * Φ e i0) = 0 := by
        rw [map_sub, hcoord, sub_self]
      rwa [show c' * c * Φ e i0 - c' * Φ e i0 = c' * (c - 1) * Φ e i0 by ring,
        hc'mul] at hsub
    exact one_ne_zero (by rw [← ht1, hzero])

theorem exists_higman_of_equiv {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) M)
    {E : Type} [Field E] (ιD : EndRing ρ →+* E) {κ : Type} [Fintype κ] [DecidableEq κ]
    (R : G →* Matrix κ κ E) (Φ : (CFSG.QuasithinUnique.Setup.X7.matRep R).Equiv (matRepE b ιD))
    (U : Subgroup G) [Fintype ↥U] (φ : (κ → E) →ₗ[E] (κ → E))
    (hφ : ∀ y, ∑ u : ↥U, (R u).mulVec (φ ((R ((u : G)⁻¹)).mulVec y)) = y) :
    ∃ ψ : M →ₗ[ZMod 2] M, ∀ x, ∑ u : ↥U, ρ u (ψ (ρ ((u : G)⁻¹) x)) = x := by
  classical
  obtain ⟨t, ht, ht1⟩ := exists_retraction ιD
  obtain ⟨T, hTcoord, hcol, hT⟩ := coordMap_of_retraction b ιD t ht ht1
  have ht_id : ∀ r : EndRing ρ, t (ιD r) = r := fun r => by
    have h := ht r 1
    rwa [mul_one, ht1, mul_one] at h
  let coordF : M → (Fin m → E) := fun x i => ιD (b.equivFun x i)
  have hcoord : ∀ (g : G) (x : M), coordF (ρ g x) = matRepE b ιD g (coordF x) := by
    intro g x
    funext i
    rw [matRepE_apply]
    show ιD (b.equivFun (ρ g x) i) =
      (((matRep b g).map (fun r => ιD r)).mulVec (fun j => ιD (b.equivFun x j))) i
    rw [hcol]
    exact RingHom.map_mulVec ιD (matRep b g) (b.equivFun x) i
  have hΦsymm : ∀ (g : G) (y : Fin m → E),
      Φ.symm (matRepE b ιD g y) =
        CFSG.QuasithinUnique.Setup.X7.matRep R g (Φ.symm y) :=
    fun g y => equiv_apply Φ.symm g y
  let Ψ : M →+ M :=
    { toFun := fun x => T (Φ (φ (Φ.symm (coordF x))))
      map_zero' := by
        have h0 : coordF 0 = 0 := by
          funext i
          show ιD (b.equivFun 0 i) = 0
          rw [show b.equivFun 0 = 0 from b.equivFun.map_zero]
          exact ιD.map_zero
        rw [h0]
        simp only [map_zero]
      map_add' := fun x y => by
        have hc : coordF (x + y) = coordF x + coordF y := by
          funext i
          show ιD (b.equivFun (x + y) i) = ιD (b.equivFun x i) + ιD (b.equivFun y i)
          rw [show b.equivFun (x + y) = b.equivFun x + b.equivFun y from
            b.equivFun.map_add x y]
          exact ιD.map_add _ _
        rw [hc]
        simp only [map_add] }
  have hΨ : ∀ x : M, Ψ x = T (Φ (φ (Φ.symm (coordF x)))) := fun x => rfl
  let ψ : M →ₗ[ZMod 2] M := AddMonoidHom.toZModLinearMap 2 Ψ
  have hψ : ∀ y : M, (ψ : M → M) y = Ψ y := fun y => rfl
  refine ⟨ψ, fun x => ?_⟩
  let η : κ → E := Φ.symm (coordF x)
  have hterm : ∀ u : ↥U, ρ (u : G) (ψ (ρ ((u : G)⁻¹) x)) =
      T (Φ ((R (u : G)).mulVec (φ ((R ((u : G)⁻¹)).mulVec η)))) := by
    intro u
    have h1 : Ψ (ρ ((u : G)⁻¹) x) =
        T (Φ (φ (CFSG.QuasithinUnique.Setup.X7.matRep R ((u : G)⁻¹) η))) := by
      rw [hΨ, hcoord, hΦsymm]
    have h2 : ρ (u : G) (T (Φ (φ (CFSG.QuasithinUnique.Setup.X7.matRep R
        ((u : G)⁻¹) η)))) =
        T (Φ ((R (u : G)).mulVec (φ (CFSG.QuasithinUnique.Setup.X7.matRep R
          ((u : G)⁻¹) η)))) := by
      calc ρ (u : G) (T (Φ (φ (CFSG.QuasithinUnique.Setup.X7.matRep R
            ((u : G)⁻¹) η))))
          = T (matRepE b ιD (u : G) (Φ (φ (CFSG.QuasithinUnique.Setup.X7.matRep R
              ((u : G)⁻¹) η)))) :=
            (hT (u : G) (Φ (φ (CFSG.QuasithinUnique.Setup.X7.matRep R ((u : G)⁻¹) η)))).symm
        _ = T (Φ (CFSG.QuasithinUnique.Setup.X7.matRep R (u : G)
              (φ (CFSG.QuasithinUnique.Setup.X7.matRep R ((u : G)⁻¹) η)))) :=
            congrArg T (equiv_apply Φ (u : G)
              (φ (CFSG.QuasithinUnique.Setup.X7.matRep R ((u : G)⁻¹) η))).symm
        _ = T (Φ ((R (u : G)).mulVec (φ (CFSG.QuasithinUnique.Setup.X7.matRep R
              ((u : G)⁻¹) η)))) := by
            rw [CFSG.QuasithinUnique.Setup.X7.matRep_apply]
    rw [hψ, h1, h2]
    rfl
  rw [Finset.sum_congr rfl fun u _ => hterm u]
  rw [← map_sum, ← map_sum, hφ η]
  have hfin : T (Φ η) = x := by
    have h1 : Φ η = coordF x := LinearEquiv.apply_symm_apply Φ.toLinearEquiv (coordF x)
    rw [h1]
    apply b.equivFun.injective
    rw [hTcoord]
    rw [show (fun i => t (coordF x i)) = b.equivFun x from
      funext fun i => ht_id (b.equivFun x i)]
  exact hfin

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

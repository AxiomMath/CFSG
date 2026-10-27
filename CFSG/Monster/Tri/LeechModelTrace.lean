module

public import CFSG.Monster.B.Cbar.LocalE
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Tri.Leech

open CFSG.Monster CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Griess
  CFSG.Monster.VisCert CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B
  CFSG.Monster.ScalarKernel

theorem trace_le_finrank_of_comp_self {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (f : V →ₗ[ℚ] V) (hf : f ∘ₗ f = LinearMap.id) :
    LinearMap.trace ℚ V f ≤ Module.finrank ℚ V := by
  set P : V →ₗ[ℚ] V := (1 / 2 : ℚ) • (LinearMap.id + f) with hP
  have hPP : IsIdempotentElem P := by
    ext v
    have hv : f (f v) = v := LinearMap.congr_fun hf v
    simp only [hP, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.id_apply, map_add, map_smul, hv]
    module
  have h1 : LinearMap.trace ℚ V P = (Module.finrank ℚ (LinearMap.range P) : ℚ) :=
    (LinearMap.IsIdempotentElem.isProj_range P hPP).trace
  have h2 : LinearMap.trace ℚ V P = (1 / 2) * ((Module.finrank ℚ V : ℚ) +
      LinearMap.trace ℚ V f) := by
    simp only [hP, map_smul, map_add, LinearMap.trace_id, smul_eq_mul]
  have h3 : (Module.finrank ℚ (LinearMap.range P) : ℚ) ≤ Module.finrank ℚ V := by
    exact_mod_cast Submodule.finrank_le _
  linarith

theorem coe_thetaEquiv (p : Pvis) : (thetaEquiv p : SpaceB →ₗ[ℚ] SpaceB) = theta p := rfl

theorem trace_theta (p : Pvis) :
    LinearMap.trace ℚ SpaceB (theta p) =
      LinearMap.trace ℚ symMat (thetaA (mat p.1.2)) + (LinearMap.trace ℚ SpaceX (thetaX p) +
        LinearMap.trace ℚ SpaceW (thetaW (p.1.1 : Matrix SpinIdx SpinIdx ℚ) (mat p.1.2))) := by
  rw [theta, LinearMap.trace_prodMap', LinearMap.trace_prodMap']

theorem trace_theta_comp_parity (p : Pvis) :
    LinearMap.trace ℚ SpaceB (theta p ∘ₗ parityMap) =
      LinearMap.trace ℚ symMat (thetaA (mat p.1.2)) + (LinearMap.trace ℚ SpaceX (thetaX p) -
        LinearMap.trace ℚ SpaceW (thetaW (p.1.1 : Matrix SpinIdx SpinIdx ℚ) (mat p.1.2))) := by
  have h : theta p ∘ₗ parityMap = (thetaA (mat p.1.2)).prodMap ((thetaX p).prodMap
      (-(thetaW (p.1.1 : Matrix SpinIdx SpinIdx ℚ) (mat p.1.2)))) := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, parityMap_apply, theta_apply, LinearMap.prodMap_apply,
      LinearMap.neg_apply, map_neg]
  rw [h, LinearMap.trace_prodMap', LinearMap.trace_prodMap', map_neg]
  ring

theorem trace_theta_add_xmat (p : Pvis) :
    LinearMap.trace ℚ SpaceB (thetaEquiv p : SpaceB →ₗ[ℚ] SpaceB) +
      LinearMap.trace ℚ SpaceB ((thetaEquiv p * xmat : SpaceB ≃ₗ[ℚ] SpaceB) :
        SpaceB →ₗ[ℚ] SpaceB) =
    2 * (LinearMap.trace ℚ symMat (thetaA (mat p.1.2)) + LinearMap.trace ℚ SpaceX (thetaX p)) := by
  have h : ((thetaEquiv p * xmat : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) =
      theta p ∘ₗ parityMap := by
    refine LinearMap.ext fun v => ?_
    rw [xmat_eq_xB]
    rfl
  rw [h, coe_thetaEquiv, trace_theta, trace_theta_comp_parity]
  ring

theorem trace_thetaA_le {p : Pvis} (hp : thetaEquiv p * thetaEquiv p = 1) :
    LinearMap.trace ℚ symMat (thetaA (mat p.1.2)) ≤ 300 := by
  have hcomp : thetaA (mat p.1.2) ∘ₗ thetaA (mat p.1.2) = LinearMap.id := by
    ext A : 1
    have h := congrArg (fun f : SpaceB ≃ₗ[ℚ] SpaceB => (f ((A, 0, 0) : SpaceB)).1) hp
    simpa [theta_apply, thetaEquiv_apply] using h
  have := trace_le_finrank_of_comp_self _ hcomp
  rwa [finrank_A] at this

@[expose] def fixShort (g : latticeO) : Set L2 := {y | y ∈ shortSet ∧ modTwoEnd g y = y}

theorem finite_shortSet : shortSet.Finite :=
  Set.finite_of_ncard_ne_zero (by rw [ncard_shortSet]; norm_num)

theorem finite_fixShort (g : latticeO) : (fixShort g).Finite :=
  finite_shortSet.subset fun _ hy => hy.1

theorem trace_thetaX_le (p : Pvis) :
    LinearMap.trace ℚ SpaceX (thetaX p) ≤ (fixShort p.1.2).ncard := by
  classical
  rw [trace_X_eq_sum]
  set S : Finset ShortIdx := Finset.univ.filter fun c => modTwoEnd p.1.2 (phi0 c.1) = phi0 c.1
    with hS
  have hterm : ∀ c : ShortIdx, thetaX p (Pi.single c 1) c ≤ if c ∈ S then 1 else 0 := by
    intro c
    rw [thetaX_single]
    by_cases hc : c ∈ S
    · simp only [hc, ↓reduceIte]
      unfold Xlift
      split_ifs with h
      · simp only [Pi.smul_apply, smul_eq_mul]
        by_cases hcc : (⟨coordOf (conjQ p (rep c.1)), h⟩ : ShortIdx) = c
        · rw [hcc, Pi.single_eq_same, mul_one]
          unfold sgn
          split_ifs <;> norm_num
        · rw [Pi.single_eq_of_ne' hcc, mul_zero]
          norm_num
      · simp
    · simp only [hc, ↓reduceIte]
      unfold Xlift
      split_ifs with h
      · simp only [Pi.smul_apply, smul_eq_mul]
        by_cases hcc : (⟨coordOf (conjQ p (rep c.1)), h⟩ : ShortIdx) = c
        · exfalso
          apply hc
          rw [hS, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have h1 : coordOf (conjQ p (rep c.1)) = c.1 := congrArg Subtype.val hcc
          have h2 := phi0_conjQ p (rep c.1)
          rw [h1, coordOf_rep] at h2
          exact h2.symm
        · rw [Pi.single_eq_of_ne' hcc, mul_zero]
      · simp
  calc ∑ c, thetaX p (Pi.single c 1) c ≤ ∑ c : ShortIdx, (if c ∈ S then (1 : ℚ) else 0) :=
        Finset.sum_le_sum fun c _ => hterm c
    _ = (S.card : ℚ) := by rw [Finset.sum_boole]; simp [hS]
    _ ≤ ((fixShort p.1.2).ncard : ℚ) := by
        have : S.card ≤ (fixShort p.1.2).ncard := by
          rw [← Set.ncard_coe_finset]
          refine Set.ncard_le_ncard_of_injOn (fun c : ShortIdx => phi0 c.1) (fun c hc => ?_)
            (fun c _ d _ h => ?_) (finite_fixShort _)
          · rw [Finset.mem_coe, hS, Finset.mem_filter] at hc
            exact ⟨c.2, hc.2⟩
          · exact Subtype.ext (phi0_injective h)
        exact_mod_cast this

theorem trace_theta_add_xmat_le {p : Pvis} (hp : thetaEquiv p * thetaEquiv p = 1) :
    LinearMap.trace ℚ SpaceB (thetaEquiv p : SpaceB →ₗ[ℚ] SpaceB) +
      LinearMap.trace ℚ SpaceB ((thetaEquiv p * xmat : SpaceB ≃ₗ[ℚ] SpaceB) :
        SpaceB →ₗ[ℚ] SpaceB) ≤ 600 + 2 * (fixShort p.1.2).ncard := by
  rw [trace_theta_add_xmat]
  have h1 := trace_thetaA_le hp
  have h2 := trace_thetaX_le p
  linarith

end CFSG.Monster.Tri.Leech

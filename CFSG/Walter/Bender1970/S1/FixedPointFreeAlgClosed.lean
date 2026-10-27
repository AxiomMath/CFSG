module

public import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import CFSG.Walter.Bender1970.S1.FixedPointFreeOrbits

public section

namespace CFSG.Walter

open Module

theorem bender1970_1_5_finrank_eq_of_isAlgClosed {K V Γ : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Group Γ] [Finite Γ]
    (ρ : Representation K Γ V) (N R : Subgroup Γ)
    (hN : IsMulCommutative N) (hRN : R ≤ Subgroup.normalizer (N : Set Γ))
    (hfpf : ∀ x ∈ R, x ≠ 1 → ∀ n ∈ N, x * n * x⁻¹ = n → n = 1)
    (hNchar : ((Nat.card N : ℕ) : K) ≠ 0)
    (hCN : ∀ v : V, (∀ n ∈ N, ρ n v = v) → v = 0) :
    finrank K V = Nat.card R * finrank K (Representation.invariants (ρ.comp R.subtype)) := by
  classical
  let f : N → Module.End K V := fun n => ρ n
  have hcomm (i j : N) : Commute (f i) (f j) := by
    change ρ i * ρ j = ρ j * ρ i
    rw [← map_mul, ← map_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hN.is_comm.comm i j]
  have hss (n : N) : (f n).IsFinitelySemisimple := by
    refine Module.End.IsSemisimple.isFinitelySemisimple <|
      Module.End.isSemisimple_of_squarefree_aeval_eq_zero
        (Polynomial.separable_X_pow_sub_C 1 hNchar one_ne_zero).squarefree ?_
    have h1 : f n ^ Nat.card N = 1 := by
      change ρ n ^ Nat.card N = 1
      rw [← map_pow, ← Subgroup.coe_pow, pow_card_eq_one', Subgroup.coe_one, map_one]
    simp [h1]
  let E : (N → K) → Submodule K V := fun χ => ⨅ n, (f n).eigenspace (χ n)
  have hEG (χ : N → K) : E χ = ⨅ n, (f n).maxGenEigenspace (χ n) := by
    simp only [E, (hss _).maxGenEigenspace_eq_eigenspace]
  have hind : iSupIndep E := by
    have := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
      fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
    rwa [show E = fun χ : N → K => ⨅ n, (f n).maxGenEigenspace (χ n) from funext hEG]
  have htop : ⨆ χ, E χ = ⊤ := by
    rw [show E = fun χ : N → K => ⨅ n, (f n).maxGenEigenspace (χ n) from funext hEG]
    exact Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f (fun i j _ => hcomm i j) fun i => Module.End.iSup_maxGenEigenspace_eq_top _
  have hmem (χ : N → K) (v : V) : v ∈ E χ ↔ ∀ n : N, ρ n v = χ n • v := by
    simp [E, f]
  have hconj (r : R) (n : N) : (r : Γ)⁻¹ * n * r ∈ N :=
    (Subgroup.mem_normalizer_iff''.mp (hRN r.2) n).mp n.2
  let _ : MulAction R (N → K) :=
    { smul := fun r χ n => χ ⟨(r : Γ)⁻¹ * n * r, hconj r n⟩
      one_smul := fun χ => funext fun n => congrArg χ (Subtype.ext (by simp))
      mul_smul := fun r s χ => funext fun n => congrArg χ (Subtype.ext (by simp [mul_assoc])) }
  refine finrank_eq_card_mul_finrank_invariants_of_iSupIndep (ρ.comp R.subtype) E hind htop
    (fun r χ v hv => ?_) (fun r χ hrχ hE => ?_)
  · rw [hmem] at hv ⊢
    intro n
    have h1 : (n : Γ) * r = r * ((r : Γ)⁻¹ * n * r) := by group
    change ρ n (ρ r v) = χ ⟨_, hconj r n⟩ • ρ r v
    rw [← Module.End.mul_apply, ← map_mul, h1, map_mul, Module.End.mul_apply,
      ← map_smul, ← hv ⟨_, hconj r n⟩]
  · by_contra hr
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE
    rw [hmem] at hv
    have hχ (n : N) : χ ⟨(r : Γ)⁻¹ * n * r, hconj r n⟩ = χ n := congrFun hrχ n
    have hne (n : N) : χ n ≠ 0 := fun h0 => hv0 <| by
      simpa [h0] using congrArg (ρ (n : Γ)⁻¹) (hv n)
    have hinv (n : N) : ρ (n : Γ)⁻¹ v = (χ n)⁻¹ • v := by
      rw [eq_inv_smul_iff₀ (hne n), ← map_smul, ← hv n, Representation.inv_self_apply]
    let c : N → N := fun n => n⁻¹ * ⟨(r : Γ)⁻¹ * n * r, hconj r n⟩
    have hc : Function.Injective c := by
      intro a b hab
      have h : (a : Γ)⁻¹ * ((r : Γ)⁻¹ * a * r) = (b : Γ)⁻¹ * ((r : Γ)⁻¹ * b * r) := by
        simpa [c] using congrArg Subtype.val hab
      have h1 : (r : Γ)⁻¹ * a * r = a * ((b : Γ)⁻¹ * ((r : Γ)⁻¹ * b * r)) := by
        rw [← h]
        group
      have h2 : (r : Γ)⁻¹ * (a * (b : Γ)⁻¹) * (r : Γ)⁻¹⁻¹ = a * (b : Γ)⁻¹ :=
        calc (r : Γ)⁻¹ * (a * (b : Γ)⁻¹) * (r : Γ)⁻¹⁻¹
            = ((r : Γ)⁻¹ * a * r) * ((r : Γ)⁻¹ * (b : Γ)⁻¹ * r) := by group
          _ = a * ((b : Γ)⁻¹ * ((r : Γ)⁻¹ * b * r)) * ((r : Γ)⁻¹ * (b : Γ)⁻¹ * r) := by
            rw [h1]
          _ = a * (b : Γ)⁻¹ := by group
      have hr' : (r : Γ)⁻¹ ≠ 1 := inv_ne_one.mpr fun h => hr (Subtype.ext h)
      exact Subtype.ext <| mul_inv_eq_one.mp <|
        hfpf _ (R.inv_mem r.2) hr' _ (N.mul_mem a.2 (N.inv_mem b.2)) h2
    have hcv (n : N) : ρ (c n : Γ) v = v := by
      change ρ ((n : Γ)⁻¹ * ((r : Γ)⁻¹ * n * r)) v = v
      rw [map_mul, Module.End.mul_apply, hv ⟨_, hconj r n⟩, map_smul, hinv, smul_smul, hχ,
        mul_inv_cancel₀ (hne n), one_smul]
    refine hv0 (hCN v fun m hm => ?_)
    obtain ⟨n, hn⟩ := Finite.injective_iff_surjective.mp hc ⟨m, hm⟩
    simpa [hn] using hcv n

end CFSG.Walter

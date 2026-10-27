module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.HeisenbergDefs
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

public section

namespace CFSG.StandardType.ClassicalPosition.HeisRank

private lemma heisJoint_coe_pow {F V : Type} [Semiring F] [AddCommMonoid V] [Module F V]
    (e : V ≃ₗ[F] V) (n : ℕ) :
    ((e : V →ₗ[F] V) ^ n) = ((e ^ n : V ≃ₗ[F] V) : V →ₗ[F] V) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]

private lemma heisJoint_isSemisimple {F V : Type} [Field F]
    [AddCommGroup V] [Module F V] {p : ℕ} (hp : (p : F) ≠ 0) (e : V ≃ₗ[F] V) (c : F)
    (hc : ∀ v, (e ^ p) v = c • v) (hc0 : c ≠ 0) :
    Module.End.IsSemisimple (e : V →ₗ[F] V) := by
  have hcoe : ((e : V →ₗ[F] V) ^ p) = c • 1 := by
    ext v
    rw [heisJoint_coe_pow, LinearEquiv.coe_coe, hc v]
    rfl
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.Separable.squarefree (Polynomial.separable_X_pow_sub_C c hp hc0)) ?_
  rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, hcoe, sub_self]

theorem exists_joint_eigen {F V G : Type} [Field F] [IsAlgClosed F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Group G] {p : ℕ} (hp : (p : F) ≠ 0)
    (φ : G →* (V ≃ₗ[F] V)) (hpow : ∀ g, φ g ^ p ∈ scalarAut F V)
    (hc : ∀ g h, φ g * φ h = φ h * φ g) :
    ∃ T : Type, Finite T ∧ ∃ (W : T → Submodule F V) (χ : T → G → F),
      (∀ t, W t ≠ ⊥) ∧ iSupIndep W ∧ ⨆ t, W t = ⊤ ∧
        ∀ t g, ∀ v ∈ W t, φ g v = χ t g • v := by
  classical
  by_cases hV : Subsingleton V
  · refine ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, ?_, ?_, ?_, ?_⟩
    · intro t; exact t.elim
    · rw [iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero]
      intro s v _ _ i _
      exact i.elim
    · have hbot : (⊤ : Submodule F V) = ⊥ :=
        (Submodule.eq_bot_iff _).mpr fun x _ => Subsingleton.elim x 0
      rw [iSup_of_empty]
      exact hbot.symm
    · intro t; exact t.elim
  · haveI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
    let f : G → Module.End F V := fun g => (φ g : V →ₗ[F] V)
    have hfcomm : Pairwise fun g h : G => Commute (f g) (f h) := by
      intro g h _
      show f g * f h = f h * f g
      have hh := congrArg (fun e : V ≃ₗ[F] V => (e : V →ₗ[F] V)) (hc g h)
      simpa only [f, LinearEquiv.coe_toLinearMap_mul] using hh
    have hfss : ∀ g, (f g).IsSemisimple := by
      intro g
      obtain ⟨c, hc'⟩ := (mem_scalarAut_iff (g := φ g ^ p)).mp (hpow g)
      have hc0 : c ≠ 0 := by
        rintro rfl
        obtain ⟨v, hv⟩ := exists_ne (0 : V)
        have hz : (φ g ^ p) v = (φ g ^ p) 0 := by
          rw [hc' v, hc' 0, zero_smul, smul_zero]
        exact hv ((φ g ^ p).injective hz)
      exact heisJoint_isSemisimple hp (φ g) c hc' hc0
    have hspan : (⨆ χ : G → F, ⨅ g, (f g).eigenspace (χ g)) = ⊤ :=
      TauCeti.iSup_iInf_eigenspace_eq_top_of_isSemisimple f hfcomm hfss
    have hind : iSupIndep (fun χ : G → F => ⨅ g, (f g).eigenspace (χ g)) :=
      TauCeti.iSupIndep_iInf_eigenspace f
    let T := {χ : G → F // (⨅ g, (f g).eigenspace (χ g)) ≠ ⊥}
    let W : T → Submodule F V := fun t => ⨅ g, (f g).eigenspace (t.1 g)
    let χ : T → G → F := fun t => t.1
    have hFin : Finite T := by
      haveI : Fintype T := hind.fintypeNeBotOfFiniteDimensional
      exact Finite.of_fintype T
    have hWne : ∀ t, W t ≠ ⊥ := fun t => t.2
    have hindW : iSupIndep W := hind.comp Subtype.val_injective
    have hsup : ⨆ t : T, W t = ⊤ := by
      rw [← hspan]
      exact iSup_ne_bot_subtype (fun χ : G → F => ⨅ g, (f g).eigenspace (χ g))
    refine ⟨T, hFin, W, χ, hWne, hindW, hsup, ?_⟩
    intro t g v hv
    have hv' : v ∈ (f g).eigenspace (t.1 g) := (Submodule.mem_iInf _).mp hv g
    have hmem := Module.End.mem_eigenspace_iff.mp hv'
    simpa only [f, χ, LinearEquiv.coe_coe] using hmem

end CFSG.StandardType.ClassicalPosition.HeisRank

module

public import CFSG.Quasithin.SteinbergCBGDRep
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.JacobsonDensity
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

public section

namespace CFSG.Quasithin.SteinbergCB.GDescent

open Matrix

variable {F : Type*} [Field F] {X : Type*} [Group X] {d : ℕ}

theorem isUnit_of_intertw {ρ ρ' : X →* GL (Fin d) F} (hρ : IsIrredRep ρ)
    {T : Matrix (Fin d) (Fin d) F}
    (hT : ∀ g, T * (ρ g : Matrix (Fin d) (Fin d) F) = (ρ' g : Matrix (Fin d) (Fin d) F) * T)
    (hT0 : T ≠ 0) : IsUnit T := by
  have hW : ∀ g, ∀ w ∈ LinearMap.ker (Matrix.toLin' T),
      (ρ g : Matrix (Fin d) (Fin d) F) *ᵥ w ∈ LinearMap.ker (Matrix.toLin' T) := by
    intro g w hw
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hw ⊢
    rw [Matrix.mulVec_mulVec, hT g, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  rcases hρ _ hW with h | h
  · rw [← Matrix.mulVec_injective_iff_isUnit]
    have hinj := LinearMap.ker_eq_bot.1 h
    intro v w hvw
    apply hinj
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact hvw
  · exfalso
    apply hT0
    rw [LinearMap.ker_eq_top] at h
    exact Matrix.toLin'.injective (h.trans (map_zero _).symm)

theorem exists_smul_one_of_comm [IsAlgClosed F] (hd : 1 ≤ d) {ρ : X →* GL (Fin d) F}
    (hρ : IsIrredRep ρ) {T : Matrix (Fin d) (Fin d) F}
    (hT : ∀ g, T * (ρ g : Matrix (Fin d) (Fin d) F) = (ρ g : Matrix (Fin d) (Fin d) F) * T) :
    ∃ c : F, T = c • (1 : Matrix (Fin d) (Fin d) F) := by
  have : Nontrivial (Fin d → F) := by
    have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    infer_instance
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' T)
  refine ⟨c, ?_⟩
  by_contra hne
  have hT' : T - c • (1 : Matrix (Fin d) (Fin d) F) ≠ 0 := sub_ne_zero.2 hne
  have hint : ∀ g, (T - c • (1 : Matrix (Fin d) (Fin d) F)) * (ρ g : Matrix (Fin d) (Fin d) F) =
      (ρ g : Matrix (Fin d) (Fin d) F) * (T - c • (1 : Matrix (Fin d) (Fin d) F)) := by
    intro g
    rw [sub_mul, mul_sub, hT g, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hu := isUnit_of_intertw hρ hint hT'
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hTv : (T - c • (1 : Matrix (Fin d) (Fin d) F)) *ᵥ v = 0 := by
    have h1 := Module.End.mem_eigenspace_iff.1 hv.1
    rw [Matrix.toLin'_apply] at h1
    rw [Matrix.sub_mulVec, h1, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  have hinj := Matrix.mulVec_injective_iff_isUnit.2 hu
  exact hv.2 (hinj (hTv.trans (Matrix.mulVec_zero _).symm))

@[expose] noncomputable def repOf (ρ : X →* GL (Fin d) F) : Representation F X (Fin d → F) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) F ≃ₐ[F] _).toMulEquiv.toMonoidHom.comp
    ((Units.coeHom (Matrix (Fin d) (Fin d) F)).comp ρ)

theorem repOf_apply (ρ : X →* GL (Fin d) F) (g : X) (v : Fin d → F) :
    repOf ρ g v = (ρ g : Matrix (Fin d) (Fin d) F) *ᵥ v :=
  Matrix.toLinAlgEquiv'_apply _ v

theorem repOf_eq (ρ : X →* GL (Fin d) F) (g : X) :
    repOf ρ g = Matrix.toLin' (ρ g : Matrix (Fin d) (Fin d) F) := by
  apply LinearMap.ext
  intro v
  rw [repOf_apply, Matrix.toLin'_apply]

theorem isIrreducible_repOf (hd : 1 ≤ d) {ρ : X →* GL (Fin d) F} (hρ : IsIrredRep ρ) :
    (repOf ρ).IsIrreducible := by
  have : Nontrivial (Fin d → F) := by
    have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    infer_instance
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun W => ?_ }
  · have h' := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top h'
  · have hW : ∀ g, ∀ w ∈ W.toSubmodule, (ρ g : Matrix (Fin d) (Fin d) F) *ᵥ w ∈ W.toSubmodule := by
      intro g w hw
      rw [← repOf_apply]
      exact W.apply_mem_toSubmodule g hw
    rcases hρ _ hW with h | h
    · exact Or.inl (Subrepresentation.ext h)
    · exact Or.inr (Subrepresentation.ext h)

theorem span_range_eq_top [IsAlgClosed F] (hd : 1 ≤ d) {ρ : X →* GL (Fin d) F}
    (hρ : IsIrredRep ρ) :
    Submodule.span F (Set.range fun g => (ρ g : Matrix (Fin d) (Fin d) F)) = ⊤ := by
  have : (repOf ρ).IsIrreducible := isIrreducible_repOf hd hρ
  have hadj := CFSG.Theory.Representation.jacobson_density_surjective_isAlgClosed_rep (repOf ρ)
  have hspan : Submodule.span F (Set.range (repOf ρ)) = ⊤ := by
    have h1 := Algebra.adjoin_eq_span F (Set.range (repOf ρ))
    rw [hadj, ← MonoidHom.coe_mrange, Submonoid.closure_eq, Algebra.top_toSubmodule] at h1
    exact h1.symm
  have hrange : Set.range (fun g => (ρ g : Matrix (Fin d) (Fin d) F)) =
      (((Matrix.toLin' : Matrix (Fin d) (Fin d) F ≃ₗ[F] _).symm : _ →ₗ[F] _)) ''
        Set.range (repOf ρ) := by
    ext M
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨repOf ρ g, ⟨g, rfl⟩, by
        rw [LinearEquiv.coe_coe, repOf_eq, LinearEquiv.symm_apply_apply]⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, by rw [LinearEquiv.coe_coe, repOf_eq, LinearEquiv.symm_apply_apply]⟩
  rw [hrange, ← Submodule.map_span, hspan, Submodule.map_top, LinearEquiv.range]

end CFSG.Quasithin.SteinbergCB.GDescent

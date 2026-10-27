module

public import CFSG.ThirdParty.BrauerInduction.Background.LinearChar.OneDimensional
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.AbelianGroup
public import TauCeti.RepresentationTheory.Induction.Clifford.Equivalence

public section

namespace CFSG.RepresentationTheory

universe u v

open CategoryTheory
open scoped MonoidAlgebra

theorem normal_abelian_scalar_of_small_permutation
    {k : Type u} {G : Type v} {V : Type u} [Field k] [IsAlgClosed k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [Module.Finite k V] [Nontrivial V]
    (rho : Representation k G V) (hirr : rho.IsIrreducible)
    (hperm : ∀ (Omega : Type*) [Finite Omega],
      Nat.card Omega ≤ Module.finrank k V → ∀ phi : G →* Equiv.Perm Omega, phi = 1)
    (A : Subgroup G) [A.Normal] (hA : IsMulCommutative A) :
    ∀ a : A, ∃ c : k, rho (a : G) = c • (1 : Module.End k V) := by
  classical
  let W : FDRep k G := FDRep.of rho
  have hWρ : W.ρ = rho := rfl
  have : Representation.IsIrreducible W.ρ := by
    rw [hWρ]
    exact hirr
  have : Simple W := FDRep.simple_of_isIrreducible W
  let rhoA : Representation k A V := rho.comp A.subtype
  obtain ⟨σ, hσ⟩ := Representation.exists_isAtom rhoA
  let σFD : FDRep k A := FDRep.of σ.toRepresentation
  have hσirr : Representation.IsIrreducible σFD.ρ :=
    Representation.isIrreducible_toRepresentation_of_isAtom hσ
  have : Simple σFD := FDRep.simple_of_isIrreducible σFD
  have hdimσ : Module.finrank k σFD = 1 := FDRep.abelian_simple_is_linear σFD
  obtain ⟨hfinite, e, he, hiso⟩ :=
    FDRep.clifford_restrict_iso_of_isAtom W σ hσ
  let _ : Finite (G ⧸ TauCeti.inertia σFD) := hfinite
  obtain ⟨iso⟩ := hiso
  have hdimW : Module.finrank k W = Nat.card (G ⧸ TauCeti.inertia σFD) * e * 1 := by
    calc
      Module.finrank k W = Module.finrank k (TauCeti.resFDRep A W) := rfl
      _ = Module.finrank k (σFD.cliffordSum e) := (FDRep.isoToLinearEquiv iso).finrank_eq
      _ = Nat.card (G ⧸ TauCeti.inertia σFD) * e * Module.finrank k σFD :=
        FDRep.finrank_cliffordSum σFD e
      _ = Nat.card (G ⧸ TauCeti.inertia σFD) * e * 1 := by rw [hdimσ]
  have hdimW' : Module.finrank k V = Nat.card (G ⧸ TauCeti.inertia σFD) * e * 1 := by
    simpa using hdimW
  have hcard_le : Nat.card (G ⧸ TauCeti.inertia σFD) ≤ Module.finrank k V := by
    rw [hdimW', mul_one]
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero he)
  let : Fintype (G ⧸ TauCeti.inertia σFD) := Fintype.ofFinite _
  let Ω := ULift (Fin (Fintype.card (G ⧸ TauCeti.inertia σFD)))
  let eΩ : Ω ≃ (G ⧸ TauCeti.inertia σFD) :=
    Equiv.ulift.trans (Fintype.equivFin _).symm
  let φ : G →* Equiv.Perm Ω :=
    (eΩ.symm.permCongrHom).toMonoidHom.comp
      (MulAction.toPermHom G (G ⧸ TauCeti.inertia σFD))
  have hcardΩ : Nat.card Ω ≤ Module.finrank k V := by
    rw [Nat.card_congr eΩ]
    exact hcard_le
  have hφ : φ = 1 := hperm Ω hcardΩ φ
  have htriv : MulAction.toPermHom G (G ⧸ TauCeti.inertia σFD) = 1 := by
    apply MonoidHom.ext
    intro g
    have hg := congrArg (fun ψ : G →* Equiv.Perm Ω => ψ g) hφ
    have hg' : eΩ.symm.permCongr (MulAction.toPerm g) = 1 := by
      simpa [φ] using hg
    rw [Equiv.apply_eq_iff_eq_symm_apply] at hg'
    rw [Equiv.permCongr_symm] at hg'
    have h1 : eΩ.symm.symm.permCongr (1 : Equiv.Perm Ω) = 1 := by
      change eΩ.permCongr (Equiv.refl Ω) = Equiv.refl (G ⧸ TauCeti.inertia σFD)
      exact Equiv.permCongr_refl eΩ
    rw [h1] at hg'
    simpa using hg'
  have hnc : (TauCeti.inertia σFD).normalCore = ⊤ := by
    rw [Subgroup.normalCore_eq_ker, htriv]
    simp
  have hItop : TauCeti.inertia σFD = ⊤ := by
    exact top_le_iff.mp (hnc ▸ Subgroup.normalCore_le (TauCeti.inertia σFD))
  have hconj : ∀ g : G, Nonempty
      ((TauCeti.Representation.conjSubrep rho g σ).asSubmodule ≃ₗ[k[A]] σ.asSubmodule) := by
    intro g
    exact (Representation.mem_inertia_fdRepOf_toRepresentation_iff
      (ρ := rho) (N := A) (V := V) g σ).mp (by rw [hItop]; exact Subgroup.mem_top g)
  have hisoType : IsIsotypicOfType k[A]
      (Representation.asModule rhoA) σ.asSubmodule :=
    (TauCeti.Representation.isIsotypicOfType_asSubmodule_iff
      (ρ := rho) (N := A) (V := V) (σ := σ) hσ).mpr hconj
  obtain ⟨ψ, ⟨eψ⟩⟩ := FDRep.exists_iso_ofLinearChar_of_finrank_one σFD hdimσ
  have hσ_scalar_rep (a : A) :
      σ.toRepresentation a = (ψ a : k) • (1 : Module.End k σ.toSubmodule) := by
    ext t
    let E : σ.toSubmodule ≃ₗ[k] k := FDRep.isoToLinearEquiv eψ
    have hconj' := congrArg (fun f : Module.End k (FDRep.ofLinearChar ψ) => f (E t))
      (FDRep.Iso.conj_ρ eψ a)
    simp only [LinearEquiv.conj_apply_apply] at hconj'
    rw [LinearMap.smul_apply, Module.End.one_apply]
    rw [← Subtype.ext_iff]
    apply E.injective
    rw [map_smul]
    simpa [σFD, E, FDRep.of_ρ', smul_eq_mul] using hconj'.symm
  have hσ_scalar_asModule (a : A) (s : σ.toRepresentation.asModule) :
      (MonoidAlgebra.single a (1 : k)) • s =
        (MonoidAlgebra.single (1 : A) ((ψ a : k)) : k[A]) • s := by
    apply σ.toRepresentation.asModuleEquiv.injective
    calc
      σ.toRepresentation.asModuleEquiv ((MonoidAlgebra.single a (1 : k)) • s)
          = σ.toRepresentation a (σ.toRepresentation.asModuleEquiv s) := by
            rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single]
            simp
      _ = (ψ a : k) • (σ.toRepresentation.asModuleEquiv s) := by
            rw [LinearMap.congr_fun (hσ_scalar_rep a) (σ.toRepresentation.asModuleEquiv s)]
            rfl
      _ = σ.toRepresentation.asModuleEquiv
            ((MonoidAlgebra.single (1 : A) ((ψ a : k)) : k[A]) • s) := by
            rw [show (MonoidAlgebra.single (1 : A) ((ψ a : k)) : k[A]) =
              algebraMap k k[A] (ψ a) by simp [MonoidAlgebra.coe_algebraMap]]
            rw [IsScalarTower.algebraMap_smul, map_smul]
  have hσ_scalar_asSubmodule (a : A) (s : σ.asSubmodule) :
      (MonoidAlgebra.single a (1 : k)) • s =
        (MonoidAlgebra.single (1 : A) ((ψ a : k)) : k[A]) • s := by
    have h := hσ_scalar_asModule a (σ.asModuleEquivAsSubmodule.symm s)
    have h' := congrArg σ.asModuleEquivAsSubmodule h
    simpa only [map_smul, LinearEquiv.apply_symm_apply] using h'
  have hss : IsSemisimpleModule k[A] (Representation.asModule rhoA) := by
    rw [← Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
    exact TauCeti.Representation.isSemisimpleRepresentation_comp_subtype rho
  have : Module.Finite k[A] (Representation.asModule rhoA) :=
    Module.Finite.of_restrictScalars_finite k k[A] _
  obtain ⟨n, ⟨eM⟩⟩ := hisoType.linearEquiv_fun
  have hM_scalar_algebraMap (a : A) (x : Representation.asModule rhoA) :
      (MonoidAlgebra.single a (1 : k)) • x =
        (MonoidAlgebra.single (1 : A) ((ψ a : k)) : k[A]) • x := by
    apply eM.injective
    have hpoint : ∀ y : Fin n → σ.asSubmodule,
        (MonoidAlgebra.single a (1 : k)) • y =
          (MonoidAlgebra.single (1 : A) ((ψ a : k)) : k[A]) • y := by
      intro y
      funext i
      exact hσ_scalar_asSubmodule a (y i)
    calc
      eM ((MonoidAlgebra.single a (1 : k)) • x) =
          (MonoidAlgebra.single a (1 : k)) • eM x := eM.map_smul _ _
      _ = (MonoidAlgebra.single (1 : A) ((ψ a : k)) : k[A]) • eM x := hpoint (eM x)
      _ = eM ((MonoidAlgebra.single (1 : A) ((ψ a : k)) : k[A]) • x) := (eM.map_smul _ _).symm
  have hM_scalar (a : A) (x : Representation.asModule rhoA) :
      (MonoidAlgebra.single a (1 : k)) • x = (ψ a : k) • x := by
    have hsingle : (MonoidAlgebra.single (1 : A) ((ψ a : k)) : k[A]) =
        algebraMap k k[A] (ψ a) := by
      simp [MonoidAlgebra.coe_algebraMap]
    have h := hM_scalar_algebraMap a x
    rw [hsingle, IsScalarTower.algebraMap_smul] at h
    exact h
  intro a
  refine ⟨ψ a, ?_⟩
  ext v
  have h := hM_scalar a (rhoA.asModuleEquiv.symm v)
  have h' := congrArg (fun x => (rhoA.asModuleEquiv x : V)) h
  rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single] at h'
  rw [LinearEquiv.apply_symm_apply, map_smul, LinearEquiv.apply_symm_apply] at h'
  simpa [rhoA] using h'

end CFSG.RepresentationTheory

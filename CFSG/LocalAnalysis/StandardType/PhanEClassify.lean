module

public import CFSG.LocalAnalysis.StandardType.PhanELocalParts

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding

section Transport

variable {I I' C D : Type}

theorem exists_chamberIso_restrict (X : ChamberSystem I C) (Y : ChamberSystem I' D) {R A : Set C}
    {B : Set D} (h : ChamberIso (X.restrict R) Y) (hAR : A ⊆ R)
    (hAB : ∀ c : ↥R, (c : C) ∈ A ↔ h.Φ c ∈ B) :
    Nonempty (ChamberIso (X.restrict A) (Y.restrict B)) := by
  let incl : ↥A ≃ {c : ↥R // (c : C) ∈ A} :=
    { toFun := fun a => ⟨⟨a.1, hAR a.2⟩, a.2⟩
      invFun := fun s => ⟨s.1.1, s.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨⟨h.e, incl.trans (Equiv.subtypeEquiv h.Φ hAB), fun i x y => ?_⟩⟩
  exact h.adj_iff i ⟨x.1, hAR x.2⟩ ⟨y.1, hAR y.2⟩

end Transport

section Residue

variable {ι : Type} {M : CoxeterMatrix ι} {W : Type} [Group W] (cs : CoxeterSystem M W)
  {C : Type} (δ : C → C → W)

@[expose] def buildingOver (J : Set ι) : ChamberSystem ↥J C where
  adj j y z := panelRel cs δ j y z
  equivalence _ := Relation.EqvGen.is_equivalence _

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2] (t : C → C) (J : Set ι) (a : C)

@[expose] def PhanEResidueModel (code : PhanCode) : Prop :=
  ∃ h : ChamberIso ((buildingOver cs δ J).restrict (residue cs δ J a)) (code.sys K),
    ∀ c : ↥(residue cs δ J a), (c : C) ∈ flipMaxSet cs δ t J a ↔ h.Φ c ∈ code.set K f

end Residue

@[expose] def PhanEResidueModels (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2] {n : ℕ}
    (M : CoxeterMatrix (Fin n)) {C : Type} (δ : C → C → M.Group) (t : C → C) : Prop :=
  ∀ (J : Set (Fin n)) (a : C), (J.ncard = 2 ∨ J.ncard = 3) →
    ∃ code : PhanCode, code.rank = J.ncard ∧
      PhanEResidueModel M.toCoxeterSystem δ K f t J a code

theorem phanEClassifiedAt_of_residueModels (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]
    {n : ℕ} (M : CoxeterMatrix (Fin n)) {C : Type} (δ : C → C → M.Group) (t : C → C)
    (h : PhanEResidueModels K f M δ t) : PhanEClassifiedAt K f M δ t := by
  have key : ∀ (J : Set (Fin n)) (a : C) (r : ℕ), (J.ncard = 2 ∨ J.ncard = 3) → J.ncard = r →
      ∃ code : PhanCode, code.rank = r ∧ Nonempty (ChamberIso
        (inducedSystem M.toCoxeterSystem δ J (flipMaxSet M.toCoxeterSystem δ t J a))
        ((code.sys K).restrict (code.set K f))) := by
    intro J a r hJ hr
    obtain ⟨code, hrank, hchart, hset⟩ := h J a hJ
    refine ⟨code, hrank.trans hr, ?_⟩
    exact exists_chamberIso_restrict (buildingOver M.toCoxeterSystem δ J) (code.sys K) hchart
      (fun y hy => hy.1) hset
  exact ⟨fun J x hJ => key J x 2 (Or.inl hJ) hJ, fun J x hJ => key J x 3 (Or.inr hJ) hJ⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end

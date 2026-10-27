module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Isotypic
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ConjugateRep
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SubrepresentationLattice
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.RepEquiv

namespace CFSG
end CFSG
open CFSG

/-!
# Clifford theory

Isaacs, *Character Theory of Finite Groups*, Theorem 6.5: the irreducible
constituents of the restriction to a normal subgroup form an internal direct
sum, every summand is a conjugate subrepresentation, and conjugate
constituents occur with equal multiplicities.
-/

noncomputable section

open scoped DirectSum MonoidAlgebra
namespace CFSG.Theory.Representation

open _root_.Representation


private theorem exists_supIndep_subset_sup_eq
    {ι α : Type*} [DecidableEq ι] [Lattice α] [OrderBot α] [IsModularLattice α]
    (s : Finset ι) (f : ι → α)
    (hf : ∀ i ∈ s, IsAtom (f i)) :
    ∃ t ⊆ s, t.SupIndep f ∧ t.sup f = s.sup f := by
  induction s using Finset.induction with
  | empty =>
      exact ⟨∅, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨t, hts, htind, htsup⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      by_cases hle : f a ≤ t.sup f
      · refine ⟨t, hts.trans (Finset.subset_insert a s), htind, ?_⟩
        rw [Finset.sup_insert, ← htsup]
        exact (sup_eq_right.mpr hle).symm
      · refine ⟨insert a t, Finset.insert_subset
          (Finset.mem_insert_self a s) (hts.trans (Finset.subset_insert a s)), ?_, ?_⟩
        · exact htind.insert ((hf a (Finset.mem_insert_self a s)).not_le_iff_disjoint.mp hle)
        · rw [Finset.sup_insert, Finset.sup_insert, htsup]

private theorem iSup_conjugateSubrepresentations_eq_top
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (H : Subgroup G) [H.Normal]
    (hrho : Representation.IsIrreducible rho)
    (W : Subrepresentation (rho.comp H.subtype))
    (hW : Representation.IsIrreducible W.toRepresentation) :
    (⨆ g : G, Theory.Representation.conjugateSubrepresentation rho H W g) = ⊤ := by
  let rhoH : Representation F H V := rho.comp H.subtype
  let U : G → Subrepresentation rhoH :=
    fun g => Theory.Representation.conjugateSubrepresentation rho H W g
  have hstable (x : G) :
      Theory.Representation.conjugateSubrepresentationOrderIso rho H x (⨆ g, U g) ≤
        ⨆ g, U g := by
    rw [OrderIso.map_iSup]
    refine iSup_le fun g => ?_
    rw [show U g =
      Theory.Representation.conjugateSubrepresentationOrderIso rho H g⁻¹ W by simp [U]]
    rw [← Theory.Representation.conjugateSubrepresentationOrderIso_mul]
    refine le_iSup_of_le ((x * g⁻¹)⁻¹) ?_
    simp [U]
  let T : Subrepresentation rho := {
    toSubmodule := (⨆ g, U g).toSubmodule
    apply_mem_toSubmodule x v hv := by
      have hvmap : rho x v ∈ Submodule.map (rho x) (⨆ g, U g).toSubmodule :=
        ⟨v, hv, rfl⟩
      rw [← Theory.Representation.conjugateSubrepresentationOrderIso_toSubmodule] at hvmap
      exact hstable x hvmap
  }
  have hWatom : IsAtom W :=
    (Subrepresentation.irreducible_iff_isAtom W).mp hW
  have hUone : U 1 = W := by
    apply Subrepresentation.toSubmodule_injective
    simp [U, Module.End.one_eq_id]
  have hWle : W ≤ ⨆ g, U g := by
    refine le_iSup_of_le 1 ?_
    exact hUone.ge
  have hspan_ne : (⨆ g, U g) ≠ ⊥ := by
    intro hbot
    exact hWatom.ne_bot (le_bot_iff.mp (hWle.trans_eq hbot))
  have hTne : T ≠ ⊥ := by
    intro hbot
    apply hspan_ne
    apply Subrepresentation.toSubmodule_injective
    change T.toSubmodule = (⊥ : Subrepresentation rho).toSubmodule
    exact congrArg Subrepresentation.toSubmodule hbot
  have : Representation.IsIrreducible rho := hrho
  have hTtop : T = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top T).resolve_left hTne
  apply Subrepresentation.toSubmodule_injective
  change T.toSubmodule = (⊤ : Subrepresentation rho).toSubmodule
  exact congrArg Subrepresentation.toSubmodule hTtop

private noncomputable def isaacs_6_5_ofSubmodule'_repEquiv
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V)
    {U W : Submodule (MonoidAlgebra F G) rho.asModule}
    (e : U ≃ₗ[MonoidAlgebra F G] W) :
    (Subrepresentation.ofSubmodule' U).toRepresentation ≃ₗ
      (Subrepresentation.ofSubmodule' W).toRepresentation := by
  refine Theory.Representation.RepEquiv.mk (e.restrictScalars F) ?_
  intro g
  apply LinearMap.ext
  intro v
  let v' : U := ⟨v.1, v.2⟩
  apply Subtype.ext
  calc
    rho.asModuleEquiv ↑(e (((Subrepresentation.ofSubmodule' U).toRepresentation g) v)) =
        rho.asModuleEquiv ↑(e ((MonoidAlgebra.single g (1 : F)) • v')) := by
      have hv' :
          (((Subrepresentation.ofSubmodule' U).toRepresentation g) v) =
            ((MonoidAlgebra.single g (1 : F)) • v' : U) := by
        have hsingle :
            ((MonoidAlgebra.single g (1 : F)) • v' : U) =
              (Subrepresentation.ofSubmodule' U).toRepresentation g v' := by
          apply Subtype.ext
          simp only [SetLike.val_smul, Representation.single_smul, one_smul]
          rfl
        rw [hsingle]
        rfl
      exact congrArg (fun z => rho.asModuleEquiv ↑(e z)) hv'
    _ = rho.asModuleEquiv ↑((MonoidAlgebra.single g (1 : F)) • e v') := by
      exact congrArg (fun z => rho.asModuleEquiv (Subtype.val z))
        (e.map_smul (MonoidAlgebra.single g (1 : F)) v')
    _ = rho g (rho.asModuleEquiv ↑(e v')) := by
      simp only [SetLike.val_smul, Representation.single_smul, one_smul]
      rfl
    _ = rho g (rho.asModuleEquiv ↑(e v)) := by rfl
set_option backward.isDefEq.respectTransparency false in
private theorem isaacs_6_5_nonempty_repEquiv_iff_asSubmodule_linearEquiv
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    {rho : Representation F G V}
    (U W : Subrepresentation rho) :
    Nonempty (U.toRepresentation ≃ₗ W.toRepresentation) ↔
      Nonempty (U.asSubmodule ≃ₗ[MonoidAlgebra F G] W.asSubmodule) := by
  constructor
  · rintro ⟨e⟩
    let eMod : U.toRepresentation.asModule ≃ₗ[MonoidAlgebra F G]
        W.toRepresentation.asModule :=
      LinearEquiv.ofBijective
        (Theory.Representation.RepMap.equivLinearMapAsModule
          U.toRepresentation W.toRepresentation e.toRepMap)
        e.bijective
    let f : U.asSubmodule →ₗ[MonoidAlgebra F G] W.asSubmodule := {
      toFun v := ⟨(e ⟨v.1, v.2⟩).1, (e ⟨v.1, v.2⟩).2⟩
      map_add' x y := by
        apply Subtype.ext
        exact congrArg Subtype.val (e.map_add (⟨x.1, x.2⟩ : U) (⟨y.1, y.2⟩ : U))
      map_smul' a x := by
        induction a using MonoidAlgebra.induction_linear with
        | zero =>
            apply Subtype.ext
            exact congrArg Subtype.val e.map_zero
        | add a b ha hb =>
            let xa : U := ⟨(a • x).1, (a • x).2⟩
            let xb : U := ⟨(b • x).1, (b • x).2⟩
            have headd := congrArg Subtype.val (e.map_add xa xb)
            have hsum := congrArg₂ (· + ·) (congrArg Subtype.val ha)
              (congrArg Subtype.val hb)
            simp only [RingHom.id_apply, add_smul]
            apply Subtype.ext
            exact headd.trans hsum
        | single g r =>
            let x' : U.toRepresentation.asModule := ⟨x.1, x.2⟩
            have hm := eMod.map_smul (MonoidAlgebra.single g r) x'
            apply Subtype.ext
            simp only [RingHom.id_apply, SetLike.val_smul,
              Representation.single_smul] at hm ⊢
            exact congrArg Subtype.val hm }
    refine ⟨LinearEquiv.ofBijective f ?_⟩
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply congrArg Subtype.val
      apply e.injective
      apply Subtype.ext
      exact congrArg Subtype.val hxy
    · intro y
      obtain ⟨x, hx⟩ := e.surjective (⟨y.1, y.2⟩ : W)
      refine ⟨⟨x.1, x.2⟩, ?_⟩
      apply Subtype.ext
      exact congrArg Subtype.val hx
  · rintro ⟨e⟩
    change Nonempty
      ((Subrepresentation.ofSubmodule' U.asSubmodule).toRepresentation ≃ₗ
        (Subrepresentation.ofSubmodule' W.asSubmodule).toRepresentation)
    exact ⟨isaacs_6_5_ofSubmodule'_repEquiv rho e⟩
private theorem isaacs_6_5_nonempty_repEquiv_conjugateOrderIso_iff
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (H : Subgroup G) [H.Normal]
    (x : G) (U W : Subrepresentation (rho.comp H.subtype)) :
    Nonempty (U.toRepresentation ≃ₗ W.toRepresentation) ↔
      Nonempty
        ((Theory.Representation.conjugateSubrepresentationOrderIso rho H x U).toRepresentation ≃ₗ
          (Theory.Representation.conjugateSubrepresentationOrderIso rho H x W).toRepresentation) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨Theory.Representation.conjugateSubrepresentationOrderIsoRepEquiv rho H e x⟩
  · rintro ⟨e⟩
    let e' :=
      Theory.Representation.conjugateSubrepresentationOrderIsoRepEquiv rho H e x⁻¹
    have hU :
        Theory.Representation.conjugateSubrepresentationOrderIso rho H x⁻¹
            (Theory.Representation.conjugateSubrepresentationOrderIso rho H x U) = U := by
      rw [← Theory.Representation.conjugateSubrepresentationOrderIso_mul]
      apply Subrepresentation.toSubmodule_injective
      simp [Module.End.one_eq_id]
    have hW :
        Theory.Representation.conjugateSubrepresentationOrderIso rho H x⁻¹
            (Theory.Representation.conjugateSubrepresentationOrderIso rho H x W) = W := by
      rw [← Theory.Representation.conjugateSubrepresentationOrderIso_mul]
      apply Subrepresentation.toSubmodule_injective
      simp [Module.End.one_eq_id]
    rw [hU, hW] at e'
    exact ⟨e'⟩

/-- Isaacs, Character Theory of Finite Groups, Theorem 6.5. -/
public theorem isaacs_theorem_6_5
    {F G V : Type*} [Field F] [Group G] [Finite G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (H : Subgroup G) [H.Normal]
    (hrho : Representation.IsIrreducible rho)
    (W : Subrepresentation (rho.comp H.subtype))
    (hW : Representation.IsIrreducible W.toRepresentation) :
    ∃ n : ℕ, ∃ g : Fin n → G,
      DirectSum.IsInternal (fun i : Fin n =>
        (Theory.Representation.conjugateSubrepresentation rho H W (g i)).asSubmodule) ∧
      (∀ i : Fin n, Representation.IsIrreducible
        (Theory.Representation.conjugateSubrepresentation rho H W (g i)).toRepresentation) ∧
      (∀ i : Fin n, Nonempty
        ((Theory.Representation.conjugateSubrepresentation rho H W (g i)).toRepresentation ≃ₗ
          Theory.Representation.conjugateRep (G := G) (H := H) W.toRepresentation (g i))) ∧
      ∀ {M : Type*} [AddCommGroup M] [Module F M]
        (sigma : Representation F H M),
        (∃ x : G, Nonempty (sigma ≃ₗ
          Theory.Representation.conjugateRep (G := G) (H := H) W.toRepresentation x)) →
        Nat.card {i : Fin n // Nonempty
          ((Theory.Representation.conjugateSubrepresentation rho H W (g i)).toRepresentation ≃ₗ
            W.toRepresentation)} =
        Nat.card {i : Fin n // Nonempty
          ((Theory.Representation.conjugateSubrepresentation rho H W (g i)).toRepresentation ≃ₗ sigma)} := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let rhoH : Representation F H V := rho.comp H.subtype
  let : Module (MonoidAlgebra F H) V :=
    Representation.instModuleMonoidAlgebraAsModule rhoH
  let : Ring (MonoidAlgebra F H) := MonoidAlgebra.ring
  let U : G → Subrepresentation rhoH :=
    fun x => Theory.Representation.conjugateSubrepresentation rho H W x
  have hWatom : IsAtom W :=
    (Subrepresentation.irreducible_iff_isAtom W).mp hW
  have hUatom (x : G) : IsAtom (U x) := by
    rw [show U x =
      Theory.Representation.conjugateSubrepresentationOrderIso rho H x⁻¹ W by simp [U]]
    exact ((Theory.Representation.conjugateSubrepresentationOrderIso rho H x⁻¹).isAtom_iff W).mpr
      hWatom
  let eSub : Subrepresentation rhoH ≃o Submodule (MonoidAlgebra F H) V :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  let Aall : G → Submodule (MonoidAlgebra F H) V :=
    fun x => eSub (U x)
  have hAallAtom (x : G) : IsAtom (Aall x) :=
    (eSub.isAtom_iff (U x)).mpr (hUatom x)
  obtain ⟨S, _hSuniv, hSind, hSsup⟩ :=
    exists_supIndep_subset_sup_eq (Finset.univ : Finset G) Aall
      (fun x _ => hAallAtom x)
  have hunivsup : (Finset.univ : Finset G).sup Aall = ⊤ := by
    calc
      (Finset.univ : Finset G).sup Aall =
          ⨆ x ∈ (Finset.univ : Finset G), Aall x :=
        Finset.sup_eq_iSup _ _
      _ = ⨆ x : G, Aall x := by simp
      _ = ⊤ := by
        change (⨆ x : G, eSub (U x)) = ⊤
        rw [← OrderIso.map_iSup]
        rw [show (⨆ x : G, U x) = ⊤ by
          exact iSup_conjugateSubrepresentations_eq_top rho H hrho W hW]
        exact eSub.map_top
  have hSsupTop : S.sup Aall = ⊤ := hSsup.trans hunivsup
  have hSubtypeSup : (⨆ x : S, Aall x.1) = ⊤ := by
    calc
      (⨆ x : S, Aall x.1) = S.sup Aall := by
        apply le_antisymm
        · exact iSup_le fun x => Finset.le_sup (f := Aall) x.2
        · exact Finset.sup_le fun x hx => le_iSup_of_le ⟨x, hx⟩ le_rfl
      _ = ⊤ := hSsupTop
  let n := Fintype.card S
  let e : Fin n ≃ S := (Fintype.equivFin S).symm
  let g : Fin n → G := fun i => (e i).1
  let A : Fin n → Submodule (MonoidAlgebra F H) V :=
    fun i => Aall (g i)
  have hAind : iSupIndep A := by
    simpa [A, g, Function.comp_def] using hSind.independent.comp e.injective
  have hAsup : (⨆ i : Fin n, A i) = ⊤ := by
    apply top_unique
    rw [← hSubtypeSup]
    exact iSup_le fun x => le_iSup_of_le (e.symm x) (by simp [A, g])
  have hInternal : DirectSum.IsInternal A :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hAind hAsup
  refine ⟨n, g, ?_, ?_, ?_, ?_⟩
  · change DirectSum.IsInternal (fun i : Fin n => eSub (U (g i)))
    simpa [A, Aall, eSub, U] using hInternal
  · intro i
    exact (Subrepresentation.irreducible_iff_isAtom (U (g i))).mpr (hUatom (g i))
  · intro i
    exact ⟨Theory.Representation.conjugateSubrepresentationEquiv rho H W (g i)⟩
  · intro M _ _ sigma hsigma
    obtain ⟨x, ⟨eSigmaConj⟩⟩ := hsigma
    let eSigmaUx : sigma ≃ₗ (U x).toRepresentation :=
      eSigmaConj.trans
        (Theory.Representation.conjugateSubrepresentationEquiv rho H W x).symm
    let C :=
      Theory.Representation.conjugateSubrepresentationOrderIso rho H x
    let Cmod : Submodule (MonoidAlgebra F H) V ≃o
        Submodule (MonoidAlgebra F H) V :=
      eSub.symm |>.trans (C.trans eSub)
    let B : Fin n → Submodule (MonoidAlgebra F H) V :=
      fun i => Cmod (A i)
    have hBind : iSupIndep B := hAind.map_orderIso Cmod
    have hBsup : (⨆ i : Fin n, B i) = ⊤ := by
      change (⨆ i : Fin n, Cmod (A i)) = ⊤
      rw [← OrderIso.map_iSup, hAsup]
      exact Cmod.map_top
    have hBInternal : DirectSum.IsInternal B :=
      DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hBind hBsup
    have hAatom (i : Fin n) : IsAtom (A i) := by
      simpa [A] using hAallAtom (g i)
    have hBatom (i : Fin n) : IsAtom (B i) :=
      (Cmod.isAtom_iff (A i)).mpr (hAatom i)
    have hAsimple (i : Fin n) : IsSimpleModule (MonoidAlgebra F H) (A i) :=
      isSimpleModule_iff_isAtom.mpr (hAatom i)
    have hBsimple (i : Fin n) : IsSimpleModule (MonoidAlgebra F H) (B i) :=
      isSimpleModule_iff_isAtom.mpr (hBatom i)
    have hMsimple : IsSimpleModule (MonoidAlgebra F H) (eSub W) :=
      isSimpleModule_iff_isAtom.mpr ((eSub.isAtom_iff W).mpr hWatom)
    have hmult :=
      (isaacs_lemma_1_13
        (A := MonoidAlgebra F H) (V := V) (M := eSub W)
        hMsimple A hInternal hAsimple).2.2 B hBInternal hBsimple
    have hCUx : C (U x) = W := by
      dsimp [C]
      rw [show U x =
        Theory.Representation.conjugateSubrepresentationOrderIso rho H x⁻¹ W by simp [U]]
      rw [← Theory.Representation.conjugateSubrepresentationOrderIso_mul]
      apply Subrepresentation.toSubmodule_injective
      simp [Module.End.one_eq_id]
    let eCUxW : (C (U x)).toRepresentation ≃ₗ W.toRepresentation := by
      rw [hCUx]
    have hLeft (i : Fin n) :
        Nonempty ((U (g i)).toRepresentation ≃ₗ W.toRepresentation) ↔
          Nonempty ((A i) ≃ₗ[MonoidAlgebra F H] eSub W) := by
      change Nonempty ((U (g i)).toRepresentation ≃ₗ W.toRepresentation) ↔
        Nonempty ((U (g i)).asSubmodule ≃ₗ[MonoidAlgebra F H] W.asSubmodule)
      exact isaacs_6_5_nonempty_repEquiv_iff_asSubmodule_linearEquiv
        (U (g i)) W
    have hRight (i : Fin n) :
        Nonempty ((B i) ≃ₗ[MonoidAlgebra F H] eSub W) ↔
          Nonempty ((U (g i)).toRepresentation ≃ₗ sigma) := by
      constructor
      · intro hBi
        have hCUiW :
            Nonempty
              ((C (U (g i))).toRepresentation ≃ₗ W.toRepresentation) := by
          apply
            (isaacs_6_5_nonempty_repEquiv_iff_asSubmodule_linearEquiv
              (C (U (g i))) W).mpr
          change Nonempty ((B i) ≃ₗ[MonoidAlgebra F H] eSub W)
          exact hBi
        have hCUiCUx :
            Nonempty
              ((C (U (g i))).toRepresentation ≃ₗ
                (C (U x)).toRepresentation) :=
          ⟨hCUiW.some.trans eCUxW.symm⟩
        obtain ⟨eUiUx⟩ :=
          (isaacs_6_5_nonempty_repEquiv_conjugateOrderIso_iff
            rho H x (U (g i)) (U x)).mpr hCUiCUx
        exact ⟨eUiUx.trans eSigmaUx.symm⟩
      · rintro ⟨eUiSigma⟩
        have hUiUx :
            Nonempty ((U (g i)).toRepresentation ≃ₗ (U x).toRepresentation) :=
          ⟨eUiSigma.trans eSigmaUx⟩
        have hCUiCUx :=
          (isaacs_6_5_nonempty_repEquiv_conjugateOrderIso_iff
            rho H x (U (g i)) (U x)).mp hUiUx
        have hCUiW :
            Nonempty
              ((C (U (g i))).toRepresentation ≃ₗ W.toRepresentation) :=
          ⟨hCUiCUx.some.trans eCUxW⟩
        have hLinear :=
          (isaacs_6_5_nonempty_repEquiv_iff_asSubmodule_linearEquiv
            (C (U (g i))) W).mp hCUiW
        change Nonempty ((C (U (g i))).asSubmodule ≃ₗ[MonoidAlgebra F H] W.asSubmodule) at hLinear
        change Nonempty ((B i) ≃ₗ[MonoidAlgebra F H] eSub W)
        exact hLinear
    calc
      Nat.card {i : Fin n // Nonempty
          ((U (g i)).toRepresentation ≃ₗ W.toRepresentation)} =
          Nat.card {i : Fin n // Nonempty
            ((A i) ≃ₗ[MonoidAlgebra F H] eSub W)} :=
        Nat.card_congr (Equiv.subtypeEquivRight hLeft)
      _ = Nat.card {i : Fin n // Nonempty
            ((B i) ≃ₗ[MonoidAlgebra F H] eSub W)} := hmult
      _ = Nat.card {i : Fin n // Nonempty
          ((U (g i)).toRepresentation ≃ₗ sigma)} :=
        Nat.card_congr (Equiv.subtypeEquivRight hRight)

end CFSG.Theory.Representation

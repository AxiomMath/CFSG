module

public import CFSG.LieType.Chevalley.RelativeWeylTwist
public import CFSG.LieType.Chevalley.WeylRootTransport

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {π : Equiv.Perm (Fin τ.rank)}
  (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) (K : Type) [Field K]

@[expose] def permModuleMap : ModGL τ K :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv (Finsupp.domLCongr (labelPerm π hπ))

theorem permModuleMap_hVec (i : Fin τ.rank) :
    (permModuleMap hπ K : Module.End K (RootModule τ K)) (hVec τ K i) = hVec τ K (π i) := by
  simp [permModuleMap, hVec, labelPerm]

theorem permModuleMap_rootVec (α : Fin τ.rank → ℤ) (hα : IsRoot τ α) :
    (permModuleMap hπ K : Module.End K (RootModule τ K)) (rootVec τ K α) =
      rootVec τ K (permLattice π α) := by
  simp [permModuleMap, rootVec, hα, hα.permLattice hπ, labelPerm]

theorem permModuleMap_apply_rootVec (β : Fin τ.rank → ℤ) :
    (permModuleMap hπ K : Module.End K (RootModule τ K)) (rootVec τ K β) =
      rootVec τ K (permLattice π β) := by
  by_cases hβ : IsRoot τ β
  · exact permModuleMap_rootVec hπ K β hβ
  · have hβ' : ¬IsRoot τ (permLattice π β) := (isRoot_permLattice_iff hπ).not.2 hβ
    simp [rootVec, hβ, hβ']

theorem permModuleMap_mul {π' : Equiv.Perm (Fin τ.rank)}
    (hπ' : ∀ i j, τ.cartan (π' i) (π' j) = τ.cartan i j)
    (hππ' : ∀ i j, τ.cartan ((π * π') i) ((π * π') j) = τ.cartan i j) :
    permModuleMap hπ K * permModuleMap hπ' K = permModuleMap hππ' K := by
  refine Units.ext (rootModule_end_ext (fun j => ?_) fun α _ => ?_)
  · rw [Units.val_mul, Module.End.mul_apply, permModuleMap_hVec, permModuleMap_hVec,
      permModuleMap_hVec, Equiv.Perm.mul_apply]
  · rw [Units.val_mul, Module.End.mul_apply, permModuleMap_apply_rootVec,
      permModuleMap_apply_rootVec, permModuleMap_apply_rootVec]
    rfl

theorem permModuleMap_one (h1 : ∀ i j, τ.cartan ((1 : Equiv.Perm (Fin τ.rank)) i)
    ((1 : Equiv.Perm (Fin τ.rank)) j) = τ.cartan i j) :
    permModuleMap h1 K = 1 := by
  refine Units.ext (rootModule_end_ext (fun j => ?_) fun α _ => ?_)
  · rw [permModuleMap_hVec]
    rfl
  · rw [permModuleMap_apply_rootVec]
    rfl

theorem permModuleMap_congr {π' : Equiv.Perm (Fin τ.rank)} (h : π = π')
    (hπ' : ∀ i j, τ.cartan (π' i) (π' j) = τ.cartan i j) :
    permModuleMap hπ K = permModuleMap hπ' K := by
  subst h
  rfl

theorem diagramMap_eq_permModuleMap (t : TwistTag) :
    diagramMap t K = permModuleMap t.cartan_perm K :=
  rfl

theorem permModuleMap_mul_xCoeff (i : Fin τ.rank) (k : ℕ) :
    (permModuleMap hπ K : Module.End K (RootModule τ K)) * xCoeff τ K i k =
      xCoeff τ K (π i) k * (permModuleMap hπ K : Module.End K (RootModule τ K)) := by
  refine rootModule_end_ext (fun j => ?_) (fun α hα => ?_)
  · simp only [Module.End.mul_apply, permModuleMap_hVec, xCoeff_hVec, hπ]
    split_ifs <;> simp [permModuleMap_hVec, permModuleMap_apply_rootVec, permLattice_single]
  · simp only [Module.End.mul_apply, permModuleMap_apply_rootVec]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [permLattice_single, xCoeff_rootVec_single, xCoeff_rootVec_single]
      split_ifs <;> simp [permModuleMap_apply_rootVec, permLattice_single]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [permLattice_neg_single, xCoeff_rootVec_neg_single, xCoeff_rootVec_neg_single]
      split_ifs <;> simp [permModuleMap_apply_rootVec, permModuleMap_hVec, permLattice_single,
        permLattice_neg_single]
    have hα' := hα.permLattice hπ
    have h₁' : permLattice π α ≠ Pi.single (π i) 1 := by
      rw [← permLattice_single]
      exact (permLattice_injective _).ne h₁
    have h₂' : permLattice π α ≠ -Pi.single (π i) 1 := by
      rw [← permLattice_neg_single]
      exact (permLattice_injective _).ne h₂
    rw [xCoeff_rootVec_of_ne i k hα h₁ h₂, xCoeff_rootVec_of_ne (π i) k hα' h₁' h₂',
      map_smul, permModuleMap_apply_rootVec, permLattice_add_smul_single,
      stringDown_permLattice hπ]

theorem permModuleMap_mul_yCoeff (i : Fin τ.rank) (k : ℕ) :
    (permModuleMap hπ K : Module.End K (RootModule τ K)) * yCoeff τ K i k =
      yCoeff τ K (π i) k * (permModuleMap hπ K : Module.End K (RootModule τ K)) := by
  refine rootModule_end_ext (fun j => ?_) (fun α hα => ?_)
  · simp only [Module.End.mul_apply, permModuleMap_hVec, yCoeff_hVec, hπ]
    split_ifs <;> simp [permModuleMap_hVec, permModuleMap_apply_rootVec, permLattice_neg_single]
  · simp only [Module.End.mul_apply, permModuleMap_apply_rootVec]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [permLattice_neg_single, yCoeff_rootVec_neg_single, yCoeff_rootVec_neg_single]
      split_ifs <;> simp [permModuleMap_apply_rootVec, permLattice_neg_single]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [permLattice_single, yCoeff_rootVec_single, yCoeff_rootVec_single]
      split_ifs <;> simp [permModuleMap_apply_rootVec, permModuleMap_hVec, permLattice_single,
        permLattice_neg_single]
    have hα' := hα.permLattice hπ
    have h₁' : permLattice π α ≠ Pi.single (π i) 1 := by
      rw [← permLattice_single]
      exact (permLattice_injective _).ne h₁
    have h₂' : permLattice π α ≠ -Pi.single (π i) 1 := by
      rw [← permLattice_neg_single]
      exact (permLattice_injective _).ne h₂
    rw [yCoeff_rootVec_of_ne i k hα h₁ h₂, yCoeff_rootVec_of_ne (π i) k hα' h₁' h₂',
      map_smul, permModuleMap_apply_rootVec, permLattice_sub_smul_single,
      stringUp_permLattice hπ]

theorem permModuleMap_mul_xOp (i : Fin τ.rank) (c : K) :
    (permModuleMap hπ K : Module.End K (RootModule τ K)) * xOp τ K i c =
      xOp τ K (π i) c * (permModuleMap hπ K : Module.End K (RootModule τ K)) := by
  rw [xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, permModuleMap_mul_xCoeff]

theorem permModuleMap_mul_yOp (i : Fin τ.rank) (c : K) :
    (permModuleMap hπ K : Module.End K (RootModule τ K)) * yOp τ K i c =
      yOp τ K (π i) c * (permModuleMap hπ K : Module.End K (RootModule τ K)) := by
  rw [yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, permModuleMap_mul_yCoeff]

theorem conj_permModuleMap_xUnit (i : Fin τ.rank) (c : K) :
    MulAut.conj (permModuleMap hπ K) (xUnit τ K i c) = xUnit τ K (π i) c := by
  refine Units.ext ?_
  rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, coe_xUnit, coe_xUnit,
    permModuleMap_mul_xOp, mul_assoc, Units.mul_inv, mul_one]

theorem conj_permModuleMap_yUnit (i : Fin τ.rank) (c : K) :
    MulAut.conj (permModuleMap hπ K) (yUnit τ K i c) = yUnit τ K (π i) c := by
  refine Units.ext ?_
  rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, coe_yUnit, coe_yUnit,
    permModuleMap_mul_yOp, mul_assoc, Units.mul_inv, mul_one]

theorem conj_permModuleMap_weylElt (i : Fin τ.rank) (u : Kˣ) :
    MulAut.conj (permModuleMap hπ K) (weylElt τ K i u) = weylElt τ K (π i) u := by
  rw [weylElt_eq_xUnit_mul, map_mul, map_mul, conj_permModuleMap_xUnit, conj_permModuleMap_yUnit,
    weylElt_eq_xUnit_mul]

theorem conj_permModuleMap_torusElt (i : Fin τ.rank) (u : Kˣ) :
    MulAut.conj (permModuleMap hπ K) (torusElt τ K i u) = torusElt τ K (π i) u := by
  rw [torusElt, map_mul, conj_permModuleMap_weylElt, conj_permModuleMap_weylElt, torusElt]

theorem entrywise_permModuleMap (σ : K →+* K) :
    entrywise σ (permModuleMap hπ K : Module.End K (RootModule τ K)) = permModuleMap hπ K := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywise_single]
  simp [permModuleMap]

theorem units_map_entrywiseHom_permModuleMap (σ : K →+* K) :
    Units.map (entrywiseHom σ) (permModuleMap hπ K) = permModuleMap hπ K :=
  Units.ext (entrywise_permModuleMap hπ K σ)

theorem units_map_entrywiseHom_conj_permModuleMap (σ : K →+* K) (g : ModGL τ K) :
    Units.map (entrywiseHom σ) (MulAut.conj (permModuleMap hπ K) g) =
      MulAut.conj (permModuleMap hπ K) (Units.map (entrywiseHom σ) g) := by
  rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    units_map_entrywiseHom_permModuleMap]

include hπ in
theorem foldr_reflect_map_permLattice (ω : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (ω.map π).foldr (reflect τ) (permLattice π v) = permLattice π (ω.foldr (reflect τ) v) := by
  induction ω with
  | nil => rfl
  | cons i ω ih => rw [List.map_cons, List.foldr_cons, List.foldr_cons, ih, permLattice_reflect hπ]

theorem map_conj_permModuleMap_rootSubgroup_single (j : Fin τ.rank) :
    (rootSubgroup τ K (Pi.single j 1)).map (MulAut.conj (permModuleMap hπ K)).toMonoidHom =
      rootSubgroup τ K (Pi.single (π j) 1) := by
  rw [rootSubgroup, rootSubgroup, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    refine ⟨c, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, pinnedX_single, pinnedX_single, conj_permModuleMap_xUnit]
  · rintro ⟨c, rfl⟩
    refine ⟨_, ⟨c, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, pinnedX_single, pinnedX_single, conj_permModuleMap_xUnit]

theorem map_conj_permModuleMap_rootSubgroup {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (rootSubgroup τ K α).map (MulAut.conj (permModuleMap hπ K)).toMonoidHom =
      rootSubgroup τ K (permLattice π α) := by
  obtain ⟨w, j, rfl⟩ := isRoot_iff_exists_smul_single.1 hα
  obtain ⟨ω, -, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  set n : ModGL τ K := (ω.map fun i => weylElt τ K i 1).prod
  have hn : MulAut.conj (permModuleMap hπ K) n = ((ω.map π).map fun i => weylElt τ K i 1).prod := by
    rw [map_list_prod, List.map_map, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun i _ => conj_permModuleMap_weylElt hπ K i 1)
  have hcomp : (MulAut.conj (permModuleMap hπ K)).toMonoidHom.comp (MulAut.conj n).toMonoidHom =
      (MulAut.conj (MulAut.conj (permModuleMap hπ K) n)).toMonoidHom.comp
        (MulAut.conj (permModuleMap hπ K)).toMonoidHom := by
    ext g
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [← map_conj_prod_weylElt_rootSubgroup K ω (isRoot_single τ j), Subgroup.map_map, hcomp,
    ← Subgroup.map_map, map_conj_permModuleMap_rootSubgroup_single, hn,
    map_conj_prod_weylElt_rootSubgroup K _ (isRoot_single τ (π j)), wordProd_smul, wordProd_smul,
    ← permLattice_single, foldr_reflect_map_permLattice hπ]

theorem map_conj_permModuleMap_rootSpan {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) :
    (rootSpan τ K S).map (MulAut.conj (permModuleMap hπ K)).toMonoidHom =
      rootSpan τ K (permLattice π '' S) := by
  simp only [rootSpan, Subgroup.map_iSup, iSup_image]
  exact iSup_congr fun α => iSup_congr fun hα => map_conj_permModuleMap_rootSubgroup hπ K (hS α hα)

include hπ in
theorem image_permLattice_eq {p : ℤ → Prop} :
    permLattice π '' {α | IsRoot τ α ∧ p (height α)} = {α | IsRoot τ α ∧ p (height α)} := by
  ext β
  constructor
  · rintro ⟨α, ⟨hα, hp⟩, rfl⟩
    exact ⟨hα.permLattice hπ, by rwa [height_permLattice]⟩
  · rintro ⟨hβ, hp⟩
    refine ⟨permLattice π.symm β, ⟨hβ.permLattice (cartan_perm_symm hπ), ?_⟩,
      permLattice_permLattice_symm π β⟩
    rwa [height_permLattice]

theorem map_conj_permModuleMap_posUnipotent :
    (posUnipotent τ K).map (MulAut.conj (permModuleMap hπ K)).toMonoidHom = posUnipotent τ K := by
  rw [posUnipotent, map_conj_permModuleMap_rootSpan hπ K fun α hα => hα.1,
    image_permLattice_eq hπ (p := fun h => 0 < h)]

theorem map_conj_permModuleMap_negUnipotent :
    (negUnipotent τ K).map (MulAut.conj (permModuleMap hπ K)).toMonoidHom = negUnipotent τ K := by
  rw [negUnipotent, map_conj_permModuleMap_rootSpan hπ K fun α hα => hα.1,
    image_permLattice_eq hπ (p := fun h => h < 0)]

theorem map_conj_permModuleMap_torusGroup :
    (torusGroup τ K).map (MulAut.conj (permModuleMap hπ K)).toMonoidHom = torusGroup τ K := by
  rw [torusGroup, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨⟨i, u⟩, rfl⟩, rfl⟩
    exact ⟨⟨π i, u⟩, (conj_permModuleMap_torusElt hπ K i u).symm⟩
  · rintro ⟨⟨i, u⟩, rfl⟩
    refine ⟨_, ⟨⟨π.symm i, u⟩, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [conj_permModuleMap_torusElt, Equiv.apply_symm_apply]

theorem map_conj_permModuleMap_adjointGroup :
    (adjointGroup τ K).map (MulAut.conj (permModuleMap hπ K)).toMonoidHom = adjointGroup τ K := by
  rw [adjointGroup, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨h, ⟨i, c, hh | hh⟩, rfl⟩
    · refine ⟨π i, c, Or.inl ?_⟩
      rw [show h = xUnit τ K i c from Units.ext hh, MulEquiv.coe_toMonoidHom,
        conj_permModuleMap_xUnit]
      rfl
    · refine ⟨π i, c, Or.inr ?_⟩
      rw [show h = yUnit τ K i c from Units.ext hh, MulEquiv.coe_toMonoidHom,
        conj_permModuleMap_yUnit]
      rfl
  · rintro ⟨i, c, hg | hg⟩
    · refine ⟨xUnit τ K (π.symm i) c, ⟨π.symm i, c, Or.inl rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, conj_permModuleMap_xUnit, Equiv.apply_symm_apply]
      exact (Units.ext hg).symm
    · refine ⟨yUnit τ K (π.symm i) c, ⟨π.symm i, c, Or.inr rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, conj_permModuleMap_yUnit, Equiv.apply_symm_apply]
      exact (Units.ext hg).symm

end CFSG.RankThree.Chevalley
